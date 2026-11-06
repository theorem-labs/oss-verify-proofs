(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02 YI01 YI03
YI1e YI1i YI57 YI07 YP14 YP15 YP13 YI08 YI0c YI0g YI3h YI3d
YI4v YI46 YI4g YI4c YI4d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_RB : sstate := mkSS PC_RB sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 0 5136 0 0 [mkChunk 112 (CVal 8 (SOff 32%nat 0))] ;
YQ0b.mkRegion (Some 26%nat) 0 3 0 0 [mkChunk 0 (CVal 1 (SOff 33%nat 0)); mkChunk 1 (CVal 1 (SOff 34%nat 0)); mkChunk 2 (CVal 1 (SOff 35%nat 0))] ;
YQ0b.mkRegion (Some 48%nat) 0 4 0 0 [mkChunk 0 (CVal 4 (SOff 36%nat 0))] ;
YQ0b.mkRegion (Some 20%nat) 0 48 40 44 [mkChunk 0 (CVal 8 (SOff 42%nat 0)); mkChunk 8 (CVal 8 (SOff 43%nat 0)); mkChunk 24 (CVal 8 (SOff 44%nat 0)); mkChunk 32 (CVal 8 (SOff 45%nat 0));
mkChunk 40 (CVal 4 (SOff 46%nat 0)); mkChunk 44 (CVal 4 (SOff 47%nat 0))] ;
YQ0b.mkRegion (Some 37%nat) 0 3 0 3 [] ;
YQ0b.mkRegion (Some 38%nat) 0 1 0 1 [] ;
YQ0b.mkRegion (Some 39%nat) 0 4 0 4 [] ;
YQ0b.mkRegion (Some 40%nat) 0 3 0 3 [] ;
YQ0b.mkRegion (Some 41%nat) 0 4 0 4 [] ] None
(mkFacts [(2%nat, mkAF CEIL_MIN (2^63) 4); (10%nat, mkAF 0 (2^24-1) 0); (46%nat, mkAF 0 10000 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
(36%nat, mkAF 0 10000 0); (22%nat, mkAF 0 (2^26) 0); (19%nat, mkAF 0 (2^26) 0); (18%nat, mkAF 0 (2^24) 0); (47%nat, mkAF 521 (2^24) 0)] []
[ (SAlu ALU_ADD (SMd M_MUL (SOff 10%nat 0) (SLit 3)) (SOff 23%nat 0), SOff 37%nat 0);
(SAlu ALU_ADD (SOff 24%nat 0) (SOff 10%nat 0), SOff 38%nat 0);
(SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SOff 10%nat 0) (SLit 2)), SOff 39%nat 0);
(SAlu ALU_ADD (SMd M_MUL (SOff 46%nat 0) (SLit 3)) (SOff 44%nat 0), SOff 40%nat 0);
(SAlu ALU_ADD (SOff 45%nat 0) (SAlu ALU_SLL (SOff 10%nat 0) (SLit 2)), SOff 41%nat 0);
(SAlu ALU_ADD (SOff 43%nat 0) (SOff 22%nat 0), SOff 26%nat 0);
(SAlu ALU_ADD (SOff 42%nat 0) (SOff 19%nat 0), SOff 48%nat 0) ]).
Section d.
Variable API : AllocAPI src2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src2_msyms MR.
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
Local Notation RZ_MEM_ZSUM := (rz_mem_zsum regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_HT := (rz_mem_ht regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_LIVE := (rz_mem_live regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_ARRS := (rz_mem_arrs regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay).
Local Notation RZ_MEM_KEPT := (rz_mem_kept API regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay rest).
Section Rb.
Variables (i ha : Z) (Lc : layout) (Ac : astate) (mdc : Model) (pnew fimg : Z) (imgl : list Z) (C : cht) (T' p1 x1 h1 u1 f1 : Z) (K : htab) (j : Z).
Hypothesis KNEXT : forall regs1 memc K', j + 1 < ch_T C -> AT_REH regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K' (j + 1) ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_REH) memc (seg_rom src2segs)) mdc) POST.
Hypothesis KPOST : forall regs1 memc K', AT_POST regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K' ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_POST) memc (seg_rom src2segs)) mdc) POST.
Theorem RB_stretch : forall regs1 memc, AT_RB regs1 Lc Ac memc mdc i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K j ->
SR src2segs (mkCfg (mkst regs1 (Z_to_bv 64 PC_RB) memc (seg_rom src2segs)) mdc) POST.
Proof.
intros regs1 memc HAT.
destruct HAT as (HINV & HRZF & ((G2 & G3 & G4) & G23 & G24 & G25 & G20 & G9 & G8 & G21) & G18 & G19 & G27 & G26 & G22 & (hh & G10 & Hfs & Hhz) & Hj & Huz & HK & Hcnt & LM & RZB).
pose proof LM as (RZM & S72 & S112 & HCA & HTK & RZS). pose proof HCA as (Af & Ah & Au & Ap & Ax).
pose proof HINV as (HJ & Hinit & Hfrm0 & Hra0 & Hal0 & Htp0 & HRA & Hc8 & Hclo & Hchi & Hcfp & Hro & Hwf & HW & HH & HNmax & Hbf & HB0).
pose proof (RZ_MEM_ARRS _ _ _ _ _ _ _ RZM) as (Bf & Bh & Bu).
pose proof (RZ_MEM_HT _ _ _ _ _ _ _ RZM) as (Hinv & HT & Hch & HTlt). pose proof (RZ_MEM_ZSUM _ _ _ _ _ _ _ RZM) as Hz.
pose proof (RZ_MEM_LIVE _ _ _ _ _ _ _ RZM) as (EhS & EuS & ETS).
pose proof HRZF as (Hfmt & Hi & Hha & ET').
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof (proj1 HJ) as HHc.
pose proof HJ as (_ & _ & _ & _ & _ & Hstk & _). destruct Hstk as (_ & HSTK0 & Hceil & H63 & Hstw).
assert (HRv : RGBA_STK = 24576) by reflexivity. assert (HFv : RGBA_FRAME = 5136) by reflexivity.
pose proof (ts_chain_ok _ Hch) as (RT1 & RT2 & RT3). unfold MAX_TABLE_SIZE in RT1, HTlt.
pose proof (resize_next (ch_T C) Hch HTlt) as (Hch' & HTT' & (RT1' & RT2' & RT3')). rewrite <- ET' in Hch', HTT', RT1', RT2', RT3'. unfold MAX_TABLE_SIZE in RT1'.
pose proof Hinv as ((L1 & L2 & L3 & L4 & L5) & (C1 & C2 & C3) & (B1 & B2 & B3) & I4 & _). rewrite HT in L1, L2, L3, C1, B1.
pose proof HK as ((M1 & M2 & M3 & M4 & M5) & (N1 & N2 & N3) & _). rewrite HTK in M1, M2, M3, M4, M5, N1.
set (T := ch_T C) in *.
unfold RGB_NMAX in HNmax.
destruct (rehash_step_used (ch_H C) (ch_ent C) Hinv K j HK ltac:(rewrite HT; lia) Huz ltac:(rewrite HTK; lia)) as (hh' & Hfs' & Rhh & _ & _ & HK').
rewrite Hfs in Hfs'. injection Hfs' as <-. rewrite HTK in Rhh.
set (col := key (ch_H C) j) in *. set (fq := freq (ch_H C) j) in *. set (cnt := ht_cnt K) in *.
assert (Hcol3 : col3 src2segs memc (ch_h C + 3 * j) col) by (subst col; unfold key; apply (arr8_col3 src2segs memc (ch_h C) (ht_keys (ch_H C)) j Bh); lia).
pose proof Hcol3 as (Q0 & Q1 & Q2 & (Rr & Rg & Rb)).
assert (Hsl : in_slot (ch_H C) j) by (split; [rewrite HT; lia | exact Huz]).
destruct (I4 j Hsl) as (_ & Hnth & Fq1).
pose proof (zsum_pos_le (ch_ent C) _ _ _ (ent_freq_pos (ch_H C) (ch_ent C) Hinv) Hnth) as Fq2. fold fq in Fq1, Fq2.
destruct (arr32_getz src2segs memc (ch_f C) (ht_frequ (ch_H C)) j Bf ltac:(lia)) as [Bfq _]. change (getz (ht_frequ (ch_H C)) j) with fq in Bfq.
assert (Hcnt_i : ht_cnt (ch_H C) <= i + 1) by (pose proof (zsum_ge_length (ch_ent C) (ent_freq_pos (ch_H C) (ch_ent C) Hinv)); lia).
unfold rz_blocks in RZB.
assert (INB : forall b, In b (KEEPB pnew fimg C ++ newb T' p1 x1 h1 u1 f1) -> In b (blocks Lc Ac)) by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact RZB | exact Hb]).
assert (RNG : forall q n, In (q, n) (blocks Lc Ac) -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling).
{ intros q n Hq Hn. destruct (heap_blocks_range src2_msyms MR LAWS Lc Ac memc mdc q n HHc Hq Hn) as (X0 & X1 & _). lia. }
destruct (RNG (ch_c C) CHT_SIZE ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity) ltac:(unfold CHT_SIZE; lia)) as [Rc0 Rc1]. unfold CHT_SIZE in Rc1.
destruct (RNG (ch_h C) (3 * T) ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rh0 Rh1].
destruct (RNG (ch_u C) T ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Ru0 Ru1].
destruct (RNG (ch_f C) (4 * T) ltac:(apply INB; apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rf0 Rf1].
destruct (RNG p1 (3 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rp0 Rp1].
destruct (RNG x1 (4 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rx0 Rx1].
destruct (RNG h1 (3 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rk0 Rk1].
destruct (RNG u1 T' ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rv0 Rv1].
destruct (RNG f1 (4 * T') ltac:(apply INB; apply in_app_iff; right; cbn; auto 10) ltac:(lia)) as [Rw0 Rw1].
assert (NSEP : forall l1 x l2 y, newb T' p1 x1 h1 u1 f1 = l1 ++ x :: l2 -> In y (KEEPB pnew fimg C ++ l1 ++ l2) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x).
{ intros l1 x l2 y E Hy. apply (perm_sep API Lc Ac memc mdc x y (KEEPB pnew fimg C ++ l1) l2 HHc); [| rewrite <- app_assoc; exact Hy].
rewrite <- app_assoc. rewrite <- E. exact RZB. }
assert (CSEP : forall y, In y (BASE0 ++ [(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) -> ch_c C + 48 <= fst y \/ fst y + snd y <= ch_c C).
{ intros y Hy. pose proof (perm_sep API Lc Ac memc mdc (ch_c C, CHT_SIZE) y (BASE0 ++ [(pnew, fmt * N); (fimg, N)]) ([(ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. unfold CHT_SIZE in X. apply X.
- unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB.
- apply in_app_iff in Hy. apply in_app_iff. destruct Hy as [Hy|Hy]; [left; apply in_app_iff; left; exact Hy | right; exact Hy]. }
pose proof (fun y => NSEP [] (p1, 3 * T') [(x1, 4 * T'); (h1, 3 * T'); (u1, T'); (f1, 4 * T')] y eq_refl) as SP1.
pose proof (fun y => NSEP [(p1, 3 * T')] (x1, 4 * T') [(h1, 3 * T'); (u1, T'); (f1, 4 * T')] y eq_refl) as SX1.
pose proof (fun y => NSEP [(p1, 3 * T'); (x1, 4 * T')] (h1, 3 * T') [(u1, T'); (f1, 4 * T')] y eq_refl) as SH1.
pose proof (fun y => NSEP [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T')] (u1, T') [(f1, 4 * T')] y eq_refl) as SU1.
pose proof (fun y => NSEP [(p1, 3 * T'); (x1, 4 * T'); (h1, 3 * T'); (u1, T')] (f1, 4 * T') [] y eq_refl) as SF1.
cbn [fst snd] in SP1, SX1, SH1, SU1, SF1.
assert (FHsep : ch_f C + 4 * T <= ch_h C \/ ch_h C + 3 * T <= ch_f C).
{ pose proof (perm_sep API Lc Ac memc mdc (ch_f C, 4 * T) (ch_h C, 3 * T) (BASE0 ++ [(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE)]) ([(ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) HHc) as X.
cbn [fst snd] in X. apply X; [| apply in_app_iff; right; left; reflexivity].
unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- !app_assoc. exact RZB. }
assert (FLD : forall jj v, nth_error [ch_f C; ch_hS C; ch_uS C; p1; x1; ht_cnt K; ch_TS C] jj = Some v ->
forall fd, nth_error LAY_Cht jj = Some fd -> field_ok src2segs memc (ch_c C) fd v).
{ intros jj v Hv fd Hf. exact (obj_at_nth src2segs memc (ch_c C) LAY_Cht _ jj fd v RZS Hf Hv). }
pose proof (FLD 0%nat _ eq_refl _ eq_refl) as [B0 _]. pose proof (FLD 1%nat _ eq_refl _ eq_refl) as [B1s _]. pose proof (FLD 3%nat _ eq_refl _ eq_refl) as [B3s _].
pose proof (FLD 4%nat _ eq_refl _ eq_refl) as [B4s _]. pose proof (FLD 5%nat _ eq_refl _ eq_refl) as [B5s _]. pose proof (FLD 6%nat _ eq_refl _ eq_refl) as [B6s _]. clear FLD.
cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in B0, B1s, B3s, B4s, B5s, B6s. rewrite Z.add_0_r in B0. rewrite EhS in B1s. rewrite ETS in B6s. fold cnt in B5s.
set (E := Ereg regs1 (map (Z_to_bv 64) [f1; cR col; cG col; cB col; fq; h1 + 3 * hh; u1 + hh; f1 + 4 * hh; p1 + 3 * cnt; x1 + 4 * hh; ch_f C; ch_h C; p1; x1; cnt; T; ch_f C + 4 * j] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall jj v, nth_error [f1; cR col; cG col; cB col; fq; h1 + 3 * hh; u1 + hh; f1 + 4 * hh; p1 + 3 * cnt; x1 + 4 * hh; ch_f C; ch_h C; p1; x1; cnt; T; ch_f C + 4 * j] jj = Some v -> ew E (32 + jj) = Z_to_bv 64 v)
by (intros jj v Hjv; subst E; apply Ereg_vals; exact Hjv).
assert (HE32 : ew E 32 = Z_to_bv 64 f1) by exact (HV 0%nat _ eq_refl).
assert (HE33 : ew E 33 = Z_to_bv 64 (cR col)) by exact (HV 1%nat _ eq_refl).
assert (HE34 : ew E 34 = Z_to_bv 64 (cG col)) by exact (HV 2%nat _ eq_refl).
assert (HE35 : ew E 35 = Z_to_bv 64 (cB col)) by exact (HV 3%nat _ eq_refl).
assert (HE36 : ew E 36 = Z_to_bv 64 fq) by exact (HV 4%nat _ eq_refl).
assert (HE37 : ew E 37 = Z_to_bv 64 (h1 + 3 * hh)) by exact (HV 5%nat _ eq_refl).
assert (HE38 : ew E 38 = Z_to_bv 64 (u1 + hh)) by exact (HV 6%nat _ eq_refl).
assert (HE39 : ew E 39 = Z_to_bv 64 (f1 + 4 * hh)) by exact (HV 7%nat _ eq_refl).
assert (HE40 : ew E 40 = Z_to_bv 64 (p1 + 3 * cnt)) by exact (HV 8%nat _ eq_refl).
assert (HE41 : ew E 41 = Z_to_bv 64 (x1 + 4 * hh)) by exact (HV 9%nat _ eq_refl).
assert (HE42 : ew E 42 = Z_to_bv 64 (ch_f C)) by exact (HV 10%nat _ eq_refl).
assert (HE43 : ew E 43 = Z_to_bv 64 (ch_h C)) by exact (HV 11%nat _ eq_refl).
assert (HE44 : ew E 44 = Z_to_bv 64 p1) by exact (HV 12%nat _ eq_refl).
assert (HE45 : ew E 45 = Z_to_bv 64 x1) by exact (HV 13%nat _ eq_refl).
assert (HE46 : ew E 46 = Z_to_bv 64 cnt) by exact (HV 14%nat _ eq_refl).
assert (HE47 : ew E 47 = Z_to_bv 64 T) by exact (HV 15%nat _ eq_refl).
assert (HE48 : ew E 48 = Z_to_bv 64 (ch_f C + 4 * j)) by exact (HV 16%nat _ eq_refl).
assert (HU2 : bv_unsigned (ew E 2) = SP) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; unfold sp, sp0 in *; lia).
assert (HE26 : ew E 26 = Z_to_bv 64 (ch_h C + 3 * j)) by (rewrite (HE 26%nat 26%bv eq_refl); exact G26).
assert (HU26 : bv_unsigned (ew E 26) = ch_h C + 3 * j) by (rewrite HE26; apply unsigned_lit_small; lia).
assert (HU48 : bv_unsigned (ew E 48) = ch_f C + 4 * j) by (rewrite HE48; apply unsigned_lit_small; lia).
assert (HE20 : ew E 20 = Z_to_bv 64 (ch_c C)) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (HU20 : bv_unsigned (ew E 20) = ch_c C) by (rewrite HE20; apply unsigned_lit_small; lia).
assert (HU37 : bv_unsigned (ew E 37) = h1 + 3 * hh) by (rewrite HE37; apply unsigned_lit_small; lia).
assert (HU38 : bv_unsigned (ew E 38) = u1 + hh) by (rewrite HE38; apply unsigned_lit_small; lia).
assert (HU39 : bv_unsigned (ew E 39) = f1 + 4 * hh) by (rewrite HE39; apply unsigned_lit_small; lia).
assert (HU40 : bv_unsigned (ew E 40) = p1 + 3 * cnt) by (rewrite HE40; apply unsigned_lit_small; lia).
assert (HU41 : bv_unsigned (ew E 41) = x1 + 4 * hh) by (rewrite HE41; apply unsigned_lit_small; lia).
assert (HE10 : ew E 10 = Z_to_bv 64 hh) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
assert (HE23 : ew E 23 = Z_to_bv 64 h1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE24 : ew E 24 = Z_to_bv 64 u1) by (rewrite (HE 24%nat 24%bv eq_refl); exact G24).
assert (HE18 : ew E 18 = Z_to_bv 64 j) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (HE19 : ew E 19 = Z_to_bv 64 (4 * j)) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (HE27 : ew E 27 = Z_to_bv 64 (3 * j)) by (rewrite (HE 27%nat 27%bv eq_refl); exact G27).
assert (HE22 : ew E 22 = Z_to_bv 64 (3 * j)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (Hsp16 : SP mod 16 = 0).
{ unfold sp, sp0, RGBA_FRAME. replace (spZ regs0 - 5136) with (spZ regs0 + (-321) * 16) by lia. rewrite Z.mod_add; [exact Hal0 | lia]. }
assert (WRT : forall b n a, In (b, n) ((ch_c C, CHT_SIZE) :: newb T' p1 x1 h1 u1 f1) -> b <= a < b + n -> writable_at src2segs memc a).
{ intros b n a Hb Ha. apply (present_writable src2_msyms). replace a with (b + (a - b)) by lia.
apply (proj1 (heap_blocks src2_msyms MR LAWS Lc Ac memc mdc b n (a - b) HHc ltac:(apply INB; destruct Hb as [<-|Hb]; [apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity | apply in_app_iff; right; exact Hb]) ltac:(lia))). }
assert (HS : st_ok src2segs E ss_RB (mkst regs1 (Z_to_bv 64 PC_RB) memc (seg_rom src2segs))).
{ unfold ss_RB. subst E. apply entry_st_ok_full.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]]]]]];
unfold region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
+ rewrite HU2. split; [unfold sp, sp0 in *; lia|]. split; [unfold sp, sp0 in *; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ f1); [cbn [sv_denot]; rewrite Z.add_0_r, HE32, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. apply val_mem_word_mem. exact S112.
+ rewrite HU26. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (CK : forall k nn v, mbyte src2segs memc (ch_h C + 3 * j + k) = Some (Z_to_bv 8 v) -> 0 <= v < 256 ->
ew (Ereg regs1 (map (Z_to_bv 64) [f1; cR col; cG col; cB col; fq; h1 + 3 * hh; u1 + hh; f1 + 4 * hh; p1 + 3 * cnt; x1 + 4 * hh; ch_f C; ch_h C; p1; x1; cnt; T; ch_f C + 4 * j] ++ [])) nn = Z_to_bv 64 v ->
chunk_ok src2segs (Ereg regs1 (map (Z_to_bv 64) [f1; cR col; cG col; cB col; fq; h1 + 3 * hh; u1 + hh; f1 + 4 * hh; p1 + 3 * cnt; x1 + 4 * hh; ch_f C; ch_h C; p1; x1; cnt; T; ch_f C + 4 * j] ++ [])) memc (ch_h C + 3 * j) (mkChunk k (CVal 1 (SOff nn 0)))).
{ intros k nn v Hb Hv Hn. eapply (chunk_ok_val _ _ _ _ _ _ _ v); [cbn [sv_denot]; rewrite Z.add_0_r, Hn, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; exact Hv | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op]. apply val_mem_byte; [exact Hb | exact Hv]. }
apply Forall_cons; [apply (CK 0 33%nat (cR col)); [rewrite Z.add_0_r; exact Q0 | lia | exact HE33]|].
apply Forall_cons; [apply (CK 1 34%nat (cG col)); [exact Q1 | lia | exact HE34]|].
apply Forall_cons; [apply (CK 2 35%nat (cB col)); [exact Q2 | lia | exact HE35]|]. apply Forall_nil.
+ rewrite HU48. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val _ _ _ _ _ _ _ fq); [cbn [sv_denot]; rewrite Z.add_0_r, HE36, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact Bfq.
+ rewrite HU20. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (WRT (ch_c C) CHT_SIZE); [left; reflexivity | unfold CHT_SIZE; lia]|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]].
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_f C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE42, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. exact B0.
* eapply (chunk_ok_val _ _ _ _ _ _ _ (ch_h C)); [cbn [sv_denot]; rewrite Z.add_0_r, HE43, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B1s.
* eapply (chunk_ok_val _ _ _ _ _ _ _ p1); [cbn [sv_denot]; rewrite Z.add_0_r, HE44, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B3s.
* eapply (chunk_ok_val _ _ _ _ _ _ _ x1); [cbn [sv_denot]; rewrite Z.add_0_r, HE45, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B4s.
* eapply (chunk_ok_val _ _ _ _ _ _ _ cnt); [cbn [sv_denot]; rewrite Z.add_0_r, HE46, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B5s.
* eapply (chunk_ok_val _ _ _ _ _ _ _ T); [cbn [sv_denot]; rewrite Z.add_0_r, HE47, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact B6s.
+ rewrite HU37. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (WRT h1 (3 * T')); [right; cbn; auto 10 | lia].
+ rewrite HU38. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (WRT u1 T'); [right; cbn; auto 10 | lia].
+ rewrite HU39. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (WRT f1 (4 * T')); [right; cbn; auto 10 | lia].
+ rewrite HU40. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (WRT p1 (3 * T')); [right; cbn; auto 10 | lia].
+ rewrite HU41. split; [lia|]. split; [lia|]. split; [| constructor]. intros o Ho. apply (WRT x1 (4 * T')); [right; cbn; auto 10 | lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU26, HU48, HU20, HU37, HU38, HU39, HU40, HU41.
pose proof (CSEP (ch_h C, 3 * T) ltac:(apply in_app_iff; right; cbn; auto 10)) as Y1. pose proof (CSEP (ch_f C, 4 * T) ltac:(apply in_app_iff; right; cbn; auto 10)) as Y2.
pose proof (CSEP (p1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y3. pose proof (CSEP (x1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y4.
pose proof (CSEP (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y5. pose proof (CSEP (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y6.
pose proof (CSEP (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 20)) as Y7.
pose proof (SP1 (ch_h C, 3 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z1.
pose proof (SP1 (ch_f C, 4 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z2.
pose proof (SX1 (ch_h C, 3 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z3.
pose proof (SX1 (ch_f C, 4 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z4.
pose proof (SH1 (ch_h C, 3 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z5.
pose proof (SH1 (ch_f C, 4 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z6.
pose proof (SU1 (ch_h C, 3 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z7.
pose proof (SU1 (ch_f C, 4 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z8.
pose proof (SF1 (ch_h C, 3 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z9.
pose proof (SF1 (ch_f C, 4 * T) ltac:(apply in_app_iff; left; unfold keepb; apply in_app_iff; right; apply in_app_iff; right; cbn; auto 10)) as Z10.
pose proof (SP1 (x1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W1. pose proof (SP1 (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W2.
pose proof (SP1 (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W3. pose proof (SP1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W4.
pose proof (SX1 (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W5. pose proof (SX1 (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W6.
pose proof (SX1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W7. pose proof (SH1 (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W8.
pose proof (SH1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W9. pose proof (SU1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as W10.
cbn [fst snd] in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, W1, W2, W3, W4, W5, W6, W7, W8, W9, W10.
unfold sp, sp0 in *.
repeat match goal with |- _ /\ _ => split | |- True => exact I end.
all: try (clear - Hceil HRv HFv Hj Rhh N1 Hcnt Hcnt_i Rh1 Rf1 Rc1 Rp1 Rx1 Rk1 Rv1 Rw1; lia).
all: first [ clear - FHsep Hj; lia | clear - Y1 Hj; lia | clear - Y2 Hj; lia | clear - Z1 Hj Rhh; lia | clear - Z3 Hj Rhh; lia | clear - Z5 Hj Rhh; lia | clear - Z7 Hj Rhh; lia | clear - Z9 Hj Rhh; lia
| clear - Z2 Hj Rhh N1 Hcnt Hcnt_i; lia | clear - Z4 Hj Rhh; lia | clear - Z6 Hj Rhh; lia | clear - Z8 Hj Rhh; lia | clear - Z10 Hj Rhh; lia
| clear - Y3 N1; lia | clear - Y4 Rhh; lia | clear - Y5 Rhh; lia | clear - Y6 Rhh; lia | clear - Y7 Rhh; lia
| clear - W1 Rhh N1 Hcnt Hcnt_i; lia | clear - W2 Rhh N1 Hcnt Hcnt_i; lia | clear - W3 Rhh N1 Hcnt Hcnt_i; lia | clear - W4 Rhh N1 Hcnt Hcnt_i; lia
| clear - W5 Rhh; lia | clear - W6 Rhh; lia | clear - W7 Rhh; lia | clear - W8 Rhh; lia | clear - W9 Rhh; lia | clear - W10 Rhh; lia
| clear - Z1 Hj Rhh N1 Hcnt Hcnt_i; lia | clear - Z3 Hj Rhh N1 Hcnt; lia ].
- unfold facts_ok. cbn [f_atoms f_conds f_alias]. split; [| split; [exact I|]].
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, (ew_Ereg_nat regs1 _ 10 10%bv eq_refl), G10, HE46, HE33, HE34, HE35, HE36, (ew_Ereg_nat regs1 _ 22 22%bv eq_refl), G22, (ew_Ereg_nat regs1 _ 19 19%bv eq_refl), G19, (ew_Ereg_nat regs1 _ 18 18%bv eq_refl), G18, HE47.
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r. unfold sp, sp0 in *.
try pose proof (proj1 alloc_ceiling_val) as HacR; clear - HacR Hceil H63 HRv HFv Hsp16 Rhh RT1' N1 Hcnt Hcnt_i Hi HNmax Rr Rg Rb Fq1 Fq2 Hz Hj RT1. repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
+ cbn [alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]]].
* apply U_inj. rewrite (U_atom _ 37 (h1 + 3 * hh) HE37) by lia. apply (U_mul3_add_r _ 10 23 hh h1); [exact HE10 | lia | exact HE23 | lia | lia].
* apply U_inj. rewrite (U_atom _ 38 (u1 + hh) HE38) by lia. apply (U_add_atom _ 24 u1 _ hh); [exact HE24 | lia | apply (U_atom _ 10 hh HE10); lia | lia | lia].
* apply U_inj. rewrite (U_atom _ 39 (f1 + 4 * hh) HE39) by lia. apply (U_add_sll2_r _ 10 32 hh f1); [exact HE10 | lia | exact HE32 | lia | lia].
* apply U_inj. rewrite (U_atom _ 40 (p1 + 3 * cnt) HE40) by lia. apply (U_mul3_add_r _ 46 44 cnt p1); [exact HE46 | lia | exact HE44 | lia | lia].
* apply U_inj. rewrite (U_atom _ 41 (x1 + 4 * hh) HE41) by lia. apply (U_add_sll2_r _ 10 45 hh x1); [exact HE10 | lia | exact HE45 | lia | lia].
* apply U_inj. rewrite (U_atom _ 26 (ch_h C + 3 * j) HE26) by lia. apply (U_add_atom _ 43 (ch_h C) _ (3 * j)); [exact HE43 | lia | apply (U_atom _ 22 (3 * j) HE22); lia | lia | lia].
* apply U_inj. rewrite (U_atom _ 48 (ch_f C + 4 * j) HE48) by lia. apply (U_add_atom _ 42 (ch_f C) _ (4 * j)); [exact HE42 | lia | apply (U_atom _ 19 (4 * j) HE19); lia | lia | lia]. }
assert (EA0 : env_agree 32 (Ereg regs1 []) E).
{ subst E. split; [intros n Hn; rewrite !ew_Ereg_lt by exact Hn; reflexivity | reflexivity]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 PC_RB) memc (seg_rom src2segs))) in HJ. clearbody E. clear HV.
assert (WRN : forall b n a, In (b, n) ((ch_c C, CHT_SIZE) :: newb T' p1 x1 h1 u1 f1) -> b <= a < b + n -> wr_byte RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac) a).
{ intros b n a Hb Ha. apply (wr_byte_tmp API L A regs0 r g bef beffmt s N img fmt rest Lc Ac memc mdc ([(pnew, fmt * N); (fimg, N)] ++ [(ch_c C, CHT_SIZE); (ch_f C, 4 * T); (ch_h C, 3 * T); (ch_u C, T)] ++ newb T' p1 x1 h1 u1 f1) b n a HHc); [| exact HB0 | | | exact Ha].
- unfold keepb in RZB. rewrite <- !app_assoc in RZB. rewrite <- ?app_assoc. exact RZB.
- destruct Hb as [E0|Hb]; [rewrite <- E0; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity | apply in_app_iff; right; apply in_app_iff; right; exact Hb].
- destruct Hb as [E0|Hb]; [injection E0 as <- <-; unfold CHT_SIZE; lia|]. unfold newb in Hb. cbn [In] in Hb. decompose [or] Hb; try contradiction; match goal with E0 : _ = (b, n) |- _ => injection E0 as <- <- end; lia. }
jrun LAWS src2tbl_ok HS HJ.
{ apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | exact HU20 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN (ch_c C) CHT_SIZE); [left; reflexivity | unfold CHT_SIZE; lia] |].
eapply wr_ok_cons_gen; [reflexivity | exact HU37 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN h1 (3 * T')); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | exact HU38 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN u1 T'); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | exact HU39 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN f1 (4 * T')); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | exact HU40 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN p1 (3 * T')); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | exact HU41 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN x1 (4 * T')); [right; cbn; auto 10 | lia] |].
apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
set (K' := ht_ins K hh col fq).
assert (HTK' : ht_T K' = T') by (subst K'; exact HTK).
assert (FACTS : forall mem' : word -> option byte,
(forall a, 0 <= a < 2 ^ 64 -> ~ rb_w f1 h1 u1 p1 x1 K hh a -> ~ (ch_c C + 40 <= a < ch_c C + 44) -> mbyte src2segs mem' a = mbyte src2segs memc a) ->
val_mem src2segs mem' (ch_c C + 40) 4 (cnt + 1) ->
mbyte src2segs mem' (h1 + 3 * hh) = Some (Z_to_bv 8 (cR col)) -> mbyte src2segs mem' (h1 + 3 * hh + 1) = Some (Z_to_bv 8 (cG col)) -> mbyte src2segs mem' (h1 + 3 * hh + 2) = Some (Z_to_bv 8 (cB col)) ->
mbyte src2segs mem' (u1 + hh) = Some (Z_to_bv 8 1) -> val_mem src2segs mem' (f1 + 4 * hh) 4 fq ->
mbyte src2segs mem' (p1 + 3 * cnt) = Some (Z_to_bv 8 (cR col)) -> mbyte src2segs mem' (p1 + 3 * cnt + 1) = Some (Z_to_bv 8 (cG col)) -> mbyte src2segs mem' (p1 + 3 * cnt + 2) = Some (Z_to_bv 8 (cB col)) ->
val_mem src2segs mem' (x1 + 4 * hh) 4 cnt ->
loop_mem regs0 r cfp g wfn ctx path attr gen loops W H bef beffmt cur s N img fmt fattr delay mem' i ha pnew fimg imgl C T' p1 x1 h1 u1 f1 K').
{ intros mem' KEEP S4 K0 K1 K2 U1 F4 P0 P1 P2 X4.
assert (HCA' : cht_arrays src2segs mem' f1 h1 u1 p1 x1 K').
{ subst K'. apply (cht_arrays_ins memc mem' f1 h1 u1 p1 x1 K hh col fq HCA);
rewrite ?HTK; fold cnt; [lia | lia | lia | lia | lia | lia | lia | lia | exact (conj Rr (conj Rg Rb)) | lia | lia | | | | | | | | | | | exact K0 | exact K1 | exact K2 | exact P0 | exact P1 | exact P2 | exact U1 | exact X4 | exact F4 | ].
- pose proof (W' := SP1 (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SH1 (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SX1 (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SH1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SP1 (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SP1 (x1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SP1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SX1 (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SU1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- pose proof (W' := SX1 (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)). cbn [fst snd] in W'. clear - W'. intros a [X Y]. lia.
- intros a Ha Hna. apply KEEP; [| exact Hna |].
+ clear - Ha Rp0 Rp1 Rx0 Rx1 Rk0 Rk1 Rv0 Rv1 Rw0 Rw1 Hac. lia.
+ pose proof (CSEP (p1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y3. pose proof (CSEP (x1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y4.
pose proof (CSEP (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y5. pose proof (CSEP (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y6.
pose proof (CSEP (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 20)) as Y7. cbn [fst snd] in Y3, Y4, Y5, Y6, Y7. clear - Ha Y3 Y4 Y5 Y6 Y7. lia. }
assert (KH : forall a, alloc_ceiling <= a < 2 ^ 64 -> mbyte src2segs mem' a = mbyte src2segs memc a).
{ intros a Ha. apply KEEP; [lia | unfold rb_w; rewrite ?HTK; fold cnt; clear - Ha Rhh N1 Rp1 Rx1 Rk1 Rv1 Rw1; lia | lia]. }
unfold loop_mem.
split. { apply (RZ_MEM_KEPT Lc Ac memc mem' mdc i ha pnew fimg imgl C _ i HHc ltac:(unfold sp, sp0 in *; lia) ltac:(unfold sp, sp0 in *; lia) Hfmt RZB RZM); [| | exact Hz].
- intros a Ha Hs _ _. apply KH. exact Ha.
- intros b n k Hb Hk.
assert (Hkb : In (b, n) (KEEPB pnew fimg C)) by (apply (keepb_sub r g bef beffmt s N img fmt rest); exact Hb).
pose proof (SP1 (b, n) ltac:(apply in_app_iff; left; exact Hkb)) as V1. pose proof (SX1 (b, n) ltac:(apply in_app_iff; left; exact Hkb)) as V2.
pose proof (SH1 (b, n) ltac:(apply in_app_iff; left; exact Hkb)) as V3. pose proof (SU1 (b, n) ltac:(apply in_app_iff; left; exact Hkb)) as V4.
pose proof (SF1 (b, n) ltac:(apply in_app_iff; left; exact Hkb)) as V5.
pose proof (CSEP (b, n) ltac:(apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply in_app_iff; left; exact Hb])) as V6.
cbn [fst snd] in V1, V2, V3, V4, V5, V6.
destruct (RNG b n ltac:(apply INB; apply in_app_iff; left; exact Hkb) ltac:(lia)) as [Rb0 Rb1].
apply KEEP; [clear - Hk Rb0 Rb1 Hac; lia | unfold rb_w; rewrite ?HTK; fold cnt; clear - Hk V1 V2 V3 V4 V5 Rhh N1; lia | clear - Hk V6; lia]. }
split. { unfold slot, SL_72 in S72 |- *. apply (val_mem_kept8 memc); [exact S72|]. intros k Hk. apply KH. unfold sp, sp0 in *; lia. }
split. { unfold slot, SL_112 in S112 |- *. apply (val_mem_kept8 memc); [exact S112|]. intros k Hk. apply KH. unfold sp, sp0 in *; lia. }
split; [exact HCA'|]. split; [exact HTK'|].
subst K'. cbn [ht_cnt ht_ins]. fold cnt. apply (obj_at_cht_set_cnt memc mem' (ch_c C) _ _ _ _ _ cnt _ (cnt + 1) RZS); [| exact S4 | lia].
intros a Ha Hna. apply KEEP; [lia | | exact Hna].
pose proof (CSEP (p1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y3. pose proof (CSEP (x1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y4.
pose proof (CSEP (h1, 3 * T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y5. pose proof (CSEP (u1, T') ltac:(apply in_app_iff; right; cbn; auto 10)) as Y6.
pose proof (CSEP (f1, 4 * T') ltac:(apply in_app_iff; right; cbn; auto 20)) as Y7. cbn [fst snd] in Y3, Y4, Y5, Y6, Y7.
unfold rb_w. rewrite ?HTK. fold cnt. clear - Ha Y3 Y4 Y5 Y6 Y7 Rhh N1. lia. }
assert (READ : forall ss ms', st_ok src2segs E ss ms' -> ss_mem ss = ss_mem (fst (sym_runN src2segs src2tbl FUEL ss_RB)) ->
val_mem src2segs (ms_mem ms') (ch_c C + 40) 4 (cnt + 1) /\
mbyte src2segs (ms_mem ms') (h1 + 3 * hh) = Some (Z_to_bv 8 (cR col)) /\ mbyte src2segs (ms_mem ms') (h1 + 3 * hh + 1) = Some (Z_to_bv 8 (cG col)) /\ mbyte src2segs (ms_mem ms') (h1 + 3 * hh + 2) = Some (Z_to_bv 8 (cB col)) /\
mbyte src2segs (ms_mem ms') (u1 + hh) = Some (Z_to_bv 8 1) /\ val_mem src2segs (ms_mem ms') (f1 + 4 * hh) 4 fq /\
mbyte src2segs (ms_mem ms') (p1 + 3 * cnt) = Some (Z_to_bv 8 (cR col)) /\ mbyte src2segs (ms_mem ms') (p1 + 3 * cnt + 1) = Some (Z_to_bv 8 (cG col)) /\ mbyte src2segs (ms_mem ms') (p1 + 3 * cnt + 2) = Some (Z_to_bv 8 (cB col)) /\
val_mem src2segs (ms_mem ms') (x1 + 4 * hh) 4 cnt).
{ intros ss ms' HS' Hss.
assert (VAL : forall (ri p : nat) (off : Z) (n : BinNums.N) (e : sv) (b v : Z) rg, nth_error (ss_mem ss) ri = Some rg -> r_base rg = Some p -> In (mkChunk off (CVal n e)) (r_chunks rg) ->
bv_unsigned (ew E p) = b -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 -> val_mem src2segs (ms_mem ms') (b + off) (N.to_nat n) v)
by (intros ri p off n e b v rg Hri Hb Hin Hp He Hv Hn; exact (st_chunk_val_g E _ ms' ri rg p off n e b v HS' Hri Hb Hin Hp He Hv Hn)).
rewrite Hss in VAL. clear Hss.
lazymatch type of VAL with context [ss_mem ?x] => let v := eval vm_compute in (ss_mem x) in change (ss_mem x) with v in VAL end.
split. { apply (VAL 3%nat 20%nat 40 4%N (SOff 46 1) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU20 | cbn [sv_denot]; rewrite HE46, unsigned_lit_small by lia; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. replace (h1 + 3 * hh) with (h1 + 3 * hh + 0) by lia.
apply (VAL 4%nat 37%nat 0 1%N (SOff 33 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU37 | cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. apply (VAL 4%nat 37%nat 1 1%N (SOff 34 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU37 | cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. apply (VAL 4%nat 37%nat 2 1%N (SOff 35 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU37 | cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. replace (u1 + hh) with (u1 + hh + 0) by lia.
apply (VAL 5%nat 38%nat 0 1%N (SLit 1) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU38 | reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { replace (f1 + 4 * hh) with (f1 + 4 * hh + 0) by lia.
apply (VAL 6%nat 39%nat 0 4%N (SOff 36 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU39 | cbn [sv_denot]; rewrite Z.add_0_r, HE36, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. replace (p1 + 3 * cnt) with (p1 + 3 * cnt + 0) by lia.
apply (VAL 7%nat 40%nat 0 1%N (SOff 33 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU40 | cbn [sv_denot]; rewrite Z.add_0_r, HE33, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. apply (VAL 7%nat 40%nat 1 1%N (SOff 34 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU40 | cbn [sv_denot]; rewrite Z.add_0_r, HE34, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
split. { apply mbyte_of_val_mem1'; [|lia]. apply (VAL 7%nat 40%nat 2 1%N (SOff 35 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU40 | cbn [sv_denot]; rewrite Z.add_0_r, HE35, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
replace (x1 + 4 * hh) with (x1 + 4 * hh + 0) by lia.
apply (VAL 8%nat 41%nat 0 4%N (SOff 46 0) _ _ _ eq_refl eq_refl); [cbn; auto | exact HU41 | cbn [sv_denot]; rewrite Z.add_0_r, HE46, Z_to_bv_bv_unsigned; reflexivity | cbn -[cR cG cB col cnt fq]; lia | cbn; lia]. }
pose proof (regs_kept_of_st_ok src2segs E _ _ regs1 [] [2; 3; 4; 23; 24; 25; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK.
assert (SR' : forall rs : bvmap 5 word, (forall rr, In rr [2; 3; 4; 23; 24; 25; 20; 9; 8; 21]%bv -> getr rs rr = getr regs1 rr) -> s_regs regs0 r rs i C T' h1 u1).
{ intros rs GK'. unfold s_regs, rgba_regs. rewrite (GK' 2%bv ltac:(cbv; auto 20)), (GK' 3%bv ltac:(cbv; auto 20)), (GK' 4%bv ltac:(cbv; auto 20)), (GK' 23%bv ltac:(cbv; auto 20)), (GK' 24%bv ltac:(cbv; auto 20)),
(GK' 25%bv ltac:(cbv; auto 20)), (GK' 20%bv ltac:(cbv; auto 20)), (GK' 9%bv ltac:(cbv; auto 20)), (GK' 8%bv ltac:(cbv; auto 20)), (GK' 21%bv ltac:(cbv; auto 20)).
split; [split; [exact G2 | split; [exact G3 | exact G4]]|]. repeat (split; [assumption|]). exact G21. }
assert (WROK : forall E', (forall n, (n < 49)%nat -> ew E' n = ew E n) -> wr_ok E' (ss_mem (fst (sym_runN src2segs src2tbl FUEL ss_RB))) RGBA_STK (sp0 regs0) (FPfoot r g bef beffmt s N) (blocks L A) (blocks Lc Ac)).
{ intros E' HE'. lazymatch goal with |- wr_ok _ ?rs _ _ _ _ _ => let v := eval vm_compute in rs in change rs with v end. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|].
eapply wr_ok_cons_gen; [reflexivity | rewrite HE' by lia; exact HU20 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN (ch_c C) CHT_SIZE); [left; reflexivity | unfold CHT_SIZE; lia] |].
eapply wr_ok_cons_gen; [reflexivity | rewrite HE' by lia; exact HU37 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN h1 (3 * T')); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | rewrite HE' by lia; exact HU38 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN u1 T'); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | rewrite HE' by lia; exact HU39 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN f1 (4 * T')); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | rewrite HE' by lia; exact HU40 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN p1 (3 * T')); [right; cbn; auto 10 | lia] |].
eapply wr_ok_cons_gen; [reflexivity | rewrite HE' by lia; exact HU41 | cbn [r_wlo r_whi]; intros a Ha; apply (WRN x1 (4 * T')); [right; cbn; auto 10 | lia] |].
apply wr_ok_nil. }
jbranch src2tbl HS.
-
rewrite branch_ltu_U, (U_atom_off E 18 j 1 HE18), (U_atom E 47 T HE47) in Hc by lia. apply Z.ltb_lt in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_REH. { apply WROK. intros; reflexivity. }
cbn [ms_mem mkst] in HF0.
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ rb_w f1 h1 u1 p1 x1 K hh a -> ~ (ch_c C + 40 <= a < ch_c C + 44) -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs memc a).
{ intros a Ha Hna Hnc. unfold rb_w in Hna. fold cnt in Hna.
mb_frame_g HF0; [| lia | lia | lia | rewrite HU20; exact Hnc | rewrite HU37; clear - Hna; lia | rewrite HU38; clear - Hna; lia | rewrite HU39; clear - Hna; lia | rewrite HU40; clear - Hna; lia | rewrite HU41; clear - Hna; lia].
mb_frame_g HF; [reflexivity | lia | lia | lia | rewrite HU20; exact Hnc | rewrite HU37; clear - Hna; lia | rewrite HU38; clear - Hna; lia | rewrite HU39; clear - Hna; lia | rewrite HU40; clear - Hna; lia | rewrite HU41; clear - Hna; lia]. }
destruct (READ _ _ HS ltac:(vm_compute; reflexivity)) as (S4 & K0 & K1 & K2 & U1 & F4 & P0 & P1 & P2 & X4).
pose proof (FACTS (ms_mem ms0) KEEP0 S4 K0 K1 K2 U1 F4 P0 P1 P2 X4) as LM'.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 23; 24; 25; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK0 end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80252) with (Z_to_bv 64 PC_REH).
apply (KNEXT (ms_regs ms0) (ms_mem ms0) K'); [lia|]. unfold at_REH.
split. { apply (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc _ mdc HINV HJ).
intros a Ha Hna. apply KEEP0; [lia | unfold rb_w; rewrite ?HTK; fold cnt; clear - Ha Rhh N1 Rp1 Rx1 Rk1 Rv1 Rw1; lia | lia]. }
split; [exact HRZF|]. split; [exact (SR' _ GK0)|].
split. { unfold reh_regs.
split; [eapply (getr_of_U src2segs); [exact HS|]; eval_sr_get; apply (U_atom_off E 18 j 1 HE18); lia|].
split; [eapply (getr_of_U src2segs); [exact HS|]; eval_sr_get; replace (4 * (j + 1)) with (4 * j + 4) by lia; apply (U_atom_off E 19 (4 * j) 4 HE19); lia|].
split; [eapply (getr_of_U src2segs); [exact HS|]; eval_sr_get; replace (3 * (j + 1)) with (3 * j + 3) by lia; apply (U_atom_off E 27 (3 * j) 3 HE27); lia|].
split; [eapply (getr_of_U src2segs); [exact HS|]; eval_sr_get; apply (U_atom E 47 T HE47); lia|].
jreg HS (22%bv:reg) as Hq; exact Hq. }
split; [lia|]. split; [exact HK'|]. split; [exact LM' | exact RZB].
-
rewrite branch_ltu_U, (U_atom_off E 18 j 1 HE18), (U_atom E 47 T HE47) in Hc by lia. apply Z.ltb_ge in Hc.
jrun_to LAWS src2tbl_ok HS HJ PC_POST. { apply WROK. intros; reflexivity. }
cbn [ms_mem mkst] in HF0.
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ rb_w f1 h1 u1 p1 x1 K hh a -> ~ (ch_c C + 40 <= a < ch_c C + 44) -> mbyte src2segs (ms_mem ms0) a = mbyte src2segs memc a).
{ intros a Ha Hna Hnc. unfold rb_w in Hna. fold cnt in Hna.
mb_frame_g HF0; [| lia | lia | lia | rewrite HU20; exact Hnc | rewrite HU37; clear - Hna; lia | rewrite HU38; clear - Hna; lia | rewrite HU39; clear - Hna; lia | rewrite HU40; clear - Hna; lia | rewrite HU41; clear - Hna; lia].
mb_frame_g HF; [reflexivity | lia | lia | lia | rewrite HU20; exact Hnc | rewrite HU37; clear - Hna; lia | rewrite HU38; clear - Hna; lia | rewrite HU39; clear - Hna; lia | rewrite HU40; clear - Hna; lia | rewrite HU41; clear - Hna; lia]. }
destruct (READ _ _ HS ltac:(vm_compute; reflexivity)) as (S4 & K0 & K1 & K2 & U1 & F4 & P0 & P1 & P2 & X4).
pose proof (FACTS (ms_mem ms0) KEEP0 S4 K0 K1 K2 U1 F4 P0 P1 P2 X4) as LM'.
lazymatch type of HS with st_ok _ _ ?ssf ?msf =>
pose proof (regs_kept_of_st_ok src2segs E ssf msf regs1 [] [2; 3; 4; 23; 24; 25; 20; 9; 8; 21]%bv HS EA0 ltac:(vm_compute; reflexivity)) as GK0 end.
rewrite (st_ok_mkst src2segs _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 80504) with (Z_to_bv 64 PC_POST).
apply (KPOST (ms_regs ms0) (ms_mem ms0) K'). unfold at_POST.
split. { apply (rgba_inv_mem API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc _ mdc HINV HJ).
intros a Ha Hna. apply KEEP0; [lia | unfold rb_w; rewrite ?HTK; fold cnt; clear - Ha Rhh N1 Rp1 Rx1 Rk1 Rv1 Rw1; lia | lia]. }
split; [exact HRZF|]. split; [exact (SR' _ GK0)|].
split; [replace (ch_T C) with (j + 1) by (subst T; lia); exact HK'|]. split; [exact LM' | exact RZB].
Qed.
End Rb.
End d.
End c.
