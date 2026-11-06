(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0w YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0a YF8r YF8s YF8x YF0d YF0e.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YL02 YL07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DEP_STK, kNodesBlockSize, kStoreBlockSize, TFX_IMG_END, TFX_TP, TFX_GP, TFX_DEPOT, TFX_STORE,
d_map1, d_nuniq, d_tab_words, zcanon, M64 in *.
Lemma tfx_dhash_u64 : forall tr, 0 <= tfx_dhash tr < 2 ^ 64.
Proof.
intros tr. unfold tfx_dhash. cbn zeta.
set (h := dh_mul (Z.lxor (Z.shiftr (dh_step (fold_left dh_step tr _) 0) 47) (dh_step (fold_left dh_step tr _) 0))).
assert (R : 0 <= h < 2 ^ 64) by (img_try ((subst h; cbv beta); img_apply dh_mul_u64)).
img_apply (lxor_u64 (Z.shiftr h 47) h); [img_try (img_apply shiftr_u64; [img_exact R | img_lia]) | img_try (img_exact R)].
Qed.
Lemma depot_len_bound : forall U (d : list (list Z)), universe_ok U -> List.NoDup d -> incl d U -> Z.of_nat (length d) <= DEPOT_MAX.
Proof.
intros U d (HU & _ & _) Hnd Hincl. pose proof (NoDup_incl_length Hnd Hincl). img_lia.
Qed.
Lemma depot_frames_bound {imgk : img} : forall U (d : list (list Z)), universe_ok U -> incl d U ->
0 <= fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 d <= 31 * Z.of_nat (length d).
Proof.
intros U d (_ & HF & _) Hincl. induction d as [|t d IH]; cbn [fold_right length]; [img_lia|].
assert (Ht : (length t <= kUnwindMax)%nat) by (img_try (img_apply (proj1 (Forall_forall _ _) HF); img_apply Hincl; left; img_refl)).
unfold kUnwindMax in Ht. specialize (IH ltac:(img_try (intros x Hx; img_apply Hincl; right; img_exact Hx))). img_lia.
Qed.
Lemma le4_bytes : forall b0 b1 b2 b3 (k : nat), 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> (k < 4)%nat ->
YP0g.le_byte (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) 4 k = nth k [b0; b1; b2; b3] 0.
Proof.
intros b0 b1 b2 b3 k B0 B1 B2 B3 Hk. unfold YP0g.le_byte.
rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat 4))) by (img_try (img_change (2 ^ (8 * Z.of_nat 4)) with 4294967296; img_lia)).
assert (Q1 : (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 256 = b1 + 256 * b2 + 65536 * b3).
{ symmetry. apply Z.div_unique with (r := b0); [img_try (left; img_lia) | img_lia]. }
assert (Q2 : (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 65536 = b2 + 256 * b3).
{ symmetry. apply Z.div_unique with (r := b0 + 256 * b1); [img_try (left; img_lia) | img_lia]. }
assert (Q3 : (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 16777216 = b3).
{ symmetry. apply Z.div_unique with (r := b0 + 256 * b1 + 65536 * b2); [img_try (left; img_lia) | img_lia]. }
destruct k as [|[|[|[|k]]]]; [ | | | | img_lia]; cbn [nth].
- img_change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z.mod_unique with (q := b1 + 256 * b2 + 65536 * b3); [img_try (left; img_lia) | img_lia].
- img_change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 8) with 256. rewrite Q1.
symmetry. apply Z.mod_unique with (q := b2 + 256 * b3); [img_try (left; img_lia) | img_lia].
- img_change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 16) with 65536. rewrite Q2.
symmetry. apply Z.mod_unique with (q := b3); [img_try (left; img_lia) | img_lia].
- img_change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 24) with 16777216. rewrite Q3. img_apply Z.mod_small. img_lia.
Qed.
Definition byteZ {imgk : img} (m : word -> option byte) (a : Z) : Z := match mbyte tfxsegs m a with Some b => bv_unsigned b | None => 0 end.
Definition rdu32 {imgk : img} (m : word -> option byte) (a : Z) : Z := byteZ m a + 256 * byteZ m (a + 1) + 65536 * byteZ m (a + 2) + 16777216 * byteZ m (a + 3).
Lemma byteZ_range {imgk : img} : forall m a, 0 <= byteZ m a < 256.
Proof. intros m a. unfold byteZ. destruct (mbyte tfxsegs m a) as [b|]; [| img_lia]. pose proof (bv_unsigned_in_range 8 b) as H. img_change (bv_modulus 8) with 256 in H. img_lia. Qed.
Lemma rdu32_range {imgk : img} : forall m a, 0 <= rdu32 m a < 2 ^ 32.
Proof. intros m a. unfold rdu32. pose proof (byteZ_range m a). pose proof (byteZ_range m (a + 1)). pose proof (byteZ_range m (a + 2)). pose proof (byteZ_range m (a + 3)). img_lia. Qed.
Lemma val_mem_rdu32 {imgk : img} : forall m a, (forall k, (k < 4)%nat -> mbyte tfxsegs m (a + Z.of_nat k) <> None) -> val_mem tfxsegs m a 4 (rdu32 m a).
Proof.
intros m a Hp k Hk.
assert (E : forall j, mbyte tfxsegs m (a + j) <> None -> mbyte tfxsegs m (a + j) = Some (Z_to_bv 8 (byteZ m (a + j)))).
{ intros j Hj. unfold byteZ. destruct (mbyte tfxsegs m (a + j)) as [b|]; [| img_try (congruence)]. rewrite Z_to_bv_bv_unsigned. img_refl. }
specialize (Hp k Hk). rewrite (E (Z.of_nat k) Hp). f_equal. f_equal. unfold rdu32.
rewrite (le4_bytes _ _ _ _ k (byteZ_range m a) (byteZ_range m (a + 1)) (byteZ_range m (a + 2)) (byteZ_range m (a + 3)) Hk).
destruct k as [|[|[|[|k]]]]; [ | | | | img_lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; img_refl.
Qed.

Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section s. Context {imgk : img}.
Variable B : asyms.
Hypothesis HB : TfxSyms B.
Hypothesis HDH : forall t, as_dhash B t = tfx_dhash t.
Variables (W : world tfxsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z) (tr : list Z).
Variables (heads links : Z -> Z).
#[local] Notation Hd := (w_H W).
#[local] Notation rd0 := (aview tfxsegs (w_H W) mem).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (bv_unsigned (getr regs 2%bv)).
#[local] Notation NB := (ly_NB ly).
#[local] Notation SB := (ly_SB ly).
Definition nD : Z := depot_ids S.
Definition hashes : Z -> Z := fun id => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S) []).
Definition HSH : Z := tfx_dhash tr.
Definition bkt : Z := HSH mod d_tab_words.
Definition TOT : Z := Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S.
Definition S2 : Z := TFX_DEPOT + 4 * bkt.
Definition HDv : Z := heads bkt.
Definition STD {imgk : img} : Z := rdu32 m0 (TFX_STORE + 24).
Definition NDN : Z := NB + 16 * (nD + 1).
Definition SLOT : Z := SB + 8 * TOT.
Definition NUQ {imgk : img} : Z := TFX_DEPOT + d_nuniq.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis WF : Wf (as_universe B) S.
Hypothesis Htr : In tr (as_universe B).
Hypothesis HCONST : Forall (cell_holds B ly rd0) (as_const B ly).
Hypothesis HCELLS : Forall (cell_holds B ly rd0) (depot_cells ly S).
Hypothesis D1 : forall b, 0 <= b < d_tab_words -> 0 <= heads b <= nD /\ rd32 rd0 (as_depot B + 4 * b) (heads b).
Hypothesis D2 : forall id, 1 <= id <= nD -> 0 <= links id < id /\ rd64 rd0 (NB + 16 * id) (hashes id mod 2 ^ 64) /\ rd32 rd0 (NB + 16 * id + 8) (links id).
Hypothesis D3 : forall id, 1 <= id <= nD -> chain_has links hashes (Z.to_nat nD) (heads ((hashes id mod 2 ^ 64) mod d_tab_words)) (hashes id).
Hypothesis HVIS : Forall (range_vis B ly rd0) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)].
Hypotheses (R10 : getr regs 10%bv = Z_to_bv 64 buf) (R11 : getr regs 11%bv = Z_to_bv 64 (Z.of_nat (length tr)))
(R3 : getr regs 3%bv = Z_to_bv 64 (as_gp B)) (R4 : getr regs 4%bv = Z_to_bv 64 TFX_TP) (Hra : YK0s.ret_ok (getr regs 1%bv)).
Hypothesis Hwords : forall i, (i < length tr)%nat -> val_mem tfxsegs m0 (buf + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypotheses (Hbuf8 : buf mod 8 = 0) (Hbuflo : ly_stk_lo ly <= buf) (Hbufhi : buf + 8 * 30 <= ly_stk_hi ly) (Hbuf_sp : buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hsplo : ly_stk_lo ly <= sp - DEP_STK) (Hsphi : sp <= ly_stk_hi ly)
(P_stk : forall a, sp - DEP_STK <= a < sp -> apresent Hd mem a).
Lemma tr_len : (length tr <= 30)%nat.
Proof. pose proof (ts_universe B HB) as (_ & HU & _). img_exact (proj1 (Forall_forall _ _) HU tr Htr). Qed.
Lemma nD_range : 1 <= nD <= 4097.
Proof.
unfold nD, depot_ids. pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
pose proof (depot_len_bound _ _ (ts_universe B HB) Hnd Hincl). unfold DEPOT_MAX in *. img_lia.
Qed.
Lemma TOT_range : 2 <= TOT <= 127008.
Proof.
unfold TOT, depot_frames. pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
pose proof (depot_frames_bound _ _ (ts_universe B HB) Hincl) as F. pose proof (depot_len_bound _ _ (ts_universe B HB) Hnd Hincl) as L.
pose proof (lo_tr0 ly LY) as T. unfold DEPOT_MAX in L. img_lia.
Qed.
Lemma HSH_range : 0 <= HSH < 2 ^ 64.
Proof. img_apply tfx_dhash_u64. Qed.
Lemma bkt_range : 0 <= bkt < d_tab_words.
Proof. unfold bkt, d_tab_words. img_apply Z.mod_pos_bound. img_lia. Qed.
Lemma HDv_range : 0 <= HDv <= nD.
Proof. unfold HDv. img_exact (proj1 (D1 bkt bkt_range)). Qed.
Lemma STD_range : 0 <= STD < 2 ^ 32.
Proof. img_apply rdu32_range. Qed.
Lemma hashes_u64 : forall id, 0 <= hashes id < 2 ^ 64.
Proof. intros id. unfold hashes. rewrite HDH. img_apply tfx_dhash_u64. Qed.
Lemma hashes_mod : forall id, hashes id mod 2 ^ 64 = hashes id.
Proof. intros id. img_apply Z.mod_small. img_apply hashes_u64. Qed.
Lemma blocks_facts :
4096 <= NB /\ NB + kNodesBlockSize <= 140737479966720 /\ 4096 <= SB /\ SB + kStoreBlockSize <= 140737479966720 /\
NB mod 4096 = 0 /\ SB mod 4096 = 0 /\
zdisjoint (NB, kNodesBlockSize) (SB, kStoreBlockSize) /\
zdisjoint (NB, kNodesBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (SB, kStoreBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_T ly, kThreadObjSize) (NB, kNodesBlockSize) /\ zdisjoint (ly_T ly, kThreadObjSize) (SB, kStoreBlockSize) /\
zdisjoint (ly_T ly, kThreadObjSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (NB, kNodesBlockSize) (ly_C ly, 256) /\ zdisjoint (SB, kStoreBlockSize) (ly_C ly, 256) /\
zdisjoint (ly_C ly, 256) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
4096 <= ly_T ly /\ 4096 <= ly_C ly.
Proof.
pose proof (lo_app ly LY) as HH. unfold owned_extents in HH.
pose proof (proj1 (Forall_forall _ _) HH (NB, kNodesBlockSize) ltac:(img_try (cbn; tauto))) as [N1 N2].
pose proof (proj1 (Forall_forall _ _) HH (SB, kStoreBlockSize) ltac:(img_try (cbn; tauto))) as [S1 S2'].
pose proof (proj1 (Forall_forall _ _) HH (ly_T ly, kThreadObjSize) ltac:(img_try (cbn; tauto))) as [T1 _].
pose proof (proj1 (Forall_forall _ _) HH (ly_C ly, 256) ltac:(img_try (cbn; tauto))) as [C1 _].
cbn [fst snd] in N1, N2, S1, S2', T1, C1.
pose proof (lo_disj ly LY) as PD. unfold static_extents, owned_extents in PD. cbn [app] in PD.
destruct PD as (_ & _ & FT & _ & FNB & FSB & FC & _).
pose proof (proj1 (Forall_forall _ _) FT (NB, kNodesBlockSize) ltac:(img_try (cbn; tauto))) as TN.
pose proof (proj1 (Forall_forall _ _) FT (SB, kStoreBlockSize) ltac:(img_try (cbn; tauto))) as TS.
pose proof (proj1 (Forall_forall _ _) FT (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(img_try (cbn; tauto))) as TK.
pose proof (proj1 (Forall_forall _ _) FNB (SB, kStoreBlockSize) ltac:(img_try (cbn; tauto))) as NS.
pose proof (proj1 (Forall_forall _ _) FNB (ly_C ly, 256) ltac:(img_try (cbn; tauto))) as NC.
pose proof (proj1 (Forall_forall _ _) FNB (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(img_try (cbn; tauto))) as NK.
pose proof (proj1 (Forall_forall _ _) FSB (ly_C ly, 256) ltac:(img_try (cbn; tauto))) as SC.
pose proof (proj1 (Forall_forall _ _) FSB (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(img_try (cbn; tauto))) as SK.
pose proof (proj1 (Forall_forall _ _) FC (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(img_try (cbn; tauto))) as CK.
pose proof (lo_NB_al ly LY) as A1. pose proof (lo_SB_al ly LY) as A2. unfold page_aligned in A1, A2.
assert (N2' : NB + kNodesBlockSize <= 140737479966720) by (img_try (clear - N2; ceil; unfold kLowShadowBeg, ASAN_CEIL in *; img_lia)).
assert (S2'' : SB + kStoreBlockSize <= 140737479966720) by (img_try (clear - S2'; ceil; unfold kLowShadowBeg, ASAN_CEIL in *; img_lia)).
repeat split; assumption.
Qed.
Local Ltac zone_of x sz k :=
pose proof (lo_disj ly LY) as PD; unfold static_extents, owned_extents in PD; cbn [app] in PD;
let F := fresh "F" in
lazymatch k with
| 2 => destruct PD as (_ & _ & F & _) | 4 => destruct PD as (_ & _ & _ & _ & F & _) | 5 => destruct PD as (_ & _ & _ & _ & _ & F & _)
| 6 => destruct PD as (_ & _ & _ & _ & _ & _ & F & _) | 7 => destruct PD as (_ & _ & _ & _ & _ & _ & _ & F & _) end;
let AP := fresh "AP" in
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (x, sz) ltac:(img_try (unfold owned_extents; cbn; tauto))) as AP; cbn [fst snd] in AP;
assert (SZ : 0 <= sz) by (img_try (unfold kNodesBlockSize, kStoreBlockSize, kThreadObjSize; img_lia));
img_apply (zone3_intro ly x sz IMG SZ AP);
img_apply (proj1 (Forall_forall _ _) F (ly_img ly)); cbn; tauto.
Lemma NB_zone : zone3 NB kNodesBlockSize. Proof. zone_of (ly_NB ly) kNodesBlockSize 4. Qed.
Lemma SB_zone : zone3 SB kStoreBlockSize. Proof. zone_of (ly_SB ly) kStoreBlockSize 5. Qed.
Lemma T_zone : zone3 (ly_T ly) kThreadObjSize. Proof. zone_of (ly_T ly) kThreadObjSize 2. Qed.
Lemma C_zone : zone3 (ly_C ly) 256. Proof. zone_of (ly_C ly) 256 6. Qed.
Lemma D_zone : zone3 (ly_D ly) 4096. Proof. zone_of (ly_D ly) 4096 7. Qed.
Ltac zoneNS := pose proof NB_zone as NZ; pose proof SB_zone as SZ';
unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in NZ, SZ'.
Lemma NB_off : forall a, NB <= a < NB + kNodesBlockSize -> off_img a. Proof. intros a Ha. img_exact (zone3_off_img _ _ a NB_zone Ha). Qed.
Lemma SB_off : forall a, SB <= a < SB + kStoreBlockSize -> off_img a. Proof. intros a Ha. img_exact (zone3_off_img _ _ a SB_zone Ha). Qed.
Lemma zone_facts :
0x10007fff8000 <= ly_stk_lo ly /\ ly_stk_hi ly <= 0x800000000000 /\ ly_stk_lo ly <= sp - 512 /\ sp <= ly_stk_hi ly /\
ly_stk_lo ly <= buf /\ buf + 240 <= ly_stk_hi ly /\ (buf + 240 <= sp - 512 \/ sp <= buf) /\ (length tr <= 30)%nat /\
4096 <= NB /\ NB + 0x100000 <= 140737479966720 /\ 4096 <= SB /\ SB + 0x800000 <= 140737479966720 /\
(NB + 0x100000 <= SB \/ SB + 0x800000 <= NB) /\
(NB + 0x100000 <= ly_stk_lo ly \/ ly_stk_hi ly <= NB) /\ (SB + 0x800000 <= ly_stk_lo ly \/ ly_stk_hi ly <= SB) /\
1 <= nD <= 4097 /\ 2 <= TOT <= 127008 /\ 0 <= HSH < 2 ^ 64 /\ 0 <= bkt < 1048576 /\ 0 <= HDv <= nD /\ 0 <= STD < 2 ^ 32 /\
sp mod 16 = 0 /\ buf mod 8 = 0 /\ NB mod 4096 = 0 /\ SB mod 4096 = 0.
Proof.
pose proof (lo_top ly LY) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
pose proof blocks_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & _).
pose proof tr_len as TL. pose proof nD_range as NR. pose proof TOT_range as TR. pose proof HSH_range as HR. pose proof bkt_range as KR.
pose proof HDv_range as DR. pose proof STD_range as SR.
pose proof Hsplo as C1. pose proof Hsphi as C2. pose proof Hbuflo as C3. pose proof Hbufhi as C4. pose proof Hbuf_sp as C5. pose proof Hsp16 as C6. pose proof Hbuf8 as C7.
clear - A1 A2 A3 A4 A5 A6 A7 B1 B2 B3 B4 B5 B6 B7 B8 B9 TL NR TR HR KR DR SR C1 C2 C3 C4 C5 C6 C7.
unfold zdisjoint in B7, B8, B9. cbn [fst snd] in B7, B8, B9.
ceil; unfold ly_bot, kHighMemBeg, kHighMemEnd, ASAN_CEIL, DEP_STK, kNodesBlockSize, kStoreBlockSize, d_tab_words in *.
repeat split; first [img_lia | img_exact TL].
Qed.
Ltac zone := pose proof zone_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25).
Definition XW : list word :=
[Z_to_bv 64 NB; Z_to_bv 64 SB; Z_to_bv 64 TOT; Z_to_bv 64 nD; Z_to_bv 64 HSH; Z_to_bv 64 S2; Z_to_bv 64 HDv; Z_to_bv 64 STD; Z_to_bv 64 NDN; Z_to_bv 64 SLOT].
Definition E0 : env := Ereg regs XW.
Lemma EaNB : ew E0 aNB = Z_to_bv 64 NB. Proof. img_refl. Qed.
Lemma EaSB : ew E0 aSB = Z_to_bv 64 SB. Proof. img_refl. Qed.
Lemma EaTOT : ew E0 aTOT = Z_to_bv 64 TOT. Proof. img_refl. Qed.
Lemma EaN : ew E0 aN = Z_to_bv 64 nD. Proof. img_refl. Qed.
Lemma EaHASH : ew E0 aHASH = Z_to_bv 64 HSH. Proof. img_refl. Qed.
Lemma EaS2 : ew E0 aS2 = Z_to_bv 64 S2. Proof. img_refl. Qed.
Lemma EaHD : ew E0 aHD = Z_to_bv 64 HDv. Proof. img_refl. Qed.
Lemma EaSTD : ew E0 aSTD = Z_to_bv 64 STD. Proof. img_refl. Qed.
Lemma EaNDN : ew E0 aNDN = Z_to_bv 64 NDN. Proof. img_refl. Qed.
Lemma EaSLOT : ew E0 aSLOT = Z_to_bv 64 SLOT. Proof. img_refl. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs XW k r Hk). Qed.
Lemma E1 : ew E0 1 = getr regs 1%bv. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E2 : ew E0 2 = getr regs 2%bv. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = Z_to_bv 64 buf. Proof. rewrite <- R10. img_exact (Er 10 10%bv eq_refl). Qed.
Lemma E11 : ew E0 11 = Z_to_bv 64 (Z.of_nat (length tr)). Proof. rewrite <- R11. img_exact (Er 11 11%bv eq_refl). Qed.
Lemma sp_range : 0 <= sp < 2 ^ 64. Proof. img_apply u64_range. Qed.
Definition envD (E : env) : Prop := forall k, (k < K_D)%nat -> ew E k = ew E0 k.
Lemma envD_E0 : envD E0. Proof. intros k _. img_refl. Qed.
Lemma envD_havoc : forall E k ws, envD E -> (K_D <= k)%nat -> envD (havoc E k ws).
Proof. intros E k ws HE Hk j Hj. rewrite ew_havoc_old by img_lia. img_exact (HE j Hj). Qed.
Record fixedU (E : env) : Prop := {
U2 : bv_unsigned (ew E 2) = sp;
U10 : bv_unsigned (ew E 10) = buf;
U11 : bv_unsigned (ew E 11) = Z.of_nat (length tr);
U32 : bv_unsigned (ew E aNB) = NB;
U33 : bv_unsigned (ew E aSB) = SB;
U34 : bv_unsigned (ew E aTOT) = TOT;
U35 : bv_unsigned (ew E aN) = nD;
U36 : bv_unsigned (ew E aHASH) = HSH;
U37 : bv_unsigned (ew E aS2) = S2;
U38 : bv_unsigned (ew E aHD) = HDv;
U39 : bv_unsigned (ew E aSTD) = STD;
U40 : bv_unsigned (ew E aNDN) = NDN;
U41 : bv_unsigned (ew E aSLOT) = SLOT }.
Lemma fixedU_of_envD : forall E, envD E -> fixedU E.
Proof.
intros E HE. zone. pose proof sp_range as SR.
assert (L : forall k z, (k < K_D)%nat -> ew E0 k = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew E k) = z).
{ intros k z Hk Hz Hr. rewrite (HE k Hk), Hz. img_apply unsigned_lit_small. img_exact Hr. }
unfold K_D in L. constructor.
- rewrite (HE 2%nat ltac:(img_try (unfold K_D; img_lia))), E2. img_refl.
- img_apply (L 10%nat buf ltac:(img_lia) E10). clear - Z1 Z5 Z6 Z2. img_lia.
- img_apply (L 11%nat _ ltac:(img_lia) E11). clear - Z8. img_lia.
- img_apply (L aNB _ ltac:(img_try (unfold aNB; img_lia)) EaNB). clear - Z9 Z10. img_lia.
- img_apply (L aSB _ ltac:(img_try (unfold aSB; img_lia)) EaSB). clear - Z11 Z12. img_lia.
- img_apply (L aTOT _ ltac:(img_try (unfold aTOT; img_lia)) EaTOT). clear - Z17. img_lia.
- img_apply (L aN _ ltac:(img_try (unfold aN; img_lia)) EaN). clear - Z16. img_lia.
- img_apply (L aHASH _ ltac:(img_try (unfold aHASH; img_lia)) EaHASH). img_exact Z18.
- img_apply (L aS2 _ ltac:(img_try (unfold aS2; img_lia)) EaS2). unfold S2. clear - Z19. numconst. img_lia.
- img_apply (L aHD _ ltac:(img_try (unfold aHD; img_lia)) EaHD). clear - Z20 Z16. img_lia.
- img_apply (L aSTD _ ltac:(img_try (unfold aSTD; img_lia)) EaSTD). clear - Z21. img_lia.
- img_apply (L aNDN _ ltac:(img_try (unfold aNDN; img_lia)) EaNDN). unfold NDN. clear - Z9 Z10 Z16. img_lia.
- img_apply (L aSLOT _ ltac:(img_try (unfold aSLOT; img_lia)) EaSLOT). unfold SLOT. clear - Z11 Z12 Z17. img_lia.
Qed.
Ltac fixu HE := pose proof (fixedU_of_envD _ HE) as [V2 V10 V11 V32 V33 V34 V35 V36 V37 V38 V39 V40 V41];
unfold aNB, aSB, aTOT, aN, aHASH, aS2, aHD, aSTD, aNDN, aSLOT in V32, V33, V34, V35, V36, V37, V38, V39, V40, V41.

Lemma rw_writable : forall (m : word -> option byte) a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> writable_at tfxsegs m a.
Proof. intros m a Ha. unfold writable_at. img_apply tfx_rw_window. rewrite unsigned_lit_small by img_lia. img_exact Ha. Qed.
Lemma const_val : forall a (w : nat) v,
cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) -> val_mem tfxsegs m0 a w v.
Proof.
intros a w v E. img_apply (cell_holds_val_mem B ly Hd mem (ANum a) w (ANum v)).
img_apply (proj1 (Forall_forall (cell_holds B ly rd0) (as_const B ly)) HCONST). rewrite (ts_const B HB ly). img_exact (cell_lookup_In _ _ _ E).
Qed.
Lemma cells_val :
val_mem tfxsegs m0 NUQ 4 nD /\ val_mem tfxsegs m0 (TFX_DEPOT + d_map1) 8 NB /\ val_mem tfxsegs m0 TFX_STORE 8 TOT /\ val_mem tfxsegs m0 (TFX_STORE + 16) 8 SB.
Proof.
pose proof HCELLS as HC. unfold depot_cells in HC.
apply Forall_inv in HC as C1'. apply Forall_inv_tail in HC. apply Forall_inv in HC as C2'. apply Forall_inv_tail in HC.
apply Forall_inv in HC as C3'. apply Forall_inv_tail in HC. apply Forall_inv in HC as C4'. clear HC.
pose proof (cell_holds_val_mem B ly Hd mem _ _ _ C1') as V1. pose proof (cell_holds_val_mem B ly Hd mem _ _ _ C2') as V2.
pose proof (cell_holds_val_mem B ly Hd mem _ _ _ C3') as V3. pose proof (cell_holds_val_mem B ly Hd mem _ _ _ C4') as V4.
cbn [aeval] in V1, V2, V3, V4. rewrite (ts_depot B HB) in V1, V2. rewrite (ts_store B HB) in V3, V4.
unfold s_total, s_block0 in V3, V4. rewrite ?Z.add_0_r in V2. rewrite ?Z.add_0_r in V3. rewrite ?Z.add_0_r in V4.
unfold NUQ, nD, TOT. repeat split; assumption.
Qed.
Lemma rd32_val_mem : forall a v, rd32 rd0 a v -> val_mem tfxsegs m0 a 4 v.
Proof. intros a v H k Hk. rewrite <- le_byte_eq. img_apply aview_byte. img_exact (H k Hk). Qed.
Lemma rd64_val_mem : forall a v, rd64 rd0 a v -> val_mem tfxsegs m0 a 8 v.
Proof. intros a v H k Hk. rewrite <- le_byte_eq. img_apply aview_byte. img_exact (H k Hk). Qed.
Lemma tab_val : val_mem tfxsegs m0 S2 4 HDv.
Proof. unfold S2, HDv. rewrite <- (ts_depot B HB). img_apply rd32_val_mem. img_exact (proj2 (D1 bkt bkt_range)). Qed.
Lemma vis_at : forall k e len i, nth_error [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] k = Some (e, len) ->
0 <= i < len -> exists b, mbyte tfxsegs m0 (aeval B ly e + i) = Some b.
Proof. intros k e len i Hk Hi. img_apply (range_vis_mbyte B ly Hd mem e len i); [| img_try (img_exact Hi)]. img_exact (Forall_nth_error _ _ k _ HVIS Hk). Qed.
Lemma STD_val : val_mem tfxsegs m0 (TFX_STORE + 24) 4 STD.
Proof.
unfold STD. img_apply val_mem_rdu32. intros k Hk. destruct (vis_at 2 (AStore 24) 8 (Z.of_nat k) eq_refl ltac:(img_lia)) as [b Hb].
cbn [aeval] in Hb. rewrite (ts_store B HB) in Hb. rewrite Hb. discriminate.
Qed.
Lemma NB_present : forall a, NB <= a < NB + kNodesBlockSize -> exists b, mbyte tfxsegs m0 a = Some b.
Proof.
intros a Ha. destruct (vis_at 3 (ANB 0) kNodesBlockSize (a - NB) eq_refl ltac:(img_lia)) as [b Hb]. cbn [aeval] in Hb.
replace (NB + 0 + (a - NB)) with a in Hb by img_lia. exists b. img_exact Hb.
Qed.
Lemma SB_present : forall a, SB <= a < SB + kStoreBlockSize -> exists b, mbyte tfxsegs m0 a = Some b.
Proof.
intros a Ha. destruct (vis_at 4 (ASB 0) kStoreBlockSize (a - SB) eq_refl ltac:(img_lia)) as [b Hb]. cbn [aeval] in Hb.
replace (SB + 0 + (a - SB)) with a in Hb by img_lia. exists b. img_exact Hb.
Qed.
Lemma region_ok_cell8r : forall E (m : word -> option byte) a k v,
val_mem tfxsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> region_ok tfxsegs E m (cell8r a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, cell8r. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E m 0 a 8 (SOff k 0) v); [| img_try (img_exact Hr) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact Hv)].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by img_exact Hr. f_equal. img_lia.
Qed.
Lemma region_ok_cell8 : forall E (m : word -> option byte) a k v,
val_mem tfxsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> (0xa1000 + D_1000) <= a -> a + 8 <= (0x5ff000 + D_1000) -> region_ok tfxsegs E m (cell8 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, cell8. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_apply rw_writable; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E m 0 a 8 (SOff k 0) v); [| img_try (img_exact Hr) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact Hv)].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by img_exact Hr. f_equal. img_lia.
Qed.
Lemma region_ok_cell4 : forall E (m : word -> option byte) a k v,
val_mem tfxsegs m a 4 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> (0xa1000 + D_1000) <= a -> a + 4 <= (0x5ff000 + D_1000) -> region_ok tfxsegs E m (cell4 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, cell4. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_apply rw_writable; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E m 0 a 4 (SOff k 0) v); [| img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_l; img_exact Hv)].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by img_lia. f_equal. img_lia.
Qed.
#[local] Notation msD0 := (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfxsegs)).
Lemma REG0_ok : Forall (region_ok tfxsegs E0 m0) DMEM0.
Proof.
zone. pose proof sp_range as SR. pose proof cells_val as (V1 & V2 & V3 & V4). pose proof tab_val as VT. pose proof STD_val as VS.
unfold DMEM0, DFIX, D_consts, D_cf, R_DS, R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8. cbn [app].
img_apply Forall_cons. { img_apply (region_ok_stack tfxsegs E0 m0 2 sp (- DEP_STK)); [img_try (rewrite E2; img_refl) | img_try (clear - Z1 Z3; numconst; img_lia) | img_try (clear - SR; img_lia) |].
intros a Ha. img_apply apresent_writable; [img_try (clear - Ha Z1 Z3 SR; numconst; img_lia) | img_try (img_apply P_stk; img_exact Ha)]. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 0x102e8 8 DH_M); [img_try (img_apply const_val; (img_case; vm_compute); img_refl) | img_try (unfold DH_M; cbn; img_lia) | img_try (cbn; img_lia) | img_lia | img_try (cbn; img_lia)]. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0x10308 + D_8) 8 DH_M8); [img_try (img_apply const_val; (img_case; vm_compute); img_refl) | img_try (unfold DH_M8; cbn; img_lia) | img_try (cbn; img_lia) | img_lia | img_try (cbn; img_lia)]. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0x103a0 + D_20) 8 DH_SEED); [img_try (img_apply const_val; (img_case; vm_compute); img_refl) | img_try (unfold DH_SEED; cbn; img_lia) | img_try (cbn; img_lia) | img_lia | img_try (cbn; img_lia)]. }
img_apply Forall_cons. { img_apply (region_ok_cell8r E0 m0 _ aNB NB V2 EaNB); clear - Z9 Z10; numconst; img_lia. }
img_apply Forall_cons. { unfold NUQ in V1. img_apply (region_ok_cell4 E0 m0 _ aN nD V1 EaN); clear - Z16; numconst; img_lia. }
img_apply Forall_cons. { unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite EaS2, unsigned_lit_small by (img_try (unfold S2; clear - Z19; numconst; img_lia)).
split; [img_try (unfold S2; clear - Z19; numconst; img_lia)|]. split; [img_try (unfold S2; clear - Z19; numconst; img_lia)|].
split; [img_try (intros o Ho; img_apply rw_writable; unfold S2; clear - Z19 Ho; numconst; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E0 m0 S2 0 4 (SOff aHD 0) HDv); [img_try (cbn [sv_denot]; rewrite EaHD, unsigned_lit_small by (clear - Z16 Z20; img_lia); f_equal; img_lia)
| img_try (clear - Z16 Z20; cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_r; img_exact VT)]. }
img_apply Forall_cons. { img_apply (region_ok_cell8 E0 m0 _ aTOT TOT V3 EaTOT); clear - Z17; numconst; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_cell8r E0 m0 _ aSB SB V4 EaSB); clear - Z11 Z12; numconst; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_cell4 E0 m0 _ aSTD STD VS EaSTD); clear - Z21; numconst; img_lia. }
img_apply Forall_cons. { img_apply (region_ok_window E0 m0 aNDN NDN); [img_try (rewrite EaNDN; img_apply unsigned_lit_small; unfold NDN; clear - Z9 Z10 Z16; numconst; img_lia)
| img_try (unfold NDN; clear - Z9 Z10 Z16; numconst; img_lia) | img_try (unfold NDN; clear - Z9 Z10 Z16; numconst; img_lia) |].
intros a Ha. destruct (NB_present a ltac:(img_try (unfold NDN in Ha; clear - Ha Z16; numconst; img_lia))) as [b Hb].
img_apply (mbyte_off_writable _ a b); [img_try (img_apply NB_off; unfold NDN in Ha; clear - Ha Z16; numconst; img_lia) | img_try (img_exact Hb)]. }
img_apply Forall_cons. { img_apply (region_ok_window E0 m0 aSLOT SLOT); [img_try (rewrite EaSLOT; img_apply unsigned_lit_small; unfold SLOT; clear - Z11 Z12 Z17; numconst; img_lia)
| img_try (unfold SLOT; clear - Z11 Z12 Z17; numconst; img_lia) | img_try (unfold SLOT; clear - Z11 Z12 Z17; numconst; img_lia) |].
intros a Ha. destruct (SB_present a ltac:(img_try (unfold SLOT in Ha; clear - Ha Z17; numconst; img_lia))) as [b Hb].
img_apply (mbyte_off_writable _ a b); [img_try (img_apply SB_off; unfold SLOT in Ha; clear - Ha Z17; numconst; img_lia) | img_try (img_exact Hb)]. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0xa2150 + D_10f0) 8 (0x13bce8 + D_10c0)); [img_try (img_apply const_val; (img_case; vm_compute); img_refl) | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_lia | img_try (cbn; img_lia)]. }
img_apply Forall_cons. { img_apply (region_ok_lit E0 m0 (0x13bdd8 + D_10c0) 8 0x101000100000000); [img_try (img_apply const_val; (img_case; vm_compute); img_refl) | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_lia | img_try (cbn; img_lia)]. }
img_apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 DMEM0.
Proof.
zone. pose proof sp_range as SR.
img_apply pairwise_disjoint_of_extents. unfold DMEM0, DFIX, D_consts, D_cf, R_DS, R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8, cell8, cell8r, cell4, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E2, EaS2, EaNDN, EaSLOT. rewrite !unsigned_lit_small by (img_try (unfold S2, NDN, SLOT; clear - Z9 Z10 Z11 Z12 Z16 Z17 Z19; numconst; img_lia)).
zoneNS.
unfold S2, NDN, SLOT. clear - Z1 Z2 Z3 Z4 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR NZ SZ'.
numconst. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; img_lia.
Qed.
Lemma AFo : forall E k X lo hi al, ew E k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k (mkAF lo hi al).
Proof. intros E k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. rewrite unsigned_lit_small by img_exact HX. repeat split; img_lia. Qed.
Lemma FACTS_fixed : forall E, (1 <= length tr)%nat -> envD E -> Forall (fun nf => afact_ok E (fst nf) (snd nf)) DF_fixed.
Proof.
intros E Htr1 HE. zone. pose proof sp_range as SR.
assert (E2' : ew E 2 = Z_to_bv 64 sp) by (img_try (rewrite (HE 2%nat ltac:(unfold K_D; img_lia)), E2; symmetry; img_apply Z_to_bv_bv_unsigned)).
assert (G : forall k w, (k < K_D)%nat -> ew E0 k = w -> ew E k = w) by (img_try (intros k w Hk Hw; rewrite (HE k Hk); img_exact Hw)). unfold K_D in G.
unfold DF_fixed, u64f. unfold aNB, aSB, aTOT, aN, aHASH, aS2, aHD, aSTD, aNDN, aSLOT.
img_apply Forall_cons. { img_apply (AFo E 2%nat sp _ _ _ E2'); clear - SR Z1 Z3 Z4 Z2 Z22; [img_lia | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 4) with 16. img_exact Z22. }
img_apply Forall_cons. { img_apply (AFo E 10%nat buf _ _ _ (G 10%nat _ ltac:(img_lia) E10)); clear - Z1 Z2 Z5 Z6 Z23; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_change (2 ^ 3) with 8; img_exact Z23) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 11%nat _ _ _ _ (G 11%nat _ ltac:(img_lia) E11)); clear - Z8 Htr1; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 32%nat NB _ _ _ (G 32%nat _ ltac:(img_lia) EaNB)); clear - Z9 Z10 Z24; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_change (2 ^ 12) with 4096; img_exact Z24) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 33%nat SB _ _ _ (G 33%nat _ ltac:(img_lia) EaSB)); clear - Z11 Z12 Z25; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_change (2 ^ 12) with 4096; img_exact Z25) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 34%nat TOT _ _ _ (G 34%nat _ ltac:(img_lia) EaTOT)); clear - Z17; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 35%nat nD _ _ _ (G 35%nat _ ltac:(img_lia) EaN)); clear - Z16; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 36%nat HSH _ _ _ (G 36%nat _ ltac:(img_lia) EaHASH)); clear - Z18; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 37%nat S2 _ _ _ (G 37%nat _ ltac:(img_lia) EaS2)); unfold S2; clear - Z19; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 2) with 4. img_apply Z.mod_divide; [img_lia|]. exists ((405542 + D_430) + bkt). numconst. img_lia. }
img_apply Forall_cons. { img_apply (AFo E 38%nat HDv _ _ _ (G 38%nat _ ltac:(img_lia) EaHD)); clear - Z16 Z20; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 39%nat STD _ _ _ (G 39%nat _ ltac:(img_lia) EaSTD)); clear - Z21; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { img_apply (AFo E 40%nat NDN _ _ _ (G 40%nat _ ltac:(img_lia) EaNDN)); unfold NDN; clear - Z9 Z10 Z16 Z24; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 4) with 16. apply Z.mod_divide in Z24 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (256 * q + (nD + 1)). img_lia. }
img_apply Forall_cons. { img_apply (AFo E 41%nat SLOT _ _ _ (G 41%nat _ ltac:(img_lia) EaSLOT)); unfold SLOT; clear - Z11 Z12 Z17 Z25; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 3) with 8. apply Z.mod_divide in Z25 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (512 * q + TOT). img_lia. }
img_apply Forall_nil.
Qed.
Lemma atoms_ok_of_Forall : forall E l, Forall (fun nf : nat * afact => afact_ok E (fst nf) (snd nf)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [| [k f] l Hh Ht IH]; cbn; [img_try (img_exact I) | img_try (split; [img_exact Hh | img_exact IH])]. Qed.
Lemma SEED_ok : (1 <= length tr)%nat -> st_ok tfxsegs E0 SS_D0 (restrict Hd msD0).
Proof.
intros Htr1. rewrite restrict_mkst_fx. unfold SS_D0, DREGS0. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; rewrite R3, (ts_gp B HB); img_refl)].
img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact R4)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_exact REG0_ok.
- img_exact PAIRS_ok.
- split; [| img_try (split; img_exact I)]. unfold DF0. cbn [f_atoms]. img_apply atoms_ok_of_Forall. img_apply (FACTS_fixed E0 Htr1). img_apply envD_E0.
Qed.
Definition WIN (a : Z) : Prop :=
(sp - DEP_STK <= a < sp) \/ (S2 <= a < S2 + 4) \/ (NUQ <= a < NUQ + 4) \/ (NDN <= a < NDN + 16) \/
(TFX_STORE <= a < TFX_STORE + 8) \/ (TFX_STORE + 24 <= a < TFX_STORE + 28) \/ (SLOT <= a < SLOT + 248).
Definition WSKD {imgk : img} : list (option nat * Z * Z) :=
[(Some 2%nat, - DEP_STK, 0); (None, NUQ, NUQ + 4); (Some aS2, 0, 4); (None, TFX_STORE, TFX_STORE + 8); (None, TFX_STORE + 24, TFX_STORE + 28);
(Some aNDN, 0, 16); (Some aSLOT, 0, 248)].
Definition WSKM {imgk : img} : list (option nat * Z * Z) := WSKD ++ [(Some aDC, 0, 1)].
Definition wsk_ok (sk : list (option nat * Z * Z)) (rs : smem) : bool :=
forallb (fun t => existsb (win_eqb t) sk || (snd t <=? snd (fst t))) (windows rs).
Lemma windows_WINM : forall E rs a, envD E -> wsk_ok WSKM rs = true -> in_wrange E rs a ->
WIN a \/ (bv_unsigned (ew E aDC) <= a < bv_unsigned (ew E aDC) + 1).
Proof.
intros E rs a HE Hb Hw. fixu HE.
destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. exfalso. clear - Hr Ht. img_lia. }
unfold WSKM, WSKD in Ht. cbn [existsb app] in Ht. unfold WIN.
repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
- rewrite V2 in Hr. clear - Hr. img_lia.
- clear - Hr. img_lia.
- unfold aS2 in Hr. rewrite V37 in Hr. clear - Hr. img_lia.
- clear - Hr. img_lia.
- clear - Hr. img_lia.
- unfold aNDN in Hr. rewrite V40 in Hr. clear - Hr. img_lia.
- unfold aSLOT in Hr. rewrite V41 in Hr. clear - Hr. img_lia.
- right. clear - Hr. img_lia.
- discriminate Ht.
Qed.
Lemma wsk_DM : forall rs, wsk_ok WSKD rs = true -> wsk_ok WSKM rs = true.
Proof.
intros rs H. unfold wsk_ok in *. img_apply forallb_forall. intros t Ht. pose proof (proj1 (forallb_forall _ _) H t Ht) as X.
apply Bool.orb_prop in X as [X|X]; [| img_try (rewrite X, Bool.orb_true_r; img_refl)].
unfold WSKM. rewrite existsb_app, X. img_refl.
Qed.
Lemma windows_WIN : forall E rs a, envD E -> wsk_ok WSKD rs = true -> in_wrange E rs a ->
WIN a \/ (bv_unsigned (ew E aDC) <= a < bv_unsigned (ew E aDC) + 1).
Proof. intros E rs a HE Hb Hw. img_exact (windows_WINM E rs a HE (wsk_DM rs Hb) Hw). Qed.
Lemma WIN_foot : forall a, WIN a -> (sp - DEP_STK <= a < sp) \/ depot_footprint B ly a.
Proof.
intros a Ha. zone. unfold depot_footprint. rewrite (ts_depot B HB), (ts_store B HB). unfold WIN, S2, NUQ, NDN, SLOT in Ha.
clear - Ha Z16 Z17 Z19. numconst. img_lia.
Qed.
Lemma buf_outside : forall q, 0 <= q < 240 -> ~ WIN (buf + q).
Proof.
intros q Hq Hw. zone. unfold WIN, S2, NUQ, NDN, SLOT in Hw.
zoneNS. clear - Hq Hw Z1 Z5 Z6 Z7 Z9 Z10 Z11 Z12 Z14 Z15 Z16 Z17 Z19 NZ SZ'. numconst. img_lia.
Qed.
Definition INV (m : word -> option byte) : Prop :=
(forall x : word, ~ WIN (bv_unsigned x) -> m x = mem x) /\ mem_grows (mrestrict Hd mem) (mrestrict Hd m).
Lemma INV_mem : INV mem.
Proof. split; [img_try (intros x _; img_refl) | img_try (intros a Ha; img_exact Ha)]. Qed.
Lemma INV_apresent : forall m a, INV m -> apresent Hd mem a -> apresent Hd m a.
Proof. intros m a [_ HG] Ha. img_exact (apresent_grows Hd mem m a HG Ha). Qed.
Lemma INV_aview : forall m a, INV m -> rd0 a <> None -> aview tfxsegs Hd m a <> None.
Proof.
intros m a [_ HG] Ha. img_apply (proj2 (aview_vis Hd m a)). apply (proj1 (aview_vis Hd mem a)) in Ha.
unfold mbyte in *. specialize (HG (Z_to_bv 64 a)).
destruct (mrestrict Hd mem (Z_to_bv 64 a)) as [b|]; [| img_try (destruct (mrestrict Hd m (Z_to_bv 64 a)); [discriminate | img_exact Ha])].
destruct (mrestrict Hd m (Z_to_bv 64 a)) as [b'|]; [img_try (discriminate) | img_try (exfalso; img_apply HG; [discriminate | img_refl])].
Qed.
Lemma INV_runM : forall E rs (m m' : word -> option byte),
INV m -> envD E -> wsk_ok WSKM rs = true -> frame_of E rs m m' -> mem_grows (mrestrict Hd m) (mrestrict Hd m') ->
SLOT <= bv_unsigned (ew E aDC) -> bv_unsigned (ew E aDC) + 1 <= SLOT + 248 -> INV m'.
Proof.
intros E rs m m' [IF IP] HE Hb HF HG D1' D2'. split.
- intros x Hx. rewrite (HF x). { img_exact (IF x Hx). } intros Hw. destruct (windows_WINM E rs _ HE Hb Hw) as [H|H]; [img_try (img_exact (Hx H))|].
img_apply Hx. unfold WIN. clear - H D1' D2'. img_lia.
- img_exact (mem_grows_trans' _ _ _ IP HG).
Qed.
Lemma INV_runD : forall E rs (m m' : word -> option byte),
INV m -> envD E -> wsk_ok WSKD rs = true -> frame_of E rs m m' -> mem_grows (mrestrict Hd m) (mrestrict Hd m') -> INV m'.
Proof.
intros E rs m m' [IF IP] HE Hb HF HG. split.
- intros x Hx. rewrite (HF x). { img_exact (IF x Hx). } intros Hw.
destruct (in_wrange_windows E rs _ Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. clear - Hr Ht. img_lia. }
img_apply Hx. fixu HE. unfold WSKD in Ht. cbn [existsb app] in Ht. unfold WIN.
repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
+ rewrite V2 in Hr. clear - Hr. img_lia.
+ clear - Hr. img_lia.
+ unfold aS2 in Hr. rewrite V37 in Hr. clear - Hr. img_lia.
+ clear - Hr. img_lia.
+ clear - Hr. img_lia.
+ unfold aNDN in Hr. rewrite V40 in Hr. clear - Hr. img_lia.
+ unfold aSLOT in Hr. rewrite V41 in Hr. clear - Hr. img_lia.
+ discriminate Ht.
- img_exact (mem_grows_trans' _ _ _ IP HG).
Qed.
Lemma val_mem_mod64 : forall (m : word -> option byte) a v, val_mem tfxsegs m a 8 v -> val_mem tfxsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YP0g.le_byte. img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
rewrite Z.mod_mod by img_lia. img_refl.
Qed.
Lemma words_INV : forall m, INV m -> forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict Hd m) (buf + 8 * Z.of_nat i) 8 ((nth i tr 0) mod 2 ^ 64).
Proof.
intros m [IF _] i Hi. zone. img_apply val_mem_mod64. eapply (val_mem_frame Hd mem m); [| img_try (img_exact (Hwords i Hi))].
intros k Hk. img_apply IF. rewrite unsigned_lit_small by (img_try (clear - Hi Hk Z1 Z5 Z6 Z2 Z8; numconst; img_lia)).
replace (buf + 8 * Z.of_nat i + Z.of_nat k) with (buf + (8 * Z.of_nat i + Z.of_nat k)) by img_lia. img_apply buf_outside. clear - Hi Hk Z8. img_lia.
Qed.
Lemma byte_INV : forall m q, INV m -> 0 <= q < 8 * Z.of_nat (length tr) -> val_mem tfxsegs (mrestrict Hd m) (buf + q) 1 (byteZ m0 (buf + q)).
Proof.
intros m q [IF _] Hq k Hk. zone. destruct k as [|k]; [| img_try (exfalso; clear - Hk; img_lia)]. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hwords (Z.to_nat (q / 8)) ltac:(img_try (clear - Hq Z8; img_apply Nat2Z.inj_lt; rewrite Z2Nat.id by (img_apply Z.div_pos; img_lia); img_apply Z.div_lt_upper_bound; img_lia))) as VW.
pose proof (Z.div_mod q 8 ltac:(img_lia)) as D. pose proof (Z.mod_pos_bound q 8 ltac:(img_lia)) as R.
specialize (VW (Z.to_nat (q mod 8)) ltac:(img_try (clear - R; img_lia))). rewrite !Z2Nat.id in VW by (img_try (clear - Hq R; try img_apply Z.div_pos; img_lia)).
replace (buf + 8 * (q / 8) + q mod 8) with (buf + q) in VW by (img_try (clear - D; img_lia)).
assert (Eq : mbyte tfxsegs (mrestrict Hd m) (buf + q) = mbyte tfxsegs m0 (buf + q)).
{ img_apply (mbyte_mrestrict_same Hd). img_apply IF. rewrite unsigned_lit_small by (img_try (clear - Hq Z1 Z5 Z6 Z2 Z8; numconst; img_lia)). img_apply buf_outside. clear - Hq Z8; img_lia. }
rewrite Eq. unfold byteZ. rewrite VW. f_equal. rewrite unsigned_lit_small8 by (img_try (img_apply Z.mod_pos_bound; img_lia)).
unfold YP0g.le_byte. img_change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r, !Z.mod_mod by img_lia. img_refl.
Qed.
Definition LT42 (j : nat) : bool := (j <? 42)%nat.
Lemma agree_pd_havoc : forall E k ws, (42 <= k)%nat -> env_agree_pd LT42 PT E (havoc E k ws).
Proof.
intros E k ws Hk. split; [| img_try (intros d _; rewrite ed_havoc; img_refl)].
intros n Hn. unfold LT42 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_havoc_old by img_lia. img_refl.
Qed.
Lemma sub_mem_ok : forall E E' ss (m : word -> option byte) rs,
mem_ok tfxsegs E m (ss_mem ss) -> submem rs (ss_mem ss) -> regions_wf rs = true -> mem_atoms_lt 42 rs = true ->
(forall n, (n < 42)%nat -> ew E' n = ew E n) -> ed E' = ed E -> mem_ok tfxsegs E' m rs.
Proof.
intros E E' ss m rs HM Hsub WF1 WF2 HEE HED.
img_apply (mem_ok_agree tfxsegs 42 E E'); [img_try (split; [img_exact HEE | img_exact HED]) | img_try (img_exact WF2) |].
img_apply (mem_ok_sub tfxsegs E m (ss_mem ss) rs Hsub WF1 HM).
Qed.
Lemma condZ : forall E (c : branch_cond) n1 k1 n2 k2 (r : bool),
branch_taken c (sv_denot E (SOff n1 k1)) (sv_denot E (SOff n2 k2)) = r ->
0 <= bv_unsigned (ew E n1) + k1 < 2 ^ 64 -> 0 <= bv_unsigned (ew E n2) + k2 < 2 ^ 64 ->
match c with
| BC_EQ => (bv_unsigned (ew E n1) + k1 =? bv_unsigned (ew E n2) + k2) = r
| BC_NE => negb (bv_unsigned (ew E n1) + k1 =? bv_unsigned (ew E n2) + k2) = r
| BC_LTU => (bv_unsigned (ew E n1) + k1 <? bv_unsigned (ew E n2) + k2) = r
| BC_GEU => negb (bv_unsigned (ew E n1) + k1 <? bv_unsigned (ew E n2) + k2) = r
| _ => True
end.
Proof.
intros E c n1 k1 n2 k2 r Hc H1 H2. unfold branch_taken, bv_ltu, bv_eqb in Hc. rewrite !denot_SOff in Hc. unfold zcanon, M64 in Hc.
rewrite !Z.mod_small in Hc by assumption. destruct c; first [img_exact Hc | img_exact I].
Qed.
Lemma condZ_lit : forall E (c : branch_cond) n1 k1 z (r : bool),
branch_taken c (sv_denot E (SOff n1 k1)) (sv_denot E (SLit z)) = r ->
0 <= bv_unsigned (ew E n1) + k1 < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
match c with
| BC_EQ => (bv_unsigned (ew E n1) + k1 =? z) = r
| BC_NE => negb (bv_unsigned (ew E n1) + k1 =? z) = r
| BC_LTU => (bv_unsigned (ew E n1) + k1 <? z) = r
| BC_GEU => negb (bv_unsigned (ew E n1) + k1 <? z) = r
| _ => True
end.
Proof.
intros E c n1 k1 z r Hc H1 H2. unfold branch_taken, bv_ltu, bv_eqb in Hc. rewrite denot_SOff in Hc. cbn [sv_denot] in Hc. unfold zcanon, M64 in Hc.
rewrite unsigned_lit_small in Hc by img_exact H2. rewrite !Z.mod_small in Hc by assumption. destruct c; first [img_exact Hc | img_exact I].
Qed.
Lemma denot_of_U : forall E e z, U E e = z -> sv_denot E e = Z_to_bv 64 z.
Proof. intros E e z H. unfold U in H. rewrite <- H. symmetry. img_apply Z_to_bv_bv_unsigned. Qed.
Lemma OBr : forall E' (rg : bvmap 5 word) (r r' : bv 5) k (w : word), ew E' k = w -> getr rg r' = w -> bv_unsigned r = bv_unsigned r' -> ew E' k = getr rg r.
Proof. intros E' rg r r' k w H1 H2 H3. rewrite H1, <- H2. f_equal. symmetry. img_apply bv_eq. img_exact H3. Qed.
Lemma JKf : forall E' k (w : word), ew E' k = w -> afact_ok E' k u64f.
Proof. intros E' k w Hk. unfold afact_ok, u64f. cbn [af_lo af_hi af_al2]. pose proof (u64_range (ew E' k)). split; [img_lia|]. split; [img_try (img_apply Z.mod_1_r) | img_lia]. Qed.
Definition H0v : Z := Z.lxor ((Z.of_nat (length tr) * DH_M8) mod 2 ^ 64) DH_SEED.
Definition hacc (i : nat) : Z := fold_left dh_step (firstn i tr) H0v.
Lemma H0v_u64 : 0 <= H0v < 2 ^ 64.
Proof. unfold H0v. img_apply lxor_u64; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (unfold DH_SEED; img_lia)]. Qed.
Lemma fold_dh_u64 : forall l h, 0 <= h < 2 ^ 64 -> 0 <= fold_left dh_step l h < 2 ^ 64.
Proof. induction l as [|w l IH]; intros h Hh; cbn; [img_try (img_exact Hh) | img_try (img_apply IH; img_apply dh_step_u64)]. Qed.
Lemma hacc_u64 : forall i, 0 <= hacc i < 2 ^ 64.
Proof. intros i. unfold hacc. img_apply fold_dh_u64. img_apply H0v_u64. Qed.
Lemma firstn_S_nth : forall (l : list Z) i, (i < length l)%nat -> firstn (Datatypes.S i) l = firstn i l ++ [nth i l 0].
Proof.
induction l as [|x l IH]; intros i Hi; cbn in Hi; [img_lia|].
destruct i as [|i]; [img_refl|]. cbn [firstn nth app]. rewrite (IH i) by img_lia. img_refl.
Qed.
Lemma hacc_S : forall i, (i < length tr)%nat -> hacc (Datatypes.S i) = dh_step (hacc i) (nth i tr 0).
Proof. intros i Hi. unfold hacc. rewrite (firstn_S_nth tr i Hi), fold_left_app. img_refl. Qed.
Lemma dh_step_mod : forall h w, dh_step h (w mod 2 ^ 64) = dh_step h w.
Proof. intros h w. unfold dh_step, dh_mul. rewrite Z.mul_mod_idemp_l by img_lia. img_refl. Qed.
Lemma hacc_full : DFIN (hacc (length tr)) = HSH.
Proof. unfold HSH, tfx_dhash, DFIN, hacc, H0v. rewrite firstn_all. img_refl. Qed.
Definition EH (E : env) (i : nat) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64); Z_to_bv 64 (hacc i); Z_to_bv 64 (buf + 8 * Z.of_nat i); Z_to_bv 64 (buf + 8 * Z.of_nat (length tr));
getr rg 15%bv; getr rg 16%bv].
Lemma RW_disj : forall E i, envD E -> (i < length tr)%nat -> bv_unsigned (ew E dP) = buf + 8 * Z.of_nat i -> all_disjoint E R_W DFIX'.
Proof.
intros E i HE Hi HP. zone. pose proof sp_range as SR. fixu HE.
img_apply all_disjoint_of_extents. unfold DFIX', DFIX, D_consts, D_cf, R_W, R_DS', R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8, cell8, cell8r, cell4, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. unfold dP, aS2, aNDN, aSLOT in *. rewrite HP, V2, V37, V40, V41.
unfold S2, NDN, SLOT. zoneNS. clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR Hi NZ SZ'.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Lemma reabs_H : forall E ss ms i,
st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_HLOOP ->
reabs_check LT42 ss HREGS HF = true -> submem DFIX' (ss_mem ss) -> (i < length tr)%nat ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 (buf + 8 * Z.of_nat i) -> getr (ms_regs ms) 12%bv = Z_to_bv 64 (hacc i) ->
getr (ms_regs ms) 14%bv = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)) -> INV (ms_mem ms) ->
let E' := EH E i (ms_regs ms) in
st_ok tfxsegs E' S_H (restrict Hd ms) /\ envD E' /\
ew E' dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64) /\ ew E' dH = Z_to_bv 64 (hacc i) /\
ew E' dP = Z_to_bv 64 (buf + 8 * Z.of_nat i) /\ ew E' dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)).
Proof.
intros E ss ms i HS HE Hpc Hck Hsub Hi G11 G12 G14 HI. zone. cbn zeta. set (E' := EH E i (ms_regs ms)).
assert (HE' : envD E') by (img_try (img_apply envD_havoc; [img_try (img_exact HE) | img_try (unfold K_D; img_lia)])).
assert (EW : ew E' dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64)) by img_refl. assert (EHh : ew E' dH = Z_to_bv 64 (hacc i)) by img_refl.
assert (EP : ew E' dP = Z_to_bv 64 (buf + 8 * Z.of_nat i)) by img_refl. assert (EE : ew E' dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr))) by img_refl.
pose proof (Z.mod_pos_bound (nth i tr 0) (2 ^ 64) ltac:(img_lia)) as WR. pose proof (hacc_u64 i) as HR.
assert (UP : bv_unsigned (ew E' dP) = buf + 8 * Z.of_nat i) by (img_try (rewrite EP; img_apply unsigned_lit_small; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; img_lia)).
split; [| img_try (split; [img_exact HE' | split; [img_exact EW | split; [img_exact EHh | split; [img_exact EP | img_exact EE]]]])].
unfold S_H. rewrite <- Hpc.
img_apply (st_ok_add_region E' (mkSS (ss_pc ss) HREGS DFIX' None HF) (restrict Hd ms) R_W).
- img_apply (st_ok_reabs tfxsegs LT42 E E' ss (restrict Hd ms) HREGS DFIX' HF HS (agree_pd_havoc E 42 _ ltac:(img_lia)) Hck).
+ cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* img_apply (OBr E' _ _ 11%bv 44%nat _ EP G11). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 12%bv 43%nat _ EHh G12). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 14%bv 45%nat _ EE G14). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 15%bv 46%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 16%bv 47%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ assert (FO : fact_obls LT42 HF = [(dW, u64f); (dH, u64f); (dP, mkAF kHighMemBeg (kHighMemEnd - 8) 3); (dE, mkAF kHighMemBeg kHighMemEnd 3); (46%nat, u64f); (47%nat, u64f)])
by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
img_apply Forall_cons; [img_try (img_apply (JKf E' _ _ EW))|]. img_apply Forall_cons; [img_try (img_apply (JKf E' _ _ EHh))|].
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' dP _ _ _ _ EP); clear - Hi Z1 Z2 Z5 Z6 Z8 Z23; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 3) with 8. apply Z.mod_divide in Z23 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (q + Z.of_nat i). img_lia. }
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' dE _ _ _ _ EE); clear - Z1 Z2 Z5 Z6 Z8 Z23; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 3) with 8. apply Z.mod_divide in Z23 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (q + Z.of_nat (length tr)). img_lia. }
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 15%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 16%bv)); img_refl)|]. img_apply Forall_nil.
+ cbn [ms_mem restrict]. img_apply (sub_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EH. rewrite ew_havoc_old by img_lia. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. unfold region_ok, R_W. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite UP. split; [img_try (clear - Z1 Z5; numconst; img_lia)|]. split; [img_try (clear - Hi Z2 Z6 Z8; numconst; img_lia)|]. split; [img_try (intros o Ho; exfalso; clear - Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E' _ _ 0 8 (SOff dW 0) ((nth i tr 0) mod 2 ^ 64)); [img_try (cbn [sv_denot]; rewrite EW, unsigned_lit_small by img_exact WR; f_equal; img_lia) | img_try (img_exact WR) | img_try (cbn; img_lia) |].
rewrite Z.add_0_r. img_exact (words_INV _ HI i Hi).
- cbn [ss_mem]. img_exact (RW_disj E' i HE' Hi UP).
Qed.
Definition POST_B : world tfxsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists E' ms' mat', c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md) /\
st_ok tfxsegs E' S_B (restrict Hd ms') /\ envD E' /\ INV (ms_mem ms').
Definition EB (E : env) (rg : bvmap 5 word) : env :=
havoc E 42 [getr rg 10%bv; getr rg 11%bv; getr rg 12%bv; getr rg 14%bv; getr rg 15%bv; getr rg 16%bv].
Lemma reabs_B : forall E ss ms,
st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_BKT -> reabs_check LT42 ss BREGS BFc = true -> submem DFIX' (ss_mem ss) ->
st_ok tfxsegs (EB E (ms_regs ms)) S_B (restrict Hd ms) /\ envD (EB E (ms_regs ms)).
Proof.
intros E ss ms HS HE Hpc Hck Hsub. set (E' := EB E (ms_regs ms)).
assert (HE' : envD E') by (img_try (img_apply envD_havoc; [img_try (img_exact HE) | img_try (unfold K_D; img_lia)])). split; [| img_try (img_exact HE')].
unfold S_B. rewrite <- Hpc.
img_apply (st_ok_reabs tfxsegs LT42 E E' ss (restrict Hd ms) BREGS DFIX' BFc HS (agree_pd_havoc E 42 _ ltac:(img_lia)) Hck).
- cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | [H | []]]]]]]; injection H as <- <-.
+ img_apply (OBr E' _ _ 10%bv 42%nat (getr (ms_regs ms) 10%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 11%bv 43%nat (getr (ms_regs ms) 11%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 12%bv 44%nat (getr (ms_regs ms) 12%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 14%bv 45%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 15%bv 46%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 16%bv 47%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
- assert (FO : fact_obls LT42 BFc = [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f); (46%nat, u64f); (47%nat, u64f)]) by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 10%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 11%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 12%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 14%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 15%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 16%bv)); img_refl)|]. img_apply Forall_nil.
- cbn [ms_mem restrict]. img_apply (sub_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EB. rewrite ew_havoc_old by img_lia. img_refl.
Qed.
Ltac red_sr :=
lazymatch goal with |- _ = U _ (sr_get ?rs ?r) => let e := img_ev (sr_get rs r) in img_change (sr_get rs r) with e end.
Ltac inv_stepD HI HE INVn :=
lazymatch goal with
| HF : frame_of ?E ?rs ?mold (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INVn : INV (ms_mem msA)) by (img_try (img_apply (INV_runD E rs _ _ HI HE ltac:((img_case; vm_compute); img_refl) HF HG))); clear HF HG HI
end.
Lemma hash_loop : forall k i E ms mat,
(length tr - i <= k)%nat -> (i < length tr)%nat ->
st_ok tfxsegs E S_H (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
ew E dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64) -> ew E dH = Z_to_bv 64 (hacc i) ->
ew E dP = Z_to_bv 64 (buf + 8 * Z.of_nat i) -> ew E dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POST_B.
Proof.
induction k as [|k IH]; intros i E ms mat Hk Hi HS HE HI EW EHh EP EE; [img_try (exfalso; clear - Hk Hi; img_lia)|].
pose proof Hwx_tfa as HWX. zone.
pose proof (Z.mod_pos_bound (nth i tr 0) (2 ^ 64) ltac:(img_lia)) as WR. pose proof (hacc_u64 i) as HR.
assert (UW : bv_unsigned (ew E dW) = (nth i tr 0) mod 2 ^ 64) by (img_try (rewrite EW; img_apply unsigned_lit_small; img_exact WR)).
assert (UH : bv_unsigned (ew E dH) = hacc i) by (img_try (rewrite EHh; img_apply unsigned_lit_small; img_exact HR)).
assert (UP : bv_unsigned (ew E dP) = buf + 8 * Z.of_nat i) by (img_try (rewrite EP; img_apply unsigned_lit_small; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; img_lia)).
assert (UE : bv_unsigned (ew E dE) = buf + 8 * Z.of_nat (length tr)) by (img_try (rewrite EE; img_apply unsigned_lit_small; clear - Z1 Z5 Z6 Z2 Z8; numconst; img_lia)).
unfold dW in UW. unfold dH in UH. unfold dP in UP. unfold dE in UE.
srr_runG tfxtbl_rtD_ok HS. inv_stepD HI HE INV1.
srr_branch_with tfxtbl_rtD_ok HS.
-
apply (condZ E BC_NE 44 8 45 0 true) in Hc; [| img_try (rewrite UP; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; img_lia) | img_try (rewrite UE; clear - Z1 Z5 Z6 Z2 Z8; numconst; img_lia)].
cbn beta iota in Hc. rewrite UP, UE, Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
assert (Hi' : (Datatypes.S i < length tr)%nat) by (img_try (clear - Hc Hi; img_lia)).
srr_runG tfxtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
rreg HS (11%bv : bv 5) G11. rewrite UP in G11.
pose proof (st_ok_reg_denot Hd E _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot E ?e => replace e with X_STEP in G12 by img_refl end.
rewrite (denot_of_U E X_STEP _ (step_val E (hacc i) _ UW UH WR HR)) in G12. rewrite dh_step_mod, <- (hacc_S i Hi) in G12.
rreg HS (14%bv : bv 5) G14.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
destruct (reabs_H E ss2 ms2 (Datatypes.S i) HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop))) Hi'
ltac:(img_try (rewrite G11; f_equal; img_lia)) G12 ltac:(img_try (rewrite G14; img_exact EE)) INV2)
as (HS' & HE' & EW' & EH' & EP' & EE')
end.
lazymatch type of HS' with st_ok _ ?E' _ (restrict _ ?ms2) =>
apply (IH (Datatypes.S i) E' ms2 _ ltac:(img_try (clear - Hk Hi'; img_lia)) Hi' HS' HE' INV2 EW' EH' EP' EE') end.
-
apply (condZ E BC_NE 44 8 45 0 false) in Hc; [| img_try (rewrite UP; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; img_lia) | img_try (rewrite UE; clear - Z1 Z5 Z6 Z2 Z8; numconst; img_lia)].
cbn beta iota in Hc. rewrite UP, UE, Z.add_0_r in Hc. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
assert (Hn : Datatypes.S i = length tr) by (img_try (clear - Hc Hi; img_lia)).
srr_runG tfxtbl_rtD_ok HS. inv_stepD INV1 HE INV3.
assert (FIN : U E X_FIN = HSH).
{ rewrite (fin_val E (hacc i) _ UW UH WR HR), dh_step_mod, <- (hacc_S i Hi), Hn. img_exact hacc_full. }
fixu HE.
apply (st_ok_pin_regU E _ _ 19%bv (SOff aHASH 0)) in HS; [| img_try (intros X; discriminate) |].
2:{ lazymatch goal with |- _ = U E ?e => replace e with X_FIN by img_refl end. rewrite FIN, U_SOff. unfold aHASH. rewrite V36. unfold zcanon, M64. rewrite Z.add_0_r. rewrite Z.mod_small by img_exact Z18. img_refl. }
apply (st_ok_pin_regU E _ _ 18%bv (SOff aS2 0)) in HS; [| img_try (intros X; discriminate) |].
2:{ lazymatch goal with |- _ = U E ?e => replace e with X_S2 by img_refl end. rewrite s2_of_fin, FIN, U_SOff. unfold aS2. rewrite V37. unfold zcanon, M64, S2, bkt, d_tab_words. rewrite Z.add_0_r.
rewrite Z.mod_small by (img_try (clear - Z19; numconst; img_lia)). img_refl. }
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) =>
destruct (reabs_B E ss3 ms3 HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))) as [HSB HEB];
img_apply SRr_ret; split; [img_refl|]; exists (EB E (ms_regs ms3)), ms3, mat; split; [img_refl|]; split; [img_try (img_exact HSB) | img_try (split; [img_exact HEB | img_exact INV3])]
end.
Qed.
Definition INVC (cur : Z) : Prop := chain_has links hashes (Z.to_nat nD) HDv HSH -> exists f, chain_has links hashes f cur HSH.
Lemma chain_has_0 : forall f h, ~ chain_has links hashes f 0 h.
Proof. intros [|f] h; cbn; [img_try (tauto) | img_try (intros [H _]; img_apply H; img_refl)]. Qed.
Lemma INVC_start : INVC HDv.
Proof. intros H. exists (Z.to_nat nD). img_exact H. Qed.
Lemma INVC_step : forall cur, INVC cur -> cur <> 0 -> hashes cur <> HSH -> INVC (links cur).
Proof.
intros cur HC Hc Hh A. destruct (HC A) as [[|f] H]; cbn in H; [img_try (destruct H)|].
destruct H as [_ [H|H]]; [img_try (exfalso; img_exact (Hh H)) | img_try (exists f; img_exact H)].
Qed.
Lemma trace_eqb_eq : forall a b, trace_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [img_refl|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite H1, (IH b H2). img_refl.
Qed.
Lemma miss_no_trace : ~ chain_has links hashes (Z.to_nat nD) HDv HSH -> mem_trace tr (st_depot S) = false.
Proof.
intros NC. destruct (mem_trace tr (st_depot S)) eqn:Hm; [img_try (exfalso) | img_refl]. img_apply NC.
assert (X : exists j, nth_error (st_depot S) j = Some tr).
{ clear - Hm. induction (st_depot S) as [|u l IH]; cbn in Hm; [img_try (discriminate)|].
apply Bool.orb_prop in Hm as [Hm|Hm]; [img_try (exists 0%nat; cbn; rewrite (trace_eqb_eq _ _ Hm); img_refl)|].
destruct (IH Hm) as [j Hj]. exists (Datatypes.S j). img_exact Hj. }
destruct X as [j Hj]. assert (Lj : (j < length (st_depot S))%nat) by (img_try (img_apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate)).
set (id0 := Z.of_nat j + 2).
assert (Hid : 1 <= id0 <= nD) by (img_try (unfold id0, nD, depot_ids; clear - Lj; img_lia)).
assert (Hh : hashes id0 = HSH).
{ unfold hashes, HSH, depot_traces. rewrite HDH. replace (Z.to_nat (id0 - 1)) with (Datatypes.S j) by (img_try (unfold id0; clear; img_lia)).
cbn [nth]. rewrite (nth_error_nth _ _ _ Hj). img_refl. }
pose proof (D3 id0 Hid) as C. rewrite Hh, (Z.mod_small HSH (2 ^ 64)) in C by img_apply HSH_range. fold bkt in C. fold HDv in C. img_exact C.
Qed.
Definition EFL (E : env) (cur : Z) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 cur; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; getr rg 14%bv; getr rg 15%bv; getr rg 16%bv; getr rg 10%bv; getr rg 12%bv].
Lemma reabs_FL : forall E ss ms cur,
st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_FLOOP -> reabs_check LT42 ss FLREGS FLc = true -> submem DFIX' (ss_mem ss) ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 cur -> 0 <= cur <= 4097 ->
st_ok tfxsegs (EFL E cur (ms_regs ms)) S_FL (restrict Hd ms) /\ envD (EFL E cur (ms_regs ms)) /\ ew (EFL E cur (ms_regs ms)) aID = Z_to_bv 64 cur.
Proof.
intros E ss ms cur HS HE Hpc Hck Hsub G11 Hcur. set (E' := EFL E cur (ms_regs ms)).
assert (HE' : envD E') by (img_try (img_apply envD_havoc; [img_try (img_exact HE) | img_try (unfold K_D; img_lia)])).
assert (EI : ew E' aID = Z_to_bv 64 cur) by img_refl.
split; [| img_try (split; [img_exact HE' | img_exact EI])]. unfold S_FL. rewrite <- Hpc.
img_apply (st_ok_reabs tfxsegs LT42 E E' ss (restrict Hd ms) FLREGS DFIX' FLc HS (agree_pd_havoc E 42 _ ltac:(img_lia)) Hck).
- cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | [H | []]]]]]]; injection H as <- <-.
+ img_apply (OBr E' _ _ 10%bv 49%nat (getr (ms_regs ms) 10%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 11%bv 42%nat _ EI G11). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 12%bv 50%nat (getr (ms_regs ms) 12%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 14%bv 46%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 15%bv 47%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 16%bv 48%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
- assert (FO : fact_obls LT42 FLc = [(aID, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f); (49%nat, u64f); (50%nat, u64f)]) by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aID cur _ _ _ EI); clear - Hcur; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 14%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 15%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 16%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 10%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 12%bv)); img_refl)|]. img_apply Forall_nil.
- cbn [ms_mem restrict]. img_apply (sub_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EFL. rewrite ew_havoc_old by img_lia. img_refl.
Qed.
Definition EFN (E : env) (cur : Z) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 cur; Z_to_bv 64 (NB + 16 * cur); Z_to_bv 64 (hashes cur); Z_to_bv 64 (links cur); getr rg 14%bv; getr rg 15%bv; getr rg 16%bv].
Lemma ND_disj : forall E cur, envD E -> 1 <= cur <= nD -> bv_unsigned (ew E aND) = NB + 16 * cur -> all_disjoint E R_ND DFIX'.
Proof.
intros E cur HE Hcur HA. zone. pose proof sp_range as SR. fixu HE.
img_apply all_disjoint_of_extents. unfold DFIX', DFIX, D_consts, D_cf, R_ND, R_DS', R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8, cell8, cell8r, cell4, extent_of_region.
cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. unfold aND, aS2, aNDN, aSLOT in *. rewrite HA, V2, V37, V40, V41.
unfold S2, NDN, SLOT. zoneNS. clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR Hcur NZ SZ'.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
Qed.
Lemma node_vals : forall m cur, INV m -> 1 <= cur <= nD ->
val_mem tfxsegs (mrestrict Hd m) (NB + 16 * cur) 8 (hashes cur) /\ val_mem tfxsegs (mrestrict Hd m) (NB + 16 * cur + 8) 4 (links cur).
Proof.
intros m cur [IF _] Hcur. zone. destruct (D2 cur Hcur) as (_ & R1 & R2). rewrite hashes_mod in R1.
assert (OUT : forall k, 0 <= k < 12 -> m (Z_to_bv 64 (NB + 16 * cur + k)) = mem (Z_to_bv 64 (NB + 16 * cur + k))).
{ intros k Hk. img_apply IF. rewrite unsigned_lit_small by (img_try (clear - Hk Hcur Z9 Z10 Z16; numconst; img_lia)). unfold WIN, S2, NUQ, NDN, SLOT.
zoneNS. clear - Hk Hcur Z9 Z10 Z13 Z14 Z16 Z17 Z19 Z1 Z3 Z4 NZ SZ'. numconst. img_lia. }
split.
- eapply (val_mem_frame Hd mem m); [| img_try (img_exact (rd64_val_mem _ _ R1))]. intros k Hk. img_apply OUT. img_lia.
- eapply (val_mem_frame Hd mem m); [| img_try (img_exact (rd32_val_mem _ _ R2))]. intros k Hk. replace (NB + 16 * cur + 8 + Z.of_nat k) with (NB + 16 * cur + (8 + Z.of_nat k)) by img_lia. img_apply OUT. img_lia.
Qed.
Lemma reabs_FN : forall E ss ms cur,
st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_FNODE -> reabs_check LT42 ss FNREGS FFc = true -> submem DFIX' (ss_mem ss) ->
1 <= cur <= nD -> getr (ms_regs ms) 10%bv = Z_to_bv 64 cur -> getr (ms_regs ms) 11%bv = Z_to_bv 64 (NB + 16 * cur) -> INV (ms_mem ms) ->
let E' := EFN E cur (ms_regs ms) in
st_ok tfxsegs E' S_FN (restrict Hd ms) /\ envD E' /\
ew E' aID = Z_to_bv 64 cur /\ ew E' aNH = Z_to_bv 64 (hashes cur) /\ ew E' aNL = Z_to_bv 64 (links cur).
Proof.
intros E ss ms cur HS HE Hpc Hck Hsub Hcur G10 G11 HI. zone. cbn zeta. set (E' := EFN E cur (ms_regs ms)).
assert (HE' : envD E') by (img_try (img_apply envD_havoc; [img_try (img_exact HE) | img_try (unfold K_D; img_lia)])).
assert (EI : ew E' aID = Z_to_bv 64 cur) by img_refl. assert (EA : ew E' aND = Z_to_bv 64 (NB + 16 * cur)) by img_refl.
assert (ENH : ew E' aNH = Z_to_bv 64 (hashes cur)) by img_refl. assert (ENL : ew E' aNL = Z_to_bv 64 (links cur)) by img_refl.
pose proof (hashes_u64 cur) as HR. pose proof (proj1 (D2 cur Hcur)) as LR.
assert (UA : bv_unsigned (ew E' aND) = NB + 16 * cur) by (img_try (rewrite EA; img_apply unsigned_lit_small; clear - Hcur Z9 Z10 Z16; numconst; img_lia)).
split; [| img_try (split; [img_exact HE' | split; [img_exact EI | split; [img_exact ENH | img_exact ENL]]])]. unfold S_FN. rewrite <- Hpc.
img_apply (st_ok_add_region E' (mkSS (ss_pc ss) FNREGS DFIX' None FFc) (restrict Hd ms) R_ND).
- img_apply (st_ok_reabs tfxsegs LT42 E E' ss (restrict Hd ms) FNREGS DFIX' FFc HS (agree_pd_havoc E 42 _ ltac:(img_lia)) Hck).
+ cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* img_apply (OBr E' _ _ 10%bv 42%nat _ EI G10). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 11%bv 43%nat _ EA G11). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 14%bv 46%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 15%bv 47%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 16%bv 48%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ assert (FO : fact_obls LT42 FFc = [(aID, mkAF 0 4097 0); (aND, mkAF 4096 CEIL_MAX 4); (aNH, u64f); (aNL, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f)])
by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aID cur _ _ _ EI); clear - Hcur Z16; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aND _ _ _ _ EA); clear - Hcur Z9 Z10 Z16 Z24; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | | img_lia].
img_change (2 ^ 4) with 16. apply Z.mod_divide in Z24 as [q Hq]; [|img_lia]. rewrite Hq. img_apply Z.mod_divide; [img_lia|]. exists (256 * q + cur). img_lia. }
img_apply Forall_cons; [img_try (img_apply (JKf E' _ _ ENH))|].
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aNL _ _ _ _ ENL); clear - Hcur LR Z16; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 14%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 15%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 16%bv)); img_refl)|]. img_apply Forall_nil.
+ cbn [ms_mem restrict]. img_apply (sub_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EFN. rewrite ew_havoc_old by img_lia. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. destruct (node_vals (ms_mem ms) cur HI Hcur) as [VH VL].
unfold region_ok, R_ND. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite UA. split; [img_try (clear - Hcur Z9; numconst; img_lia)|]. split; [img_try (clear - Hcur Z9 Z10 Z16; numconst; img_lia)|]. split; [img_try (intros o Ho; exfalso; clear - Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_cons; [| img_apply Forall_nil])].
+ eapply (chunk_ok_val tfxsegs E' _ _ 0 8 (SOff aNH 0) (hashes cur)); [img_try (cbn [sv_denot]; rewrite ENH, unsigned_lit_small by img_exact HR; f_equal; img_lia) | img_try (img_exact HR) | img_try (cbn; img_lia) |].
rewrite Z.add_0_r. img_exact VH.
+ eapply (chunk_ok_val tfxsegs E' _ _ 8 4 (SOff aNL 0) (links cur)); [img_try (cbn [sv_denot]; rewrite ENL, unsigned_lit_small by (clear - LR Hcur Z16; img_lia); f_equal; img_lia) | img_try (clear - LR Hcur Z16; cbn; img_lia) | img_try (cbn; img_lia) |].
img_exact VL.
- cbn [ss_mem]. img_exact (ND_disj E' cur HE' Hcur UA).
Qed.
Definition POST_F : world tfxsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists E' ms' mat', c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md) /\ envD E' /\ INV (ms_mem ms') /\
(st_ok tfxsegs E' S_FOUND (restrict Hd ms') \/ (st_ok tfxsegs E' S_MISS (restrict Hd ms') /\ mem_trace tr (st_depot S) = false)).
Lemma find_loop : forall k cur E ms mat,
(Z.to_nat cur < k)%nat -> st_ok tfxsegs E S_FL (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
ew E aID = Z_to_bv 64 cur -> (cur = 0 \/ 1 <= cur <= nD) -> INVC cur ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POST_F.
Proof.
induction k as [|k IH]; intros cur E ms mat Hk HS HE HI EI Hcur HC; [img_try (exfalso; clear - Hk; img_lia)|].
pose proof Hwx_tfa as HWX. zone. fixu HE.
assert (UI : bv_unsigned (ew E aID) = cur) by (img_try (rewrite EI; img_apply unsigned_lit_small; clear - Hcur Z16; img_lia)). unfold aID in UI.
srr_branch_with tfxtbl_rtD_ok HS.
-
apply (condZ_lit E BC_EQ 42 0 0 true) in Hc; [| img_try (rewrite UI; clear - Hcur Z16; img_lia) | img_try (clear; img_lia)]. cbn beta iota in Hc. rewrite UI, Z.add_0_r in Hc. apply Z.eqb_eq in Hc.
srr_runG tfxtbl_rtD_ok HS. inv_stepD HI HE INV1.
lazymatch goal with |- SRr _ _ (mkCfg ?msA (with_vm_backing _ ?matc _)) _ => img_apply SRr_ret; split; [img_refl|]; exists E, msA, matc end.
split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact INV1)|]. right. split; [img_try (img_exact HS)|].
img_apply miss_no_trace. intros A. destruct (HC A) as [f Hf]. rewrite Hc in Hf. img_exact (chain_has_0 f _ Hf).
-
apply (condZ_lit E BC_EQ 42 0 0 false) in Hc; [| img_try (rewrite UI; clear - Hcur Z16; img_lia) | img_try (clear; img_lia)]. cbn beta iota in Hc. rewrite UI, Z.add_0_r in Hc. apply Z.eqb_neq in Hc.
assert (Hcur' : 1 <= cur <= nD) by (img_try (clear - Hcur Hc; img_lia)). clear Hcur Hc.
srr_runG tfxtbl_rtD_ok HS. inv_stepD HI HE INV1.
apply (st_ok_pin_regU E _ _ 12%bv (SLit (TFX_DEPOT + d_map1))) in HS; [| img_try (intros X; discriminate) |].
2:{ red_sr. rewrite U_SLit, (map1_valw E cur UI ltac:(img_try (clear - Hcur' Z16; img_lia))). img_refl. }
srr_runG tfxtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
rreg HS (10%bv : bv 5) G10.
pose proof (st_ok_reg_denot Hd E _ _ 11%bv HS) as G11. cbn [ms_regs restrict] in G11.
lazymatch type of G11 with _ = sv_denot E ?e =>
rewrite (denot_of_U E e _ (node_val E NB cur V32 UI ltac:(img_try (clear - Hcur' Z16; img_lia)) ltac:(img_try (clear - Z9; numconst; img_lia)) ltac:(img_try (clear - Z9 Z10; numconst; img_lia)))) in G11 end.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
destruct (reabs_FN E ss2 ms2 cur HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
Hcur' ltac:(img_try (rewrite G10; img_change (ew E 42) with (ew E aID); img_exact EI)) G11 INV2) as (HS' & HE' & EI' & ENH & ENL) end.
clear HS G10 G11. rename HS' into HS.
pose proof (hashes_u64 cur) as HR. pose proof (proj1 (D2 cur Hcur')) as LR.
pose proof (U36 _ (fixedU_of_envD _ HE')) as X36. unfold aHASH in X36.
pose proof ENH as X44. unfold aNH in X44. apply (f_equal bv_unsigned) in X44. rewrite unsigned_lit_small in X44 by img_exact HR.
pose proof ENL as X45. unfold aNL in X45. apply (f_equal bv_unsigned) in X45. rewrite unsigned_lit_small in X45 by (img_try (clear - LR Hcur' Z16; img_lia)).
srr_runG tfxtbl_rtD_ok HS. inv_stepD INV2 HE' INV3.
srr_branch_with tfxtbl_rtD_ok HS.
+
apply (condZ _ BC_NE 36 0 44 0 true) in Hc; [| img_try (rewrite X36; clear - Z18; img_lia) | img_try (rewrite X44; clear - HR; img_lia)]. cbn beta iota in Hc.
rewrite X36, X44, !Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
srr_runG tfxtbl_rtD_ok HS. inv_stepD INV3 HE' INV4.
rreg HS (11%bv : bv 5) G11.
lazymatch type of HS with st_ok _ ?E' ?ss5 (restrict _ ?ms5) =>
destruct (reabs_FL E' ss5 ms5 (links cur) HS HE' eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
ltac:(img_try (rewrite G11, <- X45; symmetry; img_apply Z_to_bv_bv_unsigned)) ltac:(img_try (clear - LR Hcur' Z16; img_lia))) as (HS2 & HE2 & EI2);
apply (IH (links cur) _ ms5 _ ltac:(img_try (clear - Hk LR Hcur'; img_lia)) HS2 HE2 INV4 EI2 ltac:(img_try (clear - LR Hcur'; img_lia)))
end.
img_apply (INVC_step cur HC ltac:(img_try (clear - Hcur'; img_lia))). intros X. img_apply Hc. rewrite X. img_refl.
+
srr_runG tfxtbl_rtD_ok HS. inv_stepD INV3 HE' INV4.
lazymatch goal with |- SRr _ _ (mkCfg ?msA (with_vm_backing _ ?matc _)) _ =>
lazymatch type of HS with st_ok _ ?E' _ _ => img_apply SRr_ret; split; [img_refl|]; exists E', msA, matc end end.
split; [img_refl|]. split; [img_try (img_exact HE')|]. split; [img_try (img_exact INV4)|]. left. img_exact HS.
Qed.
Lemma B_phase : forall E ms mat, st_ok tfxsegs E S_B (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POST_F.
Proof.
intros E ms mat HS HE HI. pose proof Hwx_tfa as HWX. zone. fixu HE.
srr_runG tfxtbl_rtD_ok HS. inv_stepD HI HE INV1.
pose proof (hd_and_val E HDv V38 ltac:(img_try (clear - Z20 Z16; img_lia))) as A1. pose proof (hd_and_val0 E HDv V38 ltac:(img_try (clear - Z20 Z16; img_lia))) as A0.
apply (st_ok_pin_regU E _ _ 25%bv (SOff aHD 0)) in HS; [| img_try (intros X; discriminate) |].
2:{ red_sr. rewrite A1, U_SOff. unfold aHD. rewrite V38. unfold zcanon, M64. rewrite Z.add_0_r. img_apply Z.mod_small. clear - Z20 Z16; img_lia. }
pose proof (st_ok_reg_denot Hd E _ _ 11%bv HS) as G11. cbn [ms_regs restrict] in G11.
lazymatch type of G11 with _ = sv_denot E ?e => rewrite (denot_of_U E e _ A0) in G11 end.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
destruct (reabs_FL E ss1 ms1 HDv HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
G11 ltac:(img_try (clear - Z20 Z16; img_lia))) as (HS' & HE' & EI');
apply (find_loop (Datatypes.S (Z.to_nat HDv)) HDv _ ms1 _ ltac:(img_try (clear; img_lia)) HS' HE' INV1 EI' ltac:(img_try (clear - Z20; img_lia)) INVC_start)
end.
Qed.
Lemma rd_unchanged : forall m a, INV m -> ~ WIN a -> 0 <= a < 2 ^ 64 -> aview tfxsegs Hd m a = rd0 a.
Proof. intros m a [IF _] Hw Ha. img_apply (aview_same Hd). img_apply IF. rewrite unsigned_lit_small by img_exact Ha. img_exact Hw. Qed.
Lemma val_mem_rdZ : forall m a (w : nat) v k, val_mem tfxsegs (mrestrict Hd m) a w v -> (k < w)%nat ->
aview tfxsegs Hd m (a + Z.of_nat k) = Some (YG0h.le_byte v w k).
Proof.
intros m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma val_mem_rd32 : forall m a v, val_mem tfxsegs (mrestrict Hd m) a 4 v -> rd32 (aview tfxsegs Hd m) a v.
Proof. intros m a v Hv k Hk. img_exact (val_mem_rdZ m a 4 v k Hv Hk). Qed.
Lemma val_mem_rd64 : forall m a v, val_mem tfxsegs (mrestrict Hd m) a 8 v -> rd64 (aview tfxsegs Hd m) a v.
Proof. intros m a v Hv k Hk. img_exact (val_mem_rdZ m a 8 v k Hv Hk). Qed.
Lemma val_mem_cell : forall m e (w : nat) v, val_mem tfxsegs (mrestrict Hd m) (aeval B ly e) w (aeval B ly v) -> cell_holds B ly (aview tfxsegs Hd m) (ACell e w (AV v)).
Proof. intros m e w v Hv k Hk. cbn [c_at c_w]. img_exact (val_mem_rdZ m _ w _ k Hv Hk). Qed.
Lemma tab_unchanged : forall m b k, INV m -> 0 <= b < d_tab_words -> b <> bkt -> 0 <= k < 4 ->
aview tfxsegs Hd m (as_depot B + 4 * b + k) = rd0 (as_depot B + 4 * b + k).
Proof.
intros m b k HI Hb Hbk Hk. zone. rewrite (ts_depot B HB). img_apply (rd_unchanged m _ HI); [| img_try (clear - Hb Hk; numconst; img_lia)].
unfold WIN, S2, NUQ, NDN, SLOT. zoneNS. clear - Hb Hbk Hk Z9 Z11 Z1 Z3 Z16 Z17 Z19 NZ SZ'. numconst. img_lia.
Qed.
Lemma depot_ok_found : forall m, INV m -> val_mem tfxsegs (mrestrict Hd m) S2 4 HDv -> depot_ok B ly (aview tfxsegs Hd m) S.
Proof.
intros m HI VT. exists heads, links. fold nD. img_change (fun id : Z => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S) [])) with hashes.
split; [| img_try (split)].
- intros b Hb. destruct (D1 b Hb) as [R1 R2]. split; [img_try (img_exact R1)|].
destruct (Z.eq_dec b bkt) as [->|Hne].
+ rewrite (ts_depot B HB). fold HDv. img_change (TFX_DEPOT + 4 * bkt) with S2. img_exact (val_mem_rd32 m _ _ VT).
+ intros k Hk. rewrite (tab_unchanged m b (Z.of_nat k) HI Hb Hne ltac:(img_lia)). img_exact (R2 k Hk).
- intros id Hid. destruct (D2 id Hid) as (L1 & _ & _). split; [img_try (img_exact L1)|]. destruct (node_vals m id HI Hid) as [VH VL].
rewrite hashes_mod. split; [img_try (img_exact (val_mem_rd64 m _ _ VH)) | img_try (img_exact (val_mem_rd32 m _ _ VL))].
- img_exact D3.
Qed.
Lemma depot_cells_hold : forall m S', INV m -> st_regions S' = st_regions S ->
val_mem tfxsegs (mrestrict Hd m) NUQ 4 (depot_ids S') -> val_mem tfxsegs (mrestrict Hd m) TFX_STORE 8 (Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S') ->
Forall (cell_holds B ly (aview tfxsegs Hd m)) (depot_cells ly S').
Proof.
intros m S' HI _ V1 V3. zone. pose proof HCELLS as HC. unfold depot_cells in HC |- *.
apply Forall_inv_tail in HC. pose proof (Forall_inv HC) as C2. do 2 apply Forall_inv_tail in HC. pose proof (Forall_inv HC) as C4. clear HC.
img_apply Forall_cons. { img_apply val_mem_cell. cbn [aeval]. rewrite (ts_depot B HB). img_exact V1. }
img_apply Forall_cons. { eapply cell_holds_agree; [img_try (img_exact C2)|]. intros k Hk. cbn [c_at c_w aeval c8 c4 z8 z4] in Hk |- *. rewrite (ts_depot B HB). img_apply (rd_unchanged m _ HI); [| img_try (clear - Hk; numconst; img_lia)].
unfold WIN, S2, NUQ, NDN, SLOT. zoneNS. clear - Hk Z9 Z11 Z1 Z3 Z16 Z17 Z19 NZ SZ'. numconst. img_lia. }
img_apply Forall_cons. { img_apply val_mem_cell. cbn [aeval]. rewrite (ts_store B HB). unfold s_total. rewrite Z.add_0_r. img_exact V3. }
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply cell_holds_agree; [img_try (img_exact C4)|]. intros k Hk. cbn [c_at c_w aeval c8 c4 z8 z4] in Hk |- *. rewrite (ts_store B HB). img_apply (rd_unchanged m _ HI); [| img_try (clear - Hk; unfold s_block0 in *; numconst; img_lia)].
unfold WIN, S2, NUQ, NDN, SLOT. unfold s_block0 in *. zoneNS. clear - Hk Z9 Z11 Z1 Z3 Z16 Z17 Z19 NZ SZ'. numconst. img_lia.
Qed.
Lemma vis_kept : forall m, INV m -> Forall (range_vis B ly (aview tfxsegs Hd m)) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)].
Proof. intros m HI. img_apply (Forall_range_vis_keep B ly rd0); [| img_try (img_exact HVIS)]. intros a Ha. img_exact (INV_aview m a HI Ha). Qed.
Lemma depot_mem_ok_found : forall m, INV m -> val_mem tfxsegs (mrestrict Hd m) S2 4 HDv -> val_mem tfxsegs (mrestrict Hd m) NUQ 4 nD ->
val_mem tfxsegs (mrestrict Hd m) TFX_STORE 8 TOT -> depot_mem_ok B ly S (aview tfxsegs Hd m).
Proof.
intros m HI VT V1 V3. split; [| img_try (split; [img_exact (depot_ok_found m HI VT) | img_exact (vis_kept m HI)])].
img_apply (depot_cells_hold m S HI eq_refl); [img_try (img_exact V1) | img_try (img_exact V3)].
Qed.
Definition wsafe {imgk : img} (a : Z) (w : nat) : bool :=
(0 <=? a) && forallb (fun k => let x := a + Z.of_nat k in
negb (((TFX_STORE <=? x) && (x <? TFX_STORE + 8)) || ((TFX_STORE + 24 <=? x) && (x <? TFX_STORE + 28)) ||
((TFX_DEPOT <=? x) && (x <? TFX_DEPOT + d_nuniq + 4)) ||
(x <? TFX_IMG_LO) || ((TFX_IMG_END <=? x) && (x <? kLowShadowBeg)) || (kLowShadowEnd <=? x))) (seq 0 (Nat.max 1 w)).
Definition cell_safe {imgk : img} (c : acell) : bool :=
match c_at c with
| ANum a => wsafe a (c_w c)
| ATsd o => wsafe (TFX_TSD + o) (c_w c)
| ATp o => wsafe (TFX_TP + o) (c_w c)
| AInst o => wsafe (TFX_INST + o) (c_w c)
| AT o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? kThreadObjSize)
| AC o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? 256)
| AD o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? 4096)
| _ => false
end.
Lemma wsafe_sound : forall a w, wsafe a w = true -> forall k, 0 <= k < Z.max 1 (Z.of_nat w) -> ~ WIN (a + k) /\ 0 <= a + k < 2 ^ 64.
Proof.
intros a w H k Hk. zone. unfold wsafe in H. apply andb_prop in H as [Ha H]. apply Z.leb_le in Ha.
pose proof (proj1 (forallb_forall _ _) H (Z.to_nat k) ltac:(img_try (img_apply in_seq; clear - Hk; img_lia))) as X. cbn beta in X. rewrite Z2Nat.id in X by (img_try (clear - Hk; img_lia)).
apply Bool.negb_true_iff in X.
apply Bool.orb_false_iff in X as [X XHI]. apply Bool.orb_false_iff in X as [X XMID]. apply Bool.orb_false_iff in X as [X XLO].
apply Bool.orb_false_iff in X as [X X1]. apply Bool.orb_false_iff in X as [X X0].
assert (L : forall p q x, ((p <=? x) && (x <? q)) = false -> ~ (p <= x < q)) by (img_try (clear; intros p q x E [A C]; rewrite (proj2 (Z.leb_le _ _) A), (proj2 (Z.ltb_lt _ _) C) in E; discriminate)).
apply L in X. apply L in X0. apply L in X1. apply L in XMID. apply Z.ltb_ge in XLO. apply Z.leb_gt in XHI.
unfold WIN, S2, NUQ, NDN, SLOT. zoneNS. clear - X X0 X1 XLO XMID XHI Ha Hk Z1 Z3 Z9 Z11 Z16 Z17 Z19 NZ SZ'. numconst. unfold TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd in *. img_lia.
Qed.
Lemma rd_unchanged_mod : forall m a, INV m -> ~ WIN (a mod 2 ^ 64) -> aview tfxsegs Hd m a = rd0 a.
Proof. intros m a [IF _] Hw. img_apply (aview_same Hd). img_apply IF. rewrite Z_to_bv_unsigned. img_exact Hw. Qed.
Lemma le_byte_mod64 : forall v k, YG0h.le_byte v 8 k = YG0h.le_byte (v mod 2 ^ 64) 8 k.
Proof. intros v k. unfold YG0h.le_byte. img_change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by img_lia. img_refl. Qed.
Lemma tsd_val : ly_tsd ly mod 2 ^ 64 = TFX_TSD.
Proof.
pose proof HCONST as HC. rewrite (ts_const B HB) in HC.
pose proof (proj1 (Forall_forall _ _) HC (c8 (ATp (-88)) (ATsd 0)) ltac:(img_try (unfold Tfx_const, Tfx_const_sym; cbn; tauto))) as A.
pose proof (proj1 (Forall_forall _ _) HC (z8 (ANum (0x5dd0f8 + D_10c0)) (0x5fe4f8 + D_10c0)) ltac:(img_try (img_apply in_app_iff; right; img_apply in_app_iff; left; unfold Tfx_const_abs; cbn; tauto))) as Bc.
cbn [cell_holds c_at c_w c_val c8 z8 aeval] in A, Bc. rewrite (ts_tp B HB) in A. img_change (TFX_TP + -88) with (6148344 + D_10c0) in A. rewrite Z.add_0_r in A.
assert (E8 : forall k, (k < 8)%nat -> YG0h.le_byte (ly_tsd ly mod 2 ^ 64) 8 k = YG0h.le_byte (6284536 + D_10c0) 8 k).
{ intros k Hk. rewrite <- le_byte_mod64. specialize (A k Hk). specialize (Bc k Hk). rewrite A in Bc. injection Bc as E. img_exact E. }
pose proof (le_bytes8_sum (ly_tsd ly mod 2 ^ 64) ltac:(img_try (img_apply Z.mod_pos_bound; img_lia))) as S1. cbn beta zeta in S1.
rewrite !E8 in S1 by img_lia. rewrite <- S1. img_case; vm_compute. all: img_refl.
Qed.
Lemma d_facts : zdisjoint (NB, kNodesBlockSize) (ly_D ly, 4096) /\ zdisjoint (SB, kStoreBlockSize) (ly_D ly, 4096) /\
zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ 4096 <= ly_D ly /\ ly_D ly + 4096 <= 140737479966720.
Proof.
pose proof (lo_app ly LY) as HH. unfold owned_extents in HH.
pose proof (proj1 (Forall_forall _ _) HH (ly_D ly, 4096) ltac:(img_try (cbn; tauto))) as [XD1 XD2]. cbn [fst snd] in XD1, XD2.
assert (XD2' : ly_D ly + 4096 <= 140737479966720) by (img_try (clear - XD2; ceil; unfold kLowShadowBeg, ASAN_CEIL in *; img_lia)). clear XD2.
pose proof (lo_disj ly LY) as PD. unfold static_extents, owned_extents in PD. cbn [app] in PD.
destruct PD as (_ & _ & _ & _ & FNB & FSB & _ & FD & _).
pose proof (proj1 (Forall_forall _ _) FNB (ly_D ly, 4096) ltac:(img_try (cbn; tauto))) as ND.
pose proof (proj1 (Forall_forall _ _) FSB (ly_D ly, 4096) ltac:(img_try (cbn; tauto))) as SD.
pose proof (proj1 (Forall_forall _ _) FD (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(img_try (cbn; tauto))) as DK.
repeat split; assumption.
Qed.
Lemma const_cell_kept : forall m c, INV m -> cell_safe c = true -> cell_holds B ly rd0 c -> cell_holds B ly (aview tfxsegs Hd m) c.
Proof.
intros m c HI H Hc. zone. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TN & TS & TK & NC & SC & CK & TH & CH).
eapply cell_holds_agree; [img_try (img_exact Hc)|]. intros k Hk.
unfold cell_safe in H. destruct (c_at c) as [a|o|o|o|o|o|o|o|r o|o|o|o|o|o|o|o|o|o|e]; try discriminate H; cbn [aeval].
- destruct (wsafe_sound a _ H k Hk) as [X R]. img_apply (rd_unchanged m _ HI X R).
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zdisjoint in TN, TS, TK. cbn [fst snd] in TN, TS, TK.
pose proof (zone3_off_img _ _ (ly_T ly + o + k) T_zone ltac:(img_try (clear - H1 H2 Hk; unfold kThreadObjSize in *; img_lia))) as TO. unfold off_img, TFX_IMG_LO, TFX_IMG_END in TO.
img_apply (rd_unchanged m _ HI); unfold WIN, S2, NUQ, NDN, SLOT; zoneNS; clear - H1 H2 Hk TN TS TK TO Z1 Z3 Z4 Z9 Z11 Z16 Z17 Z19 NZ SZ'; unfold kThreadObjSize in *; numconst; img_lia.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zdisjoint in NC, SC, CK. cbn [fst snd] in NC, SC, CK.
pose proof (zone3_off_img _ _ (ly_C ly + o + k) C_zone ltac:(img_try (clear - H1 H2 Hk; img_lia))) as CO. unfold off_img, TFX_IMG_LO, TFX_IMG_END in CO.
img_apply (rd_unchanged m _ HI); unfold WIN, S2, NUQ, NDN, SLOT; zoneNS; clear - H1 H2 Hk NC SC CK CO Z1 Z3 Z4 Z9 Z11 Z16 Z17 Z19 NZ SZ'; numconst; img_lia.
- destruct (wsafe_sound _ _ H k Hk) as [X R]. img_apply (rd_unchanged_mod m _ HI).
assert (EQ : (ly_tsd ly + o + k) mod 2 ^ 64 = TFX_TSD + o + k).
{ replace (ly_tsd ly + o + k) with (ly_tsd ly + (o + k)) by (img_try (clear; img_lia)). rewrite <- Zplus_mod_idemp_l, tsd_val. rewrite Z.mod_small by (img_try (clear - R; img_lia)). clear; img_lia. }
rewrite EQ. img_exact X.
- rewrite (ts_inst B HB). destruct (wsafe_sound _ _ H k Hk) as [X R]. img_apply (rd_unchanged m _ HI X R).
- rewrite (ts_tp B HB). destruct (wsafe_sound _ _ H k Hk) as [X R]. img_apply (rd_unchanged m _ HI X R).
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof d_facts as (DN & DS & DK & DH & DH2).
unfold zdisjoint in DN, DS, DK. cbn [fst snd] in DN, DS, DK.
pose proof (zone3_off_img _ _ (ly_D ly + o + k) D_zone ltac:(img_try (clear - H1 H2 Hk; img_lia))) as DO. unfold off_img, TFX_IMG_LO, TFX_IMG_END in DO.
img_apply (rd_unchanged m _ HI); unfold WIN, S2, NUQ, NDN, SLOT; zoneNS; clear - H1 H2 Hk DN DS DK DO Z1 Z3 Z4 Z9 Z11 Z16 Z17 Z19 NZ SZ'; numconst; img_lia.
Qed.
Lemma const_kept : forall m, INV m -> Forall (cell_holds B ly (aview tfxsegs Hd m)) (as_const B ly).
Proof.
intros m HI. pose proof HCONST as HC. rewrite (ts_const B HB) in HC |- *.
assert (CK : forallb cell_safe (Tfx_const ly) = true) by (img_try ((img_case; vm_compute); img_refl)).
img_apply Forall_forall. intros c Hc. img_apply (const_cell_kept m c HI); [| img_try (img_exact (proj1 (Forall_forall _ _) HC c Hc))].
img_exact (proj1 (forallb_forall _ _) CK c Hc).
Qed.
Definition DPOST : world tfxsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists z regs' mem' mat, c' = mkCfg (mkst regs' (getr regs 1%bv) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
aok S (KDepot tr) z /\ regs_preserved regs regs' /\
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent Hd mem a -> apresent Hd mem' a) /\
depot_mem_ok B ly (depot_after z tr S) (aview tfxsegs Hd mem') /\
Forall (cell_holds B ly (aview tfxsegs Hd mem')) (as_const B ly).
Definition exit_regs_ok {imgk : img} (sr : list sv) : bool :=
forallb (fun p : bv 5 * sv => sv_eqb (sr_get sr (fst p)) (snd p))
[(1%bv, SOff 1%nat 0); (2%bv, SOff 2%nat 0); (3%bv, SLit TFX_GP); (4%bv, SLit TFX_TP); (8%bv, SOff 8%nat 0); (9%bv, SOff 9%nat 0);
(18%bv, SOff 18%nat 0); (19%bv, SOff 19%nat 0); (20%bv, SOff 20%nat 0); (21%bv, SOff 21%nat 0); (22%bv, SOff 22%nat 0); (23%bv, SOff 23%nat 0);
(24%bv, SOff 24%nat 0); (25%bv, SOff 25%nat 0); (26%bv, SOff 26%nat 0); (27%bv, SOff 27%nat 0)].
Lemma exit_regs : forall E ss ms, st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> exit_regs_ok (ss_regs ss) = true ->
regs_preserved regs (ms_regs ms) /\ getr (ms_regs ms) 1%bv = getr regs 1%bv.
Proof.
intros E ss ms HS HE Hck.
assert (G : forall (r : bv 5) e, sv_eqb (sr_get (ss_regs ss) r) e = true -> getr (ms_regs ms) r = sv_denot E e).
{ intros r e Hq. apply sv_eqb_eq in Hq. rewrite <- Hq. img_exact (st_ok_reg_denot Hd E ss ms r HS). }
unfold exit_regs_ok in Hck. cbn [forallb fst snd] in Hck. repeat (apply andb_prop in Hck as [?GG Hck]).
assert (A : forall (r : bv 5) (n : nat), sv_eqb (sr_get (ss_regs ss) r) (SOff n 0) = true -> (n < K_D)%nat -> Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = getr regs r).
{ intros r n Hq Hn Hrn. rewrite (G r _ Hq). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE n Hn). img_exact (Er n r Hrn). }
unfold K_D in A. split.
- img_apply regs_preserved_intro.
+ img_apply (A 2%bv 2%nat GG0); [img_lia | img_refl].
+ rewrite (G 3%bv _ GG1). cbn [sv_denot]. rewrite R3, (ts_gp B HB). img_refl.
+ rewrite (G 4%bv _ GG2). cbn [sv_denot]. rewrite R4. img_refl.
+ img_apply (A 8%bv 8%nat GG3); [img_lia | img_refl].
+ img_apply (A 9%bv 9%nat GG4); [img_lia | img_refl].
+ img_apply (A 18%bv 18%nat GG5); [img_lia | img_refl].
+ img_apply (A 19%bv 19%nat GG6); [img_lia | img_refl].
+ img_apply (A 20%bv 20%nat GG7); [img_lia | img_refl].
+ img_apply (A 21%bv 21%nat GG8); [img_lia | img_refl].
+ img_apply (A 22%bv 22%nat GG9); [img_lia | img_refl].
+ img_apply (A 23%bv 23%nat GG10); [img_lia | img_refl].
+ img_apply (A 24%bv 24%nat GG11); [img_lia | img_refl].
+ img_apply (A 25%bv 25%nat GG12); [img_lia | img_refl].
+ img_apply (A 26%bv 26%nat GG13); [img_lia | img_refl].
+ img_apply (A 27%bv 27%nat GG14); [img_lia | img_refl].
- img_apply (A 1%bv 1%nat GG); [img_lia | img_refl].
Qed.
Lemma exit_frame : forall m, INV m ->
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> m x = mem x) /\
(forall a, apresent Hd mem a -> apresent Hd m a).
Proof.
intros m HI. split; [| img_try (intros a Ha; img_exact (INV_apresent m a HI Ha))].
intros x N1 N2. img_apply (proj1 HI). intros Hw. destruct (WIN_foot _ Hw) as [H|H]; [img_try (img_exact (N1 H)) | img_try (img_exact (N2 H))].
Qed.
Lemma found_exit : forall E ms mat, st_ok tfxsegs E S_FOUND (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat HS HE HI. pose proof Hwx_tfa as HWX. zone. fixu HE.
destruct (exit_regs E _ ms HS HE ltac:(img_try ((img_case; vm_compute); img_refl))) as [RP R1].
eapply (SRr_ret_at tfxsegs tfxtbl_rtD tfxtbl_rtD_ok HWX W); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_collapse. split; [img_refl|].
exists 0, (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split; [img_try (left; img_refl)|]. split; [img_try (img_exact RP)|].
destruct (exit_frame _ HI) as [F1 F2]. split; [img_try (img_exact F1)|]. split; [img_try (img_exact F2)|].
split; [| img_try (img_exact (const_kept _ HI))].
cbn [depot_after Z.eqb]. img_apply (depot_mem_ok_found _ HI).
- memv HS 7%nat 0%nat; [img_try (unfold aS2; rewrite V37; img_lia) | img_try (cbn [sv_denot]; unfold aHD; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- (Z_to_bv_bv_unsigned 64 (ew E 38)), V38; img_refl) | img_try (clear - Z20 Z16; img_lia)].
- memv HS 6%nat 0%nat; [img_try ((img_case; vm_compute); img_refl) | img_try (cbn [sv_denot]; unfold aN; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- (Z_to_bv_bv_unsigned 64 (ew E 35)), V35; img_refl) | img_try (clear - Z16; img_lia)].
- memv HS 8%nat 0%nat; [img_try ((img_case; vm_compute); img_refl) | img_try (cbn [sv_denot]; unfold aTOT; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- (Z_to_bv_bv_unsigned 64 (ew E 34)), V34; img_refl) | img_try (clear - Z17; img_lia)].
Qed.
Lemma entry_phase : forall mat, (1 <= length tr)%nat -> SRr tfxsegs W (mkCfg msD0 (with_vm_backing (m_vm_lazy md) mat md)) POST_B.
Proof.
intros mat Htr1. pose proof Hwx_tfa as HWX. zone. pose proof (SEED_ok Htr1) as HS. pose proof INV_mem as HI. pose proof envD_E0 as HE. fixu HE.
srr_run_toG tfxtbl_rtD_ok HS A_HLOOP. inv_stepD HI HE INV1.
apply (st_ok_pin_regU E0 _ _ 13%bv (SLit 0)) in HS; [| img_try (intros X; discriminate) |].
2:{ red_sr. img_apply (pin_tag0 E0 _ V11). clear - Z8; img_lia. }
rreg HS (11%bv : bv 5) G11. rewrite E10 in G11.
pose proof (st_ok_reg_denot Hd E0 _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot _ ?e => rewrite (denot_of_U E0 e _ (h0_val E0 _ V11 ltac:(img_try (clear - Z8; img_lia)))) in G12 end.
pose proof (st_ok_reg_denot Hd E0 _ _ 14%bv HS) as G14. cbn [ms_regs restrict] in G14.
lazymatch type of G14 with _ = sv_denot _ ?e => rewrite (denot_of_U E0 e _ (end_val E0 _ buf V11 ltac:(img_try (clear - Z8; img_lia)) V10 ltac:(img_try (clear - Z1 Z5; img_lia)) ltac:(img_try (clear - Z2 Z6 Z8; img_lia)))) in G14 end.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
destruct (reabs_H E0 ss1 ms1 0%nat HS envD_E0 eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop)))
Htr1 ltac:(img_try (rewrite G11; f_equal; img_lia)) ltac:(img_try (rewrite G12; img_refl)) G14 INV1) as (HS' & HE' & EW & EHh & EP & EE);
apply (hash_loop (length tr) 0%nat _ ms1 _ ltac:(img_try (clear; img_lia)) Htr1 HS' HE' INV1 EW EHh EP EE)
end.
Qed.
Definition S_ins : astate := set_depot (st_depot S ++ [tr]) S.
Definition heads' (b : Z) : Z := if b =? bkt then nD + 1 else heads b.
Definition links' (id : Z) : Z := if id =? nD + 1 then HDv else links id.
Definition hashes' : Z -> Z := fun id => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S_ins) []).
Lemma nD_ins : depot_ids S_ins = nD + 1.
Proof. unfold depot_ids, S_ins, nD, depot_ids. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. img_lia. Qed.
Lemma frames_shift : forall (l : list (list Z)) a,
fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) a l = fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 l + a.
Proof. induction l as [|t l IH]; intros a; cbn [fold_right]; [img_lia|]. rewrite (IH a). img_lia. Qed.
Lemma frames_ins : depot_frames S_ins = depot_frames S + (Z.of_nat (length tr) + 1).
Proof.
unfold depot_frames, S_ins. cbn [st_depot set_depot]. rewrite fold_right_app. cbn [fold_right]. rewrite frames_shift. img_lia.
Qed.
Lemma hashes'_old : forall id, id <= nD -> hashes' id = hashes id.
Proof.
intros id Hid. unfold hashes', hashes, depot_traces, S_ins. cbn [st_depot set_depot].
img_change (ly_tr0 ly :: st_depot S ++ [tr]) with ((ly_tr0 ly :: st_depot S) ++ [tr]). rewrite app_nth1; [img_refl|].
cbn [length]. unfold nD, depot_ids in Hid. img_lia.
Qed.
Lemma hashes'_new : hashes' (nD + 1) = HSH.
Proof.
unfold hashes', HSH, depot_traces, S_ins. cbn [st_depot set_depot]. rewrite HDH.
img_change (ly_tr0 ly :: st_depot S ++ [tr]) with ((ly_tr0 ly :: st_depot S) ++ [tr]). rewrite app_nth2 by (img_try (cbn [length]; unfold nD, depot_ids; img_lia)).
replace (Z.to_nat (nD + 1 - 1) - length (ly_tr0 ly :: st_depot S))%nat with 0%nat by (img_try (cbn [length]; unfold nD, depot_ids; img_lia)). img_refl.
Qed.
Lemma chain_fuel : forall L Hh f cur h, chain_has L Hh f cur h -> chain_has L Hh (Datatypes.S f) cur h.
Proof. induction f as [|f IH]; intros cur h Hc; cbn in Hc |- *; [img_try (destruct Hc)|]. destruct Hc as [H1 [H2|H2]]; [img_try (tauto) | img_try (split; [img_exact H1 | right; img_exact (IH _ _ H2)])]. Qed.
Lemma chain_ext : forall f cur h, 0 <= cur <= nD -> chain_has links hashes f cur h -> chain_has links' hashes' f cur h.
Proof.
induction f as [|f IH]; intros cur h Hcur Hc; cbn in Hc |- *; [img_try (destruct Hc)|]. destruct Hc as [H1 H2].
assert (R : 1 <= cur <= nD) by img_lia. pose proof (proj1 (D2 cur R)) as LR.
split; [img_try (img_exact H1)|]. rewrite (hashes'_old cur) by img_lia.
assert (EL : links' cur = links cur) by (img_try (unfold links'; replace (cur =? nD + 1) with false by (symmetry; img_apply Z.eqb_neq; img_lia); img_refl)).
rewrite EL. destruct H2 as [H2|H2]; [img_try (left; img_exact H2) | img_try (right)]. img_apply IH; [img_try (clear - LR Hcur; img_lia) | img_try (img_exact H2)].
Qed.
Lemma depot_ok_ins : forall m, INV m ->
val_mem tfxsegs (mrestrict Hd m) S2 4 (nD + 1) -> val_mem tfxsegs (mrestrict Hd m) NDN 8 HSH -> val_mem tfxsegs (mrestrict Hd m) (NDN + 8) 4 HDv ->
depot_ok B ly (aview tfxsegs Hd m) S_ins.
Proof.
intros m HI VT VH VL. zone. exists heads', links'. rewrite nD_ins. img_change (fun id : Z => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S_ins) [])) with hashes'.
split; [| img_try (split)].
- intros b Hb. destruct (D1 b Hb) as [R1 R2]. unfold heads'. destruct (Z.eqb_spec b bkt) as [->|Hne].
+ split; [img_try (clear - Z16; img_lia)|]. rewrite (ts_depot B HB). img_change (TFX_DEPOT + 4 * bkt) with S2. img_exact (val_mem_rd32 m _ _ VT).
+ split; [img_try (clear - R1; img_lia)|]. intros k Hk. rewrite (tab_unchanged m b (Z.of_nat k) HI Hb Hne ltac:(img_lia)). img_exact (R2 k Hk).
- intros id Hid. unfold links'. destruct (Z.eqb_spec id (nD + 1)) as [->|Hne].
+ split; [img_try (clear - Z20; img_lia)|]. rewrite hashes'_new, (Z.mod_small HSH (2 ^ 64)) by img_exact Z18. fold NDN. split; [img_try (img_exact (val_mem_rd64 m _ _ VH)) | img_try (img_exact (val_mem_rd32 m _ _ VL))].
+ assert (R : 1 <= id <= nD) by (img_try (clear - Hid Hne; img_lia)). destruct (D2 id R) as (L1 & _ & _). split; [img_try (img_exact L1)|].
rewrite (hashes'_old id) by img_lia. destruct (node_vals m id HI R) as [NVH NVL]. rewrite hashes_mod.
split; [img_try (img_exact (val_mem_rd64 m _ _ NVH)) | img_try (img_exact (val_mem_rd32 m _ _ NVL))].
- intros id Hid. replace (Z.to_nat (nD + 1)) with (Datatypes.S (Z.to_nat nD)) by (img_try (clear - Z16; img_lia)). destruct (Z.eqb_spec id (nD + 1)) as [->|Hne].
+ rewrite hashes'_new, (Z.mod_small HSH (2 ^ 64)) by img_exact Z18. fold bkt. unfold heads'. rewrite Z.eqb_refl. cbn [chain_has].
split; [img_try (clear - Z16; img_lia) | img_try (left; img_exact hashes'_new)].
+ assert (R : 1 <= id <= nD) by (img_try (clear - Hid Hne; img_lia)). rewrite (hashes'_old id) by img_lia. pose proof (D3 id R) as C.
destruct (Z.eq_dec ((hashes id mod 2 ^ 64) mod d_tab_words) bkt) as [Eb|Nb].
* rewrite Eb in C |- *. fold HDv in C. unfold heads'. rewrite (Z.eqb_refl bkt). cbn [chain_has]. split; [img_try (clear - Z16; img_lia) | img_try (right)].
replace (links' (nD + 1)) with HDv by (img_try (unfold links'; rewrite Z.eqb_refl; img_refl)). img_apply chain_ext; [img_try (clear - Z20; img_lia) | img_try (img_exact C)].
* unfold heads'. replace ((hashes id mod 2 ^ 64) mod d_tab_words =? bkt) with false by (img_try (symmetry; img_apply Z.eqb_neq; img_exact Nb)).
img_apply chain_fuel. img_apply chain_ext; [| img_try (img_exact C)]. img_exact (proj1 (D1 _ ltac:(img_try (unfold d_tab_words; img_apply Z.mod_pos_bound; img_lia)))).
Qed.
Lemma depot_mem_ok_ins : forall m, INV m ->
val_mem tfxsegs (mrestrict Hd m) S2 4 (nD + 1) -> val_mem tfxsegs (mrestrict Hd m) NUQ 4 (nD + 1) ->
val_mem tfxsegs (mrestrict Hd m) TFX_STORE 8 (TOT + Z.of_nat (length tr) + 1) ->
val_mem tfxsegs (mrestrict Hd m) NDN 8 HSH -> val_mem tfxsegs (mrestrict Hd m) (NDN + 8) 4 HDv ->
depot_mem_ok B ly S_ins (aview tfxsegs Hd m).
Proof.
intros m HI VT V1 V3 VH VL. split; [| img_try (split; [img_exact (depot_ok_ins m HI VT VH VL) | img_exact (vis_kept m HI)])].
img_apply (depot_cells_hold m S_ins HI eq_refl); rewrite ?nD_ins, ?frames_ins; [img_try (img_exact V1)|]. unfold TOT in V3.
replace (Z.of_nat (length (ly_tr0 ly)) + 1 + (depot_frames S + (Z.of_nat (length tr) + 1))) with (Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S + Z.of_nat (length tr) + 1) by img_lia. img_exact V3.
Qed.
Definition EEND (E : env) (rg : bvmap 5 word) : env := havoc E 42 [getr rg 11%bv; getr rg 13%bv; getr rg 14%bv; getr rg 16%bv].
Lemma reabs_END : forall E ss ms,
st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_END -> reabs_check LT42 ss ENDREGS ENDF = true -> submem ENDMEM (ss_mem ss) ->
st_ok tfxsegs (EEND E (ms_regs ms)) S_END (restrict Hd ms) /\ envD (EEND E (ms_regs ms)).
Proof.
intros E ss ms HS HE Hpc Hck Hsub. set (E' := EEND E (ms_regs ms)).
assert (HE' : envD E') by (img_try (img_apply envD_havoc; [img_try (img_exact HE) | img_try (unfold K_D; img_lia)])). split; [| img_try (img_exact HE')].
unfold S_END. rewrite <- Hpc.
img_apply (st_ok_reabs tfxsegs LT42 E E' ss (restrict Hd ms) ENDREGS ENDMEM ENDF HS (agree_pd_havoc E 42 _ ltac:(img_lia)) Hck).
- cbn [ms_regs restrict]. img_apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | []]]]]; injection H as <- <-.
+ img_apply (OBr E' _ _ 11%bv 42%nat (getr (ms_regs ms) 11%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 13%bv 43%nat (getr (ms_regs ms) 13%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 14%bv 44%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ img_apply (OBr E' _ _ 16%bv 45%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
- assert (FO : fact_obls LT42 ENDF = [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f)]) by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 11%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 13%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 14%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 16%bv)); img_refl)|]. img_apply Forall_nil.
- cbn [ms_mem restrict]. img_apply (sub_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EEND. rewrite ew_havoc_old by img_lia. img_refl.
Qed.
Lemma ins_exit : forall E ms mat, st_ok tfxsegs E S_END (restrict Hd ms) -> envD E -> INV (ms_mem ms) -> mem_trace tr (st_depot S) = false ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat HS HE HI MT. pose proof Hwx_tfa as HWX. zone. fixu HE.
destruct (exit_regs E _ ms HS HE ltac:(img_try ((img_case; vm_compute); img_refl))) as [RP R1].
eapply (SRr_ret_at tfxsegs tfxtbl_rtD tfxtbl_rtD_ok HWX W); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_collapse. split; [img_refl|].
exists 1, (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split; [img_try (right; split; [img_refl | img_exact MT])|]. split; [img_try (img_exact RP)|].
destruct (exit_frame _ HI) as [F1 F2]. split; [img_try (img_exact F1)|]. split; [img_try (img_exact F2)|].
split; [| img_try (img_exact (const_kept _ HI))].
cbn [depot_after Z.eqb]. img_change (set_depot (st_depot S ++ [tr]) S) with S_ins. img_apply (depot_mem_ok_ins _ HI).
- memv HS 6%nat 0%nat; [img_try (unfold aS2; rewrite V37; img_lia) | img_try (cbn [sv_denot]; unfold aN; rewrite V35; img_refl) | img_try (clear - Z16; img_lia)].
- memv HS 5%nat 0%nat; [img_try ((img_case; vm_compute); img_refl) | img_try (cbn [sv_denot]; rewrite V35; img_refl) | img_try (clear - Z16; img_lia)].
- memv HS 7%nat 0%nat; [img_try ((img_case; vm_compute); img_refl) | img_try (img_apply denot_of_U; rewrite (tot_val E _ _ V11 V34); clear - Z8 Z17; img_lia) | img_try (clear - Z8 Z17; img_lia)].
- memv HS 10%nat 2%nat; [img_try (unfold aNDN; rewrite V40; img_lia) | img_try (cbn [sv_denot]; unfold aHASH; rewrite Z.add_0_r, V36; img_refl) | img_try (img_exact Z18)].
- memv HS 10%nat 0%nat; [img_try (unfold aNDN; rewrite V40; img_lia) | img_try (cbn [sv_denot]; unfold aHD; rewrite Z.add_0_r, V38; img_refl) | img_try (clear - Z20 Z16; img_lia)].
Qed.
Lemma tail_phase : forall E ms mat, st_ok tfxsegs E S_T1 (restrict Hd ms) -> envD E -> INV (ms_mem ms) -> mem_trace tr (st_depot S) = false ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat HS HE HI MT. pose proof Hwx_tfa as HWX. zone. fixu HE.
lazymatch (img_ev (ss_mem S_T1)) with ?a :: ?b :: ?rest =>
apply (st_ok_drop_regions E _ _ [a; b] rest) in HS; [| img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl)] end.
apply (st_ok_pin_regU E _ _ 10%bv (SLit (TFX_STORE + 24))) in HS; [| img_try (intros X; discriminate) |].
2:{ red_sr. etransitivity; [| img_try (img_apply (std_val E TOT V34); clear - Z17; img_lia)]. rewrite !U_SLit. img_case; vm_compute. all: img_refl. }
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD HI HE INV1.
srr_branch_with tfxtbl_rtD_ok HS.
- srr_runG tfxtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
lazymatch type of HS with st_ok _ _ ?ssE (restrict _ ?msE) =>
destruct (reabs_END E ssE msE HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; img_apply submem_keep; [img_try (split; [img_refl | split; [cbn; img_lia | split; [cbn; img_lia | split; [cbn; img_lia | intros c0 Hc0; destruct Hc0]]]]) | img_try (img_apply submem_refl)]))) as [HS' HE'];
img_exact (ins_exit _ msE _ HS' HE' INV2 MT) end.
- srr_runG tfxtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
lazymatch type of HS with st_ok _ _ ?ssE (restrict _ ?msE) =>
destruct (reabs_END E ssE msE HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))
ltac:(img_try (cbn [ss_mem]; img_apply submem_keep; [img_try (split; [img_refl | split; [cbn; img_lia | split; [cbn; img_lia | split; [cbn; img_lia | intros c0 Hc0; destruct Hc0]]]]) | img_try (img_apply submem_refl)]))) as [HS' HE'];
img_exact (ins_exit _ msE _ HS' HE' INV2 MT) end.
Qed.
Definition EMC (E : env) (j : Z) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 (buf + j); Z_to_bv 64 (SLOT + 8 + j); Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)); Z_to_bv 64 (byteZ m0 (buf + j));
getr rg 14%bv; Z_to_bv 64 0; getr rg 16%bv].
Lemma present_now : forall m a b, INV m -> off_img a -> mbyte tfxsegs m0 a = Some b -> exists b', mbyte tfxsegs (mrestrict Hd m) a = Some b'.
Proof.
intros m a b [_ HG] Ha Hb. specialize (HG (Z_to_bv 64 a)). unfold mbyte in Hb |- *.
rewrite (seg_rom_none_off a Ha) in Hb |- *. destruct (mrestrict Hd mem (Z_to_bv 64 a)) as [x|]; [| img_try (discriminate)].
destruct (mrestrict Hd m (Z_to_bv 64 a)) as [y|]; [img_try (exists y; img_refl) | img_try (exfalso; img_apply HG; [discriminate | img_refl])].
Qed.
Lemma MC_disj : forall E j, envD E -> 0 <= j < 8 * Z.of_nat (length tr) ->
bv_unsigned (ew E aSC) = buf + j -> bv_unsigned (ew E aDC) = SLOT + 8 + j ->
all_disjoint E R_SRC (R_DST :: MCFIX) /\ all_disjoint E R_DST MCFIX.
Proof.
intros E j HE Hj US UD. zone. pose proof sp_range as SR. fixu HE. unfold aSC in US. unfold aDC in UD.
split; img_apply all_disjoint_of_extents; unfold MCFIX, R_SRC, R_DST, extent_of_region, aSC, aDC, aBY; cbn [map app YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?US, ?UD, V2, V37, V40; unfold S2, NDN, SLOT; zoneNS; clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR Hj NZ SZ';
numconst; cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; img_lia.
Qed.
Lemma reabs_MC : forall E ss ms j,
st_ok tfxsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_MC -> reabs_check LT42 ss MCREGS MCF = true -> submem MCFIX (ss_mem ss) ->
0 <= j < 8 * Z.of_nat (length tr) ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 (buf + j) -> getr (ms_regs ms) 13%bv = Z_to_bv 64 (SLOT + 8 + j) ->
getr (ms_regs ms) 12%bv = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)) -> INV (ms_mem ms) ->
let E' := EMC E j (ms_regs ms) in
st_ok tfxsegs E' S_MC (restrict Hd ms) /\ envD E' /\
ew E' aSC = Z_to_bv 64 (buf + j) /\ ew E' aDC = Z_to_bv 64 (SLOT + 8 + j) /\ ew E' aME = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)).
Proof.
intros E ss ms j HS HE Hpc Hck Hsub Hj G11 G13 G12 HI. zone. cbn zeta. set (E' := EMC E j (ms_regs ms)).
assert (HE' : envD E') by (img_try (img_apply envD_havoc; [img_try (img_exact HE) | img_try (unfold K_D; img_lia)])).
assert (ESC : ew E' aSC = Z_to_bv 64 (buf + j)) by img_refl. assert (EDC : ew E' aDC = Z_to_bv 64 (SLOT + 8 + j)) by img_refl.
assert (EME : ew E' aME = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr))) by img_refl. assert (EBY : ew E' aBY = Z_to_bv 64 (byteZ m0 (buf + j))) by img_refl.
pose proof (byteZ_range m0 (buf + j)) as BR.
assert (USC : bv_unsigned (ew E' aSC) = buf + j) by (img_try (rewrite ESC; img_apply unsigned_lit_small; clear - Hj Z1 Z5 Z6 Z2 Z8; numconst; img_lia)).
assert (UDC : bv_unsigned (ew E' aDC) = SLOT + 8 + j) by (img_try (rewrite EDC; img_apply unsigned_lit_small; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; img_lia)).
split; [| img_try (split; [img_exact HE' | split; [img_exact ESC | split; [img_exact EDC | img_exact EME]]])]. unfold S_MC. rewrite <- Hpc.
destruct (MC_disj E' j HE' Hj USC UDC) as [DJ1 DJ2].
img_apply (st_ok_add_region E' (mkSS (ss_pc ss) MCREGS (R_DST :: MCFIX) None MCF) (restrict Hd ms) R_SRC).
1: img_apply (st_ok_add_region E' (mkSS (ss_pc ss) MCREGS MCFIX None MCF) (restrict Hd ms) R_DST).
- img_apply (st_ok_reabs tfxsegs LT42 E E' ss (restrict Hd ms) MCREGS MCFIX MCF HS (agree_pd_havoc E 42 _ ltac:(img_lia)) Hck).
+ cbn [ms_regs restrict]. img_apply Forall_forall. intros [r k] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* img_apply (OBr E' _ _ 11%bv 42%nat _ ESC G11). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 12%bv 44%nat _ EME G12). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 13%bv 43%nat _ EDC G13). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 14%bv 46%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
* img_apply (OBr E' _ _ 16%bv 48%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). (img_case; vm_compute); img_refl.
+ assert (FO : fact_obls LT42 MCF = [(aSC, mkAF kHighMemBeg kHighMemEnd 0); (aDC, mkAF 4096 CEIL_MAX 0); (aME, mkAF 4096 CEIL_MAX 0); (aBY, mkAF 0 255 0); (46%nat, u64f); (48%nat, u64f)])
by (img_try (clear; (img_case; vm_compute); img_refl)).
rewrite FO. clear FO.
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aSC _ _ _ _ ESC); clear - Hj Z1 Z2 Z5 Z6 Z8; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aDC _ _ _ _ EDC); unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aME _ _ _ _ EME); unfold SLOT; clear - Z11 Z12 Z17 Z8; [img_try (numconst; img_lia) | img_try (numconst; img_lia) | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons. { cbn [fst snd]. img_apply (AFo E' aBY _ _ _ _ EBY); clear - BR; [img_lia | img_lia | img_try (img_apply Z.mod_1_r) | img_lia]. }
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 14%bv)); img_refl)|].
img_apply Forall_cons; [img_try (img_apply (JKf E' _ (getr (ms_regs ms) 16%bv)); img_refl)|]. img_apply Forall_nil.
+ cbn [ms_mem restrict]. img_apply (sub_mem_ok E E' ss); [img_try (img_exact (st_ok_mem_ok tfxsegs E ss _ HS)) | img_try (img_exact Hsub) | img_try ((img_case; vm_compute); img_refl) | img_try ((img_case; vm_compute); img_refl) | | img_refl].
intros n Hn. (subst E'; cbv beta). unfold EMC. rewrite ew_havoc_old by img_lia. img_refl.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. img_apply (region_ok_window E' _ aDC (SLOT + 8 + j)); [img_try (img_exact UDC) | img_try (unfold SLOT; clear - Hj Z11 Z17; numconst; img_lia) | img_try (unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; img_lia) |].
intros a Ha. destruct (SB_present a ltac:(img_try (unfold SLOT in Ha; clear - Ha Hj Z17 Z8; numconst; img_lia))) as [b Hb].
assert (OFFa : off_img a) by (img_try (img_apply SB_off; unfold SLOT in Ha; clear - Ha Hj Z17 Z8; numconst; img_lia)).
destruct (present_now (ms_mem ms) a b HI OFFa Hb) as [b' Hb'].
img_apply (mbyte_off_writable _ a b'); [img_try (img_exact OFFa) | img_try (img_exact Hb')].
- cbn [ss_mem]. img_exact DJ2.
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem restrict]. unfold region_ok, R_SRC. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite USC. split; [img_try (clear - Hj Z1 Z5; numconst; img_lia)|]. split; [img_try (clear - Hj Z2 Z6 Z8; numconst; img_lia)|]. split; [img_try (intros o Ho; exfalso; clear - Ho; img_lia)|].
img_apply Forall_cons; [| img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs E' _ _ 0 1 (SOff aBY 0) (byteZ m0 (buf + j))); [img_try (cbn [sv_denot]; rewrite EBY, unsigned_lit_small by (clear - BR; img_lia); f_equal; img_lia) | img_try (clear - BR; cbn; img_lia) | img_try (cbn; img_lia) |].
rewrite Z.add_0_r. img_exact (byte_INV _ _ HI Hj).
- cbn [ss_mem]. img_exact DJ1.
Qed.
Lemma mc_loop : forall k j E ms mat,
(Z.to_nat (8 * Z.of_nat (length tr) - j) <= k)%nat -> 0 <= j < 8 * Z.of_nat (length tr) ->
st_ok tfxsegs E S_MC (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
ew E aSC = Z_to_bv 64 (buf + j) -> ew E aDC = Z_to_bv 64 (SLOT + 8 + j) -> ew E aME = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)) ->
mem_trace tr (st_depot S) = false ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
induction k as [|k IH]; intros j E ms mat Hk Hj HS HE HI ESC EDC EME MT; [img_try (exfalso; clear - Hk Hj; img_lia)|].
pose proof Hwx_tfa as HWX. zone. fixu HE.
assert (USC : bv_unsigned (ew E aSC) = buf + j) by (img_try (rewrite ESC; img_apply unsigned_lit_small; clear - Hj Z1 Z5 Z6 Z2 Z8; numconst; img_lia)).
assert (UDC : bv_unsigned (ew E aDC) = SLOT + 8 + j) by (img_try (rewrite EDC; img_apply unsigned_lit_small; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; img_lia)).
assert (UME : bv_unsigned (ew E aME) = SLOT + 8 + 8 * Z.of_nat (length tr)) by (img_try (rewrite EME; img_apply unsigned_lit_small; unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; img_lia)).
unfold aSC in USC. unfold aDC in UDC. unfold aME in UME.
srr_runG tfxtbl_rtD_ok HS.
lazymatch goal with | HF : frame_of _ ?rs _ (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INV1 : INV (ms_mem msA)) by (img_try (img_apply (INV_runM E rs _ _ HI HE ltac:((img_case; vm_compute); img_refl) HF HG); unfold aDC; rewrite UDC; clear - Hj Z8; img_lia)); clear HF HG HI end.
srr_branch_with tfxtbl_rtD_ok HS.
-
apply (condZ E BC_NE 43 1 44 0 true) in Hc; [| img_try (rewrite UDC; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; img_lia) | img_try (rewrite UME; unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; img_lia)].
cbn beta iota in Hc. rewrite UDC, UME, Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
assert (Hj' : 0 <= j + 1 < 8 * Z.of_nat (length tr)) by (img_try (clear - Hc Hj; img_lia)).
srr_runG tfxtbl_rtD_ok HS.
lazymatch goal with | HF : frame_of _ ?rs _ (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INV2 : INV (ms_mem msA)) by (img_try (img_apply (INV_runM E rs _ _ INV1 HE ltac:((img_case; vm_compute); img_refl) HF HG); unfold aDC; rewrite UDC; clear - Hj Z8; img_lia)); clear HF HG INV1 end.
rreg HS (11%bv : bv 5) G11. rreg HS (13%bv : bv 5) G13. rreg HS (12%bv : bv 5) G12.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
destruct (reabs_MC E ss2 ms2 (j + 1) HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (cbn [ss_mem]; repeat (img_apply submem_refl || img_apply submem_drop))) Hj'
ltac:(img_try (rewrite G11, USC; f_equal; img_lia)) ltac:(img_try (rewrite G13, UDC; f_equal; img_lia)) ltac:(img_try (rewrite G12; img_exact EME)) INV2)
as (HS' & HE' & ESC' & EDC' & EME')
end.
lazymatch type of HS' with st_ok _ ?E' _ (restrict _ ?ms2) =>
apply (IH (j + 1) E' ms2 _ ltac:(img_try (clear - Hk Hj'; img_lia)) Hj' HS' HE' INV2 ESC' EDC' EME' MT) end.
-
apply (condZ E BC_NE 43 1 44 0 false) in Hc; [| img_try (rewrite UDC; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; img_lia) | img_try (rewrite UME; unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; img_lia)].
cbn beta iota in Hc. rewrite UDC, UME, Z.add_0_r in Hc. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
srr_runG tfxtbl_rtD_ok HS.
lazymatch goal with | HF : frame_of _ ?rs _ (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INV2 : INV (ms_mem msA)) by (img_try (img_apply (INV_runM E rs _ _ INV1 HE ltac:((img_case; vm_compute); img_refl) HF HG); unfold aDC; rewrite UDC; clear - Hj Z8; img_lia)); clear HF HG INV1 end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msT) => img_exact (tail_phase E msT _ HS HE INV2 MT) end.
Qed.
Ltac sub_mem_tac := cbn [ss_mem]; repeat (img_apply submem_refl || (img_apply submem_keep; [img_try (img_apply subregion_refl)|]) || img_apply submem_drop).
Lemma ins_phase : forall E ms mat, (1 <= length tr)%nat -> st_ok tfxsegs E S_MISS (restrict Hd ms) -> envD E -> INV (ms_mem ms) -> mem_trace tr (st_depot S) = false ->
SRr tfxsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat Htr1 HS HE HI MT. pose proof Hwx_tfa as HWX. zone. fixu HE.
assert (E10' : ew E 10 = Z_to_bv 64 buf) by (img_try (rewrite (HE 10%nat ltac:(unfold K_D; img_lia)); img_exact E10)).
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD HI HE INV1.
apply (st_ok_pin_regU E _ _ 10%bv (SLit (TFX_DEPOT + d_map1))) in HS; [| img_try (intros X; discriminate) |].
2:{ red_sr. rewrite U_SLit, (map1_val1 E nD V35 ltac:(img_try (clear - Z16; img_lia))). img_case; vm_compute. all: img_refl. }
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
assert (NV : forall k, (k <= 2)%nat -> U E (SOff aNDN 0) = U E (Nat.iter k (fun e => SAlu ALU_ADD e (SLit 0)) (SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 35%nat 1) (SLit 65535)) (SLit 4))))).
{ intros k Hk. rewrite (node_val1 E NB nD k V32 V35 ltac:(img_try (clear - Z16; img_lia)) ltac:(img_try (clear - Z9; numconst; img_lia)) ltac:(img_try (clear - Z9 Z10; numconst; img_lia)) Hk).
rewrite U_SOff. unfold aNDN. rewrite V40. unfold zcanon, NDN. rewrite Z.add_0_r. img_apply Z.mod_small. clear - Z9 Z10 Z16; numconst; img_lia. }
apply (st_ok_pin_regU E _ _ 10%bv (SOff aNDN 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_exact (NV 1%nat ltac:(img_lia)))].
apply (st_ok_pin_regU E _ _ 8%bv (SOff aNDN 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_exact (NV 2%nat ltac:(img_lia)))].
apply (st_ok_pin_regU E _ _ 9%bv (SOff aNDN 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_exact (NV 0%nat ltac:(img_lia)))].
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD INV2 HE INV3.
apply (st_ok_pin_regU E _ _ 21%bv (SLit 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_apply (pin_tag0 E _ V11); clear - Z8; img_lia)].
apply (st_ok_pin_regU E _ _ 11%bv (SOff 11%nat 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_apply (or_tag_val E _ V11); clear - Z8; img_lia)].
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD INV3 HE INV4.
apply (st_ok_pin_regU E _ _ 5%bv (SLit 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_apply (t0_val E _ V34); clear - Z17; img_lia)].
apply (st_ok_pin_regU E _ _ 6%bv (SLit 0)) in HS; [| img_try (intros X; discriminate) | img_try (red_sr; img_apply (t1_val E _ _ V11 V34); clear - Z8 Z17; img_lia)].
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD INV4 HE INV5.
srr_branch_with tfxtbl_rtD_ok HS.
-
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD INV5 HE INV6.
apply (st_ok_pin_regU E _ _ 10%bv (SOff aSLOT 0)) in HS; [| img_try (intros X; discriminate) |].
2:{ red_sr. rewrite (slot_val E SB TOT V33 V34 ltac:(img_try (clear - Z17; img_lia)) ltac:(img_try (clear - Z11; img_lia)) ltac:(img_try (clear - Z11 Z12; numconst; img_lia))), U_SOff. unfold aSLOT. rewrite V41.
unfold zcanon, SLOT. rewrite Z.add_0_r. img_apply Z.mod_small. clear - Z11 Z12 Z17; numconst; img_lia. }
srr_run_shG tfxtbl_rtD_ok HS. inv_stepD INV6 HE INV7.
rreg HS (11%bv : bv 5) G11. rewrite E10' in G11. rreg HS (13%bv : bv 5) G13. rewrite V41 in G13.
pose proof (st_ok_reg_denot Hd E _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot _ ?e =>
rewrite (denot_of_U E e _ (mcend_val E _ SLOT V11 V41 ltac:(img_try (clear - Z8; img_lia)) ltac:(img_try (unfold SLOT; clear - Z11 Z17; img_lia)) ltac:(img_try (unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; img_lia)))) in G12 end.
lazymatch type of HS with st_ok _ _ ?ss7 (restrict _ ?ms7) =>
destruct (reabs_MC E ss7 ms7 0 HS HE eq_refl ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try (sub_mem_tac)) ltac:(img_try (clear - Htr1; img_lia))
ltac:(img_try (rewrite G11; f_equal; img_lia)) ltac:(img_try (rewrite G13; f_equal; img_lia)) G12 INV7) as (HS' & HE' & ESC & EDC & EME);
apply (mc_loop (Z.to_nat (8 * Z.of_nat (length tr))) 0 _ ms7 _ ltac:(img_try (clear; img_lia)) ltac:(img_try (clear - Htr1; img_lia)) HS' HE' INV7 ESC EDC EME MT)
end.
-
exfalso. img_apply (eq_refute E _ _ (t32_val E TOT V34 ltac:(img_try (clear - Z17; img_lia))) Hc).
Qed.
Lemma dep_main : forall mat, (1 <= length tr)%nat -> SRr tfxsegs W (mkCfg msD0 (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros mat Htr1. img_apply (SRr_bind tfxsegs W _ POST_B DPOST (entry_phase mat Htr1)).
intros W1 c1 _ HP. unfold POST_B in HP. destruct HP as (HW & E1 & ms1 & mat1 & Hc & HS1 & HE1 & HI1). (subst W1 c1; cbv beta).
img_apply (SRr_bind tfxsegs W _ POST_F DPOST (B_phase E1 ms1 mat1 HS1 HE1 HI1)).
intros W2 c2 _ HP. unfold POST_F in HP. destruct HP as (HW & E2 & ms2 & mat2 & Hc & HE2 & HI2 & [HS2 | [HS2 MT]]); (subst W2 c2; cbv beta).
- img_exact (found_exit E2 ms2 mat2 HS2 HE2 HI2).
- img_exact (ins_phase E2 ms2 mat2 Htr1 HS2 HE2 HI2 MT).
Qed.
Theorem dep_spec_ok : (1 <= length tr)%nat -> SRr tfxsegs W (mkCfg msD0 md) DPOST.
Proof. intros Htr1. rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)). img_apply dep_main. img_exact Htr1. Qed.
Definition SS_E0 {imgk : img} : sstate := mkSS A_StackDepotPut (sr_set DREGS0 11%bv (SLit 0)) [R_DS] None (mkFacts [(2%nat, mkAF (kHighMemBeg + DEP_STK) kHighMemEnd 4)] [] []).
Lemma SEED_E : length tr = 0%nat -> st_ok tfxsegs E0 SS_E0 (restrict Hd msD0).
Proof.
intros H0. zone. pose proof sp_range as SR. rewrite restrict_mkst_fx. unfold SS_E0, DREGS0. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; rewrite R11, H0; img_refl)].
img_apply regs_ok_pin; [| img_try (intros X; discriminate) | img_try (cbn [sv_denot]; rewrite R3, (ts_gp B HB); img_refl)].
img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros X; discriminate) | img_try (cbn [sv_denot]; img_exact R4)].
- img_case; vm_compute. all: img_refl.
- cbn [ms_mem mkst]. img_apply Forall_cons; [| img_try (img_apply Forall_nil)]. img_exact (Forall_inv REG0_ok).
- cbn. split; img_exact I.
- split; [| img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. split; [| img_try (img_exact I)].
assert (E2' : ew E0 2 = Z_to_bv 64 sp) by (img_try (rewrite E2; symmetry; img_apply Z_to_bv_bv_unsigned)).
img_apply (AFo E0 2%nat sp _ _ _ E2'); clear - SR Z1 Z3 Z4 Z2 Z22; [img_lia | img_try (numconst; img_lia) | img_try (img_change (2 ^ 4) with 16; img_exact Z22) | img_lia].
Qed.
Lemma dep_empty : length tr = 0%nat -> SRr tfxsegs W (mkCfg msD0 md) DPOST.
Proof.
intros H0. rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)).
pose proof Hwx_tfa as HWX. zone. pose proof (SEED_E H0) as HS. pose proof envD_E0 as HE. fixu HE.
srr_runG tfxtbl_rtD_ok HS.
assert (FR : forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ms_mem ms x = mem x).
{ intros x Hx. img_apply HF. intros (r & Hin & Hr). destruct Hin as [<-|[]]. unfold R_DS in Hr. cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. rewrite V2 in Hr. img_apply Hx. clear - Hr. numconst. img_lia. }
assert (HI : INV (ms_mem ms)). { split; [| img_try (img_exact HG)]. intros x Hx. img_apply FR. intros Hs. img_apply Hx. unfold WIN. left. img_exact Hs. }
assert (VF : forall a (n : nat) v, val_mem tfxsegs m0 a n v -> a + Z.of_nat n <= (0x5ff000 + D_1000) -> 0 <= a -> val_mem tfxsegs (mrestrict Hd (ms_mem ms)) a n v).
{ intros a n v Hv Hhi Hlo. eapply (val_mem_frame Hd mem); [| img_try (img_exact Hv)]. intros k Hk. img_apply FR. rewrite unsigned_lit_small by (img_try (clear - Hk Hhi Hlo; img_lia)).
clear - Hk Hhi Hlo Z1 Z3. numconst. img_lia. }
pose proof cells_val as (V1 & _ & V3 & _). pose proof tab_val as VT.
destruct (exit_regs E0 _ ms HS HE ltac:(img_try ((img_case; vm_compute); img_refl))) as [RP R1].
eapply (SRr_ret_at tfxsegs tfxtbl_rtD tfxtbl_rtD_ok HWX W); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_collapse. split; [img_refl|].
exists 0, (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. img_refl. }
split; [img_try (left; img_refl)|]. split; [img_try (img_exact RP)|].
destruct (exit_frame _ HI) as [F1 F2]. split; [img_try (img_exact F1)|]. split; [img_try (img_exact F2)|].
split; [| img_try (img_exact (const_kept _ HI))].
cbn [depot_after Z.eqb]. img_apply (depot_mem_ok_found _ HI).
- img_apply (VF _ 4%nat _ VT); unfold S2; clear - Z19; numconst; img_lia.
- img_apply (VF _ 4%nat _ V1); unfold NUQ; clear; numconst; img_lia.
- img_apply (VF _ 8%nat _ V3); clear; numconst; img_lia.
Qed.
End s.
Theorem tfx_depot_ok {imgk : img} : forall B, TfxSyms B -> (forall t, as_dhash B t = tfx_dhash t) -> tfx_depot_spec B.
Proof.
intros B HB HDH W ly S regs mem md buf tr. cbn zeta.
intros LY IMG WF Htr HCONST HDEP R10 R11 R3 R4 Hra Hwords Hbuf8 Hbuflo Hbufhi Hbuf_sp Hsp16 Hsplo Hsphi P_stk.
destruct HDEP as (HCELLS & (heads & links & D1 & D2 & D3) & HVIS).
destruct (Nat.eq_dec (length tr) 0) as [HL|HL].
- eapply (dep_empty B HB HDH W ly S regs mem md buf tr heads links); eassumption.
- eapply (dep_spec_ok B HB HDH W ly S regs mem md buf tr heads links); try eassumption. img_lia.
Qed.
End g.
