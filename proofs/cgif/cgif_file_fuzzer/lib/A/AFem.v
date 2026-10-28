(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0q YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AB1h AF0l AF0m AF0x AFl0 AFl3 AFek AFel.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YL02 YL09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DEP_STK, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_END, TFIB_TP, TFIB_GP, TFIB_DEPOT, TFIB_STORE,
d_map1, d_nuniq, d_tab_words, zcanon, M64 in *.
Lemma tfib_dhash_u64 : forall tr, 0 <= tfib_dhash tr < 2 ^ 64.
Proof.
intros tr. unfold tfib_dhash. cbn zeta.
set (h := dh_mul (Z.lxor (Z.shiftr (dh_step (fold_left dh_step tr _) 0) 47) (dh_step (fold_left dh_step tr _) 0))).
assert (R : 0 <= h < 2 ^ 64) by (subst h; apply dh_mul_u64).
apply (lxor_u64 (Z.shiftr h 47) h); [apply shiftr_u64; [exact R | lia] | exact R].
Qed.
Lemma depot_len_bound : forall U (d : list (list Z)), universe_ok U -> List.NoDup d -> incl d U -> Z.of_nat (length d) <= DEPOT_MAX.
Proof.
intros U d (HU & _ & _) Hnd Hincl. pose proof (NoDup_incl_length Hnd Hincl). lia.
Qed.
Lemma depot_frames_bound : forall U (d : list (list Z)), universe_ok U -> incl d U ->
0 <= fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 d <= 31 * Z.of_nat (length d).
Proof.
intros U d (_ & HF & _) Hincl. induction d as [|t d IH]; cbn [fold_right length]; [lia|].
assert (Ht : (length t <= kUnwindMax)%nat) by (apply (proj1 (Forall_forall _ _) HF); apply Hincl; left; reflexivity).
unfold kUnwindMax in Ht. specialize (IH ltac:(intros x Hx; apply Hincl; right; exact Hx)). lia.
Qed.
Lemma le4_bytes : forall b0 b1 b2 b3 (k : nat), 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> (k < 4)%nat ->
YO0f.le_byte (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) 4 k = nth k [b0; b1; b2; b3] 0.
Proof.
intros b0 b1 b2 b3 k B0 B1 B2 B3 Hk. unfold YO0f.le_byte.
rewrite (Z.mod_small _ (2 ^ (8 * Z.of_nat 4))) by (change (2 ^ (8 * Z.of_nat 4)) with 4294967296; lia).
assert (Q1 : (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 256 = b1 + 256 * b2 + 65536 * b3).
{ symmetry. apply Z.div_unique with (r := b0); [left; lia | lia]. }
assert (Q2 : (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 65536 = b2 + 256 * b3).
{ symmetry. apply Z.div_unique with (r := b0 + 256 * b1); [left; lia | lia]. }
assert (Q3 : (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) / 16777216 = b3).
{ symmetry. apply Z.div_unique with (r := b0 + 256 * b1 + 65536 * b2); [left; lia | lia]. }
destruct k as [|[|[|[|k]]]]; [ | | | | lia]; cbn [nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. symmetry. apply Z.mod_unique with (q := b1 + 256 * b2 + 65536 * b3); [left; lia | lia].
- change (8 * Z.of_nat 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Q1.
symmetry. apply Z.mod_unique with (q := b2 + 256 * b3); [left; lia | lia].
- change (8 * Z.of_nat 2) with 16. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536. rewrite Q2.
symmetry. apply Z.mod_unique with (q := b3); [left; lia | lia].
- change (8 * Z.of_nat 3) with 24. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216. rewrite Q3. apply Z.mod_small. lia.
Qed.
Definition byteZ (m : word -> option byte) (a : Z) : Z := match mbyte tfibsegs m a with Some b => bv_unsigned b | None => 0 end.
Definition rdu32 (m : word -> option byte) (a : Z) : Z := byteZ m a + 256 * byteZ m (a + 1) + 65536 * byteZ m (a + 2) + 16777216 * byteZ m (a + 3).
Lemma byteZ_range : forall m a, 0 <= byteZ m a < 256.
Proof. intros m a. unfold byteZ. destruct (mbyte tfibsegs m a) as [b|]; [| lia]. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. lia. Qed.
Lemma rdu32_range : forall m a, 0 <= rdu32 m a < 2 ^ 32.
Proof. intros m a. unfold rdu32. pose proof (byteZ_range m a). pose proof (byteZ_range m (a + 1)). pose proof (byteZ_range m (a + 2)). pose proof (byteZ_range m (a + 3)). lia. Qed.
Lemma val_mem_rdu32 : forall m a, (forall k, (k < 4)%nat -> mbyte tfibsegs m (a + Z.of_nat k) <> None) -> val_mem tfibsegs m a 4 (rdu32 m a).
Proof.
intros m a Hp k Hk.
assert (E : forall j, mbyte tfibsegs m (a + j) <> None -> mbyte tfibsegs m (a + j) = Some (Z_to_bv 8 (byteZ m (a + j)))).
{ intros j Hj. unfold byteZ. destruct (mbyte tfibsegs m (a + j)) as [b|]; [| congruence]. rewrite Z_to_bv_bv_unsigned. reflexivity. }
specialize (Hp k Hk). rewrite (E (Z.of_nat k) Hp). f_equal. f_equal. unfold rdu32.
rewrite (le4_bytes _ _ _ _ k (byteZ_range m a) (byteZ_range m (a + 1)) (byteZ_range m (a + 2)) (byteZ_range m (a + 3)) Hk).
destruct k as [|[|[|[|k]]]]; [ | | | | lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; reflexivity.
Qed.
Lemma pairwise_cons_inv {X} (R : X -> X -> Prop) x l : pairwise R (x :: l) -> Forall (R x) l /\ pairwise R l.
Proof. intros H. exact H. Qed.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section s.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis HDH : forall t, as_dhash B t = tfib_dhash t.
Variables (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z) (tr : list Z).
Variables (heads links : Z -> Z).
#[local] Notation Hd := (w_H W).
#[local] Notation rd0 := (aview tfibsegs (w_H W) mem).
#[local] Notation m0 := (mrestrict (w_H W) mem).
#[local] Notation sp := (bv_unsigned (getr regs 2%bv)).
#[local] Notation NB := (ly_NB ly).
#[local] Notation SB := (ly_SB ly).
Definition nD : Z := depot_ids S.
Definition hashes : Z -> Z := fun id => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S) []).
Definition HSH : Z := tfib_dhash tr.
Definition bkt : Z := HSH mod d_tab_words.
Definition TOT : Z := Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S.
Definition S2 : Z := TFIB_DEPOT + 4 * bkt.
Definition HDv : Z := heads bkt.
Definition STD : Z := rdu32 m0 (TFIB_STORE + 24).
Definition NDN : Z := NB + 16 * (nD + 1).
Definition SLOT : Z := SB + 8 * TOT.
Definition NUQ : Z := TFIB_DEPOT + d_nuniq.
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
(R3 : getr regs 3%bv = Z_to_bv 64 (as_gp B)) (R4 : getr regs 4%bv = Z_to_bv 64 TFIB_TP) (Hra : YK0s.ret_ok (getr regs 1%bv)).
Hypothesis Hwords : forall i, (i < length tr)%nat -> val_mem tfibsegs m0 (buf + 8 * Z.of_nat i) 8 (nth i tr 0).
Hypotheses (Hbuf8 : buf mod 8 = 0) (Hbuflo : ly_stk_lo ly <= buf) (Hbufhi : buf + 8 * 30 <= ly_stk_hi ly) (Hbuf_sp : buf + 8 * 30 <= sp - DEP_STK \/ sp <= buf).
Hypotheses (Hsp16 : sp mod 16 = 0) (Hsplo : ly_stk_lo ly <= sp - DEP_STK) (Hsphi : sp <= ly_stk_hi ly)
(P_stk : forall a, sp - DEP_STK <= a < sp -> apresent Hd mem a).
Lemma tr_len : (length tr <= 30)%nat.
Proof. pose proof (ts_universe B HB) as (_ & HU & _). exact (proj1 (Forall_forall _ _) HU tr Htr). Qed.
Lemma nD_range : 1 <= nD <= 4097.
Proof.
unfold nD, depot_ids. pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
pose proof (depot_len_bound _ _ (ts_universe B HB) Hnd Hincl). unfold DEPOT_MAX in *. lia.
Qed.
Lemma TOT_range : 2 <= TOT <= 127070.
Proof.
unfold TOT, depot_frames. pose proof (wf_depot _ _ _ _ _ WF) as [Hnd Hincl].
pose proof (depot_frames_bound _ _ (ts_universe B HB) Hincl) as F. pose proof (depot_len_bound _ _ (ts_universe B HB) Hnd Hincl) as L.
pose proof (lo_tr0 ly LY) as T. unfold DEPOT_MAX in L. lia.
Qed.
Lemma HSH_range : 0 <= HSH < 2 ^ 64.
Proof. apply tfib_dhash_u64. Qed.
Lemma bkt_range : 0 <= bkt < d_tab_words.
Proof. unfold bkt, d_tab_words. apply Z.mod_pos_bound. lia. Qed.
Lemma HDv_range : 0 <= HDv <= nD.
Proof. unfold HDv. exact (proj1 (D1 bkt bkt_range)). Qed.
Lemma STD_range : 0 <= STD < 2 ^ 32.
Proof. apply rdu32_range. Qed.
Lemma hashes_u64 : forall id, 0 <= hashes id < 2 ^ 64.
Proof. intros id. unfold hashes. rewrite HDH. apply tfib_dhash_u64. Qed.
Lemma hashes_mod : forall id, hashes id mod 2 ^ 64 = hashes id.
Proof. intros id. apply Z.mod_small. apply hashes_u64. Qed.
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
pose proof (proj1 (Forall_forall _ _) HH (NB, kNodesBlockSize) ltac:(cbn; tauto)) as [N1 N2].
pose proof (proj1 (Forall_forall _ _) HH (SB, kStoreBlockSize) ltac:(cbn; tauto)) as [S1 S2'].
pose proof (proj1 (Forall_forall _ _) HH (ly_T ly, kThreadObjSize) ltac:(cbn; tauto)) as [T1 _].
pose proof (proj1 (Forall_forall _ _) HH (ly_C ly, 256) ltac:(cbn; tauto)) as [C1 _].
cbn [fst snd] in N1, N2, S1, S2', T1, C1.
pose proof (lo_disj ly LY) as PD. unfold static_extents, owned_extents in PD. cbn [app] in PD.
destruct PD as (_ & _ & FT & _ & FNB & FSB & FC & _).
pose proof (proj1 (Forall_forall _ _) FT (NB, kNodesBlockSize) ltac:(cbn; tauto)) as TN.
pose proof (proj1 (Forall_forall _ _) FT (SB, kStoreBlockSize) ltac:(cbn; tauto)) as TS.
pose proof (proj1 (Forall_forall _ _) FT (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(cbn; tauto)) as TK.
pose proof (proj1 (Forall_forall _ _) FNB (SB, kStoreBlockSize) ltac:(cbn; tauto)) as NS.
pose proof (proj1 (Forall_forall _ _) FNB (ly_C ly, 256) ltac:(cbn; tauto)) as NC.
pose proof (proj1 (Forall_forall _ _) FNB (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(cbn; tauto)) as NK.
pose proof (proj1 (Forall_forall _ _) FSB (ly_C ly, 256) ltac:(cbn; tauto)) as SC.
pose proof (proj1 (Forall_forall _ _) FSB (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(cbn; tauto)) as SK.
pose proof (proj1 (Forall_forall _ _) FC (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(cbn; tauto)) as CK.
pose proof (lo_NB_al ly LY) as A1. pose proof (lo_SB_al ly LY) as A2. unfold page_aligned in A1, A2.
assert (N2' : NB + kNodesBlockSize <= 140737479966720) by (clear - N2; ceil; unfold kLowShadowBeg, ASAN_CEIL in *; lia).
assert (S2'' : SB + kStoreBlockSize <= 140737479966720) by (clear - S2'; ceil; unfold kLowShadowBeg, ASAN_CEIL in *; lia).
repeat split; assumption.
Qed.
Local Ltac zone_of x sz k :=
pose proof (lo_disj ly LY) as PD; unfold static_extents, owned_extents in PD; cbn [app] in PD;
let F := fresh "F" in
lazymatch k with
| 2 => destruct PD as (_ & _ & F & _) | 4 => destruct PD as (_ & _ & _ & _ & F & _) | 5 => destruct PD as (_ & _ & _ & _ & _ & F & _)
| 6 => destruct PD as (_ & _ & _ & _ & _ & _ & F & _) | 7 => destruct PD as (_ & _ & _ & _ & _ & _ & _ & F & _) end;
let AP := fresh "AP" in
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) (x, sz) ltac:(unfold owned_extents; cbn; tauto)) as AP; cbn [fst snd] in AP;
assert (SZ : 0 <= sz) by (unfold kNodesBlockSize, kStoreBlockSize, kThreadObjSize; lia);
apply (zone3_intro ly x sz IMG SZ AP);
apply (proj1 (Forall_forall _ _) F (ly_img ly)); cbn; tauto.
Lemma NB_zone : zone3 NB kNodesBlockSize. Proof. zone_of (ly_NB ly) kNodesBlockSize 4. Qed.
Lemma SB_zone : zone3 SB kStoreBlockSize. Proof. zone_of (ly_SB ly) kStoreBlockSize 5. Qed.
Lemma T_zone : zone3 (ly_T ly) kThreadObjSize. Proof. zone_of (ly_T ly) kThreadObjSize 2. Qed.
Lemma C_zone : zone3 (ly_C ly) 256. Proof. zone_of (ly_C ly) 256 6. Qed.
Lemma D_zone : zone3 (ly_D ly) 4096. Proof. zone_of (ly_D ly) 4096 7. Qed.
Ltac zoneNS := pose proof NB_zone as NZ; pose proof SB_zone as SZ';
unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kNodesBlockSize, kStoreBlockSize in NZ, SZ'.
Lemma NB_off : forall a, NB <= a < NB + kNodesBlockSize -> off_img a. Proof. intros a Ha. exact (zone3_off_img _ _ a NB_zone Ha). Qed.
Lemma SB_off : forall a, SB <= a < SB + kStoreBlockSize -> off_img a. Proof. intros a Ha. exact (zone3_off_img _ _ a SB_zone Ha). Qed.
Lemma zone_facts :
0x10007fff8000 <= ly_stk_lo ly /\ ly_stk_hi ly <= 0x800000000000 /\ ly_stk_lo ly <= sp - 512 /\ sp <= ly_stk_hi ly /\
ly_stk_lo ly <= buf /\ buf + 240 <= ly_stk_hi ly /\ (buf + 240 <= sp - 512 \/ sp <= buf) /\ (length tr <= 30)%nat /\
4096 <= NB /\ NB + 0x100000 <= 140737479966720 /\ 4096 <= SB /\ SB + 0x800000 <= 140737479966720 /\
(NB + 0x100000 <= SB \/ SB + 0x800000 <= NB) /\
(NB + 0x100000 <= ly_stk_lo ly \/ ly_stk_hi ly <= NB) /\ (SB + 0x800000 <= ly_stk_lo ly \/ ly_stk_hi ly <= SB) /\
1 <= nD <= 4097 /\ 2 <= TOT <= 127070 /\ 0 <= HSH < 2 ^ 64 /\ 0 <= bkt < 1048576 /\ 0 <= HDv <= nD /\ 0 <= STD < 2 ^ 32 /\
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
repeat split; first [lia | exact TL].
Qed.
Ltac zone := pose proof zone_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14 & Z15 & Z16 & Z17 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25).
Definition XW : list word :=
[Z_to_bv 64 NB; Z_to_bv 64 SB; Z_to_bv 64 TOT; Z_to_bv 64 nD; Z_to_bv 64 HSH; Z_to_bv 64 S2; Z_to_bv 64 HDv; Z_to_bv 64 STD; Z_to_bv 64 NDN; Z_to_bv 64 SLOT].
Definition E0 : env := Ereg regs XW.
Lemma EaNB : ew E0 aNB = Z_to_bv 64 NB. Proof. reflexivity. Qed.
Lemma EaSB : ew E0 aSB = Z_to_bv 64 SB. Proof. reflexivity. Qed.
Lemma EaTOT : ew E0 aTOT = Z_to_bv 64 TOT. Proof. reflexivity. Qed.
Lemma EaN : ew E0 aN = Z_to_bv 64 nD. Proof. reflexivity. Qed.
Lemma EaHASH : ew E0 aHASH = Z_to_bv 64 HSH. Proof. reflexivity. Qed.
Lemma EaS2 : ew E0 aS2 = Z_to_bv 64 S2. Proof. reflexivity. Qed.
Lemma EaHD : ew E0 aHD = Z_to_bv 64 HDv. Proof. reflexivity. Qed.
Lemma EaSTD : ew E0 aSTD = Z_to_bv 64 STD. Proof. reflexivity. Qed.
Lemma EaNDN : ew E0 aNDN = Z_to_bv 64 NDN. Proof. reflexivity. Qed.
Lemma EaSLOT : ew E0 aSLOT = Z_to_bv 64 SLOT. Proof. reflexivity. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs r.
Proof. intros Hk. exact (ew_Ereg_nat regs XW k r Hk). Qed.
Lemma E1 : ew E0 1 = getr regs 1%bv. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E2 : ew E0 2 = getr regs 2%bv. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = Z_to_bv 64 buf. Proof. rewrite <- R10. exact (Er 10 10%bv eq_refl). Qed.
Lemma E11 : ew E0 11 = Z_to_bv 64 (Z.of_nat (length tr)). Proof. rewrite <- R11. exact (Er 11 11%bv eq_refl). Qed.
Lemma sp_range : 0 <= sp < 2 ^ 64. Proof. apply u64_range. Qed.
Definition envD (E : env) : Prop := forall k, (k < K_D)%nat -> ew E k = ew E0 k.
Lemma envD_E0 : envD E0. Proof. intros k _. reflexivity. Qed.
Lemma envD_havoc : forall E k ws, envD E -> (K_D <= k)%nat -> envD (havoc E k ws).
Proof. intros E k ws HE Hk j Hj. rewrite ew_havoc_old by lia. exact (HE j Hj). Qed.
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
{ intros k z Hk Hz Hr. rewrite (HE k Hk), Hz. apply unsigned_lit_small. exact Hr. }
unfold K_D in L. constructor.
- rewrite (HE 2%nat ltac:(unfold K_D; lia)), E2. reflexivity.
- apply (L 10%nat buf ltac:(lia) E10). clear - Z1 Z5 Z6 Z2. lia.
- apply (L 11%nat _ ltac:(lia) E11). clear - Z8. lia.
- apply (L aNB _ ltac:(unfold aNB; lia) EaNB). clear - Z9 Z10. lia.
- apply (L aSB _ ltac:(unfold aSB; lia) EaSB). clear - Z11 Z12. lia.
- apply (L aTOT _ ltac:(unfold aTOT; lia) EaTOT). clear - Z17. lia.
- apply (L aN _ ltac:(unfold aN; lia) EaN). clear - Z16. lia.
- apply (L aHASH _ ltac:(unfold aHASH; lia) EaHASH). exact Z18.
- apply (L aS2 _ ltac:(unfold aS2; lia) EaS2). unfold S2. clear - Z19. numconst. lia.
- apply (L aHD _ ltac:(unfold aHD; lia) EaHD). clear - Z20 Z16. lia.
- apply (L aSTD _ ltac:(unfold aSTD; lia) EaSTD). clear - Z21. lia.
- apply (L aNDN _ ltac:(unfold aNDN; lia) EaNDN). unfold NDN. clear - Z9 Z10 Z16. lia.
- apply (L aSLOT _ ltac:(unfold aSLOT; lia) EaSLOT). unfold SLOT. clear - Z11 Z12 Z17. lia.
Qed.
Ltac fixu HE := pose proof (fixedU_of_envD _ HE) as [V2 V10 V11 V32 V33 V34 V35 V36 V37 V38 V39 V40 V41];
unfold aNB, aSB, aTOT, aN, aHASH, aS2, aHD, aSTD, aNDN, aSLOT in V32, V33, V34, V35, V36, V37, V38, V39, V40, V41.
Lemma tfibsegs_TSEGS : tfibsegs = TSEGS. Proof. reflexivity. Qed.
Lemma rw_writable : forall (m : word -> option byte) a, 0x9d000 <= a < 0x5fb000 -> writable_at tfibsegs m a.
Proof. intros m a Ha. unfold writable_at. rewrite tfibsegs_TSEGS. apply tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha. Qed.
Lemma const_val : forall a (w : nat) v,
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum v))) -> val_mem tfibsegs m0 a w v.
Proof.
intros a w v E. apply (cell_holds_val_mem B ly Hd mem (ANum a) w (ANum v)).
apply (proj1 (Forall_forall (cell_holds B ly rd0) (as_const B ly)) HCONST). rewrite (ts_const B HB ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma cells_val :
val_mem tfibsegs m0 NUQ 4 nD /\ val_mem tfibsegs m0 (TFIB_DEPOT + d_map1) 8 NB /\ val_mem tfibsegs m0 TFIB_STORE 8 TOT /\ val_mem tfibsegs m0 (TFIB_STORE + 16) 8 SB.
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
Lemma rd32_val_mem : forall a v, rd32 rd0 a v -> val_mem tfibsegs m0 a 4 v.
Proof. intros a v H k Hk. rewrite <- le_byte_eq. apply aview_byte. exact (H k Hk). Qed.
Lemma rd64_val_mem : forall a v, rd64 rd0 a v -> val_mem tfibsegs m0 a 8 v.
Proof. intros a v H k Hk. rewrite <- le_byte_eq. apply aview_byte. exact (H k Hk). Qed.
Lemma tab_val : val_mem tfibsegs m0 S2 4 HDv.
Proof. unfold S2, HDv. rewrite <- (ts_depot B HB). apply rd32_val_mem. exact (proj2 (D1 bkt bkt_range)). Qed.
Lemma vis_at : forall k e len i, nth_error [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)] k = Some (e, len) ->
0 <= i < len -> exists b, mbyte tfibsegs m0 (aeval B ly e + i) = Some b.
Proof. intros k e len i Hk Hi. apply (range_vis_mbyte B ly Hd mem e len i); [| exact Hi]. exact (Forall_nth_error _ _ k _ HVIS Hk). Qed.
Lemma STD_val : val_mem tfibsegs m0 (TFIB_STORE + 24) 4 STD.
Proof.
unfold STD. apply val_mem_rdu32. intros k Hk. destruct (vis_at 2 (AStore 24) 8 (Z.of_nat k) eq_refl ltac:(lia)) as [b Hb].
cbn [aeval] in Hb. rewrite (ts_store B HB) in Hb. rewrite Hb. discriminate.
Qed.
Lemma NB_present : forall a, NB <= a < NB + kNodesBlockSize -> exists b, mbyte tfibsegs m0 a = Some b.
Proof.
intros a Ha. destruct (vis_at 3 (ANB 0) kNodesBlockSize (a - NB) eq_refl ltac:(lia)) as [b Hb]. cbn [aeval] in Hb.
replace (NB + 0 + (a - NB)) with a in Hb by lia. exists b. exact Hb.
Qed.
Lemma SB_present : forall a, SB <= a < SB + kStoreBlockSize -> exists b, mbyte tfibsegs m0 a = Some b.
Proof.
intros a Ha. destruct (vis_at 4 (ASB 0) kStoreBlockSize (a - SB) eq_refl ltac:(lia)) as [b Hb]. cbn [aeval] in Hb.
replace (SB + 0 + (a - SB)) with a in Hb by lia. exists b. exact Hb.
Qed.
Lemma region_ok_cell8r : forall E (m : word -> option byte) a k v,
val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> region_ok tfibsegs E m (cell8r a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, cell8r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.
Lemma region_ok_cell8 : forall E (m : word -> option byte) a k v,
val_mem tfibsegs m a 8 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0x9d000 <= a -> a + 8 <= 0x5fb000 -> region_ok tfibsegs E m (cell8 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, cell8. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 8 (SOff k 0) v); [| exact Hr | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hr. f_equal. lia.
Qed.
Lemma region_ok_cell4 : forall E (m : word -> option byte) a k v,
val_mem tfibsegs m a 4 v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> 0x9d000 <= a -> a + 4 <= 0x5fb000 -> region_ok tfibsegs E m (cell4 a k).
Proof.
intros E m a k v Hv Hk Hr Ha Hh. unfold region_ok, cell4. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; apply rw_writable; lia|]. apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs E m 0 a 4 (SOff k 0) v); [| cbn; lia | cbn; lia | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia. f_equal. lia.
Qed.
#[local] Notation msD0 := (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)).
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) DMEM0.
Proof.
zone. pose proof sp_range as SR. pose proof cells_val as (V1 & V2 & V3 & V4). pose proof tab_val as VT. pose proof STD_val as VS.
unfold DMEM0, DFIX, D_consts, D_cf, R_DS, R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8. cbn [app].
apply Forall_cons. { apply (region_ok_stack tfibsegs E0 m0 2 sp (- DEP_STK)); [rewrite E2; reflexivity | clear - Z1 Z3; numconst; lia | clear - SR; lia |].
intros a Ha. apply apresent_writable; [clear - Ha Z1 Z3 SR; numconst; lia | apply P_stk; exact Ha]. }
apply Forall_cons. { apply (region_ok_lit E0 m0 0x102e8 8 DH_M); [apply const_val; vm_compute; reflexivity | unfold DH_M; cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons. { apply (region_ok_lit E0 m0 0x10308 8 DH_M8); [apply const_val; vm_compute; reflexivity | unfold DH_M8; cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons. { apply (region_ok_lit E0 m0 0x10398 8 DH_SEED); [apply const_val; vm_compute; reflexivity | unfold DH_SEED; cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons. { apply (region_ok_cell8r E0 m0 _ aNB NB V2 EaNB); clear - Z9 Z10; numconst; lia. }
apply Forall_cons. { unfold NUQ in V1. apply (region_ok_cell4 E0 m0 _ aN nD V1 EaN); clear - Z16; numconst; lia. }
apply Forall_cons. { unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite EaS2, unsigned_lit_small by (unfold S2; clear - Z19; numconst; lia).
split; [unfold S2; clear - Z19; numconst; lia|]. split; [unfold S2; clear - Z19; numconst; lia|].
split; [intros o Ho; apply rw_writable; unfold S2; clear - Z19 Ho; numconst; lia|].
apply Forall_cons; [| apply Forall_nil].
eapply (chunk_ok_val tfibsegs E0 m0 S2 0 4 (SOff aHD 0) HDv); [cbn [sv_denot]; rewrite EaHD, unsigned_lit_small by (clear - Z16 Z20; lia); f_equal; lia
| clear - Z16 Z20; cbn; lia | cbn; lia | rewrite Z.add_0_r; exact VT]. }
apply Forall_cons. { apply (region_ok_cell8 E0 m0 _ aTOT TOT V3 EaTOT); clear - Z17; numconst; lia. }
apply Forall_cons. { apply (region_ok_cell8r E0 m0 _ aSB SB V4 EaSB); clear - Z11 Z12; numconst; lia. }
apply Forall_cons. { apply (region_ok_cell4 E0 m0 _ aSTD STD VS EaSTD); clear - Z21; numconst; lia. }
apply Forall_cons. { apply (region_ok_window E0 m0 aNDN NDN); [rewrite EaNDN; apply unsigned_lit_small; unfold NDN; clear - Z9 Z10 Z16; numconst; lia
| unfold NDN; clear - Z9 Z10 Z16; numconst; lia | unfold NDN; clear - Z9 Z10 Z16; numconst; lia |].
intros a Ha. destruct (NB_present a ltac:(unfold NDN in Ha; clear - Ha Z16; numconst; lia)) as [b Hb].
apply (mbyte_off_writable _ a b); [apply NB_off; unfold NDN in Ha; clear - Ha Z16; numconst; lia | exact Hb]. }
apply Forall_cons. { apply (region_ok_window E0 m0 aSLOT SLOT); [rewrite EaSLOT; apply unsigned_lit_small; unfold SLOT; clear - Z11 Z12 Z17; numconst; lia
| unfold SLOT; clear - Z11 Z12 Z17; numconst; lia | unfold SLOT; clear - Z11 Z12 Z17; numconst; lia |].
intros a Ha. destruct (SB_present a ltac:(unfold SLOT in Ha; clear - Ha Z17; numconst; lia)) as [b Hb].
apply (mbyte_off_writable _ a b); [apply SB_off; unfold SLOT in Ha; clear - Ha Z17; numconst; lia | exact Hb]. }
apply Forall_cons. { apply (region_ok_lit E0 m0 0x9df88 8 0x137b28); [apply const_val; vm_compute; reflexivity | cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_cons. { apply (region_ok_lit E0 m0 0x137c18 8 0x101000100000000); [apply const_val; vm_compute; reflexivity | cbn; lia | cbn; lia | lia | cbn; lia]. }
apply Forall_nil.
Qed.
Lemma PAIRS_ok : pairwise_disjoint E0 DMEM0.
Proof.
zone. pose proof sp_range as SR.
apply pairwise_disjoint_of_extents. unfold DMEM0, DFIX, D_consts, D_cf, R_DS, R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8, cell8, cell8r, cell4, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E2, EaS2, EaNDN, EaSLOT. rewrite !unsigned_lit_small by (unfold S2, NDN, SLOT; clear - Z9 Z10 Z11 Z12 Z16 Z17 Z19; numconst; lia).
zoneNS.
unfold S2, NDN, SLOT. clear - Z1 Z2 Z3 Z4 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR NZ SZ'.
numconst. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
Qed.
Lemma AFo : forall E k X lo hi al, ew E k = Z_to_bv 64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E k (mkAF lo hi al).
Proof. intros E k X lo hi al HE HX HBd HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. rewrite unsigned_lit_small by exact HX. repeat split; lia. Qed.
Lemma FACTS_fixed : forall E, (1 <= length tr)%nat -> envD E -> Forall (fun nf => afact_ok E (fst nf) (snd nf)) DF_fixed.
Proof.
intros E Htr1 HE. zone. pose proof sp_range as SR.
assert (E2' : ew E 2 = Z_to_bv 64 sp) by (rewrite (HE 2%nat ltac:(unfold K_D; lia)), E2; symmetry; apply Z_to_bv_bv_unsigned).
assert (G : forall k w, (k < K_D)%nat -> ew E0 k = w -> ew E k = w) by (intros k w Hk Hw; rewrite (HE k Hk); exact Hw). unfold K_D in G.
unfold DF_fixed, u64f. unfold aNB, aSB, aTOT, aN, aHASH, aS2, aHD, aSTD, aNDN, aSLOT.
apply Forall_cons. { apply (AFo E 2%nat sp _ _ _ E2'); clear - SR Z1 Z3 Z4 Z2 Z22; [lia | numconst; lia | | lia].
change (2 ^ 4) with 16. exact Z22. }
apply Forall_cons. { apply (AFo E 10%nat buf _ _ _ (G 10%nat _ ltac:(lia) E10)); clear - Z1 Z2 Z5 Z6 Z23; [numconst; lia | numconst; lia | change (2 ^ 3) with 8; exact Z23 | lia]. }
apply Forall_cons. { apply (AFo E 11%nat _ _ _ _ (G 11%nat _ ltac:(lia) E11)); clear - Z8 Htr1; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo E 32%nat NB _ _ _ (G 32%nat _ ltac:(lia) EaNB)); clear - Z9 Z10 Z24; [numconst; lia | numconst; lia | change (2 ^ 12) with 4096; exact Z24 | lia]. }
apply Forall_cons. { apply (AFo E 33%nat SB _ _ _ (G 33%nat _ ltac:(lia) EaSB)); clear - Z11 Z12 Z25; [numconst; lia | numconst; lia | change (2 ^ 12) with 4096; exact Z25 | lia]. }
apply Forall_cons. { apply (AFo E 34%nat TOT _ _ _ (G 34%nat _ ltac:(lia) EaTOT)); clear - Z17; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo E 35%nat nD _ _ _ (G 35%nat _ ltac:(lia) EaN)); clear - Z16; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo E 36%nat HSH _ _ _ (G 36%nat _ ltac:(lia) EaHASH)); clear - Z18; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo E 37%nat S2 _ _ _ (G 37%nat _ ltac:(lia) EaS2)); unfold S2; clear - Z19; [numconst; lia | numconst; lia | | lia].
change (2 ^ 2) with 4. apply Z.mod_divide; [lia|]. exists (401334 + bkt). numconst. lia. }
apply Forall_cons. { apply (AFo E 38%nat HDv _ _ _ (G 38%nat _ ltac:(lia) EaHD)); clear - Z16 Z20; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo E 39%nat STD _ _ _ (G 39%nat _ ltac:(lia) EaSTD)); clear - Z21; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { apply (AFo E 40%nat NDN _ _ _ (G 40%nat _ ltac:(lia) EaNDN)); unfold NDN; clear - Z9 Z10 Z16 Z24; [numconst; lia | numconst; lia | | lia].
change (2 ^ 4) with 16. apply Z.mod_divide in Z24 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (256 * q + (nD + 1)). lia. }
apply Forall_cons. { apply (AFo E 41%nat SLOT _ _ _ (G 41%nat _ ltac:(lia) EaSLOT)); unfold SLOT; clear - Z11 Z12 Z17 Z25; [numconst; lia | numconst; lia | | lia].
change (2 ^ 3) with 8. apply Z.mod_divide in Z25 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (512 * q + TOT). lia. }
apply Forall_nil.
Qed.
Lemma atoms_ok_of_Forall : forall E l, Forall (fun nf : nat * afact => afact_ok E (fst nf) (snd nf)) l -> atoms_ok E l.
Proof. intros E l H. induction H as [| [k f] l Hh Ht IH]; cbn; [exact I | split; [exact Hh | exact IH]]. Qed.
Lemma SEED_ok : (1 <= length tr)%nat -> st_ok tfibsegs E0 SS_D0 (restrict Hd msD0).
Proof.
intros Htr1. rewrite restrict_mkst_fx. unfold SS_D0, DREGS0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite R3, (ts_gp B HB); reflexivity].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R4].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok.
- exact PAIRS_ok.
- split; [| split; exact I]. unfold DF0. cbn [f_atoms]. apply atoms_ok_of_Forall. apply (FACTS_fixed E0 Htr1). apply envD_E0.
Qed.
Definition WIN (a : Z) : Prop :=
(sp - DEP_STK <= a < sp) \/ (S2 <= a < S2 + 4) \/ (NUQ <= a < NUQ + 4) \/ (NDN <= a < NDN + 16) \/
(TFIB_STORE <= a < TFIB_STORE + 8) \/ (TFIB_STORE + 24 <= a < TFIB_STORE + 28) \/ (SLOT <= a < SLOT + 248).
Definition WSKD : list (option nat * Z * Z) :=
[(Some 2%nat, - DEP_STK, 0); (None, NUQ, NUQ + 4); (Some aS2, 0, 4); (None, TFIB_STORE, TFIB_STORE + 8); (None, TFIB_STORE + 24, TFIB_STORE + 28);
(Some aNDN, 0, 16); (Some aSLOT, 0, 248)].
Definition WSKM : list (option nat * Z * Z) := WSKD ++ [(Some aDC, 0, 1)].
Definition wsk_ok (sk : list (option nat * Z * Z)) (rs : smem) : bool :=
forallb (fun t => existsb (win_eqb t) sk || (snd t <=? snd (fst t))) (windows rs).
Lemma windows_WINM : forall E rs a, envD E -> wsk_ok WSKM rs = true -> in_wrange E rs a ->
WIN a \/ (bv_unsigned (ew E aDC) <= a < bv_unsigned (ew E aDC) + 1).
Proof.
intros E rs a HE Hb Hw. fixu HE.
destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. exfalso. clear - Hr Ht. lia. }
unfold WSKM, WSKD in Ht. cbn [existsb app] in Ht. unfold WIN.
repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
- rewrite V2 in Hr. clear - Hr. lia.
- clear - Hr. lia.
- unfold aS2 in Hr. rewrite V37 in Hr. clear - Hr. lia.
- clear - Hr. lia.
- clear - Hr. lia.
- unfold aNDN in Hr. rewrite V40 in Hr. clear - Hr. lia.
- unfold aSLOT in Hr. rewrite V41 in Hr. clear - Hr. lia.
- right. clear - Hr. lia.
- discriminate Ht.
Qed.
Lemma wsk_DM : forall rs, wsk_ok WSKD rs = true -> wsk_ok WSKM rs = true.
Proof.
intros rs H. unfold wsk_ok in *. apply forallb_forall. intros t Ht. pose proof (proj1 (forallb_forall _ _) H t Ht) as X.
apply Bool.orb_prop in X as [X|X]; [| rewrite X, Bool.orb_true_r; reflexivity].
unfold WSKM. rewrite existsb_app, X. reflexivity.
Qed.
Lemma windows_WIN : forall E rs a, envD E -> wsk_ok WSKD rs = true -> in_wrange E rs a ->
WIN a \/ (bv_unsigned (ew E aDC) <= a < bv_unsigned (ew E aDC) + 1).
Proof. intros E rs a HE Hb Hw. exact (windows_WINM E rs a HE (wsk_DM rs Hb) Hw). Qed.
Lemma WIN_foot : forall a, WIN a -> (sp - DEP_STK <= a < sp) \/ depot_footprint B ly a.
Proof.
intros a Ha. zone. unfold depot_footprint. rewrite (ts_depot B HB), (ts_store B HB). unfold WIN, S2, NUQ, NDN, SLOT in Ha.
clear - Ha Z16 Z17 Z19. numconst. lia.
Qed.
Lemma buf_outside : forall q, 0 <= q < 240 -> ~ WIN (buf + q).
Proof.
intros q Hq Hw. zone. unfold WIN, S2, NUQ, NDN, SLOT in Hw.
zoneNS. clear - Hq Hw Z1 Z5 Z6 Z7 Z9 Z10 Z11 Z12 Z14 Z15 Z16 Z17 Z19 NZ SZ'. numconst. lia.
Qed.
Definition INV (m : word -> option byte) : Prop :=
(forall x : word, ~ WIN (bv_unsigned x) -> m x = mem x) /\ mem_grows (mrestrict Hd mem) (mrestrict Hd m).
Lemma INV_mem : INV mem.
Proof. split; [intros x _; reflexivity | intros a Ha; exact Ha]. Qed.
Lemma INV_apresent : forall m a, INV m -> apresent Hd mem a -> apresent Hd m a.
Proof. intros m a [_ HG] Ha. exact (apresent_grows Hd mem m a HG Ha). Qed.
Lemma INV_aview : forall m a, INV m -> rd0 a <> None -> aview tfibsegs Hd m a <> None.
Proof.
intros m a [_ HG] Ha. apply (proj2 (aview_vis Hd m a)). apply (proj1 (aview_vis Hd mem a)) in Ha.
unfold mbyte in *. specialize (HG (Z_to_bv 64 a)).
destruct (mrestrict Hd mem (Z_to_bv 64 a)) as [b|]; [| destruct (mrestrict Hd m (Z_to_bv 64 a)); [discriminate | exact Ha]].
destruct (mrestrict Hd m (Z_to_bv 64 a)) as [b'|]; [discriminate | exfalso; apply HG; [discriminate | reflexivity]].
Qed.
Lemma INV_runM : forall E rs (m m' : word -> option byte),
INV m -> envD E -> wsk_ok WSKM rs = true -> frame_of E rs m m' -> mem_grows (mrestrict Hd m) (mrestrict Hd m') ->
SLOT <= bv_unsigned (ew E aDC) -> bv_unsigned (ew E aDC) + 1 <= SLOT + 248 -> INV m'.
Proof.
intros E rs m m' [IF IP] HE Hb HF HG D1' D2'. split.
- intros x Hx. rewrite (HF x). { exact (IF x Hx). } intros Hw. destruct (windows_WINM E rs _ HE Hb Hw) as [H|H]; [exact (Hx H)|].
apply Hx. unfold WIN. clear - H D1' D2'. lia.
- exact (mem_grows_trans' _ _ _ IP HG).
Qed.
Lemma INV_runD : forall E rs (m m' : word -> option byte),
INV m -> envD E -> wsk_ok WSKD rs = true -> frame_of E rs m m' -> mem_grows (mrestrict Hd m) (mrestrict Hd m') -> INV m'.
Proof.
intros E rs m m' [IF IP] HE Hb HF HG. split.
- intros x Hx. rewrite (HF x). { exact (IF x Hx). } intros Hw.
destruct (in_wrange_windows E rs _ Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
2:{ cbn [fst snd] in Ht. apply Z.leb_le in Ht. clear - Hr Ht. lia. }
apply Hx. fixu HE. unfold WSKD in Ht. cbn [existsb app] in Ht. unfold WIN.
repeat (apply Bool.orb_prop in Ht as [Ht|Ht]);
try (apply win_eqb_eq in Ht; injection Ht as -> -> ->; cbn [fst snd base_val] in Hr).
+ rewrite V2 in Hr. clear - Hr. lia.
+ clear - Hr. lia.
+ unfold aS2 in Hr. rewrite V37 in Hr. clear - Hr. lia.
+ clear - Hr. lia.
+ clear - Hr. lia.
+ unfold aNDN in Hr. rewrite V40 in Hr. clear - Hr. lia.
+ unfold aSLOT in Hr. rewrite V41 in Hr. clear - Hr. lia.
+ discriminate Ht.
- exact (mem_grows_trans' _ _ _ IP HG).
Qed.
Lemma val_mem_mod64 : forall (m : word -> option byte) a v, val_mem tfibsegs m a 8 v -> val_mem tfibsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal. unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma words_INV : forall m, INV m -> forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict Hd m) (buf + 8 * Z.of_nat i) 8 ((nth i tr 0) mod 2 ^ 64).
Proof.
intros m [IF _] i Hi. zone. apply val_mem_mod64. eapply (val_mem_frame Hd mem m); [| exact (Hwords i Hi)].
intros k Hk. apply IF. rewrite unsigned_lit_small by (clear - Hi Hk Z1 Z5 Z6 Z2 Z8; numconst; lia).
replace (buf + 8 * Z.of_nat i + Z.of_nat k) with (buf + (8 * Z.of_nat i + Z.of_nat k)) by lia. apply buf_outside. clear - Hi Hk Z8. lia.
Qed.
Lemma byte_INV : forall m q, INV m -> 0 <= q < 8 * Z.of_nat (length tr) -> val_mem tfibsegs (mrestrict Hd m) (buf + q) 1 (byteZ m0 (buf + q)).
Proof.
intros m q [IF _] Hq k Hk. zone. destruct k as [|k]; [| exfalso; clear - Hk; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hwords (Z.to_nat (q / 8)) ltac:(clear - Hq Z8; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_lt_upper_bound; lia)) as VW.
pose proof (Z.div_mod q 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as R.
specialize (VW (Z.to_nat (q mod 8)) ltac:(clear - R; lia)). rewrite !Z2Nat.id in VW by (clear - Hq R; try apply Z.div_pos; lia).
replace (buf + 8 * (q / 8) + q mod 8) with (buf + q) in VW by (clear - D; lia).
assert (Eq : mbyte tfibsegs (mrestrict Hd m) (buf + q) = mbyte tfibsegs m0 (buf + q)).
{ apply (mbyte_mrestrict_same Hd). apply IF. rewrite unsigned_lit_small by (clear - Hq Z1 Z5 Z6 Z2 Z8; numconst; lia). apply buf_outside. clear - Hq Z8; lia. }
rewrite Eq. unfold byteZ. rewrite VW. f_equal. rewrite unsigned_lit_small8 by (apply Z.mod_pos_bound; lia).
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r, !Z.mod_mod by lia. reflexivity.
Qed.
Definition LT42 (j : nat) : bool := (j <? 42)%nat.
Lemma agree_pd_havoc : forall E k ws, (42 <= k)%nat -> env_agree_pd LT42 PT E (havoc E k ws).
Proof.
intros E k ws Hk. split; [| intros d _; rewrite ed_havoc; reflexivity].
intros n Hn. unfold LT42 in Hn. apply Nat.ltb_lt in Hn. rewrite ew_havoc_old by lia. reflexivity.
Qed.
Lemma sub_mem_ok : forall E E' ss (m : word -> option byte) rs,
mem_ok tfibsegs E m (ss_mem ss) -> submem rs (ss_mem ss) -> regions_wf rs = true -> mem_atoms_lt 42 rs = true ->
(forall n, (n < 42)%nat -> ew E' n = ew E n) -> ed E' = ed E -> mem_ok tfibsegs E' m rs.
Proof.
intros E E' ss m rs HM Hsub WF1 WF2 HEE HED.
apply (mem_ok_agree tfibsegs 42 E E'); [split; [exact HEE | exact HED] | exact WF2 |].
apply (mem_ok_sub tfibsegs E m (ss_mem ss) rs Hsub WF1 HM).
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
rewrite !Z.mod_small in Hc by assumption. destruct c; first [exact Hc | exact I].
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
rewrite unsigned_lit_small in Hc by exact H2. rewrite !Z.mod_small in Hc by assumption. destruct c; first [exact Hc | exact I].
Qed.
Lemma denot_of_U : forall E e z, U E e = z -> sv_denot E e = Z_to_bv 64 z.
Proof. intros E e z H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma OBr : forall E' (rg : bvmap 5 word) (r r' : bv 5) k (w : word), ew E' k = w -> getr rg r' = w -> bv_unsigned r = bv_unsigned r' -> ew E' k = getr rg r.
Proof. intros E' rg r r' k w H1 H2 H3. rewrite H1, <- H2. f_equal. symmetry. apply bv_eq. exact H3. Qed.
Lemma JKf : forall E' k (w : word), ew E' k = w -> afact_ok E' k u64f.
Proof. intros E' k w Hk. unfold afact_ok, u64f. cbn [af_lo af_hi af_al2]. pose proof (u64_range (ew E' k)). split; [lia|]. split; [apply Z.mod_1_r | lia]. Qed.
Definition H0v : Z := Z.lxor ((Z.of_nat (length tr) * DH_M8) mod 2 ^ 64) DH_SEED.
Definition hacc (i : nat) : Z := fold_left dh_step (firstn i tr) H0v.
Lemma H0v_u64 : 0 <= H0v < 2 ^ 64.
Proof. unfold H0v. apply lxor_u64; [apply Z.mod_pos_bound; lia | unfold DH_SEED; lia]. Qed.
Lemma fold_dh_u64 : forall l h, 0 <= h < 2 ^ 64 -> 0 <= fold_left dh_step l h < 2 ^ 64.
Proof. induction l as [|w l IH]; intros h Hh; cbn; [exact Hh | apply IH; apply dh_step_u64]. Qed.
Lemma hacc_u64 : forall i, 0 <= hacc i < 2 ^ 64.
Proof. intros i. unfold hacc. apply fold_dh_u64. apply H0v_u64. Qed.
Lemma firstn_S_nth : forall (l : list Z) i, (i < length l)%nat -> firstn (Datatypes.S i) l = firstn i l ++ [nth i l 0].
Proof.
induction l as [|x l IH]; intros i Hi; cbn in Hi; [lia|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH i) by lia. reflexivity.
Qed.
Lemma hacc_S : forall i, (i < length tr)%nat -> hacc (Datatypes.S i) = dh_step (hacc i) (nth i tr 0).
Proof. intros i Hi. unfold hacc. rewrite (firstn_S_nth tr i Hi), fold_left_app. reflexivity. Qed.
Lemma dh_step_mod : forall h w, dh_step h (w mod 2 ^ 64) = dh_step h w.
Proof. intros h w. unfold dh_step, dh_mul. rewrite Z.mul_mod_idemp_l by lia. reflexivity. Qed.
Lemma hacc_full : DFIN (hacc (length tr)) = HSH.
Proof. unfold HSH, tfib_dhash, DFIN, hacc, H0v. rewrite firstn_all. reflexivity. Qed.
Definition EH (E : env) (i : nat) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64); Z_to_bv 64 (hacc i); Z_to_bv 64 (buf + 8 * Z.of_nat i); Z_to_bv 64 (buf + 8 * Z.of_nat (length tr));
getr rg 15%bv; getr rg 16%bv].
Lemma RW_disj : forall E i, envD E -> (i < length tr)%nat -> bv_unsigned (ew E dP) = buf + 8 * Z.of_nat i -> all_disjoint E R_W DFIX'.
Proof.
intros E i HE Hi HP. zone. pose proof sp_range as SR. fixu HE.
apply all_disjoint_of_extents. unfold DFIX', DFIX, D_consts, D_cf, R_W, R_DS', R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8, cell8, cell8r, cell4, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold dP, aS2, aNDN, aSLOT in *. rewrite HP, V2, V37, V40, V41.
unfold S2, NDN, SLOT. zoneNS. clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR Hi NZ SZ'.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
Qed.
Lemma reabs_H : forall E ss ms i,
st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_HLOOP ->
reabs_check LT42 ss HREGS HF = true -> submem DFIX' (ss_mem ss) -> (i < length tr)%nat ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 (buf + 8 * Z.of_nat i) -> getr (ms_regs ms) 12%bv = Z_to_bv 64 (hacc i) ->
getr (ms_regs ms) 14%bv = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)) -> INV (ms_mem ms) ->
let E' := EH E i (ms_regs ms) in
st_ok tfibsegs E' S_H (restrict Hd ms) /\ envD E' /\
ew E' dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64) /\ ew E' dH = Z_to_bv 64 (hacc i) /\
ew E' dP = Z_to_bv 64 (buf + 8 * Z.of_nat i) /\ ew E' dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)).
Proof.
intros E ss ms i HS HE Hpc Hck Hsub Hi G11 G12 G14 HI. zone. cbn zeta. set (E' := EH E i (ms_regs ms)).
assert (HE' : envD E') by (apply envD_havoc; [exact HE | unfold K_D; lia]).
assert (EW : ew E' dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64)) by reflexivity. assert (EHh : ew E' dH = Z_to_bv 64 (hacc i)) by reflexivity.
assert (EP : ew E' dP = Z_to_bv 64 (buf + 8 * Z.of_nat i)) by reflexivity. assert (EE : ew E' dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr))) by reflexivity.
pose proof (Z.mod_pos_bound (nth i tr 0) (2 ^ 64) ltac:(lia)) as WR. pose proof (hacc_u64 i) as HR.
assert (UP : bv_unsigned (ew E' dP) = buf + 8 * Z.of_nat i) by (rewrite EP; apply unsigned_lit_small; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; lia).
split; [| split; [exact HE' | split; [exact EW | split; [exact EHh | split; [exact EP | exact EE]]]]].
unfold S_H. rewrite <- Hpc.
apply (st_ok_add_region E' (mkSS (ss_pc ss) HREGS DFIX' None HF) (restrict Hd ms) R_W).
- apply (st_ok_reabs tfibsegs LT42 E E' ss (restrict Hd ms) HREGS DFIX' HF HS (agree_pd_havoc E 42 _ ltac:(lia)) Hck).
+ cbn [ms_regs restrict]. apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* apply (OBr E' _ _ 11%bv 44%nat _ EP G11). vm_compute; reflexivity.
* apply (OBr E' _ _ 12%bv 43%nat _ EHh G12). vm_compute; reflexivity.
* apply (OBr E' _ _ 14%bv 45%nat _ EE G14). vm_compute; reflexivity.
* apply (OBr E' _ _ 15%bv 46%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). vm_compute; reflexivity.
* apply (OBr E' _ _ 16%bv 47%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ assert (FO : fact_obls LT42 HF = [(dW, u64f); (dH, u64f); (dP, mkAF kHighMemBeg (kHighMemEnd - 8) 3); (dE, mkAF kHighMemBeg kHighMemEnd 3); (46%nat, u64f); (47%nat, u64f)])
by (clear; vm_compute; reflexivity).
rewrite FO. clear FO.
apply Forall_cons; [apply (JKf E' _ _ EW)|]. apply Forall_cons; [apply (JKf E' _ _ EHh)|].
apply Forall_cons. { cbn [fst snd]. apply (AFo E' dP _ _ _ _ EP); clear - Hi Z1 Z2 Z5 Z6 Z8 Z23; [numconst; lia | numconst; lia | | lia].
change (2 ^ 3) with 8. apply Z.mod_divide in Z23 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q + Z.of_nat i). lia. }
apply Forall_cons. { cbn [fst snd]. apply (AFo E' dE _ _ _ _ EE); clear - Z1 Z2 Z5 Z6 Z8 Z23; [numconst; lia | numconst; lia | | lia].
change (2 ^ 3) with 8. apply Z.mod_divide in Z23 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (q + Z.of_nat (length tr)). lia. }
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 15%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|]. apply Forall_nil.
+ cbn [ms_mem restrict]. apply (sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
intros n Hn. subst E'. unfold EH. rewrite ew_havoc_old by lia. reflexivity.
- vm_compute. reflexivity.
- cbn [ms_mem restrict]. unfold region_ok, R_W. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite UP. split; [clear - Z1 Z5; numconst; lia|]. split; [clear - Hi Z2 Z6 Z8; numconst; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
eapply (chunk_ok_val tfibsegs E' _ _ 0 8 (SOff dW 0) ((nth i tr 0) mod 2 ^ 64)); [cbn [sv_denot]; rewrite EW, unsigned_lit_small by exact WR; f_equal; lia | exact WR | cbn; lia |].
rewrite Z.add_0_r. exact (words_INV _ HI i Hi).
- cbn [ss_mem]. exact (RW_disj E' i HE' Hi UP).
Qed.
Definition POST_B : world tfibsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists E' ms' mat', c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md) /\
st_ok tfibsegs E' S_B (restrict Hd ms') /\ envD E' /\ INV (ms_mem ms').
Definition EB (E : env) (rg : bvmap 5 word) : env :=
havoc E 42 [getr rg 10%bv; getr rg 11%bv; getr rg 12%bv; getr rg 14%bv; getr rg 15%bv; getr rg 16%bv].
Lemma reabs_B : forall E ss ms,
st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_BKT -> reabs_check LT42 ss BREGS BFc = true -> submem DFIX' (ss_mem ss) ->
st_ok tfibsegs (EB E (ms_regs ms)) S_B (restrict Hd ms) /\ envD (EB E (ms_regs ms)).
Proof.
intros E ss ms HS HE Hpc Hck Hsub. set (E' := EB E (ms_regs ms)).
assert (HE' : envD E') by (apply envD_havoc; [exact HE | unfold K_D; lia]). split; [| exact HE'].
unfold S_B. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs LT42 E E' ss (restrict Hd ms) BREGS DFIX' BFc HS (agree_pd_havoc E 42 _ ltac:(lia)) Hck).
- cbn [ms_regs restrict]. apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | [H | []]]]]]]; injection H as <- <-.
+ apply (OBr E' _ _ 10%bv 42%nat (getr (ms_regs ms) 10%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 11%bv 43%nat (getr (ms_regs ms) 11%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 12%bv 44%nat (getr (ms_regs ms) 12%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 14%bv 45%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 15%bv 46%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 16%bv 47%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
- assert (FO : fact_obls LT42 BFc = [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f); (46%nat, u64f); (47%nat, u64f)]) by (clear; vm_compute; reflexivity).
rewrite FO. clear FO.
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 10%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 11%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 12%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 14%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 15%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|]. apply Forall_nil.
- cbn [ms_mem restrict]. apply (sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
intros n Hn. subst E'. unfold EB. rewrite ew_havoc_old by lia. reflexivity.
Qed.
Ltac red_sr :=
lazymatch goal with |- _ = U _ (sr_get ?rs ?r) => let e := eval vm_compute in (sr_get rs r) in change (sr_get rs r) with e end.
Ltac inv_stepD HI HE INVn :=
lazymatch goal with
| HF : frame_of ?E ?rs ?mold (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INVn : INV (ms_mem msA)) by (apply (INV_runD E rs _ _ HI HE ltac:(vm_compute; reflexivity) HF HG)); clear HF HG HI
end.
Lemma hash_loop : forall k i E ms mat,
(length tr - i <= k)%nat -> (i < length tr)%nat ->
st_ok tfibsegs E S_H (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
ew E dW = Z_to_bv 64 ((nth i tr 0) mod 2 ^ 64) -> ew E dH = Z_to_bv 64 (hacc i) ->
ew E dP = Z_to_bv 64 (buf + 8 * Z.of_nat i) -> ew E dE = Z_to_bv 64 (buf + 8 * Z.of_nat (length tr)) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POST_B.
Proof.
induction k as [|k IH]; intros i E ms mat Hk Hi HS HE HI EW EHh EP EE; [exfalso; clear - Hk Hi; lia|].
pose proof Hwx_tfa as HWX. zone.
pose proof (Z.mod_pos_bound (nth i tr 0) (2 ^ 64) ltac:(lia)) as WR. pose proof (hacc_u64 i) as HR.
assert (UW : bv_unsigned (ew E dW) = (nth i tr 0) mod 2 ^ 64) by (rewrite EW; apply unsigned_lit_small; exact WR).
assert (UH : bv_unsigned (ew E dH) = hacc i) by (rewrite EHh; apply unsigned_lit_small; exact HR).
assert (UP : bv_unsigned (ew E dP) = buf + 8 * Z.of_nat i) by (rewrite EP; apply unsigned_lit_small; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; lia).
assert (UE : bv_unsigned (ew E dE) = buf + 8 * Z.of_nat (length tr)) by (rewrite EE; apply unsigned_lit_small; clear - Z1 Z5 Z6 Z2 Z8; numconst; lia).
unfold dW in UW. unfold dH in UH. unfold dP in UP. unfold dE in UE.
srr_runG tfibtbl_rtD_ok HS. inv_stepD HI HE INV1.
srr_branch_with tfibtbl_rtD_ok HS.
-
apply (condZ E BC_NE 44 8 45 0 true) in Hc; [| rewrite UP; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; lia | rewrite UE; clear - Z1 Z5 Z6 Z2 Z8; numconst; lia].
cbn beta iota in Hc. rewrite UP, UE, Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
assert (Hi' : (Datatypes.S i < length tr)%nat) by (clear - Hc Hi; lia).
srr_runG tfibtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
rreg HS (11%bv : bv 5) G11. rewrite UP in G11.
pose proof (st_ok_reg_denot Hd E _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot E ?e => replace e with X_STEP in G12 by reflexivity end.
rewrite (denot_of_U E X_STEP _ (step_val E (hacc i) _ UW UH WR HR)) in G12. rewrite dh_step_mod, <- (hacc_S i Hi) in G12.
rreg HS (14%bv : bv 5) G14.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
destruct (reabs_H E ss2 ms2 (Datatypes.S i) HS HE eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop)) Hi'
ltac:(rewrite G11; f_equal; lia) G12 ltac:(rewrite G14; exact EE) INV2)
as (HS' & HE' & EW' & EH' & EP' & EE')
end.
lazymatch type of HS' with st_ok _ ?E' _ (restrict _ ?ms2) =>
apply (IH (Datatypes.S i) E' ms2 _ ltac:(clear - Hk Hi'; lia) Hi' HS' HE' INV2 EW' EH' EP' EE') end.
-
apply (condZ E BC_NE 44 8 45 0 false) in Hc; [| rewrite UP; clear - Hi Z1 Z5 Z6 Z2 Z8; numconst; lia | rewrite UE; clear - Z1 Z5 Z6 Z2 Z8; numconst; lia].
cbn beta iota in Hc. rewrite UP, UE, Z.add_0_r in Hc. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
assert (Hn : Datatypes.S i = length tr) by (clear - Hc Hi; lia).
srr_runG tfibtbl_rtD_ok HS. inv_stepD INV1 HE INV3.
assert (FIN : U E X_FIN = HSH).
{ rewrite (fin_val E (hacc i) _ UW UH WR HR), dh_step_mod, <- (hacc_S i Hi), Hn. exact hacc_full. }
fixu HE.
apply (st_ok_pin_regU E _ _ 19%bv (SOff aHASH 0)) in HS; [| intros X; discriminate |].
2:{ lazymatch goal with |- _ = U E ?e => replace e with X_FIN by reflexivity end. rewrite FIN, U_SOff. unfold aHASH. rewrite V36. unfold zcanon, M64. rewrite Z.add_0_r. rewrite Z.mod_small by exact Z18. reflexivity. }
apply (st_ok_pin_regU E _ _ 18%bv (SOff aS2 0)) in HS; [| intros X; discriminate |].
2:{ lazymatch goal with |- _ = U E ?e => replace e with X_S2 by reflexivity end. rewrite s2_of_fin, FIN, U_SOff. unfold aS2. rewrite V37. unfold zcanon, M64, S2, bkt, d_tab_words. rewrite Z.add_0_r.
rewrite Z.mod_small by (clear - Z19; numconst; lia). reflexivity. }
lazymatch type of HS with st_ok _ _ ?ss3 (restrict _ ?ms3) =>
destruct (reabs_B E ss3 ms3 HS HE eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop))) as [HSB HEB];
apply SRr_ret; split; [reflexivity|]; exists (EB E (ms_regs ms3)), ms3, mat; split; [reflexivity|]; split; [exact HSB | split; [exact HEB | exact INV3]]
end.
Qed.
Definition INVC (cur : Z) : Prop := chain_has links hashes (Z.to_nat nD) HDv HSH -> exists f, chain_has links hashes f cur HSH.
Lemma chain_has_0 : forall f h, ~ chain_has links hashes f 0 h.
Proof. intros [|f] h; cbn; [tauto | intros [H _]; apply H; reflexivity]. Qed.
Lemma INVC_start : INVC HDv.
Proof. intros H. exists (Z.to_nat nD). exact H. Qed.
Lemma INVC_step : forall cur, INVC cur -> cur <> 0 -> hashes cur <> HSH -> INVC (links cur).
Proof.
intros cur HC Hc Hh A. destruct (HC A) as [[|f] H]; cbn in H; [destruct H|].
destruct H as [_ [H|H]]; [exfalso; exact (Hh H) | exists f; exact H].
Qed.
Lemma trace_eqb_eq : forall a b, trace_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. rewrite H1, (IH b H2). reflexivity.
Qed.
Lemma miss_no_trace : ~ chain_has links hashes (Z.to_nat nD) HDv HSH -> mem_trace tr (st_depot S) = false.
Proof.
intros NC. destruct (mem_trace tr (st_depot S)) eqn:Hm; [exfalso | reflexivity]. apply NC.
assert (X : exists j, nth_error (st_depot S) j = Some tr).
{ clear - Hm. induction (st_depot S) as [|u l IH]; cbn in Hm; [discriminate|].
apply Bool.orb_prop in Hm as [Hm|Hm]; [exists 0%nat; cbn; rewrite (trace_eqb_eq _ _ Hm); reflexivity|].
destruct (IH Hm) as [j Hj]. exists (Datatypes.S j). exact Hj. }
destruct X as [j Hj]. assert (Lj : (j < length (st_depot S))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
set (id0 := Z.of_nat j + 2).
assert (Hid : 1 <= id0 <= nD) by (unfold id0, nD, depot_ids; clear - Lj; lia).
assert (Hh : hashes id0 = HSH).
{ unfold hashes, HSH, depot_traces. rewrite HDH. replace (Z.to_nat (id0 - 1)) with (Datatypes.S j) by (unfold id0; clear; lia).
cbn [nth]. rewrite (nth_error_nth _ _ _ Hj). reflexivity. }
pose proof (D3 id0 Hid) as C. rewrite Hh, (Z.mod_small HSH (2 ^ 64)) in C by apply HSH_range. fold bkt in C. fold HDv in C. exact C.
Qed.
Definition EFL (E : env) (cur : Z) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 cur; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; getr rg 14%bv; getr rg 15%bv; getr rg 16%bv; getr rg 10%bv; getr rg 12%bv].
Lemma reabs_FL : forall E ss ms cur,
st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_FLOOP -> reabs_check LT42 ss FLREGS FLc = true -> submem DFIX' (ss_mem ss) ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 cur -> 0 <= cur <= 4097 ->
st_ok tfibsegs (EFL E cur (ms_regs ms)) S_FL (restrict Hd ms) /\ envD (EFL E cur (ms_regs ms)) /\ ew (EFL E cur (ms_regs ms)) aID = Z_to_bv 64 cur.
Proof.
intros E ss ms cur HS HE Hpc Hck Hsub G11 Hcur. set (E' := EFL E cur (ms_regs ms)).
assert (HE' : envD E') by (apply envD_havoc; [exact HE | unfold K_D; lia]).
assert (EI : ew E' aID = Z_to_bv 64 cur) by reflexivity.
split; [| split; [exact HE' | exact EI]]. unfold S_FL. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs LT42 E E' ss (restrict Hd ms) FLREGS DFIX' FLc HS (agree_pd_havoc E 42 _ ltac:(lia)) Hck).
- cbn [ms_regs restrict]. apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | [H | []]]]]]]; injection H as <- <-.
+ apply (OBr E' _ _ 10%bv 49%nat (getr (ms_regs ms) 10%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 11%bv 42%nat _ EI G11). vm_compute; reflexivity.
+ apply (OBr E' _ _ 12%bv 50%nat (getr (ms_regs ms) 12%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 14%bv 46%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 15%bv 47%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 16%bv 48%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
- assert (FO : fact_obls LT42 FLc = [(aID, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f); (49%nat, u64f); (50%nat, u64f)]) by (clear; vm_compute; reflexivity).
rewrite FO. clear FO.
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aID cur _ _ _ EI); clear - Hcur; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 14%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 15%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 10%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 12%bv)); reflexivity|]. apply Forall_nil.
- cbn [ms_mem restrict]. apply (sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
intros n Hn. subst E'. unfold EFL. rewrite ew_havoc_old by lia. reflexivity.
Qed.
Definition EFN (E : env) (cur : Z) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 cur; Z_to_bv 64 (NB + 16 * cur); Z_to_bv 64 (hashes cur); Z_to_bv 64 (links cur); getr rg 14%bv; getr rg 15%bv; getr rg 16%bv].
Lemma ND_disj : forall E cur, envD E -> 1 <= cur <= nD -> bv_unsigned (ew E aND) = NB + 16 * cur -> all_disjoint E R_ND DFIX'.
Proof.
intros E cur HE Hcur HA. zone. pose proof sp_range as SR. fixu HE.
apply all_disjoint_of_extents. unfold DFIX', DFIX, D_consts, D_cf, R_ND, R_DS', R_MAP1, R_NUNIQ, R_TAB, R_TOT, R_SBC, R_STD, R_NODE, R_SLOT, lit8, cell8, cell8r, cell4, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. unfold aND, aS2, aNDN, aSLOT in *. rewrite HA, V2, V37, V40, V41.
unfold S2, NDN, SLOT. zoneNS. clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR Hcur NZ SZ'.
numconst. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
Qed.
Lemma node_vals : forall m cur, INV m -> 1 <= cur <= nD ->
val_mem tfibsegs (mrestrict Hd m) (NB + 16 * cur) 8 (hashes cur) /\ val_mem tfibsegs (mrestrict Hd m) (NB + 16 * cur + 8) 4 (links cur).
Proof.
intros m cur [IF _] Hcur. zone. destruct (D2 cur Hcur) as (_ & R1 & R2). rewrite hashes_mod in R1.
assert (OUT : forall k, 0 <= k < 12 -> m (Z_to_bv 64 (NB + 16 * cur + k)) = mem (Z_to_bv 64 (NB + 16 * cur + k))).
{ intros k Hk. apply IF. rewrite unsigned_lit_small by (clear - Hk Hcur Z9 Z10 Z16; numconst; lia). unfold WIN, S2, NUQ, NDN, SLOT.
zoneNS. clear - Hk Hcur Z9 Z10 Z13 Z14 Z16 Z17 Z19 Z1 Z3 Z4 NZ SZ'. numconst. lia. }
split.
- eapply (val_mem_frame Hd mem m); [| exact (rd64_val_mem _ _ R1)]. intros k Hk. apply OUT. lia.
- eapply (val_mem_frame Hd mem m); [| exact (rd32_val_mem _ _ R2)]. intros k Hk. replace (NB + 16 * cur + 8 + Z.of_nat k) with (NB + 16 * cur + (8 + Z.of_nat k)) by lia. apply OUT. lia.
Qed.
Lemma reabs_FN : forall E ss ms cur,
st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_FNODE -> reabs_check LT42 ss FNREGS FFc = true -> submem DFIX' (ss_mem ss) ->
1 <= cur <= nD -> getr (ms_regs ms) 10%bv = Z_to_bv 64 cur -> getr (ms_regs ms) 11%bv = Z_to_bv 64 (NB + 16 * cur) -> INV (ms_mem ms) ->
let E' := EFN E cur (ms_regs ms) in
st_ok tfibsegs E' S_FN (restrict Hd ms) /\ envD E' /\
ew E' aID = Z_to_bv 64 cur /\ ew E' aNH = Z_to_bv 64 (hashes cur) /\ ew E' aNL = Z_to_bv 64 (links cur).
Proof.
intros E ss ms cur HS HE Hpc Hck Hsub Hcur G10 G11 HI. zone. cbn zeta. set (E' := EFN E cur (ms_regs ms)).
assert (HE' : envD E') by (apply envD_havoc; [exact HE | unfold K_D; lia]).
assert (EI : ew E' aID = Z_to_bv 64 cur) by reflexivity. assert (EA : ew E' aND = Z_to_bv 64 (NB + 16 * cur)) by reflexivity.
assert (ENH : ew E' aNH = Z_to_bv 64 (hashes cur)) by reflexivity. assert (ENL : ew E' aNL = Z_to_bv 64 (links cur)) by reflexivity.
pose proof (hashes_u64 cur) as HR. pose proof (proj1 (D2 cur Hcur)) as LR.
assert (UA : bv_unsigned (ew E' aND) = NB + 16 * cur) by (rewrite EA; apply unsigned_lit_small; clear - Hcur Z9 Z10 Z16; numconst; lia).
split; [| split; [exact HE' | split; [exact EI | split; [exact ENH | exact ENL]]]]. unfold S_FN. rewrite <- Hpc.
apply (st_ok_add_region E' (mkSS (ss_pc ss) FNREGS DFIX' None FFc) (restrict Hd ms) R_ND).
- apply (st_ok_reabs tfibsegs LT42 E E' ss (restrict Hd ms) FNREGS DFIX' FFc HS (agree_pd_havoc E 42 _ ltac:(lia)) Hck).
+ cbn [ms_regs restrict]. apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* apply (OBr E' _ _ 10%bv 42%nat _ EI G10). vm_compute; reflexivity.
* apply (OBr E' _ _ 11%bv 43%nat _ EA G11). vm_compute; reflexivity.
* apply (OBr E' _ _ 14%bv 46%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). vm_compute; reflexivity.
* apply (OBr E' _ _ 15%bv 47%nat (getr (ms_regs ms) 15%bv) eq_refl eq_refl). vm_compute; reflexivity.
* apply (OBr E' _ _ 16%bv 48%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ assert (FO : fact_obls LT42 FFc = [(aID, mkAF 0 4097 0); (aND, mkAF 4096 CEIL_MAX 4); (aNH, u64f); (aNL, mkAF 0 4097 0); (46%nat, u64f); (47%nat, u64f); (48%nat, u64f)])
by (clear; vm_compute; reflexivity).
rewrite FO. clear FO.
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aID cur _ _ _ EI); clear - Hcur Z16; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aND _ _ _ _ EA); clear - Hcur Z9 Z10 Z16 Z24; [numconst; lia | numconst; lia | | lia].
change (2 ^ 4) with 16. apply Z.mod_divide in Z24 as [q Hq]; [|lia]. rewrite Hq. apply Z.mod_divide; [lia|]. exists (256 * q + cur). lia. }
apply Forall_cons; [apply (JKf E' _ _ ENH)|].
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aNL _ _ _ _ ENL); clear - Hcur LR Z16; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 14%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 15%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|]. apply Forall_nil.
+ cbn [ms_mem restrict]. apply (sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
intros n Hn. subst E'. unfold EFN. rewrite ew_havoc_old by lia. reflexivity.
- vm_compute. reflexivity.
- cbn [ms_mem restrict]. destruct (node_vals (ms_mem ms) cur HI Hcur) as [VH VL].
unfold region_ok, R_ND. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite UA. split; [clear - Hcur Z9; numconst; lia|]. split; [clear - Hcur Z9 Z10 Z16; numconst; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
+ eapply (chunk_ok_val tfibsegs E' _ _ 0 8 (SOff aNH 0) (hashes cur)); [cbn [sv_denot]; rewrite ENH, unsigned_lit_small by exact HR; f_equal; lia | exact HR | cbn; lia |].
rewrite Z.add_0_r. exact VH.
+ eapply (chunk_ok_val tfibsegs E' _ _ 8 4 (SOff aNL 0) (links cur)); [cbn [sv_denot]; rewrite ENL, unsigned_lit_small by (clear - LR Hcur Z16; lia); f_equal; lia | clear - LR Hcur Z16; cbn; lia | cbn; lia |].
exact VL.
- cbn [ss_mem]. exact (ND_disj E' cur HE' Hcur UA).
Qed.
Definition POST_F : world tfibsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists E' ms' mat', c' = mkCfg ms' (with_vm_backing (m_vm_lazy md) mat' md) /\ envD E' /\ INV (ms_mem ms') /\
(st_ok tfibsegs E' S_FOUND (restrict Hd ms') \/ (st_ok tfibsegs E' S_MISS (restrict Hd ms') /\ mem_trace tr (st_depot S) = false)).
Lemma find_loop : forall k cur E ms mat,
(Z.to_nat cur < k)%nat -> st_ok tfibsegs E S_FL (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
ew E aID = Z_to_bv 64 cur -> (cur = 0 \/ 1 <= cur <= nD) -> INVC cur ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POST_F.
Proof.
induction k as [|k IH]; intros cur E ms mat Hk HS HE HI EI Hcur HC; [exfalso; clear - Hk; lia|].
pose proof Hwx_tfa as HWX. zone. fixu HE.
assert (UI : bv_unsigned (ew E aID) = cur) by (rewrite EI; apply unsigned_lit_small; clear - Hcur Z16; lia). unfold aID in UI.
srr_branch_with tfibtbl_rtD_ok HS.
-
apply (condZ_lit E BC_EQ 42 0 0 true) in Hc; [| rewrite UI; clear - Hcur Z16; lia | clear; lia]. cbn beta iota in Hc. rewrite UI, Z.add_0_r in Hc. apply Z.eqb_eq in Hc.
srr_runG tfibtbl_rtD_ok HS. inv_stepD HI HE INV1.
lazymatch goal with |- SRr _ _ (mkCfg ?msA (with_vm_backing _ ?matc _)) _ => apply SRr_ret; split; [reflexivity|]; exists E, msA, matc end.
split; [reflexivity|]. split; [exact HE|]. split; [exact INV1|]. right. split; [exact HS|].
apply miss_no_trace. intros A. destruct (HC A) as [f Hf]. rewrite Hc in Hf. exact (chain_has_0 f _ Hf).
-
apply (condZ_lit E BC_EQ 42 0 0 false) in Hc; [| rewrite UI; clear - Hcur Z16; lia | clear; lia]. cbn beta iota in Hc. rewrite UI, Z.add_0_r in Hc. apply Z.eqb_neq in Hc.
assert (Hcur' : 1 <= cur <= nD) by (clear - Hcur Hc; lia). clear Hcur Hc.
srr_runG tfibtbl_rtD_ok HS. inv_stepD HI HE INV1.
apply (st_ok_pin_regU E _ _ 12%bv (SLit (TFIB_DEPOT + d_map1))) in HS; [| intros X; discriminate |].
2:{ red_sr. rewrite U_SLit, (map1_valw E cur UI ltac:(clear - Hcur' Z16; lia)). reflexivity. }
srr_runG tfibtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
rreg HS (10%bv : bv 5) G10.
pose proof (st_ok_reg_denot Hd E _ _ 11%bv HS) as G11. cbn [ms_regs restrict] in G11.
lazymatch type of G11 with _ = sv_denot E ?e =>
rewrite (denot_of_U E e _ (node_val E NB cur V32 UI ltac:(clear - Hcur' Z16; lia) ltac:(clear - Z9; numconst; lia) ltac:(clear - Z9 Z10; numconst; lia))) in G11 end.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
destruct (reabs_FN E ss2 ms2 cur HS HE eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop))
Hcur' ltac:(rewrite G10; change (ew E 42) with (ew E aID); exact EI) G11 INV2) as (HS' & HE' & EI' & ENH & ENL) end.
clear HS G10 G11. rename HS' into HS.
pose proof (hashes_u64 cur) as HR. pose proof (proj1 (D2 cur Hcur')) as LR.
pose proof (U36 _ (fixedU_of_envD _ HE')) as X36. unfold aHASH in X36.
pose proof ENH as X44. unfold aNH in X44. apply (f_equal bv_unsigned) in X44. rewrite unsigned_lit_small in X44 by exact HR.
pose proof ENL as X45. unfold aNL in X45. apply (f_equal bv_unsigned) in X45. rewrite unsigned_lit_small in X45 by (clear - LR Hcur' Z16; lia).
srr_runG tfibtbl_rtD_ok HS. inv_stepD INV2 HE' INV3.
srr_branch_with tfibtbl_rtD_ok HS.
+
apply (condZ _ BC_NE 36 0 44 0 true) in Hc; [| rewrite X36; clear - Z18; lia | rewrite X44; clear - HR; lia]. cbn beta iota in Hc.
rewrite X36, X44, !Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
srr_runG tfibtbl_rtD_ok HS. inv_stepD INV3 HE' INV4.
rreg HS (11%bv : bv 5) G11.
lazymatch type of HS with st_ok _ ?E' ?ss5 (restrict _ ?ms5) =>
destruct (reabs_FL E' ss5 ms5 (links cur) HS HE' eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop))
ltac:(rewrite G11, <- X45; symmetry; apply Z_to_bv_bv_unsigned) ltac:(clear - LR Hcur' Z16; lia)) as (HS2 & HE2 & EI2);
apply (IH (links cur) _ ms5 _ ltac:(clear - Hk LR Hcur'; lia) HS2 HE2 INV4 EI2 ltac:(clear - LR Hcur'; lia))
end.
apply (INVC_step cur HC ltac:(clear - Hcur'; lia)). intros X. apply Hc. rewrite X. reflexivity.
+
srr_runG tfibtbl_rtD_ok HS. inv_stepD INV3 HE' INV4.
lazymatch goal with |- SRr _ _ (mkCfg ?msA (with_vm_backing _ ?matc _)) _ =>
lazymatch type of HS with st_ok _ ?E' _ _ => apply SRr_ret; split; [reflexivity|]; exists E', msA, matc end end.
split; [reflexivity|]. split; [exact HE'|]. split; [exact INV4|]. left. exact HS.
Qed.
Lemma B_phase : forall E ms mat, st_ok tfibsegs E S_B (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) POST_F.
Proof.
intros E ms mat HS HE HI. pose proof Hwx_tfa as HWX. zone. fixu HE.
srr_runG tfibtbl_rtD_ok HS. inv_stepD HI HE INV1.
pose proof (hd_and_val E HDv V38 ltac:(clear - Z20 Z16; lia)) as A1. pose proof (hd_and_val0 E HDv V38 ltac:(clear - Z20 Z16; lia)) as A0.
apply (st_ok_pin_regU E _ _ 25%bv (SOff aHD 0)) in HS; [| intros X; discriminate |].
2:{ red_sr. rewrite A1, U_SOff. unfold aHD. rewrite V38. unfold zcanon, M64. rewrite Z.add_0_r. apply Z.mod_small. clear - Z20 Z16; lia. }
pose proof (st_ok_reg_denot Hd E _ _ 11%bv HS) as G11. cbn [ms_regs restrict] in G11.
lazymatch type of G11 with _ = sv_denot E ?e => rewrite (denot_of_U E e _ A0) in G11 end.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
destruct (reabs_FL E ss1 ms1 HDv HS HE eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop))
G11 ltac:(clear - Z20 Z16; lia)) as (HS' & HE' & EI');
apply (find_loop (Datatypes.S (Z.to_nat HDv)) HDv _ ms1 _ ltac:(clear; lia) HS' HE' INV1 EI' ltac:(clear - Z20; lia) INVC_start)
end.
Qed.
Lemma rd_unchanged : forall m a, INV m -> ~ WIN a -> 0 <= a < 2 ^ 64 -> aview tfibsegs Hd m a = rd0 a.
Proof. intros m a [IF _] Hw Ha. apply (aview_same Hd). apply IF. rewrite unsigned_lit_small by exact Ha. exact Hw. Qed.
Lemma val_mem_rdZ : forall m a (w : nat) v k, val_mem tfibsegs (mrestrict Hd m) a w v -> (k < w)%nat ->
aview tfibsegs Hd m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma val_mem_rd32 : forall m a v, val_mem tfibsegs (mrestrict Hd m) a 4 v -> rd32 (aview tfibsegs Hd m) a v.
Proof. intros m a v Hv k Hk. exact (val_mem_rdZ m a 4 v k Hv Hk). Qed.
Lemma val_mem_rd64 : forall m a v, val_mem tfibsegs (mrestrict Hd m) a 8 v -> rd64 (aview tfibsegs Hd m) a v.
Proof. intros m a v Hv k Hk. exact (val_mem_rdZ m a 8 v k Hv Hk). Qed.
Lemma val_mem_cell : forall m e (w : nat) v, val_mem tfibsegs (mrestrict Hd m) (aeval B ly e) w (aeval B ly v) -> cell_holds B ly (aview tfibsegs Hd m) (ACell e w (AV v)).
Proof. intros m e w v Hv k Hk. cbn [c_at c_w]. exact (val_mem_rdZ m _ w _ k Hv Hk). Qed.
Lemma tab_unchanged : forall m b k, INV m -> 0 <= b < d_tab_words -> b <> bkt -> 0 <= k < 4 ->
aview tfibsegs Hd m (as_depot B + 4 * b + k) = rd0 (as_depot B + 4 * b + k).
Proof.
intros m b k HI Hb Hbk Hk. zone. rewrite (ts_depot B HB). apply (rd_unchanged m _ HI); [| clear - Hb Hk; numconst; lia].
unfold WIN, S2, NUQ, NDN, SLOT. zoneNS. clear - Hb Hbk Hk Z9 Z11 Z1 Z3 Z16 Z17 Z19 NZ SZ'. numconst. lia.
Qed.
Lemma depot_ok_found : forall m, INV m -> val_mem tfibsegs (mrestrict Hd m) S2 4 HDv -> depot_ok B ly (aview tfibsegs Hd m) S.
Proof.
intros m HI VT. exists heads, links. fold nD. change (fun id : Z => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S) [])) with hashes.
split; [| split].
- intros b Hb. destruct (D1 b Hb) as [R1 R2]. split; [exact R1|].
destruct (Z.eq_dec b bkt) as [->|Hne].
+ rewrite (ts_depot B HB). fold HDv. change (TFIB_DEPOT + 4 * bkt) with S2. exact (val_mem_rd32 m _ _ VT).
+ intros k Hk. rewrite (tab_unchanged m b (Z.of_nat k) HI Hb Hne ltac:(lia)). exact (R2 k Hk).
- intros id Hid. destruct (D2 id Hid) as (L1 & _ & _). split; [exact L1|]. destruct (node_vals m id HI Hid) as [VH VL].
rewrite hashes_mod. split; [exact (val_mem_rd64 m _ _ VH) | exact (val_mem_rd32 m _ _ VL)].
- exact D3.
Qed.
Lemma depot_cells_hold : forall m S', INV m -> st_regions S' = st_regions S ->
val_mem tfibsegs (mrestrict Hd m) NUQ 4 (depot_ids S') -> val_mem tfibsegs (mrestrict Hd m) TFIB_STORE 8 (Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S') ->
Forall (cell_holds B ly (aview tfibsegs Hd m)) (depot_cells ly S').
Proof.
intros m S' HI _ V1 V3. zone. pose proof HCELLS as HC. unfold depot_cells in HC |- *.
apply Forall_inv_tail in HC. pose proof (Forall_inv HC) as C2. do 2 apply Forall_inv_tail in HC. pose proof (Forall_inv HC) as C4. clear HC.
apply Forall_cons. { apply val_mem_cell. cbn [aeval]. rewrite (ts_depot B HB). exact V1. }
apply Forall_cons. { eapply cell_holds_agree; [exact C2|]. intros k Hk. cbn [c_at c_w aeval c8 c4 z8 z4] in Hk |- *. rewrite (ts_depot B HB). apply (rd_unchanged m _ HI); [| clear - Hk; numconst; lia].
unfold WIN, S2, NUQ, NDN, SLOT. zoneNS. clear - Hk Z9 Z11 Z1 Z3 Z16 Z17 Z19 NZ SZ'. numconst. lia. }
apply Forall_cons. { apply val_mem_cell. cbn [aeval]. rewrite (ts_store B HB). unfold s_total. rewrite Z.add_0_r. exact V3. }
apply Forall_cons; [| apply Forall_nil].
eapply cell_holds_agree; [exact C4|]. intros k Hk. cbn [c_at c_w aeval c8 c4 z8 z4] in Hk |- *. rewrite (ts_store B HB). apply (rd_unchanged m _ HI); [| clear - Hk; unfold s_block0 in *; numconst; lia].
unfold WIN, S2, NUQ, NDN, SLOT. unfold s_block0 in *. zoneNS. clear - Hk Z9 Z11 Z1 Z3 Z16 Z17 Z19 NZ SZ'. numconst. lia.
Qed.
Lemma vis_kept : forall m, INV m -> Forall (range_vis B ly (aview tfibsegs Hd m)) [(ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize)].
Proof. intros m HI. apply (Forall_range_vis_keep B ly rd0); [| exact HVIS]. intros a Ha. exact (INV_aview m a HI Ha). Qed.
Lemma depot_mem_ok_found : forall m, INV m -> val_mem tfibsegs (mrestrict Hd m) S2 4 HDv -> val_mem tfibsegs (mrestrict Hd m) NUQ 4 nD ->
val_mem tfibsegs (mrestrict Hd m) TFIB_STORE 8 TOT -> depot_mem_ok B ly S (aview tfibsegs Hd m).
Proof.
intros m HI VT V1 V3. split; [| split; [exact (depot_ok_found m HI VT) | exact (vis_kept m HI)]].
apply (depot_cells_hold m S HI eq_refl); [exact V1 | exact V3].
Qed.
Definition wsafe (a : Z) (w : nat) : bool :=
(0 <=? a) && forallb (fun k => let x := a + Z.of_nat k in
negb (((TFIB_STORE <=? x) && (x <? TFIB_STORE + 8)) || ((TFIB_STORE + 24 <=? x) && (x <? TFIB_STORE + 28)) ||
((TFIB_DEPOT <=? x) && (x <? TFIB_DEPOT + d_nuniq + 4)) ||
(x <? TFIB_IMG_LO) || ((TFIB_IMG_END <=? x) && (x <? kLowShadowBeg)) || (kLowShadowEnd <=? x))) (seq 0 (Nat.max 1 w)).
Definition cell_safe (c : acell) : bool :=
match c_at c with
| ANum a => wsafe a (c_w c)
| ATsd o => wsafe (TFIB_TSD + o) (c_w c)
| ATp o => wsafe (TFIB_TP + o) (c_w c)
| AInst o => wsafe (TFIB_INST + o) (c_w c)
| AT o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? kThreadObjSize)
| AC o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? 256)
| AD o => (0 <=? o) && (o + Z.of_nat (Nat.max 1 (c_w c)) <=? 4096)
| _ => false
end.
Lemma wsafe_sound : forall a w, wsafe a w = true -> forall k, 0 <= k < Z.max 1 (Z.of_nat w) -> ~ WIN (a + k) /\ 0 <= a + k < 2 ^ 64.
Proof.
intros a w H k Hk. zone. unfold wsafe in H. apply andb_prop in H as [Ha H]. apply Z.leb_le in Ha.
pose proof (proj1 (forallb_forall _ _) H (Z.to_nat k) ltac:(apply in_seq; clear - Hk; lia)) as X. cbn beta in X. rewrite Z2Nat.id in X by (clear - Hk; lia).
apply Bool.negb_true_iff in X.
apply Bool.orb_false_iff in X as [X XHI]. apply Bool.orb_false_iff in X as [X XMID]. apply Bool.orb_false_iff in X as [X XLO].
apply Bool.orb_false_iff in X as [X X1]. apply Bool.orb_false_iff in X as [X X0].
assert (L : forall p q x, ((p <=? x) && (x <? q)) = false -> ~ (p <= x < q)) by (clear; intros p q x E [A C]; rewrite (proj2 (Z.leb_le _ _) A), (proj2 (Z.ltb_lt _ _) C) in E; discriminate).
apply L in X. apply L in X0. apply L in X1. apply L in XMID. apply Z.ltb_ge in XLO. apply Z.leb_gt in XHI.
unfold WIN, S2, NUQ, NDN, SLOT. zoneNS. clear - X X0 X1 XLO XMID XHI Ha Hk Z1 Z3 Z9 Z11 Z16 Z17 Z19 NZ SZ'. numconst. unfold TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd in *. lia.
Qed.
Lemma rd_unchanged_mod : forall m a, INV m -> ~ WIN (a mod 2 ^ 64) -> aview tfibsegs Hd m a = rd0 a.
Proof. intros m a [IF _] Hw. apply (aview_same Hd). apply IF. rewrite Z_to_bv_unsigned. exact Hw. Qed.
Lemma le_byte_mod64 : forall v k, YG0f.le_byte v 8 k = YG0f.le_byte (v mod 2 ^ 64) 8 k.
Proof. intros v k. unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma tsd_val : ly_tsd ly mod 2 ^ 64 = TFIB_TSD.
Proof.
pose proof HCONST as HC. rewrite (ts_const B HB) in HC.
pose proof (proj1 (Forall_forall _ _) HC (c8 (ATp (-88)) (ATsd 0)) ltac:(unfold Tfib_const, Tfib_const_sym; cbn; tauto)) as A.
pose proof (proj1 (Forall_forall _ _) HC (z8 (ANum 0x5d8f38) 0x5fa338) ltac:(apply in_app_iff; right; apply in_app_iff; left; unfold Tfib_const_abs; cbn; tauto)) as Bc.
cbn [cell_holds c_at c_w c_val c8 z8 aeval] in A, Bc. rewrite (ts_tp B HB) in A. change (TFIB_TP + -88) with 6131512 in A. rewrite Z.add_0_r in A.
assert (E8 : forall k, (k < 8)%nat -> YG0f.le_byte (ly_tsd ly mod 2 ^ 64) 8 k = YG0f.le_byte 6267704 8 k).
{ intros k Hk. rewrite <- le_byte_mod64. specialize (A k Hk). specialize (Bc k Hk). rewrite A in Bc. injection Bc as E. exact E. }
pose proof (le_bytes8_sum (ly_tsd ly mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia)) as S1. cbn beta zeta in S1.
rewrite !E8 in S1 by lia. rewrite <- S1. vm_compute. reflexivity.
Qed.
Lemma d_facts : zdisjoint (NB, kNodesBlockSize) (ly_D ly, 4096) /\ zdisjoint (SB, kStoreBlockSize) (ly_D ly, 4096) /\
zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\ 4096 <= ly_D ly /\ ly_D ly + 4096 <= 140737479966720.
Proof.
pose proof (lo_app ly LY) as HH. unfold owned_extents in HH.
pose proof (proj1 (Forall_forall _ _) HH (ly_D ly, 4096) ltac:(cbn; tauto)) as [XD1 XD2]. cbn [fst snd] in XD1, XD2.
assert (XD2' : ly_D ly + 4096 <= 140737479966720) by (clear - XD2; ceil; unfold kLowShadowBeg, ASAN_CEIL in *; lia). clear XD2.
pose proof (lo_disj ly LY) as PD. unfold static_extents, owned_extents in PD. cbn [app] in PD.
destruct PD as (_ & _ & _ & _ & FNB & FSB & _ & FD & _).
pose proof (proj1 (Forall_forall _ _) FNB (ly_D ly, 4096) ltac:(cbn; tauto)) as ND.
pose proof (proj1 (Forall_forall _ _) FSB (ly_D ly, 4096) ltac:(cbn; tauto)) as SD.
pose proof (proj1 (Forall_forall _ _) FD (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) ltac:(cbn; tauto)) as DK.
repeat split; assumption.
Qed.
Lemma const_cell_kept : forall m c, INV m -> cell_safe c = true -> cell_holds B ly rd0 c -> cell_holds B ly (aview tfibsegs Hd m) c.
Proof.
intros m c HI H Hc. zone. pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TN & TS & TK & NC & SC & CK & TH & CH).
eapply cell_holds_agree; [exact Hc|]. intros k Hk.
unfold cell_safe in H. destruct (c_at c) as [a|o|o|o|o|o|o|o|r o|o|o|o|o|o|o|o|o|o|e]; try discriminate H; cbn [aeval].
- destruct (wsafe_sound a _ H k Hk) as [X R]. apply (rd_unchanged m _ HI X R).
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zdisjoint in TN, TS, TK. cbn [fst snd] in TN, TS, TK.
pose proof (zone3_off_img _ _ (ly_T ly + o + k) T_zone ltac:(clear - H1 H2 Hk; unfold kThreadObjSize in *; lia)) as TO. unfold off_img, TFIB_IMG_LO, TFIB_IMG_END in TO.
apply (rd_unchanged m _ HI); unfold WIN, S2, NUQ, NDN, SLOT; zoneNS; clear - H1 H2 Hk TN TS TK TO Z1 Z3 Z4 Z9 Z11 Z16 Z17 Z19 NZ SZ'; unfold kThreadObjSize in *; numconst; lia.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold zdisjoint in NC, SC, CK. cbn [fst snd] in NC, SC, CK.
pose proof (zone3_off_img _ _ (ly_C ly + o + k) C_zone ltac:(clear - H1 H2 Hk; lia)) as CO. unfold off_img, TFIB_IMG_LO, TFIB_IMG_END in CO.
apply (rd_unchanged m _ HI); unfold WIN, S2, NUQ, NDN, SLOT; zoneNS; clear - H1 H2 Hk NC SC CK CO Z1 Z3 Z4 Z9 Z11 Z16 Z17 Z19 NZ SZ'; numconst; lia.
- destruct (wsafe_sound _ _ H k Hk) as [X R]. apply (rd_unchanged_mod m _ HI).
assert (EQ : (ly_tsd ly + o + k) mod 2 ^ 64 = TFIB_TSD + o + k).
{ replace (ly_tsd ly + o + k) with (ly_tsd ly + (o + k)) by (clear; lia). rewrite <- Zplus_mod_idemp_l, tsd_val. rewrite Z.mod_small by (clear - R; lia). clear; lia. }
rewrite EQ. exact X.
- rewrite (ts_inst B HB). destruct (wsafe_sound _ _ H k Hk) as [X R]. apply (rd_unchanged m _ HI X R).
- rewrite (ts_tp B HB). destruct (wsafe_sound _ _ H k Hk) as [X R]. apply (rd_unchanged m _ HI X R).
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. pose proof d_facts as (DN & DS & DK & DH & DH2).
unfold zdisjoint in DN, DS, DK. cbn [fst snd] in DN, DS, DK.
pose proof (zone3_off_img _ _ (ly_D ly + o + k) D_zone ltac:(clear - H1 H2 Hk; lia)) as DO. unfold off_img, TFIB_IMG_LO, TFIB_IMG_END in DO.
apply (rd_unchanged m _ HI); unfold WIN, S2, NUQ, NDN, SLOT; zoneNS; clear - H1 H2 Hk DN DS DK DO Z1 Z3 Z4 Z9 Z11 Z16 Z17 Z19 NZ SZ'; numconst; lia.
Qed.
Lemma const_kept : forall m, INV m -> Forall (cell_holds B ly (aview tfibsegs Hd m)) (as_const B ly).
Proof.
intros m HI. pose proof HCONST as HC. rewrite (ts_const B HB) in HC |- *.
assert (CK : forallb cell_safe (Tfib_const ly) = true) by (vm_compute; reflexivity).
apply Forall_forall. intros c Hc. apply (const_cell_kept m c HI); [| exact (proj1 (Forall_forall _ _) HC c Hc)].
exact (proj1 (forallb_forall _ _) CK c Hc).
Qed.
Definition DPOST : world tfibsegs -> config -> Prop := fun W' c' =>
W' = W /\ exists z regs' mem' mat, c' = mkCfg (mkst regs' (getr regs 1%bv) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
aok S (KDepot tr) z /\ regs_preserved regs regs' /\
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> mem' x = mem x) /\
(forall a, apresent Hd mem a -> apresent Hd mem' a) /\
depot_mem_ok B ly (depot_after z tr S) (aview tfibsegs Hd mem') /\
Forall (cell_holds B ly (aview tfibsegs Hd mem')) (as_const B ly).
Definition exit_regs_ok (sr : list sv) : bool :=
forallb (fun p : bv 5 * sv => sv_eqb (sr_get sr (fst p)) (snd p))
[(1%bv, SOff 1%nat 0); (2%bv, SOff 2%nat 0); (3%bv, SLit TFIB_GP); (4%bv, SLit TFIB_TP); (8%bv, SOff 8%nat 0); (9%bv, SOff 9%nat 0);
(18%bv, SOff 18%nat 0); (19%bv, SOff 19%nat 0); (20%bv, SOff 20%nat 0); (21%bv, SOff 21%nat 0); (22%bv, SOff 22%nat 0); (23%bv, SOff 23%nat 0);
(24%bv, SOff 24%nat 0); (25%bv, SOff 25%nat 0); (26%bv, SOff 26%nat 0); (27%bv, SOff 27%nat 0)].
Lemma exit_regs : forall E ss ms, st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> exit_regs_ok (ss_regs ss) = true ->
regs_preserved regs (ms_regs ms) /\ getr (ms_regs ms) 1%bv = getr regs 1%bv.
Proof.
intros E ss ms HS HE Hck.
assert (G : forall (r : bv 5) e, sv_eqb (sr_get (ss_regs ss) r) e = true -> getr (ms_regs ms) r = sv_denot E e).
{ intros r e Hq. apply sv_eqb_eq in Hq. rewrite <- Hq. exact (st_ok_reg_denot Hd E ss ms r HS). }
unfold exit_regs_ok in Hck. cbn [forallb fst snd] in Hck. repeat (apply andb_prop in Hck as [?GG Hck]).
assert (A : forall (r : bv 5) (n : nat), sv_eqb (sr_get (ss_regs ss) r) (SOff n 0) = true -> (n < K_D)%nat -> Z.of_nat n = bv_unsigned r -> getr (ms_regs ms) r = getr regs r).
{ intros r n Hq Hn Hrn. rewrite (G r _ Hq). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HE n Hn). exact (Er n r Hrn). }
unfold K_D in A. split.
- apply regs_preserved_intro.
+ apply (A 2%bv 2%nat GG0); [lia | reflexivity].
+ rewrite (G 3%bv _ GG1). cbn [sv_denot]. rewrite R3, (ts_gp B HB). reflexivity.
+ rewrite (G 4%bv _ GG2). cbn [sv_denot]. rewrite R4. reflexivity.
+ apply (A 8%bv 8%nat GG3); [lia | reflexivity].
+ apply (A 9%bv 9%nat GG4); [lia | reflexivity].
+ apply (A 18%bv 18%nat GG5); [lia | reflexivity].
+ apply (A 19%bv 19%nat GG6); [lia | reflexivity].
+ apply (A 20%bv 20%nat GG7); [lia | reflexivity].
+ apply (A 21%bv 21%nat GG8); [lia | reflexivity].
+ apply (A 22%bv 22%nat GG9); [lia | reflexivity].
+ apply (A 23%bv 23%nat GG10); [lia | reflexivity].
+ apply (A 24%bv 24%nat GG11); [lia | reflexivity].
+ apply (A 25%bv 25%nat GG12); [lia | reflexivity].
+ apply (A 26%bv 26%nat GG13); [lia | reflexivity].
+ apply (A 27%bv 27%nat GG14); [lia | reflexivity].
- apply (A 1%bv 1%nat GG); [lia | reflexivity].
Qed.
Lemma exit_frame : forall m, INV m ->
(forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ~ depot_footprint B ly (bv_unsigned x) -> m x = mem x) /\
(forall a, apresent Hd mem a -> apresent Hd m a).
Proof.
intros m HI. split; [| intros a Ha; exact (INV_apresent m a HI Ha)].
intros x N1 N2. apply (proj1 HI). intros Hw. destruct (WIN_foot _ Hw) as [H|H]; [exact (N1 H) | exact (N2 H)].
Qed.
Lemma found_exit : forall E ms mat, st_ok tfibsegs E S_FOUND (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat HS HE HI. pose proof Hwx_tfa as HWX. zone. fixu HE.
destruct (exit_regs E _ ms HS HE ltac:(vm_compute; reflexivity)) as [RP R1].
eapply (SRr_ret_at tfibsegs tfibtbl_rtD tfibtbl_rtD_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
exists 0, (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [left; reflexivity|]. split; [exact RP|].
destruct (exit_frame _ HI) as [F1 F2]. split; [exact F1|]. split; [exact F2|].
split; [| exact (const_kept _ HI)].
cbn [depot_after Z.eqb]. apply (depot_mem_ok_found _ HI).
- memv HS 7%nat 0%nat; [unfold aS2; rewrite V37; lia | cbn [sv_denot]; unfold aHD; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- (Z_to_bv_bv_unsigned 64 (ew E 38)), V38; reflexivity | clear - Z20 Z16; lia].
- memv HS 6%nat 0%nat; [vm_compute; reflexivity | cbn [sv_denot]; unfold aN; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- (Z_to_bv_bv_unsigned 64 (ew E 35)), V35; reflexivity | clear - Z16; lia].
- memv HS 8%nat 0%nat; [vm_compute; reflexivity | cbn [sv_denot]; unfold aTOT; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- (Z_to_bv_bv_unsigned 64 (ew E 34)), V34; reflexivity | clear - Z17; lia].
Qed.
Lemma entry_phase : forall mat, (1 <= length tr)%nat -> SRr tfibsegs W (mkCfg msD0 (with_vm_backing (m_vm_lazy md) mat md)) POST_B.
Proof.
intros mat Htr1. pose proof Hwx_tfa as HWX. zone. pose proof (SEED_ok Htr1) as HS. pose proof INV_mem as HI. pose proof envD_E0 as HE. fixu HE.
srr_run_toG tfibtbl_rtD_ok HS A_HLOOP. inv_stepD HI HE INV1.
apply (st_ok_pin_regU E0 _ _ 13%bv (SLit 0)) in HS; [| intros X; discriminate |].
2:{ red_sr. apply (pin_tag0 E0 _ V11). clear - Z8; lia. }
rreg HS (11%bv : bv 5) G11. rewrite E10 in G11.
pose proof (st_ok_reg_denot Hd E0 _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot _ ?e => rewrite (denot_of_U E0 e _ (h0_val E0 _ V11 ltac:(clear - Z8; lia))) in G12 end.
pose proof (st_ok_reg_denot Hd E0 _ _ 14%bv HS) as G14. cbn [ms_regs restrict] in G14.
lazymatch type of G14 with _ = sv_denot _ ?e => rewrite (denot_of_U E0 e _ (end_val E0 _ buf V11 ltac:(clear - Z8; lia) V10 ltac:(clear - Z1 Z5; lia) ltac:(clear - Z2 Z6 Z8; lia))) in G14 end.
lazymatch type of HS with st_ok _ _ ?ss1 (restrict _ ?ms1) =>
destruct (reabs_H E0 ss1 ms1 0%nat HS envD_E0 eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop))
Htr1 ltac:(rewrite G11; f_equal; lia) ltac:(rewrite G12; reflexivity) G14 INV1) as (HS' & HE' & EW & EHh & EP & EE);
apply (hash_loop (length tr) 0%nat _ ms1 _ ltac:(clear; lia) Htr1 HS' HE' INV1 EW EHh EP EE)
end.
Qed.
Definition S_ins : astate := set_depot (st_depot S ++ [tr]) S.
Definition heads' (b : Z) : Z := if b =? bkt then nD + 1 else heads b.
Definition links' (id : Z) : Z := if id =? nD + 1 then HDv else links id.
Definition hashes' : Z -> Z := fun id => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S_ins) []).
Lemma nD_ins : depot_ids S_ins = nD + 1.
Proof. unfold depot_ids, S_ins, nD, depot_ids. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. lia. Qed.
Lemma frames_shift : forall (l : list (list Z)) a,
fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) a l = fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 l + a.
Proof. induction l as [|t l IH]; intros a; cbn [fold_right]; [lia|]. rewrite (IH a). lia. Qed.
Lemma frames_ins : depot_frames S_ins = depot_frames S + (Z.of_nat (length tr) + 1).
Proof.
unfold depot_frames, S_ins. cbn [st_depot set_depot]. rewrite fold_right_app. cbn [fold_right]. rewrite frames_shift. lia.
Qed.
Lemma hashes'_old : forall id, id <= nD -> hashes' id = hashes id.
Proof.
intros id Hid. unfold hashes', hashes, depot_traces, S_ins. cbn [st_depot set_depot].
change (ly_tr0 ly :: st_depot S ++ [tr]) with ((ly_tr0 ly :: st_depot S) ++ [tr]). rewrite app_nth1; [reflexivity|].
cbn [length]. unfold nD, depot_ids in Hid. lia.
Qed.
Lemma hashes'_new : hashes' (nD + 1) = HSH.
Proof.
unfold hashes', HSH, depot_traces, S_ins. cbn [st_depot set_depot]. rewrite HDH.
change (ly_tr0 ly :: st_depot S ++ [tr]) with ((ly_tr0 ly :: st_depot S) ++ [tr]). rewrite app_nth2 by (cbn [length]; unfold nD, depot_ids; lia).
replace (Z.to_nat (nD + 1 - 1) - length (ly_tr0 ly :: st_depot S))%nat with 0%nat by (cbn [length]; unfold nD, depot_ids; lia). reflexivity.
Qed.
Lemma chain_fuel : forall L Hh f cur h, chain_has L Hh f cur h -> chain_has L Hh (Datatypes.S f) cur h.
Proof. induction f as [|f IH]; intros cur h Hc; cbn in Hc |- *; [destruct Hc|]. destruct Hc as [H1 [H2|H2]]; [tauto | split; [exact H1 | right; exact (IH _ _ H2)]]. Qed.
Lemma chain_ext : forall f cur h, 0 <= cur <= nD -> chain_has links hashes f cur h -> chain_has links' hashes' f cur h.
Proof.
induction f as [|f IH]; intros cur h Hcur Hc; cbn in Hc |- *; [destruct Hc|]. destruct Hc as [H1 H2].
assert (R : 1 <= cur <= nD) by lia. pose proof (proj1 (D2 cur R)) as LR.
split; [exact H1|]. rewrite (hashes'_old cur) by lia.
assert (EL : links' cur = links cur) by (unfold links'; replace (cur =? nD + 1) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
rewrite EL. destruct H2 as [H2|H2]; [left; exact H2 | right]. apply IH; [clear - LR Hcur; lia | exact H2].
Qed.
Lemma depot_ok_ins : forall m, INV m ->
val_mem tfibsegs (mrestrict Hd m) S2 4 (nD + 1) -> val_mem tfibsegs (mrestrict Hd m) NDN 8 HSH -> val_mem tfibsegs (mrestrict Hd m) (NDN + 8) 4 HDv ->
depot_ok B ly (aview tfibsegs Hd m) S_ins.
Proof.
intros m HI VT VH VL. zone. exists heads', links'. rewrite nD_ins. change (fun id : Z => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces ly S_ins) [])) with hashes'.
split; [| split].
- intros b Hb. destruct (D1 b Hb) as [R1 R2]. unfold heads'. destruct (Z.eqb_spec b bkt) as [->|Hne].
+ split; [clear - Z16; lia|]. rewrite (ts_depot B HB). change (TFIB_DEPOT + 4 * bkt) with S2. exact (val_mem_rd32 m _ _ VT).
+ split; [clear - R1; lia|]. intros k Hk. rewrite (tab_unchanged m b (Z.of_nat k) HI Hb Hne ltac:(lia)). exact (R2 k Hk).
- intros id Hid. unfold links'. destruct (Z.eqb_spec id (nD + 1)) as [->|Hne].
+ split; [clear - Z20; lia|]. rewrite hashes'_new, (Z.mod_small HSH (2 ^ 64)) by exact Z18. fold NDN. split; [exact (val_mem_rd64 m _ _ VH) | exact (val_mem_rd32 m _ _ VL)].
+ assert (R : 1 <= id <= nD) by (clear - Hid Hne; lia). destruct (D2 id R) as (L1 & _ & _). split; [exact L1|].
rewrite (hashes'_old id) by lia. destruct (node_vals m id HI R) as [NVH NVL]. rewrite hashes_mod.
split; [exact (val_mem_rd64 m _ _ NVH) | exact (val_mem_rd32 m _ _ NVL)].
- intros id Hid. replace (Z.to_nat (nD + 1)) with (Datatypes.S (Z.to_nat nD)) by (clear - Z16; lia). destruct (Z.eqb_spec id (nD + 1)) as [->|Hne].
+ rewrite hashes'_new, (Z.mod_small HSH (2 ^ 64)) by exact Z18. fold bkt. unfold heads'. rewrite Z.eqb_refl. cbn [chain_has].
split; [clear - Z16; lia | left; exact hashes'_new].
+ assert (R : 1 <= id <= nD) by (clear - Hid Hne; lia). rewrite (hashes'_old id) by lia. pose proof (D3 id R) as C.
destruct (Z.eq_dec ((hashes id mod 2 ^ 64) mod d_tab_words) bkt) as [Eb|Nb].
* rewrite Eb in C |- *. fold HDv in C. unfold heads'. rewrite (Z.eqb_refl bkt). cbn [chain_has]. split; [clear - Z16; lia | right].
replace (links' (nD + 1)) with HDv by (unfold links'; rewrite Z.eqb_refl; reflexivity). apply chain_ext; [clear - Z20; lia | exact C].
* unfold heads'. replace ((hashes id mod 2 ^ 64) mod d_tab_words =? bkt) with false by (symmetry; apply Z.eqb_neq; exact Nb).
apply chain_fuel. apply chain_ext; [| exact C]. exact (proj1 (D1 _ ltac:(unfold d_tab_words; apply Z.mod_pos_bound; lia))).
Qed.
Lemma depot_mem_ok_ins : forall m, INV m ->
val_mem tfibsegs (mrestrict Hd m) S2 4 (nD + 1) -> val_mem tfibsegs (mrestrict Hd m) NUQ 4 (nD + 1) ->
val_mem tfibsegs (mrestrict Hd m) TFIB_STORE 8 (TOT + Z.of_nat (length tr) + 1) ->
val_mem tfibsegs (mrestrict Hd m) NDN 8 HSH -> val_mem tfibsegs (mrestrict Hd m) (NDN + 8) 4 HDv ->
depot_mem_ok B ly S_ins (aview tfibsegs Hd m).
Proof.
intros m HI VT V1 V3 VH VL. split; [| split; [exact (depot_ok_ins m HI VT VH VL) | exact (vis_kept m HI)]].
apply (depot_cells_hold m S_ins HI eq_refl); rewrite ?nD_ins, ?frames_ins; [exact V1|]. unfold TOT in V3.
replace (Z.of_nat (length (ly_tr0 ly)) + 1 + (depot_frames S + (Z.of_nat (length tr) + 1))) with (Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S + Z.of_nat (length tr) + 1) by lia. exact V3.
Qed.
Definition EEND (E : env) (rg : bvmap 5 word) : env := havoc E 42 [getr rg 11%bv; getr rg 13%bv; getr rg 14%bv; getr rg 16%bv].
Lemma reabs_END : forall E ss ms,
st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_END -> reabs_check LT42 ss ENDREGS ENDF = true -> submem ENDMEM (ss_mem ss) ->
st_ok tfibsegs (EEND E (ms_regs ms)) S_END (restrict Hd ms) /\ envD (EEND E (ms_regs ms)).
Proof.
intros E ss ms HS HE Hpc Hck Hsub. set (E' := EEND E (ms_regs ms)).
assert (HE' : envD E') by (apply envD_havoc; [exact HE | unfold K_D; lia]). split; [| exact HE'].
unfold S_END. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs LT42 E E' ss (restrict Hd ms) ENDREGS ENDMEM ENDF HS (agree_pd_havoc E 42 _ ltac:(lia)) Hck).
- cbn [ms_regs restrict]. apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | []]]]]; injection H as <- <-.
+ apply (OBr E' _ _ 11%bv 42%nat (getr (ms_regs ms) 11%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 13%bv 43%nat (getr (ms_regs ms) 13%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 14%bv 44%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ apply (OBr E' _ _ 16%bv 45%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
- assert (FO : fact_obls LT42 ENDF = [(42%nat, u64f); (43%nat, u64f); (44%nat, u64f); (45%nat, u64f)]) by (clear; vm_compute; reflexivity).
rewrite FO. clear FO.
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 11%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 13%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 14%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|]. apply Forall_nil.
- cbn [ms_mem restrict]. apply (sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
intros n Hn. subst E'. unfold EEND. rewrite ew_havoc_old by lia. reflexivity.
Qed.
Lemma ins_exit : forall E ms mat, st_ok tfibsegs E S_END (restrict Hd ms) -> envD E -> INV (ms_mem ms) -> mem_trace tr (st_depot S) = false ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat HS HE HI MT. pose proof Hwx_tfa as HWX. zone. fixu HE.
destruct (exit_regs E _ ms HS HE ltac:(vm_compute; reflexivity)) as [RP R1].
eapply (SRr_ret_at tfibsegs tfibtbl_rtD tfibtbl_rtD_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
exists 1, (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [right; split; [reflexivity | exact MT]|]. split; [exact RP|].
destruct (exit_frame _ HI) as [F1 F2]. split; [exact F1|]. split; [exact F2|].
split; [| exact (const_kept _ HI)].
cbn [depot_after Z.eqb]. change (set_depot (st_depot S ++ [tr]) S) with S_ins. apply (depot_mem_ok_ins _ HI).
- memv HS 6%nat 0%nat; [unfold aS2; rewrite V37; lia | cbn [sv_denot]; unfold aN; rewrite V35; reflexivity | clear - Z16; lia].
- memv HS 5%nat 0%nat; [vm_compute; reflexivity | cbn [sv_denot]; rewrite V35; reflexivity | clear - Z16; lia].
- memv HS 7%nat 0%nat; [vm_compute; reflexivity | apply denot_of_U; rewrite (tot_val E _ _ V11 V34); clear - Z8 Z17; lia | clear - Z8 Z17; lia].
- memv HS 10%nat 2%nat; [unfold aNDN; rewrite V40; lia | cbn [sv_denot]; unfold aHASH; rewrite Z.add_0_r, V36; reflexivity | exact Z18].
- memv HS 10%nat 0%nat; [unfold aNDN; rewrite V40; lia | cbn [sv_denot]; unfold aHD; rewrite Z.add_0_r, V38; reflexivity | clear - Z20 Z16; lia].
Qed.
Lemma tail_phase : forall E ms mat, st_ok tfibsegs E S_T1 (restrict Hd ms) -> envD E -> INV (ms_mem ms) -> mem_trace tr (st_depot S) = false ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat HS HE HI MT. pose proof Hwx_tfa as HWX. zone. fixu HE.
lazymatch (eval vm_compute in (ss_mem S_T1)) with ?a :: ?b :: ?rest =>
apply (st_ok_drop_regions E _ _ [a; b] rest) in HS; [| vm_compute; reflexivity | vm_compute; reflexivity] end.
apply (st_ok_pin_regU E _ _ 10%bv (SLit (TFIB_STORE + 24))) in HS; [| intros X; discriminate |].
2:{ red_sr. etransitivity; [| apply (std_val E TOT V34); clear - Z17; lia]. rewrite !U_SLit. vm_compute. reflexivity. }
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD HI HE INV1.
srr_branch_with tfibtbl_rtD_ok HS.
- srr_runG tfibtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
lazymatch type of HS with st_ok _ _ ?ssE (restrict _ ?msE) =>
destruct (reabs_END E ssE msE HS HE eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ss_mem]; apply submem_keep; [split; [reflexivity | split; [cbn; lia | split; [cbn; lia | split; [cbn; lia | intros c0 Hc0; destruct Hc0]]]] | apply submem_refl])) as [HS' HE'];
exact (ins_exit _ msE _ HS' HE' INV2 MT) end.
- srr_runG tfibtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
lazymatch type of HS with st_ok _ _ ?ssE (restrict _ ?msE) =>
destruct (reabs_END E ssE msE HS HE eq_refl ltac:(vm_compute; reflexivity)
ltac:(cbn [ss_mem]; apply submem_keep; [split; [reflexivity | split; [cbn; lia | split; [cbn; lia | split; [cbn; lia | intros c0 Hc0; destruct Hc0]]]] | apply submem_refl])) as [HS' HE'];
exact (ins_exit _ msE _ HS' HE' INV2 MT) end.
Qed.
Definition EMC (E : env) (j : Z) (rg : bvmap 5 word) : env :=
havoc E 42 [Z_to_bv 64 (buf + j); Z_to_bv 64 (SLOT + 8 + j); Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)); Z_to_bv 64 (byteZ m0 (buf + j));
getr rg 14%bv; Z_to_bv 64 0; getr rg 16%bv].
Lemma present_now : forall m a b, INV m -> off_img a -> mbyte tfibsegs m0 a = Some b -> exists b', mbyte tfibsegs (mrestrict Hd m) a = Some b'.
Proof.
intros m a b [_ HG] Ha Hb. specialize (HG (Z_to_bv 64 a)). unfold mbyte in Hb |- *.
rewrite (seg_rom_none_off a Ha) in Hb |- *. destruct (mrestrict Hd mem (Z_to_bv 64 a)) as [x|]; [| discriminate].
destruct (mrestrict Hd m (Z_to_bv 64 a)) as [y|]; [exists y; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.
Lemma MC_disj : forall E j, envD E -> 0 <= j < 8 * Z.of_nat (length tr) ->
bv_unsigned (ew E aSC) = buf + j -> bv_unsigned (ew E aDC) = SLOT + 8 + j ->
all_disjoint E R_SRC (R_DST :: MCFIX) /\ all_disjoint E R_DST MCFIX.
Proof.
intros E j HE Hj US UD. zone. pose proof sp_range as SR. fixu HE. unfold aSC in US. unfold aDC in UD.
split; apply all_disjoint_of_extents; unfold MCFIX, R_SRC, R_DST, extent_of_region, aSC, aDC, aBY; cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?US, ?UD, V2, V37, V40; unfold S2, NDN, SLOT; zoneNS; clear - Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15 Z16 Z17 Z19 SR Hj NZ SZ';
numconst; cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
Qed.
Lemma reabs_MC : forall E ss ms j,
st_ok tfibsegs E ss (restrict Hd ms) -> envD E -> ss_pc ss = A_MC -> reabs_check LT42 ss MCREGS MCF = true -> submem MCFIX (ss_mem ss) ->
0 <= j < 8 * Z.of_nat (length tr) ->
getr (ms_regs ms) 11%bv = Z_to_bv 64 (buf + j) -> getr (ms_regs ms) 13%bv = Z_to_bv 64 (SLOT + 8 + j) ->
getr (ms_regs ms) 12%bv = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)) -> INV (ms_mem ms) ->
let E' := EMC E j (ms_regs ms) in
st_ok tfibsegs E' S_MC (restrict Hd ms) /\ envD E' /\
ew E' aSC = Z_to_bv 64 (buf + j) /\ ew E' aDC = Z_to_bv 64 (SLOT + 8 + j) /\ ew E' aME = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)).
Proof.
intros E ss ms j HS HE Hpc Hck Hsub Hj G11 G13 G12 HI. zone. cbn zeta. set (E' := EMC E j (ms_regs ms)).
assert (HE' : envD E') by (apply envD_havoc; [exact HE | unfold K_D; lia]).
assert (ESC : ew E' aSC = Z_to_bv 64 (buf + j)) by reflexivity. assert (EDC : ew E' aDC = Z_to_bv 64 (SLOT + 8 + j)) by reflexivity.
assert (EME : ew E' aME = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr))) by reflexivity. assert (EBY : ew E' aBY = Z_to_bv 64 (byteZ m0 (buf + j))) by reflexivity.
pose proof (byteZ_range m0 (buf + j)) as BR.
assert (USC : bv_unsigned (ew E' aSC) = buf + j) by (rewrite ESC; apply unsigned_lit_small; clear - Hj Z1 Z5 Z6 Z2 Z8; numconst; lia).
assert (UDC : bv_unsigned (ew E' aDC) = SLOT + 8 + j) by (rewrite EDC; apply unsigned_lit_small; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; lia).
split; [| split; [exact HE' | split; [exact ESC | split; [exact EDC | exact EME]]]]. unfold S_MC. rewrite <- Hpc.
destruct (MC_disj E' j HE' Hj USC UDC) as [DJ1 DJ2].
apply (st_ok_add_region E' (mkSS (ss_pc ss) MCREGS (R_DST :: MCFIX) None MCF) (restrict Hd ms) R_SRC).
1: apply (st_ok_add_region E' (mkSS (ss_pc ss) MCREGS MCFIX None MCF) (restrict Hd ms) R_DST).
- apply (st_ok_reabs tfibsegs LT42 E E' ss (restrict Hd ms) MCREGS MCFIX MCF HS (agree_pd_havoc E 42 _ ltac:(lia)) Hck).
+ cbn [ms_regs restrict]. apply Forall_forall. intros [r k] Hin. vm_compute in Hin. cbn [fst snd].
destruct Hin as [H | [H | [H | [H | [H | []]]]]]; injection H as <- <-.
* apply (OBr E' _ _ 11%bv 42%nat _ ESC G11). vm_compute; reflexivity.
* apply (OBr E' _ _ 12%bv 44%nat _ EME G12). vm_compute; reflexivity.
* apply (OBr E' _ _ 13%bv 43%nat _ EDC G13). vm_compute; reflexivity.
* apply (OBr E' _ _ 14%bv 46%nat (getr (ms_regs ms) 14%bv) eq_refl eq_refl). vm_compute; reflexivity.
* apply (OBr E' _ _ 16%bv 48%nat (getr (ms_regs ms) 16%bv) eq_refl eq_refl). vm_compute; reflexivity.
+ assert (FO : fact_obls LT42 MCF = [(aSC, mkAF kHighMemBeg kHighMemEnd 0); (aDC, mkAF 4096 CEIL_MAX 0); (aME, mkAF 4096 CEIL_MAX 0); (aBY, mkAF 0 255 0); (46%nat, u64f); (48%nat, u64f)])
by (clear; vm_compute; reflexivity).
rewrite FO. clear FO.
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aSC _ _ _ _ ESC); clear - Hj Z1 Z2 Z5 Z6 Z8; [numconst; lia | numconst; lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aDC _ _ _ _ EDC); unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; [numconst; lia | numconst; lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aME _ _ _ _ EME); unfold SLOT; clear - Z11 Z12 Z17 Z8; [numconst; lia | numconst; lia | apply Z.mod_1_r | lia]. }
apply Forall_cons. { cbn [fst snd]. apply (AFo E' aBY _ _ _ _ EBY); clear - BR; [lia | lia | apply Z.mod_1_r | lia]. }
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 14%bv)); reflexivity|].
apply Forall_cons; [apply (JKf E' _ (getr (ms_regs ms) 16%bv)); reflexivity|]. apply Forall_nil.
+ cbn [ms_mem restrict]. apply (sub_mem_ok E E' ss); [exact (st_ok_mem_ok tfibsegs E ss _ HS) | exact Hsub | vm_compute; reflexivity | vm_compute; reflexivity | | reflexivity].
intros n Hn. subst E'. unfold EMC. rewrite ew_havoc_old by lia. reflexivity.
- vm_compute. reflexivity.
- cbn [ms_mem restrict]. apply (region_ok_window E' _ aDC (SLOT + 8 + j)); [exact UDC | unfold SLOT; clear - Hj Z11 Z17; numconst; lia | unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; lia |].
intros a Ha. destruct (SB_present a ltac:(unfold SLOT in Ha; clear - Ha Hj Z17 Z8; numconst; lia)) as [b Hb].
assert (OFFa : off_img a) by (apply SB_off; unfold SLOT in Ha; clear - Ha Hj Z17 Z8; numconst; lia).
destruct (present_now (ms_mem ms) a b HI OFFa Hb) as [b' Hb'].
apply (mbyte_off_writable _ a b'); [exact OFFa | exact Hb'].
- cbn [ss_mem]. exact DJ2.
- vm_compute. reflexivity.
- cbn [ms_mem restrict]. unfold region_ok, R_SRC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite USC. split; [clear - Hj Z1 Z5; numconst; lia|]. split; [clear - Hj Z2 Z6 Z8; numconst; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
eapply (chunk_ok_val tfibsegs E' _ _ 0 1 (SOff aBY 0) (byteZ m0 (buf + j))); [cbn [sv_denot]; rewrite EBY, unsigned_lit_small by (clear - BR; lia); f_equal; lia | clear - BR; cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact (byte_INV _ _ HI Hj).
- cbn [ss_mem]. exact DJ1.
Qed.
Lemma mc_loop : forall k j E ms mat,
(Z.to_nat (8 * Z.of_nat (length tr) - j) <= k)%nat -> 0 <= j < 8 * Z.of_nat (length tr) ->
st_ok tfibsegs E S_MC (restrict Hd ms) -> envD E -> INV (ms_mem ms) ->
ew E aSC = Z_to_bv 64 (buf + j) -> ew E aDC = Z_to_bv 64 (SLOT + 8 + j) -> ew E aME = Z_to_bv 64 (SLOT + 8 + 8 * Z.of_nat (length tr)) ->
mem_trace tr (st_depot S) = false ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
induction k as [|k IH]; intros j E ms mat Hk Hj HS HE HI ESC EDC EME MT; [exfalso; clear - Hk Hj; lia|].
pose proof Hwx_tfa as HWX. zone. fixu HE.
assert (USC : bv_unsigned (ew E aSC) = buf + j) by (rewrite ESC; apply unsigned_lit_small; clear - Hj Z1 Z5 Z6 Z2 Z8; numconst; lia).
assert (UDC : bv_unsigned (ew E aDC) = SLOT + 8 + j) by (rewrite EDC; apply unsigned_lit_small; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; lia).
assert (UME : bv_unsigned (ew E aME) = SLOT + 8 + 8 * Z.of_nat (length tr)) by (rewrite EME; apply unsigned_lit_small; unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; lia).
unfold aSC in USC. unfold aDC in UDC. unfold aME in UME.
srr_runG tfibtbl_rtD_ok HS.
lazymatch goal with | HF : frame_of _ ?rs _ (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INV1 : INV (ms_mem msA)) by (apply (INV_runM E rs _ _ HI HE ltac:(vm_compute; reflexivity) HF HG); unfold aDC; rewrite UDC; clear - Hj Z8; lia); clear HF HG HI end.
srr_branch_with tfibtbl_rtD_ok HS.
-
apply (condZ E BC_NE 43 1 44 0 true) in Hc; [| rewrite UDC; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; lia | rewrite UME; unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; lia].
cbn beta iota in Hc. rewrite UDC, UME, Z.add_0_r in Hc. apply Bool.negb_true_iff in Hc. apply Z.eqb_neq in Hc.
assert (Hj' : 0 <= j + 1 < 8 * Z.of_nat (length tr)) by (clear - Hc Hj; lia).
srr_runG tfibtbl_rtD_ok HS.
lazymatch goal with | HF : frame_of _ ?rs _ (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INV2 : INV (ms_mem msA)) by (apply (INV_runM E rs _ _ INV1 HE ltac:(vm_compute; reflexivity) HF HG); unfold aDC; rewrite UDC; clear - Hj Z8; lia); clear HF HG INV1 end.
rreg HS (11%bv : bv 5) G11. rreg HS (13%bv : bv 5) G13. rreg HS (12%bv : bv 5) G12.
lazymatch type of HS with st_ok _ _ ?ss2 (restrict _ ?ms2) =>
destruct (reabs_MC E ss2 ms2 (j + 1) HS HE eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn [ss_mem]; repeat (apply submem_refl || apply submem_drop)) Hj'
ltac:(rewrite G11, USC; f_equal; lia) ltac:(rewrite G13, UDC; f_equal; lia) ltac:(rewrite G12; exact EME) INV2)
as (HS' & HE' & ESC' & EDC' & EME')
end.
lazymatch type of HS' with st_ok _ ?E' _ (restrict _ ?ms2) =>
apply (IH (j + 1) E' ms2 _ ltac:(clear - Hk Hj'; lia) Hj' HS' HE' INV2 ESC' EDC' EME' MT) end.
-
apply (condZ E BC_NE 43 1 44 0 false) in Hc; [| rewrite UDC; unfold SLOT; clear - Hj Z11 Z12 Z17 Z8; numconst; lia | rewrite UME; unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; lia].
cbn beta iota in Hc. rewrite UDC, UME, Z.add_0_r in Hc. apply Bool.negb_false_iff in Hc. apply Z.eqb_eq in Hc.
srr_runG tfibtbl_rtD_ok HS.
lazymatch goal with | HF : frame_of _ ?rs _ (ms_mem ?msA), HG : mem_grows _ _ |- _ =>
assert (INV2 : INV (ms_mem msA)) by (apply (INV_runM E rs _ _ INV1 HE ltac:(vm_compute; reflexivity) HF HG); unfold aDC; rewrite UDC; clear - Hj Z8; lia); clear HF HG INV1 end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msT) => exact (tail_phase E msT _ HS HE INV2 MT) end.
Qed.
Ltac sub_mem_tac := cbn [ss_mem]; repeat (apply submem_refl || (apply submem_keep; [apply subregion_refl|]) || apply submem_drop).
Lemma ins_phase : forall E ms mat, (1 <= length tr)%nat -> st_ok tfibsegs E S_MISS (restrict Hd ms) -> envD E -> INV (ms_mem ms) -> mem_trace tr (st_depot S) = false ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros E ms mat Htr1 HS HE HI MT. pose proof Hwx_tfa as HWX. zone. fixu HE.
assert (E10' : ew E 10 = Z_to_bv 64 buf) by (rewrite (HE 10%nat ltac:(unfold K_D; lia)); exact E10).
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD HI HE INV1.
apply (st_ok_pin_regU E _ _ 10%bv (SLit (TFIB_DEPOT + d_map1))) in HS; [| intros X; discriminate |].
2:{ red_sr. rewrite U_SLit, (map1_val1 E nD V35 ltac:(clear - Z16; lia)). vm_compute. reflexivity. }
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD INV1 HE INV2.
assert (NV : forall k, (k <= 2)%nat -> U E (SOff aNDN 0) = U E (Nat.iter k (fun e => SAlu ALU_ADD e (SLit 0)) (SAlu ALU_ADD (SOff 32%nat 0) (SAlu ALU_SLL (SAlu ALU_AND (SOff 35%nat 1) (SLit 65535)) (SLit 4))))).
{ intros k Hk. rewrite (node_val1 E NB nD k V32 V35 ltac:(clear - Z16; lia) ltac:(clear - Z9; numconst; lia) ltac:(clear - Z9 Z10; numconst; lia) Hk).
rewrite U_SOff. unfold aNDN. rewrite V40. unfold zcanon, NDN. rewrite Z.add_0_r. apply Z.mod_small. clear - Z9 Z10 Z16; numconst; lia. }
apply (st_ok_pin_regU E _ _ 10%bv (SOff aNDN 0)) in HS; [| intros X; discriminate | red_sr; exact (NV 1%nat ltac:(lia))].
apply (st_ok_pin_regU E _ _ 8%bv (SOff aNDN 0)) in HS; [| intros X; discriminate | red_sr; exact (NV 2%nat ltac:(lia))].
apply (st_ok_pin_regU E _ _ 9%bv (SOff aNDN 0)) in HS; [| intros X; discriminate | red_sr; exact (NV 0%nat ltac:(lia))].
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD INV2 HE INV3.
apply (st_ok_pin_regU E _ _ 21%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (pin_tag0 E _ V11); clear - Z8; lia].
apply (st_ok_pin_regU E _ _ 11%bv (SOff 11%nat 0)) in HS; [| intros X; discriminate | red_sr; apply (or_tag_val E _ V11); clear - Z8; lia].
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD INV3 HE INV4.
apply (st_ok_pin_regU E _ _ 5%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (t0_val E _ V34); clear - Z17; lia].
apply (st_ok_pin_regU E _ _ 6%bv (SLit 0)) in HS; [| intros X; discriminate | red_sr; apply (t1_val E _ _ V11 V34); clear - Z8 Z17; lia].
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD INV4 HE INV5.
srr_branch_with tfibtbl_rtD_ok HS.
-
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD INV5 HE INV6.
apply (st_ok_pin_regU E _ _ 10%bv (SOff aSLOT 0)) in HS; [| intros X; discriminate |].
2:{ red_sr. rewrite (slot_val E SB TOT V33 V34 ltac:(clear - Z17; lia) ltac:(clear - Z11; lia) ltac:(clear - Z11 Z12; numconst; lia)), U_SOff. unfold aSLOT. rewrite V41.
unfold zcanon, SLOT. rewrite Z.add_0_r. apply Z.mod_small. clear - Z11 Z12 Z17; numconst; lia. }
srr_run_shG tfibtbl_rtD_ok HS. inv_stepD INV6 HE INV7.
rreg HS (11%bv : bv 5) G11. rewrite E10' in G11. rreg HS (13%bv : bv 5) G13. rewrite V41 in G13.
pose proof (st_ok_reg_denot Hd E _ _ 12%bv HS) as G12. cbn [ms_regs restrict] in G12.
lazymatch type of G12 with _ = sv_denot _ ?e =>
rewrite (denot_of_U E e _ (mcend_val E _ SLOT V11 V41 ltac:(clear - Z8; lia) ltac:(unfold SLOT; clear - Z11 Z17; lia) ltac:(unfold SLOT; clear - Z11 Z12 Z17 Z8; numconst; lia))) in G12 end.
lazymatch type of HS with st_ok _ _ ?ss7 (restrict _ ?ms7) =>
destruct (reabs_MC E ss7 ms7 0 HS HE eq_refl ltac:(vm_compute; reflexivity) ltac:(sub_mem_tac) ltac:(clear - Htr1; lia)
ltac:(rewrite G11; f_equal; lia) ltac:(rewrite G13; f_equal; lia) G12 INV7) as (HS' & HE' & ESC & EDC & EME);
apply (mc_loop (Z.to_nat (8 * Z.of_nat (length tr))) 0 _ ms7 _ ltac:(clear; lia) ltac:(clear - Htr1; lia) HS' HE' INV7 ESC EDC EME MT)
end.
-
exfalso. apply (eq_refute E _ _ (t32_val E TOT V34 ltac:(clear - Z17; lia)) Hc).
Qed.
Lemma dep_main : forall mat, (1 <= length tr)%nat -> SRr tfibsegs W (mkCfg msD0 (with_vm_backing (m_vm_lazy md) mat md)) DPOST.
Proof.
intros mat Htr1. apply (SRr_bind tfibsegs W _ POST_B DPOST (entry_phase mat Htr1)).
intros W1 c1 _ HP. unfold POST_B in HP. destruct HP as (HW & E1 & ms1 & mat1 & Hc & HS1 & HE1 & HI1). subst W1 c1.
apply (SRr_bind tfibsegs W _ POST_F DPOST (B_phase E1 ms1 mat1 HS1 HE1 HI1)).
intros W2 c2 _ HP. unfold POST_F in HP. destruct HP as (HW & E2 & ms2 & mat2 & Hc & HE2 & HI2 & [HS2 | [HS2 MT]]); subst W2 c2.
- exact (found_exit E2 ms2 mat2 HS2 HE2 HI2).
- exact (ins_phase E2 ms2 mat2 Htr1 HS2 HE2 HI2 MT).
Qed.
Theorem dep_spec_ok : (1 <= length tr)%nat -> SRr tfibsegs W (mkCfg msD0 md) DPOST.
Proof. intros Htr1. rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)). apply dep_main. exact Htr1. Qed.
Definition SS_E0 : sstate := mkSS A_StackDepotPut (sr_set DREGS0 11%bv (SLit 0)) [R_DS] None (mkFacts [(2%nat, mkAF (kHighMemBeg + DEP_STK) kHighMemEnd 4)] [] []).
Lemma SEED_E : length tr = 0%nat -> st_ok tfibsegs E0 SS_E0 (restrict Hd msD0).
Proof.
intros H0. zone. pose proof sp_range as SR. rewrite restrict_mkst_fx. unfold SS_E0, DREGS0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite R11, H0; reflexivity].
apply regs_ok_pin; [| intros X; discriminate | cbn [sv_denot]; rewrite R3, (ts_gp B HB); reflexivity].
apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate | cbn [sv_denot]; exact R4].
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. apply Forall_cons; [| apply Forall_nil]. exact (Forall_inv REG0_ok).
- cbn. split; exact I.
- split; [| split; exact I]. cbn [f_atoms atoms_ok]. split; [| exact I].
assert (E2' : ew E0 2 = Z_to_bv 64 sp) by (rewrite E2; symmetry; apply Z_to_bv_bv_unsigned).
apply (AFo E0 2%nat sp _ _ _ E2'); clear - SR Z1 Z3 Z4 Z2 Z22; [lia | numconst; lia | change (2 ^ 4) with 16; exact Z22 | lia].
Qed.
Lemma dep_empty : length tr = 0%nat -> SRr tfibsegs W (mkCfg msD0 md) DPOST.
Proof.
intros H0. rewrite (same_but_materialized_wvb md md (same_but_materialized_refl md)).
pose proof Hwx_tfa as HWX. zone. pose proof (SEED_E H0) as HS. pose proof envD_E0 as HE. fixu HE.
srr_runG tfibtbl_rtD_ok HS.
assert (FR : forall x : word, ~ (sp - DEP_STK <= bv_unsigned x < sp) -> ms_mem ms x = mem x).
{ intros x Hx. apply HF. intros (r & Hin & Hr). destruct Hin as [<-|[]]. unfold R_DS in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite V2 in Hr. apply Hx. clear - Hr. numconst. lia. }
assert (HI : INV (ms_mem ms)). { split; [| exact HG]. intros x Hx. apply FR. intros Hs. apply Hx. unfold WIN. left. exact Hs. }
assert (VF : forall a (n : nat) v, val_mem tfibsegs m0 a n v -> a + Z.of_nat n <= 0x5fb000 -> 0 <= a -> val_mem tfibsegs (mrestrict Hd (ms_mem ms)) a n v).
{ intros a n v Hv Hhi Hlo. eapply (val_mem_frame Hd mem); [| exact Hv]. intros k Hk. apply FR. rewrite unsigned_lit_small by (clear - Hk Hhi Hlo; lia).
clear - Hk Hhi Hlo Z1 Z3. numconst. lia. }
pose proof cells_val as (V1 & _ & V3 & _). pose proof tab_val as VT.
destruct (exit_regs E0 _ ms HS HE ltac:(vm_compute; reflexivity)) as [RP R1].
eapply (SRr_ret_at tfibsegs tfibtbl_rtD tfibtbl_rtD_ok HWX W); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_collapse. split; [reflexivity|].
exists 0, (ms_regs ms), (ms_mem ms), mat'.
split. { rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split; [left; reflexivity|]. split; [exact RP|].
destruct (exit_frame _ HI) as [F1 F2]. split; [exact F1|]. split; [exact F2|].
split; [| exact (const_kept _ HI)].
cbn [depot_after Z.eqb]. apply (depot_mem_ok_found _ HI).
- apply (VF _ 4%nat _ VT); unfold S2; clear - Z19; numconst; lia.
- apply (VF _ 4%nat _ V1); unfold NUQ; clear; numconst; lia.
- apply (VF _ 8%nat _ V3); clear; numconst; lia.
Qed.
End s.
Theorem tfib_depot_ok : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> tfib_depot_spec B.
Proof.
intros B HB HDH W ly S regs mem md buf tr. cbn zeta.
intros LY IMG WF Htr HCONST HDEP R10 R11 R3 R4 Hra Hwords Hbuf8 Hbuflo Hbufhi Hbuf_sp Hsp16 Hsplo Hsphi P_stk.
destruct HDEP as (HCELLS & (heads & links & D1 & D2 & D3) & HVIS).
destruct (Nat.eq_dec (length tr) 0) as [HL|HL].
- eapply (dep_empty B HB HDH W ly S regs mem md buf tr heads links); eassumption.
- eapply (dep_spec_ok B HB HDH W ly S regs mem md buf tr heads links); try eassumption. lia.
Qed.
End g.
