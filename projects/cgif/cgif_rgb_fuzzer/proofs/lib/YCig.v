(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCi1 YCib YCil.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g YM00 YM07 YM05 YM04 YM01 YM02 YM06 YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation D := fmt_double.
Definition TN_L1 : Z := 0x85614.
Definition TN_L1END : Z := 0x856d4.
Definition TN_MD : Z := 0x854a8.
Lemma denot_of_U' : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Section f.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k1 : Z).
Variables (ly2 : alayout) (S2 : astate) (W2 : world trbsegs) (memM : word -> option byte).
Variables (regs0 : bvmap 5 word) (palp frp nln imin imax cidx res : Z) (pal fr : list Z) (pb pm fb fm : Z).
Local Abbreviation spc := (spZ regs0 - 192).
Hypothesis Hii : 0 <= imin <= imax.
Hypothesis Himax : imax < 2 ^ 30.
Hypothesis Hlenp : 3 * (imax + 1) <= zlen pal.
Hypothesis Hlenf : imax + 1 <= zlen fr.
Hypothesis Hfr1 : forall i, imin <= i <= imax -> 1 <= getz fr i.
Hypothesis Hsum : wsum (node_list pal fr imin imax 0) <= RGB_NMAX.
Hypothesis HinP : In (pb, pm) (ablocks B ly2 S2). Hypothesis HpP0 : pb <= palp. Hypothesis HpP1 : palp + zlen pal <= pb + pm.
Hypothesis HinF : In (fb, fm) (ablocks B ly2 S2). Hypothesis HfF0 : fb <= frp. Hypothesis HfF1 : frp + 4 * zlen fr <= fb + fm.
Hypothesis Hfr4 : frp mod 4 = 0.
Hypothesis HinN : In (res, NODE_SIZE) (ablocks B ly2 S2).
Hypothesis HnPF : (res, NODE_SIZE) <> (pb, pm). Hypothesis HnFF : (res, NODE_SIZE) <> (fb, fm). Hypothesis HPF : (pb, pm) <> (fb, fm).
Hypothesis HpaM : arr8 trbsegs (mrestrict (w_H W2) memM) palp pal.
Hypothesis HfaM : arr32 trbsegs (mrestrict (w_H W2) memM) frp fr.
Hypothesis Hbud : sp0 - STK <= spZ regs0 - TNTN_STK. Hypothesis Hsptop : spZ regs0 <= sp0. Hypothesis Hal16 : spZ regs0 mod 16 = 0.
Hypothesis HNW : forall blc i lyq, In (res, NODE_SIZE) blc -> 0 <= i < 56 -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i).
Lemma ntn_palv : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256.
Proof. intros j Hj. exact (proj2 (HpaM j Hj)). Qed.
Lemma ntn_frv : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32.
Proof. intros j Hj. exact (proj2 (HfaM j Hj)). Qed.
Definition NT_KEPT : list (bv 5) := [3; 4; 27]%bv.
Definition ntn_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem md (k1 + 1) /\
frm_zero (@fp_csr fy) /\
getr regs 2 = w64 spc /\ getr regs 8 = w64 nln /\ getr regs 9 = w64 res /\ getr regs 18 = w64 cidx /\ getr regs 19 = w64 imax /\
getr regs 21 = w64 frp /\ getr regs 22 = w64 palp /\ getr regs 23 = w64 SB /\
getr regs 24 = w64 24 /\ getr regs 25 = w64 (spc + 72) /\ getr regs 26 = w64 (spc + 48) /\
(forall rr : bv 5, In rr NT_KEPT -> getr regs rr = getr regs0 rr) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - TNTN_STK <= a < spZ regs0) -> ~ (res <= a < res + NODE_SIZE) ->
aview trbsegs (w_H W2) mem a = aview trbsegs (w_H W2) memM a) /\
(forall a, apresent (w_H W2) memM a -> apresent (w_H W2) mem a).
Lemma ntn_env : forall fy regs mem md, ntn_inv fy regs mem md ->
alloc_ceiling + 16384 <= spc /\ spZ regs0 <= 2 ^ 47 /\ spc mod 16 = 0 /\
4096 <= pb /\ pb + req_size pm <= alloc_ceiling /\ 4096 <= fb /\ fb + req_size fm <= alloc_ceiling /\
4096 <= res /\ res + 56 <= alloc_ceiling /\ res mod 16 = 0 /\ pm <= req_size pm /\ fm <= req_size fm /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof.
intros fy regs mem md (HJ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hpm0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fm HAR HinF) as (_ & Hf4096 & Hfceil & _ & _ & _ & Hfm0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res NODE_SIZE HAR HinN) as (Hr16 & Hr4096 & Hrceil & _).
change (req_size NODE_SIZE) with 56 in Hrceil.
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrpm]. pose proof (req_size_pos fm ltac:(lia)) as [_ Hrfm].
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (Hal : spc mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
repeat split; try assumption; try lia.
Qed.
Lemma ntn_blk_kept : forall fy regs mem md, ntn_inv fy regs mem md ->
forall b m, In (b, m) (ablocks B ly2 S2) -> (b, m) <> (res, NODE_SIZE) -> rg_blk_kept (w_H W2) (w_H W2) memM mem b (req_size m).
Proof.
intros fy regs mem md HI b m Hb Hne i Hi. pose proof HI as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KEPT & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _).
pose proof (sep_blocks trbsegs _ LAWS ly2 S2 _ _ _ b m res NODE_SIZE HAR Hb HinN Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size NODE_SIZE) with 56 in Hd.
apply KEPT; [clear - Hi Hb4096 Hbceil C1; lia | clear - Hi Hbceil Hceil Hslo Hbud; lia | unfold NODE_SIZE; clear - Hi Hd; lia].
Qed.
Lemma ntn_arrs : forall fy regs mem md, ntn_inv fy regs mem md ->
arr8 trbsegs (mrestrict (w_H W2) mem) palp pal /\ arr32 trbsegs (mrestrict (w_H W2) mem) frp fr.
Proof.
intros fy regs mem md HI. pose proof HI as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & _ & _ & _ & Hpm0).
destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fm HAR HinF) as (_ & _ & _ & _ & _ & _ & Hfm0).
pose proof (req_size_pos pm ltac:(lia)) as [_ Hrpm]. pose proof (req_size_pos fm ltac:(lia)) as [_ Hrfm].
split.
- apply (arr8_frame trbsegs _ _ palp pal HpaM). intros a Ha. apply (mbyte_of_aview trbsegs).
replace a with (pb + (a - pb)) by lia.
apply (ntn_blk_kept fy regs mem md HI pb pm HinP ltac:(intros X; symmetry in X; exact (HnPF X))). clear - Ha HpP0 HpP1 Hrpm. lia.
- apply (arr32_frame trbsegs _ _ frp fr HfaM). intros a Ha. apply (mbyte_of_aview trbsegs).
replace a with (fb + (a - fb)) by lia.
apply (ntn_blk_kept fy regs mem md HI fb fm HinF ltac:(intros X; symmetry in X; exact (HnFF X))). clear - Ha HfF0 HfF1 Hrfm. lia.
Qed.
Definition l1_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 14 0) (SLit 2)) (SOff 21 0), SOff 43 0);
(SAlu ALU_ADD (SOff 11 0) (SOff 22 0), SOff 42 0); (SAlu ALU_ADD (SOff 11 1) (SOff 22 0), SOff 42 1); (SAlu ALU_ADD (SOff 11 2) (SOff 22 0), SOff 42 2) ].
Definition l1_conds : list acond :=
[ mkAC BC_GEU (SOff 42 0) (SOff 22 0); mkAC BC_GEU (SOff 42 1) (SOff 22 0); mkAC BC_GEU (SOff 42 2) (SOff 22 0) ].
Definition l1_regs : list sv := sr_set sr_atoms 13%bv (SLit 1).
Definition l1_mem : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 192 48 96
[YQ0b.mkChunk 48 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 56 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 64 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 72 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 80 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 88 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 42%nat) 0 3 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 38 0)); YQ0b.mkChunk 1 (CVal 1 (SOff 39 0)); YQ0b.mkChunk 2 (CVal 1 (SOff 40 0))];
YQ0b.mkRegion (Some 43%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 41 0))] ].
Definition l1_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (14%nat, mkAF 0 (2^30) 0); (11%nat, mkAF 0 (3 * 2^30) 0); (19%nat, mkAF 0 (2^30) 0);
(12%nat, mkAF 18446603336221196287 18446744073709547519 0);
(21%nat, mkAF 4096 140737479966720 2); (22%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF SB SB 0);
(38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 (2^32 - 1) 0);
(42%nat, mkAF 4096 140737479966720 0); (43%nat, mkAF 4096 140737479966720 2) ] l1_conds l1_alias.
Definition ss_L1x : sstate := mkSS TN_L1 l1_regs l1_mem None l1_facts.
Definition l1_Bx : sv := SOff 23 0.
Definition l1_SH : list shent := [ mkSHE 42 0 3; mkSHE 43 0 4 ].
Definition nt_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition L1_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ntn_inv fy regs mem md /\
getr regs 14 = w64 i /\ getr regs 11 = w64 (3 * i) /\ getr regs 12 = w64 (2 ^ 64 - 1 - frp) /\ getr regs 13 = w64 1 /\ getr regs 20 = w64 imin /\
exists xs0 xs1 xs2 xm0 xm1 xm2,
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 48) 8 xs0 /\ val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 56) 8 xs1 /\
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 64) 8 xs2 /\
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 72) 8 xm0 /\ val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 80) 8 xm1 /\
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 88) 8 xm2 /\
0 <= xs0 < 2 ^ 64 /\ 0 <= xs1 < 2 ^ 64 /\ 0 <= xs2 < 2 ^ 64 /\ 0 <= xm0 < 2 ^ 64 /\ 0 <= xm1 < 2 ^ 64 /\ 0 <= xm2 < 2 ^ 64 /\
is_intd xs0 (wsum (nlp pal fr imin i 0)) /\ is_intd xs1 (wsum (nlp pal fr imin i 1)) /\ is_intd xs2 (wsum (nlp pal fr imin i 2)) /\
is_intd xm0 (wdot (nlp pal fr imin i 0)) /\ is_intd xm1 (wdot (nlp pal fr imin i 1)) /\ is_intd xm2 (wdot (nlp pal fr imin i 2)).
Lemma u64_rangeN8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Definition l1_vals (i xs0 xs1 xs2 xm0 xm1 xm2 : Z) : list Z :=
[xs0; xs1; xs2; xm0; xm1; xm2; getz pal (3 * i); getz pal (3 * i + 1); getz pal (3 * i + 2); getz fr i; palp + 3 * i; frp + 4 * i].
Lemma L1_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (i xs0 xs1 xs2 xm0 xm1 xm2 : Z),
imin <= i <= imax -> ntn_inv fy regs mem md ->
getr regs 14 = w64 i -> getr regs 11 = w64 (3 * i) -> getr regs 12 = w64 (2 ^ 64 - 1 - frp) -> getr regs 13 = w64 1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 48) 8 xs0 -> val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 56) 8 xs1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 64) 8 xs2 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 72) 8 xm0 -> val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 80) 8 xm1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 88) 8 xm2 ->
0 <= xs0 < 2 ^ 64 -> 0 <= xs1 < 2 ^ 64 -> 0 <= xs2 < 2 ^ 64 -> 0 <= xm0 < 2 ^ 64 -> 0 <= xm1 < 2 ^ 64 -> 0 <= xm2 < 2 ^ 64 ->
let vals := l1_vals i xs0 xs1 xs2 xm0 xm1 xm2 in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST TN_L1 l1_regs (sfr_atoms 64) l1_mem None l1_facts)
(restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_L1) mem (seg_rom trbsegs))) /\
sh_ok trbsegs l1_Bx l1_SH E (mrestrict (w_H W2) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
(forall n j v, nth_error vals j = Some v -> n = (32 + j)%nat -> ew E n = Z_to_bv 64 v) /\
bv_unsigned (ew E 2) = spc.
Proof.
intros fy regs mem md i xs0 xs1 xs2 xm0 xm1 xm2 Hi HI G14 G11 G12 G13 V56 V64 V72 V80 V88 V96 Rs0 Rs1 Rs2 Rm0 Rm1 Rm2 vals E0 E.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
destruct (ntn_arrs fy regs mem md HI) as [Hpa Hfa].
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24 & G25 & G26 & GK & KEPT & PRES).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (U2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Qsp Qsp47 C1; lia).
assert (U14 : bv_unsigned (ew E0 14) = i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U11 : bv_unsigned (ew E0 11) = 3 * i) by (rewrite (HE0 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U19 : bv_unsigned (ew E0 19) = imax) by (rewrite (HE0 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (Rfrp : 4096 <= frp /\ frp + 4 * zlen fr <= 140737479966720) by (clear - HfF0 HfF1 Qfb0 Qfb1 Qfm C1; lia).
assert (Rpalp : 4096 <= palp /\ palp + zlen pal <= 140737479966720) by (clear - HpP0 HpP1 Qpb0 Qpb1 Qpm C1; lia).
assert (U21 : bv_unsigned (ew E0 21) = frp) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Rfrp Hlenf Hi Hii; lia).
assert (U22 : bv_unsigned (ew E0 22) = palp) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Rpalp Hlenp Hi Hii; lia).
assert (E23 : ew E0 23 = w64 SB) by (rewrite (HE0 23%nat 23%bv eq_refl); exact G23).
assert (U12 : bv_unsigned (ew E0 12) = 2 ^ 64 - 1 - frp) by (rewrite (HE0 12%nat 12%bv eq_refl), G12; apply unsigned_lit_small; clear - Rfrp Hlenf Hi Hii; lia).
pose proof (Hpb (3 * i) ltac:(clear - Hi Hii Hlenp; lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(clear - Hi Hii Hlenp; lia)) as P1.
pose proof (Hpb (3 * i + 2) ltac:(clear - Hi Hii Hlenp; lia)) as P2. pose proof (Hfw i ltac:(clear - Hi Hii Hlenf; lia)) as Fi.
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (HA 0%nat xs0 eq_refl Rs0) as A32. pose proof (HA 1%nat xs1 eq_refl Rs1) as A33. pose proof (HA 2%nat xs2 eq_refl Rs2) as A34.
pose proof (HA 3%nat xm0 eq_refl Rm0) as A35. pose proof (HA 4%nat xm1 eq_refl Rm1) as A36. pose proof (HA 5%nat xm2 eq_refl Rm2) as A37.
pose proof (HA 6%nat _ eq_refl ltac:(clear - P0; lia)) as A38. pose proof (HA 7%nat _ eq_refl ltac:(clear - P1; lia)) as A39.
pose proof (HA 8%nat _ eq_refl ltac:(clear - P2; lia)) as A40. pose proof (HA 9%nat _ eq_refl ltac:(clear - Fi; lia)) as A41.
pose proof (HA 10%nat _ eq_refl ltac:(clear - Rpalp Hi Hii Hlenp; lia)) as A42. pose proof (HA 11%nat _ eq_refl ltac:(clear - Rfrp Hi Hii Hlenf; lia)) as A43.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43.
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trbsegs fy E0 ss_L1x (restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_L1) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_L1x. apply (entry_st_ok_full trbsegs).
- unfold l1_regs. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite G13; reflexivity].
- vm_compute. reflexivity.
- unfold l1_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U2.
split; [clear - Qsp C1; lia|]. split; [clear - Qsp47; lia|]. split.
{ intros o Ho. apply (apresent_writable trbsegs). apply Hpres. clear - Ho Hbud Hsptop WS. lia. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ spc 48 8 _ xs0); [exact (DN _ _ A32) | zside | zside | exact V56].
* apply (chunk_ok_val trbsegs E0 _ spc 56 8 _ xs1); [exact (DN _ _ A33) | zside | zside | exact V64].
* apply (chunk_ok_val trbsegs E0 _ spc 64 8 _ xs2); [exact (DN _ _ A34) | zside | zside | exact V72].
* apply (chunk_ok_val trbsegs E0 _ spc 72 8 _ xm0); [exact (DN _ _ A35) | zside | zside | exact V80].
* apply (chunk_ok_val trbsegs E0 _ spc 80 8 _ xm1); [exact (DN _ _ A36) | zside | zside | exact V88].
* apply (chunk_ok_val trbsegs E0 _ spc 88 8 _ xm2); [exact (DN _ _ A37) | zside | zside | exact V96].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite A42.
split; [clear - Rpalp Hi Hii; lia|]. split; [clear - Rpalp Hi Hii Hlenp; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ (palp + 3 * i) 0 1 _ (getz pal (3 * i))); [exact (DN _ _ A38) | zside | zside |].
apply (val_mem_byte trbsegs); [rewrite Z.add_0_r; exact (proj1 (arr8_getz trbsegs _ palp pal (3 * i) Hpa ltac:(clear - Hi Hii Hlenp; lia))) | exact P0].
* apply (chunk_ok_val trbsegs E0 _ (palp + 3 * i) 1 1 _ (getz pal (3 * i + 1))); [exact (DN _ _ A39) | zside | zside |].
apply (val_mem_byte trbsegs); [replace (palp + 3 * i + 1) with (palp + (3 * i + 1)) by lia; exact (proj1 (arr8_getz trbsegs _ palp pal (3 * i + 1) Hpa ltac:(clear - Hi Hii Hlenp; lia))) | exact P1].
* apply (chunk_ok_val trbsegs E0 _ (palp + 3 * i) 2 1 _ (getz pal (3 * i + 2))); [exact (DN _ _ A40) | zside | zside |].
apply (val_mem_byte trbsegs); [replace (palp + 3 * i + 2) with (palp + (3 * i + 2)) by lia; exact (proj1 (arr8_getz trbsegs _ palp pal (3 * i + 2) Hpa ltac:(clear - Hi Hii Hlenp; lia))) | exact P2].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite A43.
split; [clear - Rfrp Hi Hii; lia|]. split; [clear - Rfrp Hi Hii Hlenf; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E0 _ (frp + 4 * i) 0 4 _ (getz fr i)); [exact (DN _ _ A41) | zside | zside |].
rewrite Z.add_0_r. exact (proj1 (arr32_getz trbsegs _ frp fr i Hfa ltac:(clear - Hi Hii Hlenf; lia))).
- apply pairwise_disjoint_of_extents. unfold l1_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E0. rewrite U2, A42, A43.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
pose proof (sep_blocks trbsegs _ LAWS ly2 S2 _ _ _ pb pm fb fm HAR HinP HinF HPF) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
clear - Rpalp Rfrp Hi Hii Hlenp Hlenf Qsp C1 HpP0 HpP1 HfF0 HfF1 Qpb1 Qfb1 Qpm Qfm Hd. repeat split; lia.
- split; [|split].
+ cbn [l1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
rewrite U2, U14, U11, U19, U12, U21, U22, E23, A38, A39, A40, A41, A42, A43. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hf4 : (frp + 4 * i) mod 4 = 0) by (replace (frp + 4 * i) with (frp + i * 4) by lia; rewrite Z.mod_add by lia; exact Hfr4).
clear - Qsp Qsp47 Qal C1 Hi Hii Himax Rfrp Rpalp Hlenp Hlenf P0 P1 P2 Fi Hf4 Hfr4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [l1_facts f_conds conds_ok l1_conds]. unfold acond_ok. cbn [ac_c ac_a ac_b]. fold E0.
repeat split; rewrite branch_geu_U, !U_SOff, A42, U22, ?Z.add_0_r, !zcanon_id by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia); apply Bool.negb_true_iff; apply Z.ltb_ge; lia.
+ cbn [l1_facts f_alias alias_ok l1_alias]. fold E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U14, U21, A43, !Z.add_0_r.
rewrite (zcanon_id frp), (zcanon_id i) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (i * 4)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U11, U22, A42, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (3 * i)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U11, U22, A42, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (3 * i + 1)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U11, U22, A42, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (3 * i + 2)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia. }
assert (SHOK0 : sh_ok trbsegs l1_Bx l1_SH E0 (mrestrict (w_H W2) mem)).
{ unfold sh_ok, l1_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range trbsegs (w_H W2) mem E0 l1_Bx 42 (palp + 3 * i) 3 (palp + 3 * i) 0 3).
+ apply (range_addressable_of_block trbsegs B LAWS ly2 S2 W2 mem md pb pm _ _ HAR HinP); clear - Hi Hii Hlenp HpP0 HpP1 Qpm; lia.
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A42.
+ lia.
+ lia.
+ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR HinP) as Himg.
revert Hx Hia Himg Hi Hii Hlenp HpP0 HpP1 Qpm Qpb0 Qpb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trbsegs (w_H W2) mem E0 l1_Bx 43 (frp + 4 * i) 4 (frp + 4 * i) 0 4).
+ apply (range_addressable_of_block trbsegs B LAWS ly2 S2 W2 mem md fb fm _ _ HAR HinF); clear - Hi Hii Hlenf HfF0 HfF1 Qfm; lia.
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A43.
+ lia.
+ lia.
+ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fm HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ fb fm HAR HinF) as Himg.
revert Hx Hia Himg Hi Hii Hlenf HfF0 HfF1 Qfm Qfb0 Qfb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_L1x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs l1_Bx l1_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [| rewrite HEE by lia; exact U2].
intros n j v Hj ->. rewrite HEE; [apply HV; exact Hj|].
assert (Hl : (j < length vals)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn in Hl. lia.
Qed.
Definition L1_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Local Ltac rreg_byA HS r v H :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v); [refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v) | ] end.
Local Ltac aj_branchF tblok HS :=
lazymatch type of HS with
| st_okF ?segs ?E ?ss ?ms =>
lazymatch type of tblok with
| table_ok _ ?tbl =>
let why := sym_whyF segs tbl ss in
lazymatch why with
| SR_branch ?c ?a ?b =>
apply (st_okF_branch segs E ss ms _ c a b HS); clear HS;
let Hc := fresh "Hc" in intros Hc HS
| _ => fail "aj_branchF: state is not stuck at a branch:" why
end
end
end.
Lemma nt_kept_win : forall E0 rs (H : word -> bool) (m m' : word -> option byte) sp lo hi,
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some 2%nat /\ lo <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= hi)) ->
bv_unsigned (ew E0 2) = sp ->
forall x, 0 <= x < 2 ^ 64 -> ~ (sp + lo <= x < sp + hi) -> aview trbsegs H m' x = aview trbsegs H m x.
Proof.
intros E0 rs H m m' sp lo hi HF Hrs Hsp x Hx Hnw. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). destruct (Hrs rr Hin) as [Hro | (Hb & Hlo & Hhi)]; [lia|].
rewrite Hb in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
Local Ltac nt_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold l1_mem in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Definition l1_out_mem : smem :=
Eval vm_compute in (ss_mem (sh_ss (fst (sym_run_toN_tokF trbsegs trbtbl_lib 96 l1_Bx nt_Bspan l1_SH 400 TN_L1END
(mkSST TN_L1 l1_regs (sfr_atoms 64) l1_mem None l1_facts))))).
Lemma L1_read : forall (fz : FPState) E ss ms (i xs0 xs1 xs2 xm0 xm1 xm2 : Z),
@st_ok trbsegs fz E ss (restrict (w_H W2) ms) -> ss_mem ss = l1_out_mem ->
sr_get (ss_regs ss) 14 = SOff 14 1 -> sr_get (ss_regs ss) 11 = SOff 11 3 ->
imin <= i <= imax ->
bv_unsigned (ew E 2) = spc ->
bv_unsigned (ew E 32) = xs0 -> bv_unsigned (ew E 33) = xs1 -> bv_unsigned (ew E 34) = xs2 ->
bv_unsigned (ew E 35) = xm0 -> bv_unsigned (ew E 36) = xm1 -> bv_unsigned (ew E 37) = xm2 ->
bv_unsigned (ew E 38) = getz pal (3 * i) -> bv_unsigned (ew E 39) = getz pal (3 * i + 1) -> bv_unsigned (ew E 40) = getz pal (3 * i + 2) ->
bv_unsigned (ew E 41) = getz fr i ->
bv_unsigned (ew E 14) = i -> bv_unsigned (ew E 11) = 3 * i ->
is_intd xs0 (wsum (nlp pal fr imin i 0)) -> is_intd xs1 (wsum (nlp pal fr imin i 1)) -> is_intd xs2 (wsum (nlp pal fr imin i 2)) ->
is_intd xm0 (wdot (nlp pal fr imin i 0)) -> is_intd xm1 (wdot (nlp pal fr imin i 1)) -> is_intd xm2 (wdot (nlp pal fr imin i 2)) ->
exists xs0' xs1' xs2' xm0' xm1' xm2',
val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 48) 8 xs0' /\ val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 56) 8 xs1' /\
val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 64) 8 xs2' /\
val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 72) 8 xm0' /\ val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 80) 8 xm1' /\
val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 88) 8 xm2' /\
0 <= xs0' < 2 ^ 64 /\ 0 <= xs1' < 2 ^ 64 /\ 0 <= xs2' < 2 ^ 64 /\ 0 <= xm0' < 2 ^ 64 /\ 0 <= xm1' < 2 ^ 64 /\ 0 <= xm2' < 2 ^ 64 /\
is_intd xs0' (wsum (nlp pal fr imin (i + 1) 0)) /\ is_intd xs1' (wsum (nlp pal fr imin (i + 1) 1)) /\ is_intd xs2' (wsum (nlp pal fr imin (i + 1) 2)) /\
is_intd xm0' (wdot (nlp pal fr imin (i + 1) 0)) /\ is_intd xm1' (wdot (nlp pal fr imin (i + 1) 1)) /\ is_intd xm2' (wdot (nlp pal fr imin (i + 1) 2)) /\
getr (ms_regs ms) 14 = w64 (i + 1) /\ getr (ms_regs ms) 11 = w64 (3 * (i + 1)).
Proof.
intros fz E ss ms i xs0 xs1 xs2 xm0 xm1 xm2 HS Hm Q14 Q11 Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 A40 A41 U14 U11 Is0 Is1 Is2 Im0 Im1 Im2.
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
pose proof (Hpb (3 * i) ltac:(clear - Hi Hii Hlenp; lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(clear - Hi Hii Hlenp; lia)) as P1.
pose proof (Hpb (3 * i + 2) ltac:(clear - Hi Hii Hlenp; lia)) as P2. pose proof (Hfw i ltac:(clear - Hi Hii Hlenf; lia)) as Fi.
assert (HNM : RGB_NMAX = 10000) by reflexivity.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (i + 1) 0 ltac:(lia)) as Ws.
pose proof (wdot_nlp_le pal fr imin imax Hii ntn_palv Hfr1 Hlenp Hsum i) as Wd.
rewrite (nlp_snoc pal fr imin i 0) in Ws by lia. rewrite wsum_snoc in Ws.
rewrite (nlp_snoc pal fr imin i 0), (nlp_snoc pal fr imin i 1), (nlp_snoc pal fr imin i 2) by lia.
rewrite !wsum_snoc, !wdot_snoc. rewrite !(Z.add_0_r (3 * i)).
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum i 0 ltac:(lia)) as Ws0.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum i 1 ltac:(lia)) as Ws1.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum i 2 ltac:(lia)) as Ws2.
assert (Hf : 0 <= getz fr i <= RGB_NMAX) by lia.
assert (HfP : forall p, 0 <= p < 256 -> getz fr i * p < 2 ^ 32) by (intros p Hp; rewrite HNM in Hf; nia).
assert (HdP : forall d w, 0 <= d <= 2 -> 0 <= w <= 255 * RGB_NMAX -> Z.abs (w + getz fr i * getz pal (3 * i + d)) <= 2 ^ 53).
{ intros d w Hd Hw. pose proof (Hpb (3 * i + d) ltac:(clear - Hi Hii Hlenp Hd; lia)). rewrite HNM in Hf, Hw. nia. }
set (es n := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff n 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 41 0))).
set (em n p := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff n 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SMd M_MUL (SOff 41 0) (SOff p 0)))).
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
pose proof (st_ok_region_nth E ss _ 0%nat _ HS ltac:(rewrite Hm; reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
assert (CV : forall off e, In (YQ0b.mkChunk off (CVal 8 e)) (YQ0b.r_chunks (nth 0 l1_out_mem (YQ0b.mkRegion None 0 0 0 0 []))) ->
val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (spc + off) 8 (bv_unsigned (sv_denot E e))).
{ intros off e Hin.
lazymatch type of HR0 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (slot_of_region E _ spc cs lo hi wlo whi off e _ HR0 HU2 Hin); [symmetry; apply Z_to_bv_bv_unsigned | apply u64_rangeN8] end. }
exists (bv_unsigned (sv_denot E (es 32%nat))), (bv_unsigned (sv_denot E (es 33%nat))), (bv_unsigned (sv_denot E (es 34%nat))),
(bv_unsigned (sv_denot E (em 35%nat 38%nat))), (bv_unsigned (sv_denot E (em 36%nat 39%nat))), (bv_unsigned (sv_denot E (em 37%nat 40%nat))).
split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|].
split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|].
split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|].
split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|].
split; [subst es; cbv beta; apply val_fadd; [rewrite (Dat 32%nat xs0 A32); exact Is0 | apply val_cvt_wu; [apply Dat; exact A41 | lia] | lia]|].
split; [subst es; cbv beta; apply val_fadd; [rewrite (Dat 33%nat xs1 A33); exact Is1 | apply val_cvt_wu; [apply Dat; exact A41 | lia] |
rewrite (wsum_nlp_dim pal fr imin i 1 0); lia]|].
split; [subst es; cbv beta; apply val_fadd; [rewrite (Dat 34%nat xs2 A34); exact Is2 | apply val_cvt_wu; [apply Dat; exact A41 | lia] |
rewrite (wsum_nlp_dim pal fr imin i 2 0); lia]|].
split; [subst em; cbv beta; apply val_fadd; [rewrite (Dat 35%nat xm0 A35); exact Im0 | apply val_cvt_mul; [apply Dat; exact A41 | apply Dat; exact A38 | lia | lia | apply HfP; lia] |
pose proof (HdP 0 _ ltac:(lia) (Wd 0 ltac:(lia) ltac:(lia))) as X; rewrite Z.add_0_r in X; exact X]|].
split; [subst em; cbv beta; apply val_fadd; [rewrite (Dat 36%nat xm1 A36); exact Im1 | apply val_cvt_mul; [apply Dat; exact A41 | apply Dat; exact A39 | lia | lia | apply HfP; lia] |
exact (HdP 1 _ ltac:(lia) (Wd 1 ltac:(lia) ltac:(lia)))]|].
split; [subst em; cbv beta; apply val_fadd; [rewrite (Dat 37%nat xm2 A37); exact Im2 | apply val_cvt_mul; [apply Dat; exact A41 | apply Dat; exact A40 | lia | lia | apply HfP; lia] |
exact (HdP 2 _ ltac:(lia) (Wd 2 ltac:(lia) ltac:(lia)))]|].
split.
- rewrite (st_ok_restrict_reg trbsegs (w_H W2) E ss ms (14%bv : bv 5) HS), Q14. cbn [sv_denot]. rewrite U14. reflexivity.
- rewrite (st_ok_restrict_reg trbsegs (w_H W2) E ss ms (11%bv : bv 5) HS), Q11. cbn [sv_denot]. rewrite U11. unfold w64. f_equal. lia.
Qed.
Lemma L1_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (i : Z),
imin <= i <= imax -> L1_inv fy regs mem md i ->
SRr trbsegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_L1) mem (seg_rom trbsegs)) md)
(fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 (if i <? imax then TN_L1 else TN_MD)) mem' (seg_rom trbsegs)) md' /\
L1_inv fy' regs' mem' md' (i + 1) /\
(forall r : bv 5, In r L1_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 48 <= a < spc + 96) -> aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a)).
Proof.
intros fy regs mem md i Hi (HI & G14 & G11 & G12 & G13 & G20 & xs0 & xs1 & xs2 & xm0 & xm1 & xm2 & V56 & V64 & V72 & V80 & V88 & V96 &
Rs0 & Rs1 & Rs2 & Rm0 & Rm1 & Rm2 & Is0 & Is1 & Is2 & Im0 & Im1 & Im2).
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
destruct (L1_seed fy regs mem md i xs0 xs1 xs2 xm0 xm1 xm2 Hi HI G14 G11 G12 G13 V56 V64 V72 V80 V88 V96 Rs0 Rs1 Rs2 Rm0 Rm1 Rm2) as (HS & SHOK & HE & HV & HU2).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HV, HU2.
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24 & G25 & G26 & GK & KEPT & PRES).
assert (WS : TNTN_STK = 16576) by reflexivity.
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK nt_Bspan TN_L1END.
{ cbn [ss_mem]. unfold l1_mem. eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite HU2; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
pose proof (Hpb (3 * i) ltac:(clear - Hi Hii Hlenp; lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(clear - Hi Hii Hlenp; lia)) as P1.
pose proof (Hpb (3 * i + 2) ltac:(clear - Hi Hii Hlenp; lia)) as P2. pose proof (Hfw i ltac:(clear - Hi Hii Hlenf; lia)) as Fi.
assert (HA : forall n j v, nth_error (l1_vals i xs0 xs1 xs2 xm0 xm1 xm2) j = Some v -> n = (32 + j)%nat -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n j v Hj Hn Hv. rewrite (HV n j v Hj Hn). apply unsigned_lit_small. exact Hv. }
pose proof (HA 32%nat 0%nat xs0 eq_refl eq_refl Rs0) as A32. pose proof (HA 33%nat 1%nat xs1 eq_refl eq_refl Rs1) as A33.
pose proof (HA 34%nat 2%nat xs2 eq_refl eq_refl Rs2) as A34. pose proof (HA 35%nat 3%nat xm0 eq_refl eq_refl Rm0) as A35.
pose proof (HA 36%nat 4%nat xm1 eq_refl eq_refl Rm1) as A36. pose proof (HA 37%nat 5%nat xm2 eq_refl eq_refl Rm2) as A37.
pose proof (HA 38%nat 6%nat _ eq_refl eq_refl ltac:(clear - P0; lia)) as A38. pose proof (HA 39%nat 7%nat _ eq_refl eq_refl ltac:(clear - P1; lia)) as A39.
pose proof (HA 40%nat 8%nat _ eq_refl eq_refl ltac:(clear - P2; lia)) as A40. pose proof (HA 41%nat 9%nat _ eq_refl eq_refl ltac:(clear - Fi; lia)) as A41.
assert (U14 : bv_unsigned (ew E 14) = i) by (rewrite (HE 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U11 : bv_unsigned (ew E 11) = 3 * i) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U19 : bv_unsigned (ew E 19) = imax) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 48 <= a < spc + 96) -> aview trbsegs (w_H W2) (ms_mem msA) a = aview trbsegs (w_H W2) mem a).
{ apply (nt_kept_win _ _ _ _ _ spc 48 96 HFr1); [nt_rs_tac | exact HU2]. }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc', @st_ok trbsegs fz E' ss' (restrict (w_H W2) ms') -> env_agree 96 E E' ->
ss_mem ss' = l1_out_mem -> ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 14 = SOff 14 1 -> sr_get (ss_regs ss') 11 = SOff 11 3 -> sr_get (ss_regs ss') 13 = SLit 1 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) L1_KEEP = true ->
frm_zero (@fp_csr fz) ->
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms') md' (k1 + 1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 48 <= a < spc + 96) -> aview trbsegs (w_H W2) (ms_mem ms') a = aview trbsegs (w_H W2) mem a) ->
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) (ms_mem ms') a) ->
SRr trbsegs W2 (mkCfg ms' md')
(fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md'',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc') mem' (seg_rom trbsegs)) md'' /\
L1_inv fy' regs' mem' md'' (i + 1) /\
(forall r : bv 5, In r L1_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 48 <= a < spc + 96) -> aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a))).
{ intros fz E' ss' ms' md' pc' HS' [EA ED] Hm' Hpc' Hrv' Q14 Q11 Q13 QK Hfz HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) (l1_vals i xs0 xs1 xs2 xm0 xm1 xm2) ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trbsegs E' ss' _ regs _ L1_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
destruct (L1_read fz E' ss' ms' i xs0 xs1 xs2 xm0 xm1 xm2 HS' Hm' Q14 Q11 Hi
ltac:(rewrite EA by lia; exact HU2) ltac:(rewrite EA by lia; exact A32) ltac:(rewrite EA by lia; exact A33)
ltac:(rewrite EA by lia; exact A34) ltac:(rewrite EA by lia; exact A35) ltac:(rewrite EA by lia; exact A36)
ltac:(rewrite EA by lia; exact A37) ltac:(rewrite EA by lia; exact A38) ltac:(rewrite EA by lia; exact A39)
ltac:(rewrite EA by lia; exact A40) ltac:(rewrite EA by lia; exact A41) ltac:(rewrite EA by lia; exact U14)
ltac:(rewrite EA by lia; exact U11) Is0 Is1 Is2 Im0 Im1 Im2)
as (xs0' & xs1' & xs2' & xm0' & xm1' & xm2' & W56 & W64 & W72 & W80 & W88 & W96 & Rs0' & Rs1' & Rs2' & Rm0' & Rm1' & Rm2' &
Is0' & Is1' & Is2' & Im0' & Im1' & Im2' & Hq14 & Hq11).
rewrite (st_ok_restrict_mkst trbsegs (w_H W2) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [rewrite (HKR (2%bv : bv 5) ltac:(cbv; tauto)); exact G2|]. split; [rewrite (HKR (8%bv : bv 5) ltac:(cbv; tauto)); exact G8|].
split; [rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9|]. split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|].
split; [rewrite (HKR (19%bv : bv 5) ltac:(cbv; tauto)); exact G19|]. split; [rewrite (HKR (21%bv : bv 5) ltac:(cbv; tauto)); exact G21|].
split; [rewrite (HKR (22%bv : bv 5) ltac:(cbv; tauto)); exact G22|]. split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
split; [rewrite (HKR (24%bv : bv 5) ltac:(cbv; tauto)); exact G24|]. split; [rewrite (HKR (25%bv : bv 5) ltac:(cbv; tauto)); exact G25|].
split; [rewrite (HKR (26%bv : bv 5) ltac:(cbv; tauto)); exact G26|].
split; [intros rr Hrr; rewrite (HKR rr ltac:(clear - Hrr; cbv in Hrr |- *; tauto)); exact (GK rr Hrr)|].
split.
- intros a Ha Hns Hnn. rewrite (Hk' a Ha ltac:(clear - Hns WS; lia)). exact (KEPT a Ha Hns Hnn).
- intros a Ha. apply Hp'. apply PRES. exact Ha. }
split; [exact Hq14|]. split; [exact Hq11|].
split; [rewrite (HKR (12%bv : bv 5) ltac:(cbv; tauto)); exact G12|]. split; [rewrite (st_ok_restrict_reg trbsegs (w_H W2) E' ss' ms' (13%bv : bv 5) HS'), Q13; reflexivity|].
split; [rewrite (HKR (20%bv : bv 5) ltac:(cbv; tauto)); exact G20|].
exists xs0', xs1', xs2', xm0', xm1', xm2'. repeat (split; [assumption|]). exact Im2'. }
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_branchF trbtbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
rewrite branch_geu_U, !U_SOff in Hc. rewrite !(proj1 HAEx) in Hc by lia. rewrite U19, U14, !zcanon_id in Hc by (unfold M64; clear - Hi Hii Himax; lia).
rewrite Z.add_0_r in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; clear - Hc; lia).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (UspX : bv_unsigned (ew Ex 2) = spc) by (rewrite (proj1 HAEx) by lia; exact HU2) end.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK nt_Bspan TN_L1.
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite UspX; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ TN_L1 HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HJ | | ].
+ intros a Ha Hnw. rewrite (nt_kept_win _ _ _ _ _ spc 48 96 HFr ltac:(nt_rs_tac) UspX a Ha Hnw). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
rewrite branch_geu_U, !U_SOff in Hc. rewrite !(proj1 HAEx) in Hc by lia. rewrite U19, U14, !zcanon_id in Hc by (unfold M64; clear - Hi Hii Himax; lia).
rewrite Z.add_0_r in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
replace (i <? imax) with false by (symmetry; apply Z.ltb_ge; clear - Hc; lia).
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (UspX : bv_unsigned (ew Ex 2) = spc) by (rewrite (proj1 HAEx) by lia; exact HU2) end.
aj_run_to_tok trbtbl_lib_ok HSL HJ SHOK nt_Bspan TN_MD.
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite UspX; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ TN_MD HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HJ | | ].
+ intros a Ha Hnw. rewrite (nt_kept_win _ _ _ _ _ spc 48 96 HFr ltac:(nt_rs_tac) UspX a Ha Hnw). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Definition L1_post (regs : bvmap 5 word) (mem : word -> option byte) (pc j : Z) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trbsegs)) md' /\
L1_inv fy' regs' mem' md' j /\
(forall r : bv 5, In r L1_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 48 <= a < spc + 96) -> aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a).
Lemma ntn_loop1 : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (i : Z),
imin <= i <= imax -> Z.of_nat n = imax - i -> L1_inv fy regs mem md i ->
SRr trbsegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_L1) mem (seg_rom trbsegs)) md) (L1_post regs mem TN_MD (imax + 1)).
Proof.
induction n as [|n IH]; intros fy regs mem md i Hi Hn HI.
- assert (Hii' : i = imax) by lia. subst i.
eapply SRr_mono; [exact (L1_step fy regs mem md imax Hi HI)|].
cbv beta. intros W' c' _ (HW & fy' & regs' & mem' & md' & Hc & HI' & Hk' & Hm' & Hp'). rewrite Z.ltb_irrefl in Hc.
split; [exact HW|]. exists fy', regs', mem', md'. repeat (split; [assumption|]). exact Hp'.
- eapply SRr_bind; [exact (L1_step fy regs mem md i Hi HI)|].
cbv beta. intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hm' & Hp').
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; lia).
eapply SRr_mono; [exact (IH fy' regs' mem' md' (i + 1) ltac:(lia) ltac:(lia) HI')|].
cbv beta. intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc & HI'' & Hk'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc|]. split; [exact HI''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros a Ha Hna; rewrite (Hm'' a Ha Hna); apply Hm'; assumption|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
Definition TN_L2 : Z := 0x856fc.
Lemma nt_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. pose proof (Z.sub_lxor_2rlandn (2 ^ 64 - 1) x) as H.
assert (Z.land (Z.lnot (2 ^ 64 - 1)) x = 0).
{ replace (Z.lnot (2 ^ 64 - 1)) with (- (2 ^ 64)) by reflexivity.
apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_dec n 64).
- replace (- (2 ^ 64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r | lia |].
destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia | lia]. }
rewrite Z.lxor_comm. lia.
Qed.
Definition md_mem : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 192 0 0
[YQ0b.mkChunk 48 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 56 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 64 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 72 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 80 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 88 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 16 40 [] ].
Definition md_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 4096 140737479966720 4); (19%nat, mkAF 0 (2^30) 0); (20%nat, mkAF 0 (2^30) 0);
(22%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF SB SB 0); (38%nat, mkAF 18446603336221196287 18446744073709547519 0) ]
[ mkAC BC_GEU (SOff 19 0) (SOff 20 0) ] [ (SAlu ALU_XOR (SOff 9 16) (SLit (-1)), SOff 38 0) ].
Definition md_regs := sr_set (sr_set (sr_set sr_atoms 24%bv (SLit 24)) 25%bv (SOff 2 72)) 26%bv (SOff 2 48).
Definition ss_MDx : sstate := mkSS TN_MD md_regs md_mem None md_facts.
Definition md_SH : list shent := [ mkSHE 9 0 NODE_SIZE ].
Definition md_vals (xs0 xs1 xs2 xm0 xm1 xm2 : Z) : list Z := [xs0; xs1; xs2; xm0; xm1; xm2; 2 ^ 64 - 1 - (res + 16)].
Lemma MD_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (xs0 xs1 xs2 xm0 xm1 xm2 : Z),
ntn_inv fy regs mem md ->
getr regs 20 = w64 imin ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 48) 8 xs0 -> val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 56) 8 xs1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 64) 8 xs2 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 72) 8 xm0 -> val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 80) 8 xm1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 88) 8 xm2 ->
0 <= xs0 < 2 ^ 64 -> 0 <= xs1 < 2 ^ 64 -> 0 <= xs2 < 2 ^ 64 -> 0 <= xm0 < 2 ^ 64 -> 0 <= xm1 < 2 ^ 64 -> 0 <= xm2 < 2 ^ 64 ->
let vals := md_vals xs0 xs1 xs2 xm0 xm1 xm2 in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trbsegs E (mkSST TN_MD md_regs (sfr_atoms 64) md_mem None md_facts)
(restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_MD) mem (seg_rom trbsegs))) /\
sh_ok trbsegs l1_Bx md_SH E (mrestrict (w_H W2) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
(forall n j v, nth_error vals j = Some v -> n = (32 + j)%nat -> ew E n = Z_to_bv 64 v) /\
bv_unsigned (ew E 2) = spc /\ bv_unsigned (ew E 9) = res.
Proof.
intros fy regs mem md xs0 xs1 xs2 xm0 xm1 xm2 HI G20 V56 V64 V72 V80 V88 V96 Rs0 Rs1 Rs2 Rm0 Rm1 Rm2 vals E0 E.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24 & G25 & G26 & GK & KEPT & PRES).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res NODE_SIZE HAR HinN) as (_ & _ & _ & _ & Hnpres & _). change (req_size NODE_SIZE) with 56 in Hnpres.
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (U2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Qsp Qsp47 C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = res) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qr0 Qr1 C1; lia).
assert (U19 : bv_unsigned (ew E0 19) = imax) by (rewrite (HE0 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (U20 : bv_unsigned (ew E0 20) = imin) by (rewrite (HE0 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (E23 : ew E0 23 = w64 SB) by (rewrite (HE0 23%nat 23%bv eq_refl); exact G23).
assert (Rpalp : 4096 <= palp /\ palp + zlen pal <= 140737479966720) by (clear - HpP0 HpP1 Qpb0 Qpb1 Qpm C1; lia).
assert (U22 : bv_unsigned (ew E0 22) = palp) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Rpalp Hlenp Hii; lia).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (HA 0%nat xs0 eq_refl Rs0) as A32. pose proof (HA 1%nat xs1 eq_refl Rs1) as A33. pose proof (HA 2%nat xs2 eq_refl Rs2) as A34.
pose proof (HA 3%nat xm0 eq_refl Rm0) as A35. pose proof (HA 4%nat xm1 eq_refl Rm1) as A36. pose proof (HA 5%nat xm2 eq_refl Rm2) as A37.
pose proof (HA 6%nat _ eq_refl ltac:(clear - Qr0 Qr1 C1; lia)) as A38.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38.
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trbsegs fy E0 ss_MDx (restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_MD) mem (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_MDx, md_regs. apply (entry_st_ok_full trbsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite G24. reflexivity.
+ rewrite G25. cbn [sv_denot]. fold E0. rewrite U2. reflexivity.
+ rewrite G26. cbn [sv_denot]. fold E0. rewrite U2. reflexivity.
- vm_compute. reflexivity.
- unfold md_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U2.
split; [clear - Qsp C1; lia|]. split; [clear - Qsp47; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trbsegs E0 _ spc 48 8 _ xs0); [exact (DN _ _ A32) | zside | zside | exact V56].
* apply (chunk_ok_val trbsegs E0 _ spc 56 8 _ xs1); [exact (DN _ _ A33) | zside | zside | exact V64].
* apply (chunk_ok_val trbsegs E0 _ spc 64 8 _ xs2); [exact (DN _ _ A34) | zside | zside | exact V72].
* apply (chunk_ok_val trbsegs E0 _ spc 72 8 _ xm0); [exact (DN _ _ A35) | zside | zside | exact V80].
* apply (chunk_ok_val trbsegs E0 _ spc 80 8 _ xm1); [exact (DN _ _ A36) | zside | zside | exact V88].
* apply (chunk_ok_val trbsegs E0 _ spc 88 8 _ xm2); [exact (DN _ _ A37) | zside | zside | exact V96].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U9.
unfold NODE_SIZE. split; [clear - Qr0; lia|]. split; [clear - Qr1 C1; lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hnpres (res + o) ltac:(clear - Ho; lia))).
- apply pairwise_disjoint_of_extents. unfold md_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E0. rewrite U2, U9. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear - Qsp Qr1. repeat split; lia.
- split; [|split].
+ cbn [md_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
rewrite U2, U9, U19, U20, U22, E23, A38. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Qsp Qsp47 Qal Qr0 Qr1 Qr16 C1 Hii Himax Rpalp Hlenp. unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [md_facts f_conds conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b]. split; [|exact I]. fold E0.
rewrite branch_geu_U, !U_SOff, U19, U20, !Z.add_0_r, !zcanon_id by (unfold M64; clear - Hii Himax; lia).
apply Bool.negb_true_iff. apply Z.ltb_ge. clear - Hii. lia.
+ cbn [md_facts f_alias alias_ok]. split; [|exact I]. fold E0.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U9, A38, !Z.add_0_r.
rewrite (zcanon_id (res + 16)) by (unfold M64; clear - Qr0 Qr1 C1; lia). change (zcanon (-1)) with (2 ^ 64 - 1).
rewrite nt_lxor_ones64 by (clear - Qr0 Qr1 C1; lia). reflexivity. }
assert (SHOK0 : sh_ok trbsegs l1_Bx md_SH E0 (mrestrict (w_H W2) mem)).
{ unfold sh_ok, md_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem md E0 l1_Bx 9 res NODE_SIZE 0 NODE_SIZE HAR HinN).
- unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
- lia.
- change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia. }
split; [exact (st_ok_enterF trbsegs fy 64 E0 ss_MDx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trbsegs l1_Bx md_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [|split; rewrite HEE by lia; assumption].
intros n j v Hj ->. rewrite HEE; [apply HV; exact Hj|].
assert (Hl : (j < length vals)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn in Hl. lia.
Qed.
Definition MD_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 12; 18; 19; 20; 21; 22; 23; 27]%bv.
Definition MD_post (regs : bvmap 5 word) (mem : word -> option byte) : world trbsegs -> config -> Prop :=
fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 TN_L2) mem' (seg_rom trbsegs)) md' /\
ntn_inv fy' regs' mem' md' /\
getr regs' 14 = w64 (res + 16) /\ getr regs' 13 = w64 (res + 16) /\ getr regs' 15 = w64 (3 * imin) /\ getr regs' 16 = w64 1 /\
(forall r : bv 5, In r MD_KEEP -> getr regs' r = getr regs r) /\
(exists mn0 mn1 mn2,
val_mem trbsegs (mrestrict (w_H W2) mem') (res + 16) 8 mn0 /\ val_mem trbsegs (mrestrict (w_H W2) mem') (res + 24) 8 mn1 /\
val_mem trbsegs (mrestrict (w_H W2) mem') (res + 32) 8 mn2 /\
0 <= mn0 < 2 ^ 64 /\ 0 <= mn1 < 2 ^ 64 /\ 0 <= mn2 < 2 ^ 64 /\
is_quot mn0 (wdot (node_list pal fr imin imax 0)) (wsum (node_list pal fr imin imax 0)) /\
is_quot mn1 (wdot (node_list pal fr imin imax 1)) (wsum (node_list pal fr imin imax 1)) /\
is_quot mn2 (wdot (node_list pal fr imin imax 2)) (wsum (node_list pal fr imin imax 2)) /\
wdot (node_list pal fr imin imax 0) <= 255 * wsum (node_list pal fr imin imax 0) /\
wdot (node_list pal fr imin imax 1) <= 255 * wsum (node_list pal fr imin imax 1) /\
wdot (node_list pal fr imin imax 2) <= 255 * wsum (node_list pal fr imin imax 2)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (res + 16 <= a < res + 40) -> aview trbsegs (w_H W2) mem' a = aview trbsegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a).
Lemma ntn_meandiv : forall (fy : FPState) (regs : bvmap 5 word) mem md (xs0 xs1 xs2 xm0 xm1 xm2 : Z),
ntn_inv fy regs mem md ->
getr regs 20 = w64 imin ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 48) 8 xs0 -> val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 56) 8 xs1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 64) 8 xs2 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 72) 8 xm0 -> val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 80) 8 xm1 ->
val_mem trbsegs (mrestrict (w_H W2) mem) (spc + 88) 8 xm2 ->
0 <= xs0 < 2 ^ 64 -> 0 <= xs1 < 2 ^ 64 -> 0 <= xs2 < 2 ^ 64 -> 0 <= xm0 < 2 ^ 64 -> 0 <= xm1 < 2 ^ 64 -> 0 <= xm2 < 2 ^ 64 ->
is_intd xs0 (wsum (node_list pal fr imin imax 0)) -> is_intd xs1 (wsum (node_list pal fr imin imax 1)) -> is_intd xs2 (wsum (node_list pal fr imin imax 2)) ->
is_intd xm0 (wdot (node_list pal fr imin imax 0)) -> is_intd xm1 (wdot (node_list pal fr imin imax 1)) -> is_intd xm2 (wdot (node_list pal fr imin imax 2)) ->
SRr trbsegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_MD) mem (seg_rom trbsegs)) md) (MD_post regs mem).
Proof.
intros fy regs mem md xs0 xs1 xs2 xm0 xm1 xm2 HI G20 V56 V64 V72 V80 V88 V96 Rs0 Rs1 Rs2 Rm0 Rm1 Rm2 Is0 Is1 Is2 Im0 Im1 Im2.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
destruct (MD_seed fy regs mem md xs0 xs1 xs2 xm0 xm1 xm2 HI G20 V56 V64 V72 V80 V88 V96 Rs0 Rs1 Rs2 Rm0 Rm1 Rm2) as (HS & SHOK & HE & HV & HU2 & HU9).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HV, HU2, HU9.
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24 & G25 & G26 & GK & KEPT & PRES).
assert (HA : forall n j v, nth_error (md_vals xs0 xs1 xs2 xm0 xm1 xm2) j = Some v -> n = (32 + j)%nat -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n j v Hj Hn Hv. rewrite (HV n j v Hj Hn). apply unsigned_lit_small. exact Hv. }
pose proof (HA 32%nat 0%nat xs0 eq_refl eq_refl Rs0) as A32. pose proof (HA 33%nat 1%nat xs1 eq_refl eq_refl Rs1) as A33.
pose proof (HA 34%nat 2%nat xs2 eq_refl eq_refl Rs2) as A34. pose proof (HA 35%nat 3%nat xm0 eq_refl eq_refl Rm0) as A35.
pose proof (HA 36%nat 4%nat xm1 eq_refl eq_refl Rm1) as A36. pose proof (HA 37%nat 5%nat xm2 eq_refl eq_refl Rm2) as A37.
assert (U20 : bv_unsigned (ew E 20) = imin) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hii Himax; lia).
aj_run_to_tokF trbtbl_lib_ok HS HJ SHOK nt_Bspan TN_L2.
{ cbn [ss_mem]. unfold md_mem. apply awr_ok_cons_ro; [cbn; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact HU9 | | apply awr_ok_nil].
cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. replace a with (res + (a - res)) by lia. apply HNW; [exact HinN | clear - Ha; lia]. }
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL.
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) (md_vals xs0 xs1 xs2 xm0 xm1 xm2) ++ [])) E).
{ split; [intros n Hn; subst E; rewrite ew_fregs_low by lia; reflexivity | reflexivity]. }
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ MD_KEEP HSL HAE ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (res + 16 <= a < res + 40) -> aview trbsegs (w_H W2) (ms_mem ms) a = aview trbsegs (w_H W2) mem a).
{ intros a Ha Hnw. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [ss_mem] in Hin. unfold md_mem in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; [clear - Hr; lia|].
rewrite HU9 in Hr. clear - Hr Hnw. lia. }
rreg HSL (14%bv : bv 5) R14. rreg HSL (13%bv : bv 5) R13. rreg HSL (16%bv : bv 5) R16.
rreg HSL (24%bv : bv 5) R24. rreg HSL (25%bv : bv 5) R25. rreg HSL (26%bv : bv 5) R26.
rreg_byA HSL (15%bv : bv 5) (Z_to_bv 64 (3 * imin)) R15.
{ apply denot_of_U'. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SOff, U_SLit, U20, Z.add_0_r.
rewrite (zcanon_id imin), (zcanon_id 3) by (unfold M64; clear - Hii Himax; lia). rewrite zcanon_id by (unfold M64; clear - Hii Himax; lia). lia. }
pose proof (st_ok_region_nth _ _ _ 1%nat _ HSL ltac:(reflexivity)) as HR1. cbn [ms_mem restrict] in HR1.
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
assert (CV : forall off e, In (YQ0b.mkChunk off (CVal 8 e))
[YQ0b.mkChunk 32 (CVal 8 (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 37 0) (SOff 34 0)));
YQ0b.mkChunk 24 (CVal 8 (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 36 0) (SOff 33 0)));
YQ0b.mkChunk 16 (CVal 8 (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 35 0) (SOff 32 0)))] ->
val_mem trbsegs (mrestrict (w_H W2) (ms_mem ms)) (res + off) 8 (bv_unsigned (sv_denot E e))).
{ intros off e Hin.
lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
exact (field_of_region E _ 9 res cs lo hi wlo whi off 8%N e _ HR1 HU9 Hin (eq_sym (Z_to_bv_bv_unsigned 64 _)) (u64_rangeN8 _) ltac:(cbn; lia)) end. }
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
assert (TM : forall d xm xs, 0 <= d <= 2 -> is_intd xs (wsum (node_list pal fr imin imax d)) -> is_intd xm (wdot (node_list pal fr imin imax d)) ->
is_quot (fst (fp_div D RNE xm xs)) (wdot (node_list pal fr imin imax d)) (wsum (node_list pal fr imin imax d)) /\
wdot (node_list pal fr imin imax d) <= 255 * wsum (node_list pal fr imin imax d)).
{ intros d xm xs Hd Hxs Hxm. rewrite <- (nlp_full pal fr imin imax d) in *.
pose proof (nlp_node_ok pal fr imin imax Hii ntn_palv Hfr1 Hlenp (imax + 1) d ltac:(lia) Hd) as Hok.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (imax + 1) d ltac:(lia)) as Hws.
assert (Hne : nlp pal fr imin (imax + 1) d <> []).
{ unfold nlp, node_list. intros Hnil. apply (f_equal (@length _)) in Hnil. rewrite length_map, zseq_length in Hnil. cbn in Hnil. lia. }
assert (HNM : RGB_NMAX = 10000) by reflexivity. rewrite HNM in Hws.
destruct (tree_mean xm xs _ Hok Hne ltac:(clear - Hws; lia) Hxs Hxm) as (Hq & Hle & _). split; [exact Hq | exact Hle]. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W2) _ _ ms HSL eq_refl). cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W2) ms)), (ms_regs ms), (ms_mem ms). eexists. split; [reflexivity|].
split.
{ split; [exact HJ|]. split; [exact Hfrm'|].
split; [rewrite (HKR (2%bv : bv 5) ltac:(cbv; tauto)); exact G2|]. split; [rewrite (HKR (8%bv : bv 5) ltac:(cbv; tauto)); exact G8|].
split; [rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9|]. split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|].
split; [rewrite (HKR (19%bv : bv 5) ltac:(cbv; tauto)); exact G19|]. split; [rewrite (HKR (21%bv : bv 5) ltac:(cbv; tauto)); exact G21|].
split; [rewrite (HKR (22%bv : bv 5) ltac:(cbv; tauto)); exact G22|]. split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
split; [rewrite R24; reflexivity|]. split; [rewrite R25, HU2; reflexivity|]. split; [rewrite R26, HU2; reflexivity|].
split; [intros rr Hrr; rewrite (HKR rr ltac:(clear - Hrr; cbv in Hrr |- *; tauto)); exact (GK rr Hrr)|].
split.
- intros a Ha Hns Hnn. rewrite (KW a Ha ltac:(clear - Hnn; unfold NODE_SIZE in Hnn; lia)). exact (KEPT a Ha Hns Hnn).
- intros a Ha. apply (apresent_grows _ _ _ _ HG). apply PRES. exact Ha. }
split; [rewrite R14, HU9; reflexivity|]. split; [rewrite R13, HU9; reflexivity|]. split; [exact R15|]. split; [rewrite R16; reflexivity|].
split; [exact HKR|].
split.
{ exists (bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 35 0) (SOff 32 0)))),
(bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 36 0) (SOff 33 0)))),
(bv_unsigned (sv_denot E (SF2 (FP2_ari F_DIV FMT_D RNE) (SOff 37 0) (SOff 34 0)))).
split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|].
split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|].
rewrite !val_fdiv, (Dat 32%nat xs0 A32), (Dat 33%nat xs1 A33), (Dat 34%nat xs2 A34), (Dat 35%nat xm0 A35), (Dat 36%nat xm1 A36), (Dat 37%nat xm2 A37).
destruct (TM 0 xm0 xs0 ltac:(lia) Is0 Im0) as [Q0 L0]. destruct (TM 1 xm1 xs1 ltac:(lia) Is1 Im1) as [Q1 L1']. destruct (TM 2 xm2 xs2 ltac:(lia) Is2 Im2) as [Q2 L2'].
repeat (split; [assumption|]). exact L2'. }
split; [exact KW|]. intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
Qed.
End f.
