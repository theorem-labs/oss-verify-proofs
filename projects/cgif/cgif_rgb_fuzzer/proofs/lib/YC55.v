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
YG00 YG0a YG01 YG0h YG0u YG0d YC04 YC06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z YC59 YC54.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g YM00 YM07 YM05 YM04 YM01 YM02 YM06 YI0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Abbreviation D := fmt_double.
Section f.
Context {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)) (k1 : Z).
Variables (ly2 : alayout) (S2 : astate) (W2 : world trasegs) (memM : word -> option byte).
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
Hypothesis HpaM : arr8 trasegs (mrestrict (w_H W2) memM) palp pal.
Hypothesis HfaM : arr32 trasegs (mrestrict (w_H W2) memM) frp fr.
Hypothesis Hbud : sp0 - STK <= spZ regs0 - TNTN_STK. Hypothesis Hsptop : spZ regs0 <= sp0. Hypothesis Hal16 : spZ regs0 mod 16 = 0.
Hypothesis HNW : forall blc i lyq, In (res, NODE_SIZE) blc -> 0 <= i < 56 -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i).
Local Abbreviation ntn_inv := (YC54.ntn_inv B STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res).
Local Abbreviation nt_kept_win := (YC54.nt_kept_win regs0 frp).
Local Abbreviation u64_rangeN8 := (YC54.u64_rangeN8 regs0 frp).
Lemma ntn_palv : forall j, (j < length pal)%nat -> 0 <= nth j pal 0 < 256.
Proof. intros j Hj. exact (proj2 (HpaM j Hj)). Qed.
Lemma ntn_frv : forall j, (j < length fr)%nat -> 0 <= nth j fr 0 < 2 ^ 32.
Proof. intros j Hj. exact (proj2 (HfaM j Hj)). Qed.
Lemma ntn_env : forall fy regs mem md, ntn_inv fy regs mem md ->
alloc_ceiling + 16384 <= spc /\ spZ regs0 <= 2 ^ 47 /\ spc mod 16 = 0 /\
4096 <= pb /\ pb + req_size pm <= alloc_ceiling /\ 4096 <= fb /\ fb + req_size fm <= alloc_ceiling /\
4096 <= res /\ res + 56 <= alloc_ceiling /\ res mod 16 = 0 /\ pm <= req_size pm /\ fm <= req_size fm /\
140735332483072 <= alloc_ceiling <= 140737479966720.
Proof. intros fy regs mem md HI. exact (YC54.ntn_env B LAWS STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res pb pm fb fm HinP HinF HfF0 HinN Hbud Hsptop Hal16 fy regs mem md HI). Qed.
Lemma ntn_blk_kept : forall fy regs mem md, ntn_inv fy regs mem md ->
forall b m, In (b, m) (ablocks B ly2 S2) -> (b, m) <> (res, NODE_SIZE) -> rg_blk_kept (w_H W2) (w_H W2) memM mem b (req_size m).
Proof. intros fy regs mem md HI. exact (YC54.ntn_blk_kept B LAWS STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res HinN Hbud fy regs mem md HI). Qed.
Lemma ntn_arrs : forall fy regs mem md, ntn_inv fy regs mem md ->
arr8 trasegs (mrestrict (w_H W2) mem) palp pal /\ arr32 trasegs (mrestrict (w_H W2) mem) frp fr.
Proof.
intros fy regs mem md HI.
exact (YC54.ntn_arrs B LAWS STK sp0 FP ly S W0 mem0 md0 own k1 ly2 S2 W2 memM regs0 palp frp nln imax cidx res pal fr pb pm fb fm HinP HpP0 HpP1 HinF HfF0 HfF1 HinN HnPF HnFF HpaM HfaM Hbud fy regs mem md HI).
Qed.
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
Variables (mn0 mn1 mn2 : Z).
Let l0 := node_list pal fr imin imax 0. Let l1 := node_list pal fr imin imax 1. Let l2 := node_list pal fr imin imax 2.
Hypothesis Rmn0 : 0 <= mn0 < 2 ^ 64. Hypothesis Rmn1 : 0 <= mn1 < 2 ^ 64. Hypothesis Rmn2 : 0 <= mn2 < 2 ^ 64.
Hypothesis Qmn0 : is_quot mn0 (wdot l0) (wsum l0). Hypothesis Qmn1 : is_quot mn1 (wdot l1) (wsum l1). Hypothesis Qmn2 : is_quot mn2 (wdot l2) (wsum l2).
Hypothesis Lmn0 : wdot l0 <= 255 * wsum l0. Hypothesis Lmn1 : wdot l1 <= 255 * wsum l1. Hypothesis Lmn2 : wdot l2 <= 255 * wsum l2.
Definition TN_L2END : Z := 0x85334.
Definition TN_VA : Z := 0x8508c.
Definition l2_alias : list (sv * sv) :=
[ (SAlu ALU_ADD (SAlu ALU_SLL (SOff 20 0) (SLit 2)) (SOff 21 0), SOff 41 0);
(SAlu ALU_ADD (SOff 14 0) (SOff 22 0), SOff 40 0); (SAlu ALU_ADD (SOff 14 1) (SOff 22 0), SOff 40 1); (SAlu ALU_ADD (SOff 14 2) (SOff 22 0), SOff 40 2) ].
Definition l2_mem : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 192 8 56
[YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 32 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 40 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 48 (CVal 8 (SOff 35 0))];
YQ0b.mkRegion (Some 9%nat) 0 NODE_SIZE 0 0
[YQ0b.mkChunk 16 (CVal 8 (SOff 42 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 43 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 44 0))];
YQ0b.mkRegion (Some 40%nat) 0 3 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 36 0)); YQ0b.mkChunk 1 (CVal 1 (SOff 37 0)); YQ0b.mkChunk 2 (CVal 1 (SOff 38 0))];
YQ0b.mkRegion (Some 41%nat) 0 4 0 0 [YQ0b.mkChunk 0 (CVal 4 (SOff 39 0))] ].
Definition l2_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 4096 140737479966720 4); (20%nat, mkAF 0 (2^30) 0); (14%nat, mkAF 0 (3 * 2^30) 0);
(19%nat, mkAF 0 (2^30) 0);
(21%nat, mkAF 4096 140737479966720 2); (22%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF SB SB 0);
(36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 (2^32 - 1) 0);
(40%nat, mkAF 4096 140737479966720 0); (41%nat, mkAF 4096 140737479966720 2) ] [] l2_alias.
Definition l2_regs := sr_set (sr_set sr_atoms 12%bv (SOff 9 16)) 13%bv (SOff 9 16).
Definition ss_L2x : sstate := mkSS TN_L2 l2_regs l2_mem None l2_facts.
Definition l2_SH : list shent := [ mkSHE 9 0 NODE_SIZE; mkSHE 40 0 3; mkSHE 41 0 4 ].
Definition L2_inv (fy : FPState) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (i : Z) : Prop :=
ntn_inv fy regs mem md /\
getr regs 20 = w64 i /\ getr regs 14 = w64 (3 * i) /\ getr regs 12 = w64 (res + 16) /\ getr regs 13 = w64 (res + 16) /\
val_mem trasegs (mrestrict (w_H W2) mem) (res + 16) 8 mn0 /\ val_mem trasegs (mrestrict (w_H W2) mem) (res + 24) 8 mn1 /\
val_mem trasegs (mrestrict (w_H W2) mem) (res + 32) 8 mn2 /\
exists xs xv0 xv1 xv2,
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 8) 8 xs /\ val_mem trasegs (mrestrict (w_H W2) mem) (spc + 16) 8 xs /\
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 24) 8 xs /\
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 32) 8 xv0 /\ val_mem trasegs (mrestrict (w_H W2) mem) (spc + 40) 8 xv1 /\
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 48) 8 xv2 /\
0 <= xs < 2 ^ 64 /\ 0 <= xv0 < 2 ^ 64 /\ 0 <= xv1 < 2 ^ 64 /\ 0 <= xv2 < 2 ^ 64 /\
is_intd xs (wsum (nlp pal fr imin i 0)) /\
vacc xv0 (i - imin) (neq_meanb (wsum l0) (wdot l0) (nlp pal fr imin i 0)) /\
vacc xv1 (i - imin) (neq_meanb (wsum l1) (wdot l1) (nlp pal fr imin i 1)) /\
vacc xv2 (i - imin) (neq_meanb (wsum l2) (wdot l2) (nlp pal fr imin i 2)).
Definition l2_vals (i xs xv0 xv1 xv2 : Z) : list Z :=
[xs; xv0; xv1; xv2; getz pal (3 * i); getz pal (3 * i + 1); getz pal (3 * i + 2); getz fr i; palp + 3 * i; frp + 4 * i; mn0; mn1; mn2].
Lemma L2_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (i xs xv0 xv1 xv2 : Z),
imin <= i <= imax -> ntn_inv fy regs mem md ->
getr regs 20 = w64 i -> getr regs 14 = w64 (3 * i) -> getr regs 12 = w64 (res + 16) -> getr regs 13 = w64 (res + 16) ->
val_mem trasegs (mrestrict (w_H W2) mem) (res + 16) 8 mn0 -> val_mem trasegs (mrestrict (w_H W2) mem) (res + 24) 8 mn1 ->
val_mem trasegs (mrestrict (w_H W2) mem) (res + 32) 8 mn2 ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 8) 8 xs -> val_mem trasegs (mrestrict (w_H W2) mem) (spc + 16) 8 xs ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 24) 8 xs ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 32) 8 xv0 -> val_mem trasegs (mrestrict (w_H W2) mem) (spc + 40) 8 xv1 ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 48) 8 xv2 ->
0 <= xs < 2 ^ 64 -> 0 <= xv0 < 2 ^ 64 -> 0 <= xv1 < 2 ^ 64 -> 0 <= xv2 < 2 ^ 64 ->
let vals := l2_vals i xs xv0 xv1 xv2 in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST TN_L2 l2_regs (sfr_atoms 64) l2_mem None l2_facts)
(restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_L2) mem (seg_rom trasegs))) /\
sh_ok trasegs l1_Bx l2_SH E (mrestrict (w_H W2) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
(forall n j v, nth_error vals j = Some v -> n = (32 + j)%nat -> ew E n = Z_to_bv 64 v) /\
bv_unsigned (ew E 2) = spc /\ bv_unsigned (ew E 9) = res.
Proof.
intros fy regs mem md i xs xv0 xv1 xv2 Hi HI G20 G14 G12 G13 M16 M24 M32 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 vals E0 E.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
destruct (ntn_arrs fy regs mem md HI) as [Hpa Hfa].
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK & KEPT & PRES).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (U2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Qsp Qsp47 C1; lia).
assert (U9 : bv_unsigned (ew E0 9) = res) by (rewrite (HE0 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Qr0 Qr1 C1; lia).
assert (U20 : bv_unsigned (ew E0 20) = i) by (rewrite (HE0 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U14 : bv_unsigned (ew E0 14) = 3 * i) by (rewrite (HE0 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U19 : bv_unsigned (ew E0 19) = imax) by (rewrite (HE0 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (Rfrp : 4096 <= frp /\ frp + 4 * zlen fr <= 140737479966720) by (clear - HfF0 HfF1 Qfb0 Qfb1 Qfm C1; lia).
assert (Rpalp : 4096 <= palp /\ palp + zlen pal <= 140737479966720) by (clear - HpP0 HpP1 Qpb0 Qpb1 Qpm C1; lia).
assert (U21 : bv_unsigned (ew E0 21) = frp) by (rewrite (HE0 21%nat 21%bv eq_refl), G21; apply unsigned_lit_small; clear - Rfrp Hlenf Hi Hii; lia).
assert (U22 : bv_unsigned (ew E0 22) = palp) by (rewrite (HE0 22%nat 22%bv eq_refl), G22; apply unsigned_lit_small; clear - Rpalp Hlenp Hi Hii; lia).
assert (E23 : ew E0 23 = w64 SB) by (rewrite (HE0 23%nat 23%bv eq_refl); exact G23).
pose proof (Hpb (3 * i) ltac:(clear - Hi Hii Hlenp; lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(clear - Hi Hii Hlenp; lia)) as P1.
pose proof (Hpb (3 * i + 2) ltac:(clear - Hi Hii Hlenp; lia)) as P2. pose proof (Hfw i ltac:(clear - Hi Hii Hlenf; lia)) as Fi.
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (HA 0%nat xs eq_refl Rs) as A32. pose proof (HA 1%nat xv0 eq_refl R0) as A33. pose proof (HA 2%nat xv1 eq_refl R1) as A34.
pose proof (HA 3%nat xv2 eq_refl R2) as A35.
pose proof (HA 4%nat _ eq_refl ltac:(clear - P0; lia)) as A36. pose proof (HA 5%nat _ eq_refl ltac:(clear - P1; lia)) as A37.
pose proof (HA 6%nat _ eq_refl ltac:(clear - P2; lia)) as A38. pose proof (HA 7%nat _ eq_refl ltac:(clear - Fi; lia)) as A39.
pose proof (HA 8%nat _ eq_refl ltac:(clear - Rpalp Hi Hii Hlenp; lia)) as A40. pose proof (HA 9%nat _ eq_refl ltac:(clear - Rfrp Hi Hii Hlenf; lia)) as A41.
pose proof (HA 10%nat mn0 eq_refl Rmn0) as A42. pose proof (HA 11%nat mn1 eq_refl Rmn1) as A43. pose proof (HA 12%nat mn2 eq_refl Rmn2) as A44.
cbn [Nat.add] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44.
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
pose proof (sep_blocks trasegs _ LAWS ly2 S2 _ _ _ pb pm fb fm HAR HinP HinF HPF) as Hdpf.
pose proof (sep_blocks trasegs _ LAWS ly2 S2 _ _ _ res NODE_SIZE pb pm HAR HinN HinP HnPF) as Hdnp.
pose proof (sep_blocks trasegs _ LAWS ly2 S2 _ _ _ res NODE_SIZE fb fm HAR HinN HinF HnFF) as Hdnf.
unfold zdisjoint in Hdpf, Hdnp, Hdnf. cbn [fst snd] in Hdpf, Hdnp, Hdnf. change (req_size NODE_SIZE) with 56 in Hdnp, Hdnf.
assert (HS0 : @st_ok trasegs fy E0 ss_L2x (restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_L2) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_L2x, l2_regs. apply (entry_st_ok_full trasegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite G12. cbn [sv_denot]. fold E0. rewrite U9. reflexivity.
+ rewrite G13. cbn [sv_denot]. fold E0. rewrite U9. reflexivity.
- vm_compute. reflexivity.
- unfold l2_mem. repeat apply Forall_cons; try apply Forall_nil.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U2.
split; [clear - Qsp C1; lia|]. split; [clear - Qsp47; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply Hpres. clear - Ho Hbud Hsptop WS. lia. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ spc 8 8 _ xs); [exact (DN _ _ A32) | zside | zside | exact V8].
* apply (chunk_ok_val trasegs E0 _ spc 16 8 _ xs); [exact (DN _ _ A32) | zside | zside | exact V16].
* apply (chunk_ok_val trasegs E0 _ spc 24 8 _ xs); [exact (DN _ _ A32) | zside | zside | exact V24].
* apply (chunk_ok_val trasegs E0 _ spc 32 8 _ xv0); [exact (DN _ _ A33) | zside | zside | exact V32].
* apply (chunk_ok_val trasegs E0 _ spc 40 8 _ xv1); [exact (DN _ _ A34) | zside | zside | exact V40].
* apply (chunk_ok_val trasegs E0 _ spc 48 8 _ xv2); [exact (DN _ _ A35) | zside | zside | exact V48].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U9.
unfold NODE_SIZE. split; [clear - Qr0; lia|]. split; [clear - Qr1 C1; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ res 16 8 _ mn0); [exact (DN _ _ A42) | zside | zside | exact M16].
* apply (chunk_ok_val trasegs E0 _ res 24 8 _ mn1); [exact (DN _ _ A43) | zside | zside | exact M24].
* apply (chunk_ok_val trasegs E0 _ res 32 8 _ mn2); [exact (DN _ _ A44) | zside | zside | exact M32].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite A40.
split; [clear - Rpalp Hi Hii; lia|]. split; [clear - Rpalp Hi Hii Hlenp; lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ (palp + 3 * i) 0 1 _ (getz pal (3 * i))); [exact (DN _ _ A36) | zside | zside |].
apply (val_mem_byte trasegs); [rewrite Z.add_0_r; exact (proj1 (arr8_getz trasegs _ palp pal (3 * i) Hpa ltac:(clear - Hi Hii Hlenp; lia))) | exact P0].
* apply (chunk_ok_val trasegs E0 _ (palp + 3 * i) 1 1 _ (getz pal (3 * i + 1))); [exact (DN _ _ A37) | zside | zside |].
apply (val_mem_byte trasegs); [replace (palp + 3 * i + 1) with (palp + (3 * i + 1)) by lia; exact (proj1 (arr8_getz trasegs _ palp pal (3 * i + 1) Hpa ltac:(clear - Hi Hii Hlenp; lia))) | exact P1].
* apply (chunk_ok_val trasegs E0 _ (palp + 3 * i) 2 1 _ (getz pal (3 * i + 2))); [exact (DN _ _ A38) | zside | zside |].
apply (val_mem_byte trasegs); [replace (palp + 3 * i + 2) with (palp + (3 * i + 2)) by lia; exact (proj1 (arr8_getz trasegs _ palp pal (3 * i + 2) Hpa ltac:(clear - Hi Hii Hlenp; lia))) | exact P2].
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite A41.
split; [clear - Rfrp Hi Hii; lia|]. split; [clear - Rfrp Hi Hii Hlenf; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E0 _ (frp + 4 * i) 0 4 _ (getz fr i)); [exact (DN _ _ A39) | zside | zside |].
rewrite Z.add_0_r. exact (proj1 (arr32_getz trasegs _ frp fr i Hfa ltac:(clear - Hi Hii Hlenf; lia))).
- apply pairwise_disjoint_of_extents. unfold l2_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E0. rewrite U2, U9, A40, A41. unfold NODE_SIZE.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Rpalp Rfrp Hi Hii Hlenp Hlenf Qsp Qr0 Qr1 C1 HpP0 HpP1 HfF0 HfF1 Qpb1 Qfb1 Qpm Qfm Hdpf Hdnp Hdnf. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [l2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0.
rewrite U2, U9, U20, U14, U19, U21, U22, E23, A36, A37, A38, A39, A40, A41. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hf4 : (frp + 4 * i) mod 4 = 0) by (replace (frp + 4 * i) with (frp + i * 4) by lia; rewrite Z.mod_add by lia; exact Hfr4).
clear - Qsp Qsp47 Qal Qr0 Qr1 Qr16 C1 Hi Hii Himax Rfrp Rpalp Hlenp Hlenf P0 P1 P2 Fi Hf4 Hfr4. unfold SB.
repeat match goal with |- _ /\ _ => split end; lia.
+ cbn [l2_facts f_alias alias_ok l2_alias]. fold E0.
repeat match goal with |- _ /\ _ => split end; try exact I.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, U20, U21, A41, !Z.add_0_r.
rewrite (zcanon_id frp), (zcanon_id i) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia). change (Z.land (zcanon 2) 63) with 2.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite (zcanon_id (i * 4)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U14, U22, A40, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (3 * i)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U14, U22, A40, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (3 * i + 1)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U14, U22, A40, !Z.add_0_r.
rewrite (zcanon_id palp), (zcanon_id (3 * i + 2)) by (unfold M64; clear - Rfrp Rpalp Hi Hii Himax Hlenf Hlenp; lia).
f_equal. lia. }
assert (SHOK0 : sh_ok trasegs l1_Bx l2_SH E0 (mrestrict (w_H W2) mem)).
{ unfold sh_ok, l2_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trasegs B LAWS ly2 S2 W2 mem md E0 l1_Bx 9 res NODE_SIZE 0 NODE_SIZE HAR HinN).
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9.
+ lia.
+ change (req_size NODE_SIZE) with 56. unfold NODE_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W2) mem E0 l1_Bx 40 (palp + 3 * i) 3 (palp + 3 * i) 0 3).
+ apply (range_addressable_of_block trasegs B LAWS ly2 S2 W2 mem md pb pm _ _ HAR HinP); clear - Hi Hii Hlenp HpP0 HpP1 Qpm; lia.
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A40.
+ lia.
+ lia.
+ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ pb pm HAR HinP) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ pb pm HAR HinP) as Himg.
revert Hx Hia Himg Hi Hii Hlenp HpP0 HpP1 Qpm Qpb0 Qpb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
- apply (shent_ok_of_range trasegs (w_H W2) mem E0 l1_Bx 41 (frp + 4 * i) 4 (frp + 4 * i) 0 4).
+ apply (range_addressable_of_block trasegs B LAWS ly2 S2 W2 mem md fb fm _ _ HAR HinF); clear - Hi Hii Hlenf HfF0 HfF1 Qfm; lia.
+ unfold U, l1_Bx. cbn [sv_denot]. rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact A41.
+ lia.
+ lia.
+ intros x Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ fb fm HAR HinF) as (_ & _ & _ & Hia & _).
pose proof (blk_off_img _ _ _ _ _ _ fb fm HAR HinF) as Himg.
revert Hx Hia Himg Hi Hii Hlenf HfF0 HfF1 Qfm Qfb0 Qfb1 C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_L2x _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [exact (sh_ok_agree trasegs l1_Bx l2_SH 64 E0 E _ (env_agree_ew_fregs E0 64 _) ltac:(vm_compute; reflexivity) SHOK0)|].
split; [exact HE|].
split; [|split; rewrite HEE by lia; assumption].
intros n j v Hj ->. rewrite HEE; [apply HV; exact Hj|].
assert (Hl : (j < length vals)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). cbn in Hl. lia.
Qed.
Definition L2_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Local Ltac nt_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem In] in Hin; unfold l2_mem in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Definition l2_out_mem : smem :=
Eval vm_compute in (ss_mem (sh_ss (fst (sym_run_toN_tokF trasegs tratbl_lib 96 l1_Bx nt_Bspan l2_SH 400 TN_L2END
(mkSST TN_L2 l2_regs (sfr_atoms 64) l2_mem None l2_facts))))).
Lemma L2_read : forall (fz : FPState) E ss ms (i xs xv0 xv1 xv2 : Z),
@st_ok trasegs fz E ss (restrict (w_H W2) ms) -> ss_mem ss = l2_out_mem ->
sr_get (ss_regs ss) 20 = SOff 20 1 -> sr_get (ss_regs ss) 14 = SOff 14 3 ->
imin <= i <= imax ->
bv_unsigned (ew E 2) = spc ->
bv_unsigned (ew E 32) = xs -> bv_unsigned (ew E 33) = xv0 -> bv_unsigned (ew E 34) = xv1 -> bv_unsigned (ew E 35) = xv2 ->
bv_unsigned (ew E 36) = getz pal (3 * i) -> bv_unsigned (ew E 37) = getz pal (3 * i + 1) -> bv_unsigned (ew E 38) = getz pal (3 * i + 2) ->
bv_unsigned (ew E 39) = getz fr i ->
bv_unsigned (ew E 42) = mn0 -> bv_unsigned (ew E 43) = mn1 -> bv_unsigned (ew E 44) = mn2 ->
bv_unsigned (ew E 14) = 3 * i -> bv_unsigned (ew E 20) = i ->
is_intd xs (wsum (nlp pal fr imin i 0)) ->
vacc xv0 (i - imin) (neq_meanb (wsum l0) (wdot l0) (nlp pal fr imin i 0)) ->
vacc xv1 (i - imin) (neq_meanb (wsum l1) (wdot l1) (nlp pal fr imin i 1)) ->
vacc xv2 (i - imin) (neq_meanb (wsum l2) (wdot l2) (nlp pal fr imin i 2)) ->
exists xs' xv0' xv1' xv2',
val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 8) 8 xs' /\ val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 16) 8 xs' /\
val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 24) 8 xs' /\
val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 32) 8 xv0' /\ val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 40) 8 xv1' /\
val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + 48) 8 xv2' /\
0 <= xs' < 2 ^ 64 /\ 0 <= xv0' < 2 ^ 64 /\ 0 <= xv1' < 2 ^ 64 /\ 0 <= xv2' < 2 ^ 64 /\
is_intd xs' (wsum (nlp pal fr imin (i + 1) 0)) /\
vacc xv0' (i + 1 - imin) (neq_meanb (wsum l0) (wdot l0) (nlp pal fr imin (i + 1) 0)) /\
vacc xv1' (i + 1 - imin) (neq_meanb (wsum l1) (wdot l1) (nlp pal fr imin (i + 1) 1)) /\
vacc xv2' (i + 1 - imin) (neq_meanb (wsum l2) (wdot l2) (nlp pal fr imin (i + 1) 2)) /\
getr (ms_regs ms) 20 = w64 (i + 1) /\ getr (ms_regs ms) 14 = w64 (3 * (i + 1)).
Proof.
intros fz E ss ms i xs xv0 xv1 xv2 HS Hm Q20 Q14 Hi HU2 A32 A33 A34 A35 A36 A37 A38 A39 A42 A43 A44 U14 U20 Is I0 I1 I2.
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
pose proof (Hpb (3 * i) ltac:(clear - Hi Hii Hlenp; lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(clear - Hi Hii Hlenp; lia)) as P1.
pose proof (Hpb (3 * i + 2) ltac:(clear - Hi Hii Hlenp; lia)) as P2. pose proof (Hfw i ltac:(clear - Hi Hii Hlenf; lia)) as Fi.
assert (HNM : RGB_NMAX = 10000) by reflexivity.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (i + 1) 0 ltac:(lia)) as Ws.
rewrite (nlp_snoc pal fr imin i 0) in Ws by lia. rewrite wsum_snoc in Ws.
pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum i 0 ltac:(lia)) as Ws0.
assert (Hf : 1 <= getz fr i <= RGB_NMAX) by (pose proof (Hfr1 i ltac:(lia)); lia).
rewrite (nlp_snoc pal fr imin i 0), (nlp_snoc pal fr imin i 1), (nlp_snoc pal fr imin i 2) by lia.
rewrite !wsum_snoc, !neq_meanb_snoc. rewrite !(Z.add_0_r (3 * i)).
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
pose proof (st_ok_region_nth E ss _ 0%nat _ HS ltac:(rewrite Hm; reflexivity)) as HR0. cbn [ms_mem restrict] in HR0.
assert (CV : forall off e, In (YQ0b.mkChunk off (CVal 8 e)) (YQ0b.r_chunks (nth 0 l2_out_mem (YQ0b.mkRegion None 0 0 0 0 []))) ->
val_mem trasegs (mrestrict (w_H W2) (ms_mem ms)) (spc + off) 8 (bv_unsigned (sv_denot E e))).
{ intros off e Hin.
lazymatch type of HR0 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
apply (slot_of_region E _ spc cs lo hi wlo whi off e _ HR0 HU2 Hin); [symmetry; apply Z_to_bv_bv_unsigned | apply u64_rangeN8] end. }
set (es := SF2 (FP2_ari F_ADD FMT_D RNE) (SOff 32 0) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 39 0))).
set (ev := fun (ep em ea : nat) =>
let t1 := SF2 (FP2_ari F_SUB FMT_D RNE) (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff ep 0)) (SOff em 0) in
SF3 (FP3_fma F_MADD FMT_D RNE) (SF2 (FP2_ari F_MUL FMT_D RNE) t1 (SF1 (FP1_cvt FC_D FC_WU RNE) (SOff 39 0))) t1 (SOff ea 0)).
exists (bv_unsigned (sv_denot E es)), (bv_unsigned (sv_denot E (ev 36%nat 42%nat 33%nat))),
(bv_unsigned (sv_denot E (ev 37%nat 43%nat 34%nat))), (bv_unsigned (sv_denot E (ev 38%nat 44%nat 35%nat))).
split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|].
split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|]. split; [apply CV; cbn; tauto|].
split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|]. split; [apply u64_rangeN8|].
split; [subst es; apply val_fadd; [rewrite (Dat 32%nat xs A32); exact Is | apply val_cvt_wu; [apply Dat; exact A39 | lia] | rewrite HNM in Ws; lia]|].
assert (VS : forall (ep em ea : nat) (p mean acc : Z) (l : list (Z * Z)) (pos : bool),
bv_unsigned (ew E ep) = p -> 0 <= p < 256 -> bv_unsigned (ew E em) = mean -> bv_unsigned (ew E ea) = acc ->
is_quot mean (wdot l) (wsum l) -> wdot l <= 255 * wsum l ->
vacc acc (i - imin) pos ->
vacc (bv_unsigned (sv_denot E (ev ep em ea))) (i + 1 - imin) (pos || negb (p * wsum l =? wdot l))%bool).
{ intros ep em ea p mean acc l pos Hp Hpr Hmean Hacc Hq Hle Hv.
unfold ev. rewrite val_vstep. cbv zeta. rewrite (Dat em mean Hmean), (Dat ea acc Hacc).
replace (i + 1 - imin) with (i - imin + 1) by lia.
refine (proj1 (variance_step _ p mean (wdot l) (wsum l) _ (getz fr i) acc (i - imin) pos _ _ Hq Hle _ _ Hv _ _));
[apply val_cvt_wu; [apply Dat; exact Hp | lia] | lia | apply val_cvt_wu; [apply Dat; exact A39 | lia] | lia | lia | lia]. }
split; [apply (VS 36%nat 42%nat 33%nat _ mn0 xv0 l0); assumption || lia|].
split; [apply (VS 37%nat 43%nat 34%nat _ mn1 xv1 l1); assumption || lia|].
split; [apply (VS 38%nat 44%nat 35%nat _ mn2 xv2 l2); assumption || lia|].
split.
- rewrite (st_ok_restrict_reg trasegs (w_H W2) E ss ms (20%bv : bv 5) HS), Q20. cbn [sv_denot]. rewrite U20. reflexivity.
- rewrite (st_ok_restrict_reg trasegs (w_H W2) E ss ms (14%bv : bv 5) HS), Q14. cbn [sv_denot]. rewrite U14. unfold w64. f_equal. lia.
Qed.
Definition L2_post (regs : bvmap 5 word) (mem : word -> option byte) (pc j : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md',
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 pc) mem' (seg_rom trasegs)) md' /\
L2_inv fy' regs' mem' md' j /\
(forall r : bv 5, In r L2_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 8 <= a < spc + 56) -> aview trasegs (w_H W2) mem' a = aview trasegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a).
Lemma L2_step : forall (fy : FPState) (regs : bvmap 5 word) mem md (i : Z),
imin <= i <= imax -> L2_inv fy regs mem md i ->
SRr trasegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_L2) mem (seg_rom trasegs)) md)
(L2_post regs mem (if i <? imax then TN_L2 else TN_VA) (i + 1)).
Proof.
intros fy regs mem md i Hi (HI & G20 & G14 & G12 & G13 & M16 & M24 & M32 & xs & xv0 & xv1 & xv2 & V8 & V16 & V24 & V32 & V40 & V48 &
Rs & R0 & R1 & R2 & Is & I0 & I1 & I2).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
destruct (L2_seed fy regs mem md i xs xv0 xv1 xv2 Hi HI G20 G14 G12 G13 M16 M24 M32 V8 V16 V24 V32 V40 V48 Rs R0 R1 R2) as (HS & SHOK & HE & HV & HU2 & HU9).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, HV, HU2, HU9.
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK & KEPT & PRES).
assert (WS : TNTN_STK = 16576) by reflexivity.
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK nt_Bspan TN_L2END.
{ cbn [ss_mem]. unfold l2_mem. eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite HU2; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
pose proof (pal_byte pal ntn_palv) as Hpb. pose proof (fr_word fr ntn_frv) as Hfw.
pose proof (Hpb (3 * i) ltac:(clear - Hi Hii Hlenp; lia)) as P0. pose proof (Hpb (3 * i + 1) ltac:(clear - Hi Hii Hlenp; lia)) as P1.
pose proof (Hpb (3 * i + 2) ltac:(clear - Hi Hii Hlenp; lia)) as P2. pose proof (Hfw i ltac:(clear - Hi Hii Hlenf; lia)) as Fi.
assert (HA : forall n j v, nth_error (l2_vals i xs xv0 xv1 xv2) j = Some v -> n = (32 + j)%nat -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v).
{ intros n j v Hj Hn Hv. rewrite (HV n j v Hj Hn). apply unsigned_lit_small. exact Hv. }
pose proof (HA 32%nat 0%nat xs eq_refl eq_refl Rs) as A32. pose proof (HA 33%nat 1%nat xv0 eq_refl eq_refl R0) as A33.
pose proof (HA 34%nat 2%nat xv1 eq_refl eq_refl R1) as A34. pose proof (HA 35%nat 3%nat xv2 eq_refl eq_refl R2) as A35.
pose proof (HA 36%nat 4%nat _ eq_refl eq_refl ltac:(clear - P0; lia)) as A36. pose proof (HA 37%nat 5%nat _ eq_refl eq_refl ltac:(clear - P1; lia)) as A37.
pose proof (HA 38%nat 6%nat _ eq_refl eq_refl ltac:(clear - P2; lia)) as A38. pose proof (HA 39%nat 7%nat _ eq_refl eq_refl ltac:(clear - Fi; lia)) as A39.
pose proof (HA 42%nat 10%nat mn0 eq_refl eq_refl Rmn0) as A42. pose proof (HA 43%nat 11%nat mn1 eq_refl eq_refl Rmn1) as A43.
pose proof (HA 44%nat 12%nat mn2 eq_refl eq_refl Rmn2) as A44.
assert (U20 : bv_unsigned (ew E 20) = i) by (rewrite (HE 20%nat 20%bv eq_refl), G20; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U14 : bv_unsigned (ew E 14) = 3 * i) by (rewrite (HE 14%nat 14%bv eq_refl), G14; apply unsigned_lit_small; clear - Hi Hii Himax; lia).
assert (U19 : bv_unsigned (ew E 19) = imax) by (rewrite (HE 19%nat 19%bv eq_refl), G19; apply unsigned_lit_small; clear - Hii Himax; lia).
assert (KW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 8 <= a < spc + 56) -> aview trasegs (w_H W2) (ms_mem msA) a = aview trasegs (w_H W2) mem a).
{ apply (nt_kept_win _ _ _ _ _ spc 8 56 HFr1); [nt_rs_tac | exact HU2]. }
assert (FIN : forall (fz : FPState) E' ss' ms' md' pc', @st_ok trasegs fz E' ss' (restrict (w_H W2) ms') -> env_agree 96 E E' ->
ss_mem ss' = l2_out_mem -> ss_pc ss' = pc' -> ss_resv ss' = None ->
sr_get (ss_regs ss') 20 = SOff 20 1 -> sr_get (ss_regs ss') 14 = SOff 14 3 ->
sr_get (ss_regs ss') 12 = SOff 9 16 -> sr_get (ss_regs ss') 13 = SOff 9 16 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) L2_KEEP = true ->
frm_zero (@fp_csr fz) ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms') md' (k1 + 1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 8 <= a < spc + 56) -> aview trasegs (w_H W2) (ms_mem ms') a = aview trasegs (w_H W2) mem a) ->
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) (ms_mem ms') a) ->
SRr trasegs W2 (mkCfg ms' md') (L2_post regs mem pc' (i + 1))).
{ intros fz E' ss' ms' md' pc' HS' [EA ED] Hm' Hpc' Hrv' Q20 Q14 Q12 Q13 QK Hfz HJ' Hk' Hp'.
assert (HAE' : env_agree 32 (Ereg regs (map (Z_to_bv 64) (l2_vals i xs xv0 xv1 xv2) ++ [])) E').
{ split; [intros n Hn; rewrite EA by lia; subst E; rewrite ew_fregs_low by lia; reflexivity | rewrite ED; reflexivity]. }
pose proof (regs_kept_of_st_ok trasegs E' ss' _ regs _ L2_KEEP HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
destruct (L2_read fz E' ss' ms' i xs xv0 xv1 xv2 HS' Hm' Q20 Q14 Hi
ltac:(rewrite EA by lia; exact HU2) ltac:(rewrite EA by lia; exact A32) ltac:(rewrite EA by lia; exact A33)
ltac:(rewrite EA by lia; exact A34) ltac:(rewrite EA by lia; exact A35) ltac:(rewrite EA by lia; exact A36)
ltac:(rewrite EA by lia; exact A37) ltac:(rewrite EA by lia; exact A38) ltac:(rewrite EA by lia; exact A39)
ltac:(rewrite EA by lia; exact A42) ltac:(rewrite EA by lia; exact A43) ltac:(rewrite EA by lia; exact A44)
ltac:(rewrite EA by lia; exact U14) ltac:(rewrite EA by lia; exact U20) Is I0 I1 I2)
as (xs' & xv0' & xv1' & xv2' & W8 & W16 & W24 & W32 & W40 & W48 & Rs' & R0' & R1' & R2' & Is' & I0' & I1' & I2' & Hq20 & Hq14).
assert (Hq12 : getr (ms_regs ms') 12 = w64 (res + 16)).
{ rewrite (st_ok_restrict_reg trasegs (w_H W2) E' ss' ms' (12%bv : bv 5) HS'), Q12. cbn [sv_denot]. rewrite EA by lia. rewrite HU9. reflexivity. }
assert (Hq13 : getr (ms_regs ms') 13 = w64 (res + 16)).
{ rewrite (st_ok_restrict_reg trasegs (w_H W2) E' ss' ms' (13%bv : bv 5) HS'), Q13. cbn [sv_denot]. rewrite EA by lia. rewrite HU9. reflexivity. }
assert (KN : rg_blk_kept (w_H W2) (w_H W2) mem (ms_mem ms') res 56).
{ intros j Hj. apply Hk'; [clear - Hj Qr0 Qr1 C1; lia | clear - Hj Qr1 Qsp; lia]. }
rewrite (st_ok_restrict_mkst trasegs (w_H W2) E' ss' ms' HS' Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists fz, (ms_regs ms'), (ms_mem ms'), md'. split; [reflexivity|].
split.
{ split.
{ split; [exact HJ'|]. split; [exact Hfz|].
split; [rewrite (HKR (2%bv : bv 5) ltac:(cbv; tauto)); exact G2|]. split; [rewrite (HKR (8%bv : bv 5) ltac:(cbv; tauto)); exact G8|].
split; [rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9|]. split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|].
split; [rewrite (HKR (19%bv : bv 5) ltac:(cbv; tauto)); exact G19|]. split; [rewrite (HKR (21%bv : bv 5) ltac:(cbv; tauto)); exact G21|].
split; [rewrite (HKR (22%bv : bv 5) ltac:(cbv; tauto)); exact G22|]. split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
split; [intros rr Hrr; rewrite (HKR rr ltac:(clear - Hrr; cbv in Hrr |- *; tauto)); exact (GK rr Hrr)|].
split.
- intros a Ha Hns Hnn. rewrite (Hk' a Ha ltac:(clear - Hns WS; lia)). exact (KEPT a Ha Hns Hnn).
- intros a Ha. apply Hp'. apply PRES. exact Ha. }
split; [exact Hq20|]. split; [exact Hq14|]. split; [exact Hq12|]. split; [exact Hq13|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem (ms_mem ms') res 56 (res + 16) 8 mn0 M16 KN); [clear; lia | cbn; clear; lia]|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem (ms_mem ms') res 56 (res + 24) 8 mn1 M24 KN); [clear; lia | cbn; clear; lia]|].
split; [apply (rg_val_mem_blk_kept (w_H W2) (w_H W2) mem (ms_mem ms') res 56 (res + 32) 8 mn2 M32 KN); [clear; lia | cbn; clear; lia]|].
exists xs', xv0', xv1', xv2'. repeat (split; [assumption|]). exact I2'. }
split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (HAE96 : env_agree 96 E E) by (apply env_agree_refl).
aj_branchF tratbl_lib_ok HS.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
rewrite branch_geu_U, !U_SOff in Hc. rewrite !(proj1 HAEx) in Hc by lia. rewrite U19, U20, !zcanon_id in Hc by (unfold M64; clear - Hi Hii Himax; lia).
rewrite Z.add_0_r in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; clear - Hc; lia).
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (UspX : bv_unsigned (ew Ex 2) = spc) by (rewrite (proj1 HAEx) by lia; exact HU2) end.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK nt_Bspan TN_L2.
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite UspX; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ TN_L2 HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HJ | | ].
+ intros a Ha Hnw. rewrite (nt_kept_win _ _ _ _ _ spc 8 56 HFr ltac:(nt_rs_tac) UspX a Ha Hnw). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
lazymatch type of HS with st_okF _ ?Ex _ _ => assert (HAEx : env_agree 96 E Ex) by (env_agree_chain HAE96) end.
rewrite branch_geu_U, !U_SOff in Hc. rewrite !(proj1 HAEx) in Hc by lia. rewrite U19, U20, !zcanon_id in Hc by (unfold M64; clear - Hi Hii Himax; lia).
rewrite Z.add_0_r in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
replace (i <? imax) with false by (symmetry; apply Z.ltb_ge; clear - Hc; lia).
pose proof (st_okF_frm trasegs _ _ _ HS) as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS) as HSL. clear HS.
lazymatch type of HSL with st_ok _ ?Ex _ _ => assert (UspX : bv_unsigned (ew Ex 2) = spc) by (rewrite (proj1 HAEx) by lia; exact HU2) end.
aj_run_to_tok tratbl_lib_ok HSL HJ SHOK nt_Bspan TN_VA.
{ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite UspX; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HSL with st_ok _ ?Ey _ _ => assert (HAEy : env_agree 96 E Ey) by (env_agree_chain HAEx) end.
apply (FIN _ _ _ _ _ TN_VA HSL HAEy); [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | exact Hfrm' | exact HJ | | ].
+ intros a Ha Hnw. rewrite (nt_kept_win _ _ _ _ _ spc 8 56 HFr ltac:(nt_rs_tac) UspX a Ha Hnw). exact (KW1 a Ha Hnw).
+ intros a Ha. apply (apresent_grows _ _ _ _ HG). apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ntn_loop2 : forall (n : nat) (fy : FPState) (regs : bvmap 5 word) mem md (i : Z),
imin <= i <= imax -> Z.of_nat n = imax - i -> L2_inv fy regs mem md i ->
SRr trasegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_L2) mem (seg_rom trasegs)) md) (L2_post regs mem TN_VA (imax + 1)).
Proof.
induction n as [|n IH]; intros fy regs mem md i Hi Hn HI.
- assert (Hii' : i = imax) by lia. subst i.
eapply SRr_mono; [exact (L2_step fy regs mem md imax Hi HI)|].
cbv beta. intros W' c' _ HP. rewrite Z.ltb_irrefl in HP. exact HP.
- eapply SRr_bind; [exact (L2_step fy regs mem md i Hi HI)|].
cbv beta. intros W' c' _ (-> & fy' & regs' & mem' & md' & -> & HI' & Hk' & Hm' & Hp').
replace (i <? imax) with true by (symmetry; apply Z.ltb_lt; lia).
eapply SRr_mono; [exact (IH fy' regs' mem' md' (i + 1) ltac:(lia) ltac:(lia) HI')|].
cbv beta. intros W'' c'' _ (HW & fy'' & regs'' & mem'' & md'' & Hc & HI'' & Hk'' & Hm'' & Hp'').
split; [exact HW|]. exists fy'', regs'', mem'', md''. split; [exact Hc|]. split; [exact HI''|].
split; [intros r Hr; rewrite (Hk'' r Hr); apply Hk'; exact Hr|].
split; [intros a Ha Hna; rewrite (Hm'' a Ha Hna); apply Hm'; assumption|].
intros a Ha. apply Hp''. apply Hp'. exact Ha.
Qed.
End f.
