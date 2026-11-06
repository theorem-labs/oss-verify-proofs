(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Reals Lra.
From Flocq Require Import Core.Raux Core.Defs.
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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z YC59 YC54 YC55.
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
Let l0 := node_list pal fr imin imax 0. Let l1 := node_list pal fr imin imax 1. Let l2 := node_list pal fr imin imax 2.
Lemma splits_iff : forall d,
(exists a b, In a (node_list pal fr imin imax d) /\ In b (node_list pal fr imin imax d) /\ snd a <> snd b) <->
dim_splits pal imin imax d.
Proof.
intros d. split.
- intros (a & b & Ha & Hb & Hne). apply In_node_list in Ha as (i & Hi & ->). apply In_node_list in Hb as (j & Hj & ->).
cbn [snd] in Hne. exists i, j. auto.
- intros (i & j & Hi & Hj & Hne). exists (getz fr i, getz pal (3 * i + d)), (getz fr j, getz pal (3 * j + d)).
split; [apply In_node_list; exists i; auto|]. split; [apply In_node_list; exists j; auto|]. exact Hne.
Qed.
Lemma var_value : forall d xs xv, 0 <= d <= 2 ->
is_intd xs (wsum l0) ->
vacc xv (imax + 1 - imin) (neq_meanb (wsum (node_list pal fr imin imax d)) (wdot (node_list pal fr imin imax d)) (node_list pal fr imin imax d)) ->
exists v, dval (fst (fp_div D RNE xv xs)) v /\ (0 <= v)%R /\ ((0 < v)%R <-> dim_splits pal imin imax d).
Proof.
intros d xs xv Hd Hxs Hv. assert (HNM : RGB_NMAX = 10000) by reflexivity.
set (l := node_list pal fr imin imax d) in *.
assert (Hok : node_ok l) by (subst l; rewrite <- nlp_full; apply (nlp_node_ok pal fr imin imax Hii ntn_palv Hfr1 Hlenp); lia).
assert (Hlen : Z.of_nat (length l) = imax - imin + 1) by (subst l; apply node_list_length; lia).
assert (Hne : l <> []) by (intros Hnil; rewrite Hnil in Hlen; cbn in Hlen; lia).
assert (Hws : wsum l <= 2 ^ 32).
{ subst l. rewrite <- nlp_full. pose proof (wsum_nlp_le pal fr imin imax Hii Hfr1 Hsum (imax + 1) d ltac:(lia)). rewrite HNM in *. lia. }
assert (Hxs' : is_intd xs (wsum l)).
{ subst l l0. rewrite <- nlp_full, (wsum_nlp_dim pal fr imin (imax + 1) d 0), nlp_full. exact Hxs. }
replace (imax + 1 - imin) with (Z.of_nat (length l)) in Hv by lia.
destruct (variance_sign xv xs l Hok Hne Hws ltac:(lia) Hv Hxs') as (v & Hdv & Hv0 & Hiff).
exists v. split; [exact Hdv|]. split; [exact Hv0|]. rewrite Hiff. apply splits_iff.
Qed.
Lemma VA_pick : forall xs xv0 xv1 xv2 (b1 b2 b3 : bool),
is_intd xs (wsum l0) ->
vacc xv0 (imax + 1 - imin) (neq_meanb (wsum l0) (wdot l0) l0) ->
vacc xv1 (imax + 1 - imin) (neq_meanb (wsum l1) (wdot l1) l1) ->
vacc xv2 (imax + 1 - imin) (neq_meanb (wsum l2) (wdot l2) l2) ->
let w0 := fst (fp_div D RNE xv0 xs) in let w1 := fst (fp_div D RNE xv1 xs) in let w2 := fst (fp_div D RNE xv2 xs) in
fst (fp_lt D 0 w0) = b1 ->
fst (fp_lt D (if b1 then w0 else 0) w1) = b2 ->
fst (fp_lt D (if b2 then w1 else if b1 then w0 else 0) w2) = b3 ->
range_has_two pal imin imax -> dim_splits pal imin imax (if b3 then 2 else if b2 then 1 else 0).
Proof.
intros xs xv0 xv1 xv2 b1 b2 b3 Hxs V0 V1 V2 w0 w1 w2 C1 C2 C3 Hr2.
destruct (var_value 0 xs xv0 ltac:(lia) Hxs V0) as (v0 & D0 & P0 & I0).
destruct (var_value 1 xs xv1 ltac:(lia) Hxs V1) as (v1 & D1 & P1 & I1).
destruct (var_value 2 xs xv2 ltac:(lia) Hxs V2) as (v2 & D2 & P2 & I2).
fold w0 in D0. fold w1 in D1. fold w2 in D2.
assert (HP : forall v, (0 <= v)%R -> if Rlt_bool 0 v then (0 < v)%R else v = 0%R).
{ intros v Hv. destruct (Rlt_bool_spec 0 v); lra. }
pose proof (argmax_pick w0 w1 w2 v0 v1 v2 (Rlt_bool 0 v0) (Rlt_bool 0 v1) (Rlt_bool 0 v2) b1 b2 b3
D0 D1 D2 P0 P1 P2 (HP v0 P0) (HP v1 P1) (HP v2 P2) C1 C2 C3) as HA.
assert (Hex : Rlt_bool 0 v0 = true \/ Rlt_bool 0 v1 = true \/ Rlt_bool 0 v2 = true).
{ destruct (range_has_two_dim pal imin imax Hr2) as (d & Hd & Hsp).
assert (Hd3 : d = 0 \/ d = 1 \/ d = 2) by lia.
destruct Hd3 as [-> | [-> | ->]];
[ left; apply Rlt_bool_true; apply I0; exact Hsp
| right; left; apply Rlt_bool_true; apply I1; exact Hsp
| right; right; apply Rlt_bool_true; apply I2; exact Hsp ]. }
specialize (HA Hex).
destruct b3; [|destruct b2];
[ apply I2; destruct (Rlt_bool_spec 0 v2); [lra | discriminate HA]
| apply I1; destruct (Rlt_bool_spec 0 v1); [lra | discriminate HA]
| apply I0; destruct (Rlt_bool_spec 0 v0); [lra | discriminate HA] ].
Qed.
Definition TN_TAIL : Z := 0x850fc.
Definition va_mem : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 192 80 104
[YQ0b.mkChunk 8 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 32 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 40 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 48 (CVal 8 (SOff 35 0))] ].
Definition va_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
Definition ss_VAx : sstate := mkSS TN_VA sr_atoms va_mem None va_facts.
Definition va_SH : list shent := [].
Definition va_vals (xs xv0 xv1 xv2 : Z) : list Z := [xs; xv0; xv1; xv2].
Lemma VA_seed : forall (fy : FPState) (regs : bvmap 5 word) mem md (xs xv0 xv1 xv2 : Z),
ntn_inv fy regs mem md ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 8) 8 xs -> val_mem trasegs (mrestrict (w_H W2) mem) (spc + 16) 8 xs ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 24) 8 xs ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 32) 8 xv0 -> val_mem trasegs (mrestrict (w_H W2) mem) (spc + 40) 8 xv1 ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 48) 8 xv2 ->
0 <= xs < 2 ^ 64 -> 0 <= xv0 < 2 ^ 64 -> 0 <= xv1 < 2 ^ 64 -> 0 <= xv2 < 2 ^ 64 ->
let vals := va_vals xs xv0 xv1 xv2 in
let E0 := Ereg regs (map (Z_to_bv 64) vals ++ []) in
let E := ew_fregs E0 64 (@fp_regs fy) in
st_okF trasegs E (mkSST TN_VA sr_atoms (sfr_atoms 64) va_mem None va_facts)
(restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_VA) mem (seg_rom trasegs))) /\
sh_ok trasegs l1_Bx va_SH E (mrestrict (w_H W2) mem) /\
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) /\
bv_unsigned (ew E 32) = xs /\ bv_unsigned (ew E 33) = xv0 /\ bv_unsigned (ew E 34) = xv1 /\ bv_unsigned (ew E 35) = xv2 /\
bv_unsigned (ew E 2) = spc.
Proof.
intros fy regs mem md xs xv0 xv1 xv2 HI V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 vals E0 E.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK & KEPT & PRES).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (HE0 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E0 n = getr regs rr) by (intros; subst E0; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error vals j = Some v -> ew E0 (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E0; apply Ereg_vals; exact Hj).
assert (HEE : forall n, (n < 64)%nat -> ew E n = ew E0 n) by (intros n Hn; subst E; apply ew_fregs_low; exact Hn).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5. rewrite HEE by lia. apply HE0. exact Hn. }
assert (U2 : bv_unsigned (ew E0 2) = spc) by (rewrite (HE0 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; clear - Qsp Qsp47 C1; lia).
assert (HA : forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E0 (32 + j)) = v).
{ intros j v Hj Hv. rewrite (HV j v Hj). apply unsigned_lit_small. exact Hv. }
pose proof (HA 0%nat xs eq_refl Rs) as A32. pose proof (HA 1%nat xv0 eq_refl R0) as A33. pose proof (HA 2%nat xv1 eq_refl R1) as A34.
pose proof (HA 3%nat xv2 eq_refl R2) as A35.
cbn [Nat.add] in A32, A33, A34, A35.
assert (DN : forall n v, bv_unsigned (ew E0 n) = v -> sv_denot E0 (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : @st_ok trasegs fy E0 ss_VAx (restrict (w_H W2) (@mkst fy regs (Z_to_bv 64 TN_VA) mem (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_VAx. apply (entry_st_ok_full trasegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold va_mem. repeat apply Forall_cons; try apply Forall_nil.
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E0. rewrite U2.
split; [clear - Qsp C1; lia|]. split; [clear - Qsp47; lia|]. split.
{ intros o Ho. apply (apresent_writable trasegs). apply Hpres. clear - Ho Hbud Hsptop WS. lia. }
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val trasegs E0 _ spc 8 8 _ xs); [exact (DN _ _ A32) | zside | zside | exact V8].
* apply (chunk_ok_val trasegs E0 _ spc 16 8 _ xs); [exact (DN _ _ A32) | zside | zside | exact V16].
* apply (chunk_ok_val trasegs E0 _ spc 24 8 _ xs); [exact (DN _ _ A32) | zside | zside | exact V24].
* apply (chunk_ok_val trasegs E0 _ spc 32 8 _ xv0); [exact (DN _ _ A33) | zside | zside | exact V32].
* apply (chunk_ok_val trasegs E0 _ spc 40 8 _ xv1); [exact (DN _ _ A34) | zside | zside | exact V40].
* apply (chunk_ok_val trasegs E0 _ spc 48 8 _ xv2); [exact (DN _ _ A35) | zside | zside | exact V48].
- apply pairwise_disjoint_of_extents. unfold va_mem, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; exact I].
cbn [va_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E0. rewrite U2. change (2 ^ 4) with 16.
clear - Qsp Qsp47 Qal C1. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
split; [exact (st_ok_enterF trasegs fy 64 E0 ss_VAx _ HS0 ltac:(vm_compute; reflexivity) Hfrm)|].
split; [constructor|].
split; [exact HE|].
rewrite !HEE by lia. repeat (split; [assumption|]). exact U2.
Qed.
Definition VA_KEEP : list (bv 5) := [1; 2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition VA_post (regs : bvmap 5 word) (mem : word -> option byte) : world trasegs -> config -> Prop :=
fun W' c' => W' = W2 /\ exists (fy' : FPState) regs' mem' md' (cut : Z),
c' = mkCfg (@mkst fy' regs' (Z_to_bv 64 TN_TAIL) mem' (seg_rom trasegs)) md' /\
ntn_inv fy' regs' mem' md' /\
getr regs' 13 = w64 cut /\ 0 <= cut <= 2 /\
(range_has_two pal imin imax -> dim_splits pal imin imax cut) /\
(forall r : bv 5, In r VA_KEEP -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 80 <= a < spc + 104) -> aview trasegs (w_H W2) mem' a = aview trasegs (w_H W2) mem a) /\
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem' a).
Local Ltac flt_cond Hc Dat A32 A33 A34 A35 :=
apply flt_taken in Hc; rewrite ?sv_fmv_d in Hc; rewrite ?val_fdiv, ?denot_lit0 in Hc;
rewrite ?(Dat 32%nat _ A32), ?(Dat 33%nat _ A33), ?(Dat 34%nat _ A34), ?(Dat 35%nat _ A35) in Hc.
Local Ltac va_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; vm_compute in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia].
Local Ltac va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR m0 :=
aj_run_to_tokF tratbl_lib_ok HS HJ SHOK nt_Bspan TN_TAIL;
[ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spc - sp0);
[reflexivity | rewrite HU2; clear; lia | cbn [YQ0b.r_wlo]; clear - Hbud WS; lia | cbn [YQ0b.r_whi]; clear - Hsptop; lia | apply awr_ok_nil]
| lazymatch goal with
| HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msn)), HG : mem_grows (mrestrict _ _) (mrestrict _ (ms_mem ?msn)) |- SRr _ _ (mkCfg ?msn _) _ =>
let KW' := fresh "KW" in let PR' := fresh "PR" in
assert (KW' : forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 80 <= a < spc + 104) -> aview trasegs (w_H W2) (ms_mem msn) a = aview trasegs (w_H W2) m0 a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha Hn; rewrite (nt_kept_win _ _ _ _ _ spc 80 104 HFr ltac:(va_rs_tac) HU2 a Ha Hn); exact (KW a Ha Hn));
assert (PR' : forall a, apresent (w_H W2) m0 a -> apresent (w_H W2) (ms_mem msn) a)
by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_grows _ _ _ _ HG); exact (PR a Ha));
clear KW PR HFr HG; rename KW' into KW; rename PR' into PR
end ].
Lemma ntn_va : forall (fy : FPState) (regs : bvmap 5 word) mem md (xs xv0 xv1 xv2 : Z),
ntn_inv fy regs mem md ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 8) 8 xs -> val_mem trasegs (mrestrict (w_H W2) mem) (spc + 16) 8 xs ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 24) 8 xs ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 32) 8 xv0 -> val_mem trasegs (mrestrict (w_H W2) mem) (spc + 40) 8 xv1 ->
val_mem trasegs (mrestrict (w_H W2) mem) (spc + 48) 8 xv2 ->
0 <= xs < 2 ^ 64 -> 0 <= xv0 < 2 ^ 64 -> 0 <= xv1 < 2 ^ 64 -> 0 <= xv2 < 2 ^ 64 ->
is_intd xs (wsum l0) ->
vacc xv0 (imax + 1 - imin) (neq_meanb (wsum l0) (wdot l0) l0) ->
vacc xv1 (imax + 1 - imin) (neq_meanb (wsum l1) (wdot l1) l1) ->
vacc xv2 (imax + 1 - imin) (neq_meanb (wsum l2) (wdot l2) l2) ->
SRr trasegs W2 (mkCfg (@mkst fy regs (Z_to_bv 64 TN_VA) mem (seg_rom trasegs)) md) (VA_post regs mem).
Proof.
intros fy regs mem md xs xv0 xv1 xv2 HI V8 V16 V24 V32 V40 V48 Rs R0 R1 R2 Is Hv0 Hv1 Hv2.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof (ntn_env fy regs mem md HI) as (Qsp & Qsp47 & Qal & Qpb0 & Qpb1 & Qfb0 & Qfb1 & Qr0 & Qr1 & Qr16 & Qpm & Qfm & C1).
destruct (VA_seed fy regs mem md xs xv0 xv1 xv2 HI V8 V16 V24 V32 V40 V48 Rs R0 R1 R2) as (HS & SHOK & HE & A32 & A33 & A34 & A35 & HU2).
set (E := ew_fregs _ 64 _) in HS, SHOK, HE, A32, A33, A34, A35, HU2.
pose proof HI as (HJ & Hfrm & G2 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK & KEPT & PRES).
assert (WS : TNTN_STK = 16576) by reflexivity.
assert (Dat : forall n v, bv_unsigned (ew E n) = v -> bv_unsigned (sv_denot E (SOff n 0)) = v).
{ intros n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. }
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) (va_vals xs xv0 xv1 xv2) ++ [])) E).
{ split; [intros n Hn; subst E; rewrite ew_fregs_low by lia; reflexivity | reflexivity]. }
assert (FIN : forall ss' ms' md' (cut : Z), st_okF trasegs E ss' (restrict (w_H W2) ms') ->
ss_pc ss' = TN_TAIL -> ss_resv ss' = None -> sr_get (ss_regs ss') 13 = SLit cut -> 0 <= cut <= 2 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss') rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) VA_KEEP = true ->
(range_has_two pal imin imax -> dim_splits pal imin imax cut) ->
ajournal trasegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 (ms_mem ms') md' (k1 + 1) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 80 <= a < spc + 104) -> aview trasegs (w_H W2) (ms_mem ms') a = aview trasegs (w_H W2) mem a) ->
(forall a, apresent (w_H W2) mem a -> apresent (w_H W2) (ms_mem ms') a) ->
SRr trasegs W2 (mkCfg ms' md') (VA_post regs mem)).
{ intros ss' ms' md' cut HS' Hpc' Hrv' Q13 Hcut QK Hpick HJ' Hk' Hp'.
pose proof (st_okF_frm trasegs _ _ _ HS') as Hfrm'. pose proof (st_okF_to_legacy trasegs _ _ _ HS') as HSL.
pose proof (regs_kept_of_st_ok trasegs E ss' _ regs _ VA_KEEP HSL HAE QK) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W2) E ss' ms' HSL Hrv'), Hpc'. apply SRr_ret.
split; [reflexivity|]. exists (fp_of (restrict (w_H W2) ms')), (ms_regs ms'), (ms_mem ms'), md', cut. split; [reflexivity|].
split.
{ split; [exact HJ'|]. split; [exact Hfrm'|].
split; [rewrite (HKR (2%bv : bv 5) ltac:(cbv; tauto)); exact G2|]. split; [rewrite (HKR (8%bv : bv 5) ltac:(cbv; tauto)); exact G8|].
split; [rewrite (HKR (9%bv : bv 5) ltac:(cbv; tauto)); exact G9|]. split; [rewrite (HKR (18%bv : bv 5) ltac:(cbv; tauto)); exact G18|].
split; [rewrite (HKR (19%bv : bv 5) ltac:(cbv; tauto)); exact G19|]. split; [rewrite (HKR (21%bv : bv 5) ltac:(cbv; tauto)); exact G21|].
split; [rewrite (HKR (22%bv : bv 5) ltac:(cbv; tauto)); exact G22|]. split; [rewrite (HKR (23%bv : bv 5) ltac:(cbv; tauto)); exact G23|].
split; [intros rr Hrr; rewrite (HKR rr ltac:(clear - Hrr; cbv in Hrr |- *; tauto)); exact (GK rr Hrr)|].
split.
- intros a Ha Hns Hnn. rewrite (Hk' a Ha ltac:(clear - Hns WS; lia)). exact (KEPT a Ha Hns Hnn).
- intros a Ha. apply Hp'. apply PRES. exact Ha. }
split; [rewrite (st_ok_restrict_reg trasegs (w_H W2) E ss' ms' (13%bv : bv 5) HSL), Q13; reflexivity|].
split; [exact Hcut|]. split; [exact Hpick|]. split; [exact HKR|]. split; [exact Hk' | exact Hp']. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (spc + 80 <= a < spc + 104) -> aview trasegs (w_H W2) mem a = aview trasegs (w_H W2) mem a) by reflexivity.
assert (PR : forall a, apresent (w_H W2) mem a -> apresent (w_H W2) mem a) by (intros a Ha; exact Ha).
va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc Dat A32 A33 A34 A35.
- va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc0 Dat A32 A33 A34 A35.
+ va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 true true true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 2 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 true true false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 1 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
+ va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 true false true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 2 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 true false false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 0 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
- va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc0 Dat A32 A33 A34 A35.
+ va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 false true true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 2 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 false true false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 1 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
+ va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
aj_branchF tratbl_lib_ok HS; flt_cond Hc1 Dat A32 A33 A34 A35.
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 false false true Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 2 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
* va_run HS HJ SHOK HU2 Hbud Hsptop WS KW PR mem.
pose proof (VA_pick xs xv0 xv1 xv2 false false false Is Hv0 Hv1 Hv2 Hc Hc0 Hc1) as Hpick.
exact (FIN _ _ _ 0 HS eq_refl eq_refl eq_refl ltac:(lia) ltac:(vm_compute; reflexivity) Hpick HJ KW PR).
Qed.
End f.
