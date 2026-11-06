(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YK0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2u YC1b YC4u YC4z.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YC6w YC6v YC6k YC7c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition pxe (fmt : Z) : sv :=
if fmt =? 3 then SAlu ALU_ADD (SMd M_MUL (SOff 28 0) (SLit 3)) (SOff 40 0) else SAlu ALU_ADD (SAlu ALU_SLL (SOff 28 0) (SLit 2)) (SOff 40 0).
Definition px_chunks (fmt : Z) : list YQ0b.chunk :=
[YQ0b.mkChunk 0 (CVal 1 (SOff 53 0)); YQ0b.mkChunk 1 (CVal 1 (SOff 54 0)); YQ0b.mkChunk 2 (CVal 1 (SOff 55 0))] ++
(if fmt =? 3 then [] else [YQ0b.mkChunk 3 (CVal 1 (SOff 56 0))]).
Definition px_reg (fmt : Z) : YQ0b.region := YQ0b.mkRegion (Some 52%nat) 0 fmt 0 0 (px_chunks fmt).
Definition px_atoms (alo ahi : Z) : list (nat * afact) :=
[ (28%nat, mkAF 0 9999 0); (40%nat, mkAF 4096 140737479966720 0); (52%nat, mkAF 4096 140737479966720 0);
(53%nat, mkAF 0 255 0); (54%nat, mkAF 0 255 0); (55%nat, mkAF 0 255 0); (56%nat, mkAF alo ahi 0) ].
Definition HD_PINS (fmt : Z) : list (bv 5 * sv) := [(5%bv, SOff 32 8); (6%bv, SOff 32 16); (7%bv, SLit fmt)].
Definition HSHE : sv := SMdw M_REMU (SAlu ALU_OR (SAlu ALU_SLL (SOff 54 0) (SLit 8)) (SAlu ALU_OR (SAlu ALU_SLL (SOff 53 0) (SLit 16)) (SOff 55 0))) (SOff 39 0).
Definition ZXE (a : sv) : sv := SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32).
Definition UHE : sv := SAlu ALU_ADD (SOff 35 0) (ZXE HSHE).
Definition uh_reg (v : Z) : YQ0b.region := YQ0b.mkRegion (Some 57%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SLit v))].
Section d.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_HSHE : forall E (c : colour) T,
ew E 53 = Z_to_bv 64 (cR c) -> ew E 54 = Z_to_bv 64 (cG c) -> ew E 55 = Z_to_bv 64 (cB c) -> colour_ok c ->
ew E 39 = Z_to_bv 64 T -> 0 < T < 2 ^ 30 -> U E HSHE = hash0 T c.
Proof.
intros E c T H33 H34 H35 Hc HT RT. pose proof Hc as (Rr & Rg & Rb). unfold HSHE, hash0.
apply U_remuw_small; [| apply (U_atom E 39 T HT); lia | lia | lia].
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (U_atom E 53 (cR c) H33), (U_atom E 54 (cG c) H34), (U_atom E 55 (cB c) H35) by lia.
change (Z.land (zcanon 16) 63) with 16. change (Z.land (zcanon 8) 63) with 8.
rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. change (2 ^ 8) with 256.
rewrite (zcanon_id (cR c * 65536)), (zcanon_id (cG c * 256)) by (unfold M64; lia).
assert (L1 : Z.lor (cR c * 65536) (cB c) = cR c * 65536 + cB c) by (change 65536 with (2 ^ 16); apply lor_low_disjoint; lia).
rewrite L1. rewrite (zcanon_id (cR c * 65536 + cB c)) by (unfold M64; lia).
assert (L2 : Z.lor (cG c * 256) (cR c * 65536 + cB c) = cR c * 65536 + cG c * 256 + cB c).
{ rewrite Z.lor_comm. rewrite <- L1. rewrite <- Z.lor_assoc, (Z.lor_comm (cB c)), Z.lor_assoc.
assert (L3 : Z.lor (cR c * 65536) (cG c * 256) = cR c * 65536 + cG c * 256) by (change 65536 with (2 ^ 16); apply lor_low_disjoint; lia).
rewrite L3. replace (cR c * 65536 + cG c * 256) with ((cR c * 256 + cG c) * 2 ^ 8) by lia. rewrite lor_low_disjoint; lia. }
rewrite L2. apply zcanon_id. unfold M64; lia.
Qed.
Lemma U_ZXE : forall E a x, U E a = x -> 0 <= x < 2 ^ 32 -> U E (ZXE a) = x.
Proof.
intros E a x Ha Hx. unfold ZXE. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, Ha.
change (Z.land (zcanon 32) 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 32)) by (unfold M64; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia).
rewrite Z.shiftr_div_pow2, Z.div_mul by lia. apply zcanon_id. unfold M64; lia.
Qed.
Definition TRIPLE (a : sv) : sv := SAlu ALU_ADD (SAlu ALU_SLL a (SLit 1)) a.
Lemma U_TRIPLE : forall E a x, U E a = x -> 0 <= x < 2 ^ 30 -> U E (TRIPLE a) = 3 * x.
Proof.
intros E a x Ha Hx. unfold TRIPLE. rewrite !U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Ha.
change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (x * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_base_triple : forall E n b a x, ew E n = Z_to_bv 64 b -> 0 <= b -> b + 3 * x < 2 ^ 64 -> U E a = x -> 0 <= x < 2 ^ 30 ->
U E (SAlu ALU_ADD (SOff n 0) (ZXE (TRIPLE a))) = b + 3 * x.
Proof.
intros E n b a x Hn Hb Hbx Ha Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n b Hn) by lia.
rewrite (U_ZXE E (TRIPLE a) (3 * x) (U_TRIPLE E a x Ha Hx)) by lia. apply zcanon_id. unfold M64. lia.
Qed.
End d.
Lemma find_off_ge0' : forall H ent c js, ht_inv H ent -> find_off H c = Some js -> 0 <= js.
Proof. intros H ent c js INV E. exact (proj1 (proj1 (find_off_spec H ent INV c js E))). Qed.
Lemma find_off_home_free : forall H ent c, ht_inv H ent -> usedz H (hash0 (ht_T H) c) = 0 -> find_off H c = Some 0.
Proof.
intros H ent c INV Hz. destruct (find_off_exists H ent INV c) as (js & Ejs).
destruct (find_off_spec H ent INV c js Ejs) as (Hjs & _ & Hbefore).
destruct (Z.eq_dec js 0) as [->|Hne]; [exact Ejs|].
exfalso. specialize (Hbefore 0 ltac:(lia)). rewrite cyc_0 in Hbefore by (apply hash0_range; exact (inv_T_pos H ent INV)).
unfold slot_stop in Hbefore. rewrite Hz in Hbefore. discriminate Hbefore.
Qed.
Section H1.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model)
(own : list (Z * Z)).
Variables (s1v tb img fmt N : Z) (imgl : list Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 : Z).
Variable PROT : list (Z * Z).
Variables (lyH : alayout) (SH : astate) (WH : world trasegs) (memH : word -> option byte).
Hypothesis Hs1 : s1v = sp0 - 512.
Hypothesis HSTK : 512 <= STK.
Hypothesis Hsp32 : sp0 mod 32 = 0.
Hypothesis HOP : hk_opaque_ok hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav.
Hypothesis Hfmt : fmt = 3 \/ fmt = 4.
Hypothesis HN : 1 <= N <= 10000.
Hypothesis HimgP : In (img, fmt * N) PROT.
Hypothesis Himgl : zlen imgl = fmt * N.
Local Notation hcore_raw := (hcore_raw B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation hcore := (hcore B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_HL := (at_HL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation at_TL := (at_TL B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation HRS := (hcore_run_same B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19
PROT lyH SH WH memH Hs1 HSTK Hfmt HN Himgl HimgP).
Local Notation FRAMEF := (hk_frame_facts B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hs1 HSTK Hsp32).
Local Notation IMGF := (hk_img_facts B LAWS STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH Hfmt HN HimgP).
Definition pxa (i : Z) : Z := if fmt =? 3 then 0 else getz imgl (fmt * i + 3).
Lemma hd_px_side : forall (E : env) lyc Sc W mem md i (alo ahi : Z),
AR trasegs B lyc Sc W mem md -> In (img, fmt * N) (ablocks B lyc Sc) -> 0 <= i < N ->
arr8 trasegs (mrestrict (w_H W) mem) img imgl ->
ew E 25 = Z_to_bv 64 SB -> ew E 28 = Z_to_bv 64 i -> ew E 40 = Z_to_bv 64 img -> ew E 52 = Z_to_bv 64 (img + fmt * i) ->
ew E 53 = Z_to_bv 64 (getz imgl (fmt * i)) -> ew E 54 = Z_to_bv 64 (getz imgl (fmt * i + 1)) -> ew E 55 = Z_to_bv 64 (getz imgl (fmt * i + 2)) ->
ew E 56 = Z_to_bv 64 (pxa i) -> alo <= pxa i <= ahi ->
Forall (region_ok trasegs E (mrestrict (w_H W) mem)) [px_reg fmt] /\
extent_of_region E (px_reg fmt) = (img + fmt * i, img + fmt * i + fmt) /\
atoms_ok E (px_atoms alo ahi) /\ alias_ok E [(pxe fmt, SOff 52 0)] /\
Forall (shent_ok trasegs hk_Bx E (mrestrict (w_H W) mem)) [mkSHE 52 0 fmt].
Proof.
intros E lyc Sc W mem md i alo ahi HAR Hin Hi Himg E25 E28 E40 E52 E53 E54 E55 E56 Ha.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W mem md img (fmt * N) HAR Hin) as (_ & Hi4096 & Hiceil & Happ & _ & _ & Hn0).
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfmt HN; nia)) as [_ Hrq].
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4) by (destruct Hfmt as [Hf | Hf]; rewrite Hf; clear - Hi; lia).
set (pix := img + fmt * i) in *.
assert (Rpix : 4096 <= pix /\ pix + fmt <= img + fmt * N /\ pix + fmt <= alloc_ceiling) by (subst pix; clear - Hi4096 Hiceil Hrq Hfi; lia).
assert (U52 : bv_unsigned (ew E 52) = pix) by (rewrite E52; apply unsigned_lit_small; clear - Rpix C1 Hfi; lia).
assert (PB : forall j, 0 <= j < fmt -> mbyte trasegs (mrestrict (w_H W) mem) (pix + j) = Some (Z_to_bv 8 (getz imgl (fmt * i + j))) /\ 0 <= getz imgl (fmt * i + j) < 256).
{ intros j Hj. subst pix. rewrite <- Z.add_assoc. apply (arr8_getz trasegs _ img imgl); [exact Himg | rewrite Himgl; clear - Hfi Hj; lia]. }
assert (CK : forall j n, 0 <= j < fmt -> ew E n = Z_to_bv 64 (getz imgl (fmt * i + j)) ->
YQ0b.chunk_ok trasegs E (mrestrict (w_H W) mem) pix (YQ0b.mkChunk j (CVal 1 (SOff n 0)))).
{ intros j n Hj En. destruct (PB j Hj) as [Pj Rj].
apply (chunk_ok_val trasegs E _ pix j 1 _ (getz imgl (fmt * i + j))); [cbn [sv_denot]; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rj | lia |].
apply (val_mem_byte trasegs); assumption. }
assert (Rpa : 0 <= pxa i < 256).
{ unfold pxa. destruct (Z.eqb_spec fmt 3); [lia|]. apply (PB 3). clear - Hfmt n. lia. }
split.
{ apply Forall_cons; [|apply Forall_nil]. unfold px_reg, region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U52.
split; [clear - Rpix; lia|]. split; [clear - Rpix C1 Hfi; lia|]. split; [intros o Ho; lia|].
unfold px_chunks. apply Forall_app. split.
- repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK 0 53%nat); [clear - Hfmt; lia | rewrite Z.add_0_r; exact E53].
+ apply (CK 1 54%nat); [clear - Hfmt; lia | exact E54].
+ apply (CK 2 55%nat); [clear - Hfmt; lia | exact E55].
- destruct (Z.eqb_spec fmt 3) as [|Hn3]; [apply Forall_nil|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 3 56%nat); [clear - Hfmt Hn3; lia|]. rewrite E56. unfold pxa. destruct (Z.eqb_spec fmt 3); [contradiction | reflexivity]. }
split.
{ unfold extent_of_region, px_reg. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U52. f_equal; lia. }
split.
{ unfold px_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E28, E40, U52, E53, E54, E55, E56.
destruct (PB 0 ltac:(clear - Hfmt; lia)) as [_ R0]. destruct (PB 1 ltac:(clear - Hfmt; lia)) as [_ R1]. destruct (PB 2 ltac:(clear - Hfmt; lia)) as [_ R2].
rewrite Z.add_0_r in R0.
rewrite !unsigned_lit_small by (clear - Hi HN Hi4096 Hiceil Hrq C1 R0 R1 R2 Rpa Hfi; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
clear - Hi HN Hi4096 Hiceil Hrq C1 R0 R1 R2 Rpa Ha Rpix Hfi. repeat split; lia. }
split.
{ cbn [alias_ok]. split; [|exact I]. apply U_inj.
rewrite (U_atom E 52 pix E52) by (clear - Rpix C1 Hfi; lia). unfold pxe.
destruct Hfmt as [Hf | Hf]; rewrite Hf; cbn [Z.eqb Pos.eqb].
- rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 28 i E28) by (clear - Hi HN; lia).
rewrite (U_lit E 3) by lia. rewrite (U_atom E 40 img E40) by (clear - Hi4096 Hiceil Hrq C1 Hfi; lia).
rewrite (zcanon_id (i * 3)) by (unfold M64; clear - Hi HN; lia). subst pix. rewrite Hf in *. rewrite zcanon_id by (unfold M64; clear - Rpix C1 Hi; lia). lia.
- rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 28 i E28) by (clear - Hi HN; lia).
rewrite (U_lit E 2) by lia. rewrite (U_atom E 40 img E40) by (clear - Hi4096 Hiceil Hrq C1 Hfi; lia).
change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
rewrite (zcanon_id (i * 4)) by (unfold M64; clear - Hi HN; lia). subst pix. rewrite Hf in *. rewrite zcanon_id by (unfold M64; clear - Rpix C1 Hi; lia). lia. }
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 52 pix fmt pix 0 fmt).
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md img (fmt * N) _ _ HAR Hin); [subst pix; clear - Hfi; lia | clear - Rpix Hrq; lia].
- unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U52.
- lia.
- lia.
- intros x Hx. pose proof (blk_off_img _ _ _ _ _ _ img (fmt * N) HAR Hin) as Himg_off.
subst pix. revert Hx Happ Himg_off Rpix Hrq Hfi. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma hd_uh_side : forall (E : env) lyc Sc W mem md (u T : Z) (used : list Z) (c : colour) (v : Z),
AR trasegs B lyc Sc W mem md -> In (u, T) (ablocks B lyc Sc) -> arr8 trasegs (mrestrict (w_H W) mem) u used -> zlen used = T -> 0 < T < 2 ^ 30 ->
colour_ok c -> ew E 25 = Z_to_bv 64 SB -> ew E 35 = Z_to_bv 64 u -> ew E 39 = Z_to_bv 64 T ->
ew E 53 = Z_to_bv 64 (cR c) -> ew E 54 = Z_to_bv 64 (cG c) -> ew E 55 = Z_to_bv 64 (cB c) ->
ew E 57 = Z_to_bv 64 (u + hash0 T c) -> v = getz used (hash0 T c) ->
Forall (region_ok trasegs E (mrestrict (w_H W) mem)) [uh_reg v] /\
extent_of_region E (uh_reg v) = (u + hash0 T c, u + hash0 T c + 1) /\
atoms_ok E [(57%nat, mkAF 4096 140737479966720 0)] /\ alias_ok E [(UHE, SOff 57 0)] /\
Forall (shent_ok trasegs hk_Bx E (mrestrict (w_H W) mem)) [mkSHE 57 0 1].
Proof.
intros E lyc Sc W mem md u T used c v HAR Hin Hu LU RT Cok E25 E35 E39 E53 E54 E55 E57 Hv.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W mem md u T HAR Hin) as (_ & Hu4096 & Huceil & Happ & _ & _ & Hn0).
pose proof (req_size_pos T ltac:(lia)) as [_ Hrq].
set (h0 := hash0 T c) in *. assert (Rh0 : 0 <= h0 < T) by (subst h0; apply hash0_range; lia).
destruct (arr8_getz trasegs _ u used h0 Hu ltac:(lia)) as [Bu Rub]. rewrite <- Hv in Bu, Rub.
assert (U57 : bv_unsigned (ew E 57) = u + h0) by (rewrite E57; apply unsigned_lit_small; clear - Hu4096 Huceil Hrq Rh0 C1; lia).
split.
{ apply Forall_cons; [|apply Forall_nil]. unfold uh_reg, region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite U57.
split; [clear - Hu4096 Rh0; lia|]. split; [clear - Huceil Hrq Rh0 C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trasegs E _ (u + h0) 0 1 _ v); [reflexivity | exact Rub | lia |].
rewrite Z.add_0_r. apply (val_mem_byte trasegs); assumption. }
split.
{ unfold extent_of_region, uh_reg. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite U57. f_equal; lia. }
split.
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U57, Z.pow_0_r, Z.mod_1_r. clear - Hu4096 Huceil Hrq Rh0 C1. repeat split; lia. }
split.
{ cbn [alias_ok]. split; [|exact I]. apply U_inj. rewrite (U_atom E 57 (u + h0) E57) by (clear - Hu4096 Huceil Hrq Rh0 C1; lia).
unfold UHE. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 35 u E35) by (clear - Hu4096 Huceil Hrq C1 RT; lia).
rewrite (U_ZXE E HSHE h0 (U_HSHE E c T E53 E54 E55 Cok E39 RT) ltac:(clear - Rh0 RT; lia)).
apply zcanon_id. unfold M64. clear - Hu4096 Huceil Hrq Rh0 C1. lia. }
apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range trasegs (w_H W) mem E hk_Bx 57 (u + h0) 1 (u + h0) 0 1).
- apply (range_addressable_of_block trasegs B LAWS lyc Sc W mem md u T _ _ HAR Hin); clear - Rh0 Hrq; lia.
- unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U57.
- lia.
- lia.
- intros x Hx. revert Hx Happ Rh0 Hrq. clear. unfold SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma hl_head_transparent : forall lyc Sc W regs mem md k C i ha,
at_HL lyc Sc W regs mem md k C i ha -> fmt = 4 -> getz imgl (4 * i + 3) <= 127 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_HEAD) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_TAIL) mem2 (seg_rom trasegs)) md2 /\ at_TL lyc Sc W regs2 mem2 md2 k C i 1).
Proof.
intros lyc Sc W regs mem md k C i ha HAT Hf4 Halpha.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (G5 & G6 & G7 & G16 & G17 & G22 & G23 & G26 & G27) & G28 & G29 & Hi & Hha & Hz).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & Harr & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
set (pix := img + 4 * i).
assert (PB : forall j, 0 <= j < 4 -> mbyte trasegs (mrestrict (w_H W) mem) (pix + j) = Some (Z_to_bv 8 (getz imgl (4 * i + j))) /\ 0 <= getz imgl (4 * i + j) < 256).
{ intros j Hj. subst pix. rewrite <- Z.add_assoc. apply (arr8_getz trasegs _ img imgl); [exact Himg | rewrite Himgl, Hf4; clear - Hi Hj; lia]. }
destruct (PB 0 ltac:(lia)) as [P0 R0']. rewrite !Z.add_0_r in P0, R0'. destruct (PB 1 ltac:(lia)) as [P1 R1']. destruct (PB 2 ltac:(lia)) as [P2 R2']. destruct (PB 3 ltac:(lia)) as [P3 R3'].
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C)).
set (xv := [pix; getz imgl (4 * i); getz imgl (4 * i + 1); getz imgl (4 * i + 2); getz imgl (4 * i + 3)]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (vals ++ xv) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E40 : ew E 40 = Z_to_bv 64 img) by exact (HV 8%nat _ eq_refl).
assert (E51 : ew E 51 = Z_to_bv 64 N) by exact (HV 19%nat _ eq_refl).
assert (E52 : ew E 52 = Z_to_bv 64 pix) by exact (HV 20%nat _ eq_refl).
assert (E28 : ew E 28 = Z_to_bv 64 i) by (rewrite (HE 28%nat 28%bv eq_refl); exact G28).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (Rpix : 4096 <= pix /\ pix + 4 <= alloc_ceiling) by (subst pix; rewrite Hf4 in Hiceil; clear - Hi4096 Hiceil Hi; lia).
assert (U52 : bv_unsigned (ew E 52) = pix) by (rewrite E52; apply unsigned_lit_small; clear - Rpix C1; lia).
assert (Epix : pix = img + fmt * i) by (subst pix; rewrite Hf4; reflexivity).
assert (Epa : pxa i = getz imgl (4 * i + 3)) by (unfold pxa; rewrite Hf4; reflexivity).
destruct (hd_px_side E lyc Sc W mem md i 0 127 HAR Himgin Hi Himg E25 E28 E40 ltac:(rewrite <- Epix; exact E52)
ltac:(rewrite Hf4; exact (HV 21%nat _ eq_refl)) ltac:(rewrite Hf4; exact (HV 22%nat _ eq_refl)) ltac:(rewrite Hf4; exact (HV 23%nat _ eq_refl))
ltac:(rewrite Epa; exact (HV 24%nat _ eq_refl)) ltac:(rewrite Epa; clear - R3' Halpha; lia)) as (PXR & PXE & PXA & PXL & PXS).
assert (Hsep : pix + 4 <= tb \/ tb + 48 <= pix).
{ pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb C) (img, fmt * N) (tb, CHT_SIZE) HAR HPerm HimgP ltac:(left; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfmt HN; nia)) as [_ Hrq]. rewrite Hf4 in Hd, Hrq. subst pix. clear - Hd Hrq Hi. lia. }
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_HEAD false (HD_PINS fmt) [] [] [] [] [px_reg fmt] (px_atoms 0 127) [] [(pxe fmt, SOff 52 0)] [mkSHE 52 0 fmt]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) (ac_T C) xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfmt HN; nia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj) as [HS SHOK].
all: fold vals; fold E.
{ rewrite Hf4. reflexivity. }
{ reflexivity. }
{ unfold HD_PINS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
- rewrite G5. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G6. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G7. reflexivity. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ exact PXR. }
{ intros e [<- | []]. rewrite PXE. cbn [fst snd]. rewrite <- Epix, Hf4. clear - Rpix Hsep. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. auto. }
{ exact PXA. }
{ exact I. }
{ exact PXL. }
{ exact PXS. }
rewrite Hf4 in HS, SHOK.
assert (HAE : env_agree 57 E E) by (apply env_agree_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_TAIL.
{ apply (hk_awr_ok s1v tb 4 _ false [] [] [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 57 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb 4 _ false [] [] [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | []] & Hr). cbn [px_reg YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. clear - Hr. lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 57 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [16; 17; 27; 28]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
split.
{ apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]. }
split.
{ rewrite (HKR 16%bv ltac:(cbv; tauto)), (HKR 17%bv ltac:(cbv; tauto)), (HKR 27%bv ltac:(cbv; tauto)).
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RT0 : getr (ms_regs ms) 5 = Z_to_bv 64 (tb + 8))
by (rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms 5%bv HS); change (sr_get (ss_regs ssx) 5%bv) with (SOff 32 8);
apply denot_off; [rewrite (proj1 HAE1) by lia; exact E32 | clear - Htb4096 Htbceil C1; lia]);
assert (RT1 : getr (ms_regs ms) 6 = Z_to_bv 64 (tb + 16))
by (rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms 6%bv HS); change (sr_get (ss_regs ssx) 6%bv) with (SOff 32 16);
apply denot_off; [rewrite (proj1 HAE1) by lia; exact E32 | clear - Htb4096 Htbceil C1; lia]);
assert (RT2 : getr (ms_regs ms) 7 = Z_to_bv 64 fmt)
by (rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms 7%bv HS); change (sr_get (ss_regs ssx) 7%bv) with (SLit 4); rewrite Hf4; reflexivity) end.
split; [exact RT0|]. split; [exact RT1|]. split; [exact RT2|]. split; [exact G16|]. split; [exact G17 | exact G27]. }
split; [rewrite (HKR 28%bv ltac:(cbv; tauto)); exact G28|].
split.
{ lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms 12%bv HS); change (sr_get (ss_regs ssx) 12%bv) with (SLit 1); reflexivity end. }
split; [exact Hi|]. split; [right; split; [reflexivity | exact Hf4]|]. clear - Hz. lia.
Qed.
Local Notation at_PA := (at_PA B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Local Notation pxc := (pxc fmt imgl).
Definition hd_cds : list acond := if fmt =? 3 then [] else [mkAC BC_LT (SExt true 8 (SOff 56 0)) (SLit 0)].
Lemma hl_head_free : forall lyc Sc W regs mem md k C i ha,
at_HL lyc Sc W regs mem md k C i ha -> opaque_px fmt imgl i -> usedz (ac_H C) (hash0 (ac_T C) (pxc i)) = 0 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_HEAD) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 HL_PA) mem2 (seg_rom trasegs)) md2 /\
at_PA lyc Sc W regs2 mem2 md2 k C i ha (hash0 (ac_T C) (pxc i)) 0).
Proof.
intros lyc Sc W regs mem md k C i ha HAT Hop Hfree.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (G5 & G6 & G7 & G16 & G17 & G22 & G23 & G26 & G27) & G28 & G29 & Hi & Hha & Hz).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4) by (destruct Hfmt as [Hf | Hf]; rewrite Hf; clear - Hi; lia).
set (pix := img + fmt * i). set (c := pxc i). set (h0 := hash0 T c).
assert (Rh0 : 0 <= h0 < T) by (subst h0; apply hash0_range; clear - RT3; lia).
assert (PB : forall j, 0 <= j < fmt -> 0 <= getz imgl (fmt * i + j) < 256).
{ intros j Hj. apply (arr8_getz trasegs _ img imgl (fmt * i + j) Himg). rewrite Himgl. clear - Hfi Hj. lia. }
assert (Cok : colour_ok c).
{ subst c. unfold pxc, YC7c.pxc, colour_ok, cR, cG, cB, mkcol. cbn [fst snd].
pose proof (PB 0 ltac:(clear - Hfi; lia)) as R0. rewrite Z.add_0_r in R0. pose proof (PB 1 ltac:(clear - Hfi; lia)). pose proof (PB 2 ltac:(clear - Hfi; lia)). lia. }
assert (Rpa : (if fmt =? 3 then 0 else 128) <= pxa i <= 255).
{ unfold pxa. destruct (Z.eqb_spec fmt 3) as [|Hn3]; [lia|]. assert (Hf4 : fmt = 4) by (clear - Hfmt Hn3; lia).
pose proof (PB 3 ltac:(clear - Hf4; lia)). pose proof (Hop Hf4). lia. }
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [pix; cR c; cG c; cB c; pxa i; ac_u C + h0]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (vals ++ xv) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E40 : ew E 40 = Z_to_bv 64 img) by exact (HV 8%nat _ eq_refl).
assert (E28 : ew E 28 = Z_to_bv 64 i) by (rewrite (HE 28%nat 28%bv eq_refl); exact G28).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
destruct (hd_px_side E lyc Sc W mem md i (if fmt =? 3 then 0 else 128) 255 HAR Himgin Hi Himg E25 E28 E40 (HV 20%nat _ eq_refl)
(HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) (HV 24%nat _ eq_refl) Rpa) as (PXR & PXE & PXA & PXL & PXS).
destruct (hd_uh_side E lyc Sc W mem md (ac_u C) T (ht_used (ac_H C)) c 0 HAR Huin Au L1 ltac:(clear - RT2 RT3; lia) Cok E25 E35 E39
(HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) (HV 25%nat _ eq_refl) (eq_sym Hfree)) as (UHR & UHX & UHA & UHL & UHS).
assert (HsepP : pix + fmt <= tb \/ tb + 48 <= pix).
{ pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb C) (img, fmt * N) (tb, CHT_SIZE) HAR HPerm HimgP ltac:(left; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfi; lia)) as [_ Hrq]. subst pix. clear - Hd Hrq Hfi. lia. }
assert (HsepU : ac_u C + h0 + 1 <= tb \/ tb + 48 <= ac_u C + h0).
{ pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T tb CHT_SIZE HAR Huin Htbin) as Hd.
destruct (Z.eq_dec (ac_u C) tb) as [Eq | Ne].
- exfalso. pose proof (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & _ & _ & _ & _ & Hpw & _).
assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
specialize (Hd Hne). unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos T ltac:(clear - RT3; lia)). clear - Hd Eq H RT3. lia.
- assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as X _; contradiction).
specialize (Hd Hne). unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ Hrq]. clear - Hd Hrq Rh0. lia. }
assert (HsepPU : pix + fmt <= ac_u C + h0 \/ ac_u C + h0 + 1 <= pix).
{ pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb C) (img, fmt * N) (ac_u C, T) HAR HPerm HimgP
ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfi; lia)) as [_ Hrq]. pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
subst pix. clear - Hd Hrq HrqT Hfi Rh0. lia. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & Hu4096 & Huceil & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_HEAD false (HD_PINS fmt) [] [] [] [] [px_reg fmt; uh_reg 0]
(px_atoms (if fmt =? 3 then 0 else 128) 255 ++ [(57%nat, mkAF 4096 140737479966720 0); (39%nat, mkAF 524309 16777216 0); (35%nat, mkAF 4096 140737479966720 0)])
hd_cds [(pxe fmt, SOff 52 0); (UHE, SOff 57 0)] [mkSHE 52 0 fmt; mkSHE 57 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfi; lia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj) as [HS SHOK].
all: fold vals; fold E.
{ destruct Hfmt as [Hf | Hf]; rewrite Hf; reflexivity. }
{ reflexivity. }
{ unfold HD_PINS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
- rewrite G5. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G6. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G7. reflexivity. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ apply Forall_cons; [exact (Forall_inv PXR) | exact UHR]. }
{ intros e [<- | [<- | []]]; [rewrite PXE | rewrite UHX]; cbn [fst snd]; fold pix; fold h0.
- clear - HsepP Hiceil Hfi. subst pix. lia.
- clear - HsepU Huceil HrqT Rh0. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. rewrite PXE, UHX. unfold zdisj. cbn [fst snd]. fold pix. fold h0. clear - HsepPU. tauto. }
{ apply atoms_ok_app; [exact PXA|]. destruct UHA as [UHA _]. cbn [atoms_ok]. split; [exact UHA|]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E39, E35. rewrite !unsigned_lit_small by (clear - RT1 RT3 Hu4096 Huceil HrqT C1; unfold MAX_TABLE_SIZE in RT1; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. assert (HT5 : 524309 <= T) by (clear - HTc; cbv [ts_chain In] in HTc; lia). unfold MAX_TABLE_SIZE in RT1.
clear - RT1 HT5 Hu4096 Huceil HrqT C1. repeat split; lia. }
{ unfold hd_cds. destruct (Z.eqb_spec fmt 3) as [|Hn3]; [exact I|]. cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
assert (Hf4 : fmt = 4) by (clear - Hfmt Hn3; lia).
rewrite (branch_lt_sext8 E 56 (pxa i) (HV 24%nat _ eq_refl)) by (clear - Rpa; destruct (fmt =? 3); lia).
apply Z.leb_le. clear - Rpa Hn3. destruct (Z.eqb_spec fmt 3); [contradiction | lia]. }
{ cbn [alias_ok]. destruct PXL as [PXL _]. destruct UHL as [UHL _]. auto. }
{ apply Forall_cons; [exact (Forall_inv PXS) | exact UHS]. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
unfold hd_cds in HS. destruct Hfmt as [Hf | Hf]; rewrite Hf in HS, SHOK.
{ aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_PA.
{ apply (hk_awr_ok s1v tb 3 _ false [] [] [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb 3 _ false [] [] [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | [<- | []]] & Hr); cbn [px_reg uh_reg YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; clear - Hr; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27; 28; 29; 16; 17]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e v, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 v)
by (intros r e v Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SP72 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 28 0)] 72 (SOff 28 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 28 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E28 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 29 0)] 56 (SOff 29 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 29 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; rewrite (HE 29%nat 29%bv eq_refl); exact G29 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72 | exact SP56]|].
split; [exists 0; split; [exact (find_off_home_free _ _ _ Hinv Hfree)|]; split; [symmetry; apply cyc_0; exact Rh0 | reflexivity]|].
assert (DH : sv_denot E HSHE = Z_to_bv 64 h0).
{ rewrite denot_lit_U. f_equal. exact (U_HSHE E c T (HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) Cok E39 ltac:(clear - RT2 RT3; lia)). }
assert (DZ : sv_denot E (ZXE HSHE) = Z_to_bv 64 h0).
{ rewrite denot_lit_U. f_equal. apply U_ZXE; [exact (U_HSHE E c T (HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) Cok E39 ltac:(clear - RT2 RT3; lia)) | clear - Rh0 RT2; lia]. }
split; [apply (RD 20%bv (SOff 52 0) pix eq_refl); [rewrite (denot_off E 52 pix 0 (HV 20%nat _ eq_refl)), Z.add_0_r; [reflexivity | subst pix; clear - Hi4096 Hiceil C1 Hfi; lia] | reflexivity]|].
split; [apply (RD 22%bv (SOff 34 0) (ac_h C) eq_refl); [|reflexivity]|].
{ destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as (_ & Hh4096 & Hhceil & _).
rewrite (denot_off E 34 (ac_h C) 0 (HV 2%nat _ eq_refl)), Z.add_0_r; [reflexivity|]. pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)). clear - Hh4096 Hhceil C1 H RT3. lia. }
split; [apply (RD 23%bv (SOff 35 0) (ac_u C) eq_refl); [rewrite (denot_off E 35 (ac_u C) 0 E35), Z.add_0_r; [reflexivity | clear - Hu4096 Huceil HrqT C1 RT3; lia] | reflexivity]|].
split; [exact (RD 24%bv (ZXE HSHE) h0 eq_refl DZ eq_refl)|].
split; [exact (RD 26%bv HSHE h0 eq_refl DH eq_refl)|].
split; [exact (RD 13%bv (SLit 0) 0 eq_refl eq_refl eq_refl)|].
split; [rewrite (HKR 28%bv ltac:(cbv; tauto)); exact G28|]. split; [rewrite (HKR 29%bv ltac:(cbv; tauto)); exact G29|].
split; [apply (RD 5%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 6%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 7%bv (SLit 3) fmt eq_refl); [rewrite Hf; reflexivity | reflexivity]|].
split; [rewrite (HKR 16%bv ltac:(cbv; tauto)); exact G16 | rewrite (HKR 17%bv ltac:(cbv; tauto)); exact G17]. }
{ aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan HL_PA.
{ apply (hk_awr_ok s1v tb 4 _ false [] [] [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb 4 _ false [] [] [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | [<- | []]] & Hr); cbn [px_reg uh_reg YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; clear - Hr; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27; 28; 29; 16; 17]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e v, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 v)
by (intros r e v Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SP72 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 28 0)] 72 (SOff 28 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 28 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E28 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 29 0)] 56 (SOff 29 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 29 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; rewrite (HE 29%nat 29%bv eq_refl); exact G29 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72 | exact SP56]|].
split; [exists 0; split; [exact (find_off_home_free _ _ _ Hinv Hfree)|]; split; [symmetry; apply cyc_0; exact Rh0 | reflexivity]|].
assert (DH : sv_denot E HSHE = Z_to_bv 64 h0).
{ rewrite denot_lit_U. f_equal. exact (U_HSHE E c T (HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) Cok E39 ltac:(clear - RT2 RT3; lia)). }
assert (DZ : sv_denot E (ZXE HSHE) = Z_to_bv 64 h0).
{ rewrite denot_lit_U. f_equal. apply U_ZXE; [exact (U_HSHE E c T (HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) Cok E39 ltac:(clear - RT2 RT3; lia)) | clear - Rh0 RT2; lia]. }
split; [apply (RD 20%bv (SOff 52 0) pix eq_refl); [rewrite (denot_off E 52 pix 0 (HV 20%nat _ eq_refl)), Z.add_0_r; [reflexivity | subst pix; clear - Hi4096 Hiceil C1 Hfi; lia] | reflexivity]|].
split; [apply (RD 22%bv (SOff 34 0) (ac_h C) eq_refl); [|reflexivity]|].
{ destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as (_ & Hh4096 & Hhceil & _).
rewrite (denot_off E 34 (ac_h C) 0 (HV 2%nat _ eq_refl)), Z.add_0_r; [reflexivity|]. pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)). clear - Hh4096 Hhceil C1 H RT3. lia. }
split; [apply (RD 23%bv (SOff 35 0) (ac_u C) eq_refl); [rewrite (denot_off E 35 (ac_u C) 0 E35), Z.add_0_r; [reflexivity | clear - Hu4096 Huceil HrqT C1 RT3; lia] | reflexivity]|].
split; [exact (RD 24%bv (ZXE HSHE) h0 eq_refl DZ eq_refl)|].
split; [exact (RD 26%bv HSHE h0 eq_refl DH eq_refl)|].
split; [exact (RD 13%bv (SLit 0) 0 eq_refl eq_refl eq_refl)|].
split; [rewrite (HKR 28%bv ltac:(cbv; tauto)); exact G28|]. split; [rewrite (HKR 29%bv ltac:(cbv; tauto)); exact G29|].
split; [apply (RD 5%bv (SOff 32 8) (tb + 8) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 6%bv (SOff 32 16) (tb + 16) eq_refl); [apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia] | reflexivity]|].
split; [apply (RD 7%bv (SLit 4) fmt eq_refl); [rewrite Hf; reflexivity | reflexivity]|].
split; [rewrite (HKR 16%bv ltac:(cbv; tauto)); exact G16 | rewrite (HKR 17%bv ltac:(cbv; tauto)); exact G17]. }
Qed.
Local Notation at_BC := (at_BC B STK sp0 FP ly S W0 mem0 md0 own s1v tb img fmt N imgl hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav hv19 PROT lyH SH WH memH).
Lemma hl_head_used : forall lyc Sc W regs mem md k C i ha,
at_HL lyc Sc W regs mem md k C i ha -> opaque_px fmt imgl i -> usedz (ac_H C) (hash0 (ac_T C) (pxc i)) <> 0 ->
SRr trasegs W (mkCfg (mkst regs (Z_to_bv 64 HL_HEAD) mem (seg_rom trasegs)) md)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (Z_to_bv 64 A_bcmp_tra) mem2 (seg_rom trasegs)) md2 /\
at_BC lyc Sc W regs2 mem2 md2 k C i ha 0).
Proof.
intros lyc Sc W regs mem md k C i ha HAT Hop Hused0.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
destruct HAT as (HC & (G5 & G6 & G7 & G16 & G17 & G22 & G23 & G26 & G27) & G28 & G29 & Hi & Hha & Hz).
pose proof HC as ((HJ & (G2 & G9 & G8 & G3 & G4 & G25 & G18 & G19) & Hsl & Hobj & (Af & Ah & Au & Ap & Ax) & Himg & Hlens & HTc & HPerm & Hperm & Hk & Hkept) & Hinv).
pose proof (proj1 HJ) as HAR.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (FRAMEF _ _ _ _ _ _ _ _ (proj1 HC)) as (Fceil & F47 & F32 & Fpres).
destruct (IMGF _ _ _ _ _ _ _ _ (proj1 HC)) as (Himgin & Hi4096 & Hiceil).
assert (Htbin : In (tb, CHT_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htbin) as (_ & Htb4096 & Htbceil & _). change (req_size CHT_SIZE) with 48 in Htbceil.
pose proof (ts_chain_ok _ HTc) as (RT1 & RT2 & RT3). unfold ac_T in *. set (T := ht_T (ac_H C)) in *.
pose proof Hlens as (L1 & L2 & L3 & L4 & L5). fold T in L1, L2, L3, L4, L5.
assert (Huin : In (ac_u C, T) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. apply in_app_iff. right. unfold ac_blocks, cht_blocks, ac_T. fold T. cbn. tauto. }
assert (Hfi : 0 <= fmt * i /\ fmt * i + fmt <= fmt * N /\ 3 <= fmt <= 4) by (destruct Hfmt as [Hf | Hf]; rewrite Hf; clear - Hi; lia).
set (pix := img + fmt * i). set (c := pxc i). set (h0 := hash0 T c).
assert (Rh0 : 0 <= h0 < T) by (subst h0; apply hash0_range; clear - RT3; lia).
assert (PB : forall j, 0 <= j < fmt -> 0 <= getz imgl (fmt * i + j) < 256).
{ intros j Hj. apply (arr8_getz trasegs _ img imgl (fmt * i + j) Himg). rewrite Himgl. clear - Hfi Hj. lia. }
assert (Cok : colour_ok c).
{ subst c. unfold pxc, YC7c.pxc, colour_ok, cR, cG, cB, mkcol. cbn [fst snd].
pose proof (PB 0 ltac:(clear - Hfi; lia)) as R0. rewrite Z.add_0_r in R0. pose proof (PB 1 ltac:(clear - Hfi; lia)). pose proof (PB 2 ltac:(clear - Hfi; lia)). lia. }
assert (Rpa : (if fmt =? 3 then 0 else 128) <= pxa i <= 255).
{ unfold pxa. destruct (Z.eqb_spec fmt 3) as [|Hn3]; [lia|]. assert (Hf4 : fmt = 4) by (clear - Hfmt Hn3; lia).
pose proof (PB 3 ltac:(clear - Hf4; lia)). pose proof (Hop Hf4). lia. }
assert (Hused1 : usedz (ac_H C) h0 = 1) by (destruct (inv_used01 _ _ Hinv h0 Rh0) as [X | X]; [contradiction | exact X]).
set (vals := hk_vals tb img N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T).
set (xv := [pix; cR c; cG c; cB c; pxa i; ac_u C + h0]).
set (E := Ereg regs (map (Z_to_bv 64) (vals ++ xv))).
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (vals ++ xv) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; clear - Fceil F47 C1; lia).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by exact (HV 0%nat _ eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 (ac_u C)) by exact (HV 3%nat _ eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 T) by exact (HV 7%nat _ eq_refl).
assert (E40 : ew E 40 = Z_to_bv 64 img) by exact (HV 8%nat _ eq_refl).
assert (E28 : ew E 28 = Z_to_bv 64 i) by (rewrite (HE 28%nat 28%bv eq_refl); exact G28).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
destruct (hd_px_side E lyc Sc W mem md i (if fmt =? 3 then 0 else 128) 255 HAR Himgin Hi Himg E25 E28 E40 (HV 20%nat _ eq_refl)
(HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) (HV 24%nat _ eq_refl) Rpa) as (PXR & PXE & PXA & PXL & PXS).
destruct (hd_uh_side E lyc Sc W mem md (ac_u C) T (ht_used (ac_H C)) c 1 HAR Huin Au L1 ltac:(clear - RT2 RT3; lia) Cok E25 E35 E39
(HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) (HV 25%nat _ eq_refl) (eq_sym Hused1)) as (UHR & UHX & UHA & UHL & UHS).
assert (HsepP : pix + fmt <= tb \/ tb + 48 <= pix).
{ pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb C) (img, fmt * N) (tb, CHT_SIZE) HAR HPerm HimgP ltac:(left; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfi; lia)) as [_ Hrq]. subst pix. clear - Hd Hrq Hfi. lia. }
assert (HsepU : ac_u C + h0 + 1 <= tb \/ tb + 48 <= ac_u C + h0).
{ pose proof (sep_blocks trasegs B LAWS lyc Sc W mem md (ac_u C) T tb CHT_SIZE HAR Huin Htbin) as Hd.
destruct (Z.eq_dec (ac_u C) tb) as [Eq | Ne].
- exfalso. pose proof (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & _ & _ & _ & _ & Hpw & _).
assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as _ X; unfold CHT_SIZE in X; clear - X RT3; lia).
specialize (Hd Hne). unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos T ltac:(clear - RT3; lia)). clear - Hd Eq H RT3. lia.
- assert (Hne : (ac_u C, T) <> (tb, CHT_SIZE)) by (intros X; injection X as X _; contradiction).
specialize (Hd Hne). unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size CHT_SIZE) with 48 in Hd.
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ Hrq]. clear - Hd Hrq Rh0. lia. }
assert (HsepPU : pix + fmt <= ac_u C + h0 \/ ac_u C + h0 + 1 <= pix).
{ pose proof (rg_sep_app_in B LAWS lyc Sc W mem md PROT (ac_blocks tb C) (img, fmt * N) (ac_u C, T) HAR HPerm HimgP
ltac:(unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos (fmt * N) ltac:(clear - Hfi; lia)) as [_ Hrq]. pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
subst pix. clear - Hd Hrq HrqT Hfi Rh0. lia. }
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_u C) T HAR Huin) as (_ & Hu4096 & Huceil & _).
pose proof (req_size_pos T ltac:(clear - RT3; lia)) as [_ HrqT].
destruct (hk_seed B LAWS s1v tb img fmt N hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav
HL_HEAD false (HD_PINS fmt) [] [] [] [] [px_reg fmt; uh_reg 1]
(px_atoms (if fmt =? 3 then 0 else 128) 255 ++ [(57%nat, mkAF 4096 140737479966720 0); (39%nat, mkAF 524309 16777216 0); (35%nat, mkAF 4096 140737479966720 0)])
hd_cds [(pxe fmt, SOff 52 0); (UHE, SOff 57 0)] [mkSHE 52 0 fmt; mkSHE 57 0 1]
lyc Sc W regs mem md (ac_f C) (ac_h C) (ac_u C) (ac_p C) (ac_x C) (ht_cnt (ac_H C)) T xv
HAR Htbin HOP ltac:(clear - Hfmt; lia) ltac:(clear - HN; lia) ltac:(clear - Hi4096 Hiceil C1 Hfi; lia)
G9 G25 Fceil F47 F32 Fpres Hsl Hobj) as [HS SHOK].
all: fold vals; fold E.
{ destruct Hfmt as [Hf | Hf]; rewrite Hf; reflexivity. }
{ reflexivity. }
{ unfold HD_PINS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
- rewrite G5. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G6. symmetry. apply denot_off; [exact E32 | clear - Htb4096 Htbceil C1; lia].
- rewrite G7. reflexivity. }
{ apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. } { apply Forall_nil. }
{ apply Forall_cons; [exact (Forall_inv PXR) | exact UHR]. }
{ intros e [<- | [<- | []]]; [rewrite PXE | rewrite UHX]; cbn [fst snd]; fold pix; fold h0.
- clear - HsepP Hiceil Hfi. subst pix. lia.
- clear - HsepU Huceil HrqT Rh0. lia. }
{ cbn [map zpairwise_disjoint zall_disjoint]. rewrite PXE, UHX. unfold zdisj. cbn [fst snd]. fold pix. fold h0. clear - HsepPU. tauto. }
{ apply atoms_ok_app; [exact PXA|]. destruct UHA as [UHA _]. cbn [atoms_ok]. split; [exact UHA|]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E39, E35. rewrite !unsigned_lit_small by (clear - RT1 RT3 Hu4096 Huceil HrqT C1; unfold MAX_TABLE_SIZE in RT1; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r. assert (HT5 : 524309 <= T) by (clear - HTc; cbv [ts_chain In] in HTc; lia). unfold MAX_TABLE_SIZE in RT1.
clear - RT1 HT5 Hu4096 Huceil HrqT C1. repeat split; lia. }
{ unfold hd_cds. destruct (Z.eqb_spec fmt 3) as [|Hn3]; [exact I|]. cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
assert (Hf4 : fmt = 4) by (clear - Hfmt Hn3; lia).
rewrite (branch_lt_sext8 E 56 (pxa i) (HV 24%nat _ eq_refl)) by (clear - Rpa; destruct (fmt =? 3); lia).
apply Z.leb_le. clear - Rpa Hn3. destruct (Z.eqb_spec fmt 3); [contradiction | lia]. }
{ cbn [alias_ok]. destruct PXL as [PXL _]. destruct UHL as [UHL _]. auto. }
{ apply Forall_cons; [exact (Forall_inv PXS) | exact UHS]. }
assert (HAE : env_agree 58 E E) by (apply env_agree_refl).
unfold hd_cds in HS. destruct Hfmt as [Hf | Hf]; rewrite Hf in HS, SHOK.
{ aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_bcmp_tra.
{ apply (hk_awr_ok s1v tb 3 _ false [] [] [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb 3 _ false [] [] [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | [<- | []]] & Hr); cbn [px_reg uh_reg YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; clear - Hr; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e v, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 v)
by (intros r e v Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SP72 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 28 0)] 72 (SOff 28 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 28 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E28 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 29 0)] 56 (SOff 29 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 29 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; rewrite (HE 29%nat 29%bv eq_refl); exact G29 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
assert (UH : U E HSHE = h0) by exact (U_HSHE E c T (HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) Cok E39 ltac:(clear - RT2 RT3; lia)).
assert (DH : sv_denot E HSHE = Z_to_bv 64 h0) by (rewrite denot_lit_U, UH; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as (_ & Hh4096 & Hhceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
assert (Ec0 : cyc T h0 0 = h0) by (apply cyc_0; exact Rh0).
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72 | exact SP56]|].
assert (R20 : getr (ms_regs ms) 20 = Z_to_bv 64 pix).
{ apply (RD 20%bv (SOff 52 0) pix eq_refl); [rewrite (denot_off E 52 pix 0 (HV 20%nat _ eq_refl)), Z.add_0_r; [reflexivity | subst pix; clear - Hi4096 Hiceil C1 Hfi; lia] | reflexivity]. }
split.
{ unfold hprobe_regs. change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) 0) with (cyc T h0 0). change (ac_T C) with T. rewrite Ec0.
split; [exact R20|].
split; [apply (RD 21%bv (SOff 39 0) T eq_refl); [rewrite (denot_off E 39 T 0 E39), Z.add_0_r; [reflexivity | clear - RT2 RT3; lia] | reflexivity]|].
split; [apply (RD 22%bv (SOff 34 0) (ac_h C) eq_refl); [rewrite (denot_off E 34 (ac_h C) 0 (HV 2%nat _ eq_refl)), Z.add_0_r; [reflexivity | clear - Hh4096 Hhceil C1 HrqK RT3; lia] | reflexivity]|].
split; [apply (RD 23%bv (SOff 35 0) (ac_u C) eq_refl); [rewrite (denot_off E 35 (ac_u C) 0 E35), Z.add_0_r; [reflexivity | clear - Hu4096 Huceil HrqT C1 RT3; lia] | reflexivity]|].
split; [exact (RD 24%bv (SLit 0) 0 eq_refl eq_refl eq_refl) | exact (RD 26%bv HSHE h0 eq_refl DH eq_refl)]. }
destruct (find_off_exists _ _ Hinv c) as (js & Ejs).
split; [exists js; split; [exact Ejs | split; [lia | exact (find_off_ge0' _ _ _ _ Hinv Ejs)]]|].
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) 0) with (cyc T h0 0). rewrite Ec0.
split; [exact Hused0|].
split; [apply (RD 10%bv (SOff 52 0) pix eq_refl); [rewrite (denot_off E 52 pix 0 (HV 20%nat _ eq_refl)), Z.add_0_r; [reflexivity | subst pix; clear - Hi4096 Hiceil C1 Hfi; lia] | reflexivity]|].
split.
{ apply (RD 11%bv (SAlu ALU_ADD (SOff 34 0) (ZXE (TRIPLE HSHE))) (ac_h C + 3 * h0) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply (U_base_triple E 34 (ac_h C) HSHE h0 (HV 2%nat _ eq_refl)); [clear - Hh4096; lia | clear - Hhceil HrqK Rh0 C1; lia | exact UH | clear - Rh0 RT2; lia]. }
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit 534492) HL_BR eq_refl eq_refl eq_refl)]. }
{ aj_run_to_tok tratbl_lib_ok HS HJ SHOK hk_Bspan A_bcmp_tra.
{ apply (hk_awr_ok s1v tb 4 _ false [] [] [] [] _ STK sp0 FP _ _ lyc own U9 Hs1 HSTK U32); [intros X; discriminate X|].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAE1 : env_agree 58 E Ex) by (env_agree_chain HAE) end.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> aview trasegs (w_H W) (ms_mem ms) a = aview trasegs (w_H W) mem a).
{ intros a Ha Hn. apply (hk_frame_kept s1v tb 4 _ false [] [] [] [] _ _ _ _ HFr); [exact U9 | exact U32 | exact Ha | exact Hn | intros X; discriminate X|].
intros (rr & [<- | [<- | []]] & Hr); cbn [px_reg uh_reg YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; clear - Hr; lia. }
assert (HAE32 : env_agree 32 (Ereg regs (map (Z_to_bv 64) (vals ++ xv))) _) by (apply (env_agree_le 58 32); [lia | exact HAE1]).
pose proof (regs_kept_of_st_ok trasegs _ _ _ regs _ (HK_CONST ++ [27]%bv) HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
assert (RD : forall (r : bv 5) e v, sr_get (ss_regs ssx) r = e -> sv_denot E e = Z_to_bv 64 v -> sv_atoms_lt 58 e = true -> getr (ms_regs ms) r = Z_to_bv 64 v)
by (intros r e v Q Dv Hat; rewrite (st_ok_restrict_reg trasegs (w_H W) Ex ssx ms r HS), Q; rewrite (sv_denot_agree 58 E Ex e HAE1 Hat); exact Dv);
assert (SP72 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 72) 8 i)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 2%nat 72 80 72 80 [ck 72 (SOff 28 0)] 72 (SOff 28 0) i HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 28 i 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; exact E28 | clear - Hi HN; lia] | clear - Hi HN; lia]);
assert (SP56 : val_mem trasegs (mrestrict (w_H W) (ms_mem ms)) (s1v + 56) 8 ha)
by (apply (hk_slot_of_state s1v Ex ssx ms (w_H W) 1%nat 56 64 56 64 [ck 56 (SOff 29 0)] 56 (SOff 29 0) ha HS eq_refl ltac:(left; reflexivity));
[rewrite (proj1 HAE1) by lia; exact U9 | rewrite (denot_off Ex 29 ha 0), Z.add_0_r; [reflexivity | rewrite (proj1 HAE1) by lia; rewrite (HE 29%nat 29%bv eq_refl); exact G29 | clear - Hha; lia] | clear - Hha; lia]) end.
rewrite (st_ok_restrict_mkst trasegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc]. apply SRr_ret.
split; [reflexivity|]. eexists _, _, _. split; [reflexivity|].
assert (UH : U E HSHE = h0) by exact (U_HSHE E c T (HV 21%nat _ eq_refl) (HV 22%nat _ eq_refl) (HV 23%nat _ eq_refl) Cok E39 ltac:(clear - RT2 RT3; lia)).
assert (DH : sv_denot E HSHE = Z_to_bv 64 h0) by (rewrite denot_lit_U, UH; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc W mem md (ac_h C) (3 * T) HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_app_iff; right; unfold ac_blocks, cht_blocks, ac_T; fold T; cbn; tauto)) as (_ & Hh4096 & Hhceil & _).
pose proof (req_size_pos (3 * T) ltac:(clear - RT3; lia)) as [_ HrqK].
assert (Ec0 : cyc T h0 0 = h0) by (apply cyc_0; exact Rh0).
split; [apply (HRS lyc Sc W regs mem md k C _ _ _ HC HJ); [intros r Hr; apply HKR; apply in_or_app; left; exact Hr | intros a Ha H1 _; exact (KM1 a Ha H1)]|].
split; [split; [exact Hi|]; split; [exact Hha|]; split; [exact Hop|]; rewrite (HKR 27%bv ltac:(cbv; tauto)); exact G27|].
split; [exact Hz|]. split; [split; [exact SP72 | exact SP56]|].
assert (R20 : getr (ms_regs ms) 20 = Z_to_bv 64 pix).
{ apply (RD 20%bv (SOff 52 0) pix eq_refl); [rewrite (denot_off E 52 pix 0 (HV 20%nat _ eq_refl)), Z.add_0_r; [reflexivity | subst pix; clear - Hi4096 Hiceil C1 Hfi; lia] | reflexivity]. }
split.
{ unfold hprobe_regs. change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) 0) with (cyc T h0 0). change (ac_T C) with T. rewrite Ec0.
split; [exact R20|].
split; [apply (RD 21%bv (SOff 39 0) T eq_refl); [rewrite (denot_off E 39 T 0 E39), Z.add_0_r; [reflexivity | clear - RT2 RT3; lia] | reflexivity]|].
split; [apply (RD 22%bv (SOff 34 0) (ac_h C) eq_refl); [rewrite (denot_off E 34 (ac_h C) 0 (HV 2%nat _ eq_refl)), Z.add_0_r; [reflexivity | clear - Hh4096 Hhceil C1 HrqK RT3; lia] | reflexivity]|].
split; [apply (RD 23%bv (SOff 35 0) (ac_u C) eq_refl); [rewrite (denot_off E 35 (ac_u C) 0 E35), Z.add_0_r; [reflexivity | clear - Hu4096 Huceil HrqT C1 RT3; lia] | reflexivity]|].
split; [exact (RD 24%bv (SLit 0) 0 eq_refl eq_refl eq_refl) | exact (RD 26%bv HSHE h0 eq_refl DH eq_refl)]. }
destruct (find_off_exists _ _ Hinv c) as (js & Ejs).
split; [exists js; split; [exact Ejs | split; [lia | exact (find_off_ge0' _ _ _ _ Hinv Ejs)]]|].
change (cyc (ac_T C) (hash0 (ac_T C) (pxc i)) 0) with (cyc T h0 0). rewrite Ec0.
split; [exact Hused0|].
split; [apply (RD 10%bv (SOff 52 0) pix eq_refl); [rewrite (denot_off E 52 pix 0 (HV 20%nat _ eq_refl)), Z.add_0_r; [reflexivity | subst pix; clear - Hi4096 Hiceil C1 Hfi; lia] | reflexivity]|].
split.
{ apply (RD 11%bv (SAlu ALU_ADD (SOff 34 0) (ZXE (TRIPLE HSHE))) (ac_h C + 3 * h0) eq_refl); [|reflexivity].
rewrite denot_lit_U. f_equal. apply (U_base_triple E 34 (ac_h C) HSHE h0 (HV 2%nat _ eq_refl)); [clear - Hh4096; lia | clear - Hhceil HrqK Rh0 C1; lia | exact UH | clear - Rh0 RT2; lia]. }
split; [exact (RD 12%bv (SLit 3) 3 eq_refl eq_refl eq_refl) | exact (RD 1%bv (SLit 534492) HL_BR eq_refl eq_refl eq_refl)]. }
Qed.
End H1.
