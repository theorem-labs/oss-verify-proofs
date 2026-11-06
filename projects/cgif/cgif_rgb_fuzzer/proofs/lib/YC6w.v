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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition shx (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 c) (SLit 3)) (SOff 25 0).
Definition ck (off : Z) (e : sv) : YQ0b.chunk := YQ0b.mkChunk off (CVal 8 e).
Definition hk_c0 : list YQ0b.chunk := [ck 16 (SLit 7); ck 24 (SLit 65537); ck 32 (SOff 50 0); ck 40 (SOff 41 0)].
Definition hk_c80 (fmt : Z) : list YQ0b.chunk :=
[ck 80 (SOff 51 0); ck 88 (SLit fmt); ck 96 (SOff 42 0); ck 104 (SLit fmt); ck 112 (SLit 4294967295); ck 120 (SOff 40 0); ck 128 (SOff 43 0); ck 152 (SOff 32 24)].
Definition hk_c184 : list YQ0b.chunk :=
[ck 192 (SOff 44 0); ck 200 (SOff 45 0); ck 208 (SOff 32 0); ck 216 (shx 24); ck 224 (shx 40); ck 232 (shx 32); ck 240 (SOff 32 32); ck 248 (SOff 32 40);
ck 272 (shx 0); ck 280 (SOff 46 0)].
Definition hk_c304 : list YQ0b.chunk :=
[ck 304 (SOff 32 16); ck 312 (SOff 32 44); ck 320 (SOff 32 8); ck 336 (shx 8); ck 352 (shx 16); ck 368 (shx 40); ck 376 (SOff 47 0);
ck 496 (SOff 48 0); ck 504 (SOff 49 0)].
Definition hk_ro (lo hi : Z) (cs : list YQ0b.chunk) : YQ0b.region := YQ0b.mkRegion (Some 9%nat) lo hi 0 0 cs.
Definition hk_rw (lo hi : Z) (cs : list YQ0b.chunk) : YQ0b.region := YQ0b.mkRegion (Some 9%nat) lo hi lo hi cs.
Definition hk_stack (fmt : Z) (c56 c72 c160 c296 : list YQ0b.chunk) : smem :=
[ hk_ro 0 56 hk_c0; hk_rw 56 64 c56; hk_rw 72 80 c72; hk_ro 80 160 (hk_c80 fmt); hk_rw 160 184 c160; hk_ro 184 296 hk_c184; hk_rw 296 304 c296;
hk_ro 304 512 hk_c304 ].
Definition hk_tbreg (rw : bool) : YQ0b.region := YQ0b.mkRegion (Some 32%nat) 0 48 0 (if rw then 48 else 0)
[ ck 0 (SOff 33 0); ck 8 (SOff 34 0); ck 16 (SOff 35 0); ck 24 (SOff 36 0); ck 32 (SOff 37 0);
YQ0b.mkChunk 40 (CVal 4 (SOff 38 0)); YQ0b.mkChunk 44 (CVal 4 (SOff 39 0)) ].
Definition hk_atoms : list (nat * afact) :=
[ (9%nat, mkAF 70368744177664 140737488355328 5); (25%nat, mkAF SB SB 0); (32%nat, mkAF 4096 140737479966720 4) ].
Definition hk_Bx : sv := SOff 25 0.
Definition hk_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition ss_hk (pc fmt : Z) (tbw : bool) (pins : list (bv 5 * sv)) (c56 c72 c160 c296 : list YQ0b.chunk) (elems : smem)
(xat : list (nat * afact)) (cds : list acond) (als : list (sv * sv)) : sstate :=
mkSS pc (sr_sets sr_atoms pins) (hk_stack fmt c56 c72 c160 c296 ++ hk_tbreg tbw :: elems) None (mkFacts (hk_atoms ++ xat) cds als).
Definition wslot (o : Z) : Prop := 56 <= o < 64 \/ 72 <= o < 80 \/ 160 <= o < 184 \/ 296 <= o < 304.
Section HK.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Variables (s1v tb img fmt N : Z).
Variables (hv24 hv27 hv26 hv23 hv18 hv22 hv17 hv16 s0v rav : Z).
Definition hk_tab : list (Z * Z) :=
[ (16, 7); (24, 65537); (32, hv24); (40, hv27);
(80, N); (88, fmt); (96, hv26); (104, fmt); (112, 4294967295); (120, img); (128, hv23); (152, tb + 24);
(192, hv18); (200, hv22); (208, tb); (216, SB + (tb + 24) / 8); (224, SB + (tb + 40) / 8); (232, SB + (tb + 32) / 8); (240, tb + 32); (248, tb + 40);
(272, SB + (tb + 0) / 8); (280, hv17);
(304, tb + 16); (312, tb + 44); (320, tb + 8); (336, SB + (tb + 8) / 8); (352, SB + (tb + 16) / 8); (368, SB + (tb + 40) / 8); (376, hv16);
(496, s0v); (504, rav) ].
Definition hk_slots (m : word -> option byte) : Prop :=
forall off v, In (off, v) hk_tab -> val_mem trasegs m (s1v + off) 8 v.
Definition hk_vals (f h u p x cnt T : Z) : list Z :=
[tb; f; h; u; p; x; cnt; T; img; hv27; hv26; hv23; hv18; hv22; hv17; hv16; s0v; rav; hv24; N].
Definition hk_opaque_ok : Prop :=
0 <= hv24 < 2 ^ 64 /\ 0 <= hv27 < 2 ^ 64 /\ 0 <= hv26 < 2 ^ 64 /\ 0 <= hv23 < 2 ^ 64 /\ 0 <= hv18 < 2 ^ 64 /\ 0 <= hv22 < 2 ^ 64 /\
0 <= hv17 < 2 ^ 64 /\ 0 <= hv16 < 2 ^ 64 /\ 0 <= s0v < 2 ^ 64 /\ 0 <= rav < 2 ^ 64.
Lemma denot_shx : forall E c, ew E 32 = Z_to_bv 64 tb -> ew E 25 = Z_to_bv 64 SB -> 0 <= tb -> tb + c < 2 ^ 47 -> 0 <= c ->
sv_denot E (shx c) = Z_to_bv 64 (SB + (tb + c) / 8).
Proof.
intros E c Hn Hb Hp Hk Hk0. unfold shx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom_off E 32 tb c Hn) by lia. rewrite (U_atom E 25 SB Hb) by (unfold SB; lia).
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((tb + c) / 8)) by (unfold M64; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (0 <= (tb + c) / 8) by (apply Z.div_pos; lia). assert ((tb + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
rewrite (Z.add_comm SB). apply zcanon_id. unfold M64, SB. lia.
Qed.
Lemma denot_off : forall E n p c, ew E n = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (p + c).
Proof. intros E n p c Hn Hp. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by lia. reflexivity. Qed.
Lemma denot_lit : forall E v, sv_denot E (SLit v) = Z_to_bv 64 v.
Proof. intros. reflexivity. Qed.
Lemma hk_chunk_ok : forall E m off e v,
hk_slots m -> In (off, v) hk_tab -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
YQ0b.chunk_ok trasegs E m s1v (ck off e).
Proof.
intros E m off e v Hs Hin He Hv. unfold ck.
apply (chunk_ok_val trasegs E m s1v off 8 e v He); [exact Hv | lia | exact (Hs off v Hin)].
Qed.
Lemma zall_disjoint_app : forall a l1 l2, zall_disjoint a l1 -> zall_disjoint a l2 -> zall_disjoint a (l1 ++ l2).
Proof. intros a l1 l2 H1 H2. induction l1 as [|b l1 IH]; [exact H2|]. destruct H1 as [Hb H1]. split; [exact Hb | exact (IH H1)]. Qed.
Lemma zpairwise_disjoint_app : forall l1 l2, zpairwise_disjoint l1 -> zpairwise_disjoint l2 ->
(forall a, In a l1 -> zall_disjoint a l2) -> zpairwise_disjoint (l1 ++ l2).
Proof.
intros l1 l2 H1 H2 H12. induction l1 as [|a l1 IH]; [exact H2|]. destruct H1 as [Ha H1]. split.
- apply zall_disjoint_app; [exact Ha | apply H12; left; reflexivity].
- apply IH; [exact H1 | intros b Hb; apply H12; right; exact Hb].
Qed.
Lemma zall_disjoint_forall : forall a l, (forall b, In b l -> zdisj a b) -> zall_disjoint a l.
Proof. intros a l H. induction l as [|b l IH]; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros c Hc; apply H; right; exact Hc]. Qed.
Lemma atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; [exact H2|]. destruct H1 as [Hc Hr]. split; [exact Hc | exact (IH Hr)]. Qed.
Lemma hk_seed : forall pc (tbw : bool) (pins : list (bv 5 * sv)) (c56 c72 c160 c296 : list YQ0b.chunk) (elems : smem)
(xat : list (nat * afact)) (cds : list acond) (als : list (sv * sv)) (SHx : list shent)
lyc Sc (W : world trasegs) (regs : bvmap 5 word) (mem : word -> option byte) md (f h u p x cnt T : Z) (xv : list Z),
let E := Ereg regs (map (Z_to_bv 64) (hk_vals f h u p x cnt T ++ xv)) in
let m := mrestrict (w_H W) mem in
AR trasegs B lyc Sc W mem md -> In (tb, CHT_SIZE) (ablocks B lyc Sc) ->
hk_opaque_ok -> 0 <= fmt < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= img < 2 ^ 64 ->
getr regs 9 = Z_to_bv 64 s1v -> getr regs 25 = Z_to_bv 64 SB ->
alloc_ceiling <= s1v -> s1v + 512 <= 2 ^ 47 -> s1v mod 32 = 0 ->
(forall a, s1v <= a < s1v + 512 -> apresent (w_H W) mem a) ->
hk_slots m ->
obj_at trasegs m tb LAY_Cht [f; h; u; p; x; cnt; T] ->
regions_wf (hk_stack fmt c56 c72 c160 c296 ++ hk_tbreg tbw :: elems) = true ->
reg_nodup (map fst pins) = true -> Forall (fun q => bv_eqb (fst q) 0 = false /\ getr regs (fst q) = sv_denot E (snd q)) pins ->
Forall (YQ0b.chunk_ok trasegs E m s1v) c56 -> Forall (YQ0b.chunk_ok trasegs E m s1v) c72 ->
Forall (YQ0b.chunk_ok trasegs E m s1v) c160 -> Forall (YQ0b.chunk_ok trasegs E m s1v) c296 ->
Forall (region_ok trasegs E m) elems ->
(forall e, In e elems -> snd (extent_of_region E e) <= alloc_ceiling /\
(snd (extent_of_region E e) <= tb \/ tb + 48 <= fst (extent_of_region E e))) ->
zpairwise_disjoint (map (extent_of_region E) elems) ->
atoms_ok E xat -> conds_ok E cds -> alias_ok E als ->
Forall (shent_ok trasegs hk_Bx E m) SHx ->
st_ok trasegs E (ss_hk pc fmt tbw pins c56 c72 c160 c296 elems xat cds als)
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom trasegs))) /\
sh_ok trasegs hk_Bx (mkSHE 32 0 48 :: SHx) E m.
Proof.
intros pc tbw pins c56 c72 c160 c296 elems xat cds als SHx lyc Sc W regs mem md f h u p x cnt T xv E m
HAR Htb HOP Hfmt HN Himg G9 G25 Hceil Hs47 Hal Hpres Hsl Hobj Hwf Hnd Hpins H56 H72 H160 H296 Hel Helx Held Hxat Hcds Hals HSHx.
destruct HOP as (O24 & O27 & O26 & O23 & O18 & O22 & O17 & O16 & Os0 & Ora).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS lyc Sc W mem md tb CHT_SIZE HAR Htb) as (Htb16 & Htb4096 & Htbceil & Htbapp & Htbpres & _ & _).
change (req_size CHT_SIZE) with 48 in Htbceil, Htbpres, Htbapp.
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HV : forall j v, nth_error (hk_vals f h u p x cnt T) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. rewrite map_app. apply Ereg_vals. exact Hj. }
assert (E9 : ew E 9 = Z_to_bv 64 s1v) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (E25 : ew E 25 = Z_to_bv 64 SB) by (rewrite (HE 25%nat 25%bv eq_refl); exact G25).
assert (E32 : ew E 32 = Z_to_bv 64 tb) by (exact (HV 0%nat _ eq_refl)).
assert (U9 : bv_unsigned (ew E 9) = s1v) by (rewrite E9; apply unsigned_lit_small; clear - Hceil Hs47 C1; lia).
assert (U32 : bv_unsigned (ew E 32) = tb) by (rewrite E32; apply unsigned_lit_small; clear - Htb4096 Htbceil C1; lia).
assert (Htb47 : 0 <= tb /\ tb + 48 < 2 ^ 47) by (clear - Htb4096 Htbceil C1; lia).
pose proof Hobj as OBJ. cbn [obj_at LAY_Cht] in OBJ. unfold field_ok in OBJ. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add] in OBJ.
destruct OBJ as ([Vf Bf] & [Vh Bh] & [Vu Bu] & [Vp Bp] & [Vx Bx] & [Vc Bc] & [VT BT] & _).
assert (Dsh : forall c, 0 <= c <= 40 -> sv_denot E (shx c) = Z_to_bv 64 (SB + (tb + c) / 8))
by (intros c Hc; apply denot_shx; [exact E32 | exact E25 | lia | lia | lia]).
assert (Dtb : forall c, sv_denot E (SOff 32 c) = Z_to_bv 64 (tb + c)) by (intros c; apply denot_off; [exact E32 | lia]).
assert (Dat : forall j v, nth_error (hk_vals f h u p x cnt T) j = Some v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 v).
{ intros j v Hj Hv. rewrite (denot_off E (32 + j) v 0 (HV j v Hj) Hv), Z.add_0_r. reflexivity. }
assert (Hshr : forall c, 0 <= c <= 40 -> 0 <= SB + (tb + c) / 8 < 2 ^ 64).
{ intros c Hc. assert (0 <= (tb + c) / 8) by (apply Z.div_pos; lia). assert ((tb + c) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). unfold SB. lia. }
split.
- rewrite restrict_mkst_fx. unfold ss_hk. apply (entry_st_ok_full trasegs).
+ apply (regs_ok_sets E sr_atoms regs regs pins); [apply regs_ok_Ereg | exact (reg_nodup_sound _ Hnd) | intros; reflexivity | exact Hpins].
+ exact Hwf.
+ apply Forall_app. split; [|apply Forall_cons; [|exact Hel]].
*
assert (Hbnd : forall lo hi, 0 <= lo -> hi <= 512 -> 0 <= s1v + lo /\ s1v + hi <= 2 ^ 64) by (intros; clear - Hceil Hs47 C1 H H0; lia).
assert (Hwr : forall o, 0 <= o < 512 -> writable_at trasegs m (s1v + o)).
{ intros o Ho. apply (apresent_writable trasegs). apply Hpres. lia. }
unfold hk_stack. repeat apply Forall_cons; try apply Forall_nil; unfold hk_ro, hk_rw, region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; fold E; rewrite U9;
(split; [clear - Hceil C1; lia|]); (split; [clear - Hs47; lia|]); (split; [intros o Ho; first [apply Hwr; lia | exfalso; clear - Ho; lia]|]).
-- unfold hk_c0. repeat apply Forall_cons; try apply Forall_nil.
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply denot_lit | lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply denot_lit | lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 18%nat _ eq_refl O24) | exact O24].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 9%nat _ eq_refl O27) | exact O27].
-- exact H56.
-- exact H72.
-- unfold hk_c80. repeat apply Forall_cons; try apply Forall_nil.
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 19%nat _ eq_refl HN) | exact HN].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply denot_lit | exact Hfmt].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 10%nat _ eq_refl O26) | exact O26].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply denot_lit | exact Hfmt].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply denot_lit | lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 8%nat _ eq_refl Himg) | exact Himg].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 11%nat _ eq_refl O23) | exact O23].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dtb | clear - Htb47; lia].
-- exact H160.
-- unfold hk_c184. repeat apply Forall_cons; try apply Forall_nil.
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 12%nat _ eq_refl O18) | exact O18].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 13%nat _ eq_refl O22) | exact O22].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | rewrite (Dtb 0), Z.add_0_r; reflexivity | clear - Htb47; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dtb | clear - Htb47; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dtb | clear - Htb47; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 14%nat _ eq_refl O17) | exact O17].
-- exact H296.
-- unfold hk_c304. repeat apply Forall_cons; try apply Forall_nil.
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dtb | clear - Htb47; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dtb | clear - Htb47; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dtb | clear - Htb47; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | apply Dsh; lia | apply Hshr; lia].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 15%nat _ eq_refl O16) | exact O16].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 16%nat _ eq_refl Os0) | exact Os0].
++ eapply hk_chunk_ok; [exact Hsl | cbn; tauto | exact (Dat 17%nat _ eq_refl Ora) | exact Ora].
*
unfold hk_tbreg, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U32.
split; [clear - Htb47; lia|]. split; [clear - Htb47; lia|].
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (Htbpres (tb + o) ltac:(clear - Ho; destruct tbw; lia)))|].
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Bf, Bh, Bu, Bp, Bx.
repeat apply Forall_cons; try apply Forall_nil.
-- apply (chunk_ok_val trasegs E m tb 0 8 _ f); [exact (Dat 1%nat _ eq_refl Bf) | exact Bf | lia | exact Vf].
-- apply (chunk_ok_val trasegs E m tb 8 8 _ h); [exact (Dat 2%nat _ eq_refl Bh) | exact Bh | lia | exact Vh].
-- apply (chunk_ok_val trasegs E m tb 16 8 _ u); [exact (Dat 3%nat _ eq_refl Bu) | exact Bu | lia | exact Vu].
-- apply (chunk_ok_val trasegs E m tb 24 8 _ p); [exact (Dat 4%nat _ eq_refl Bp) | exact Bp | lia | exact Vp].
-- apply (chunk_ok_val trasegs E m tb 32 8 _ x); [exact (Dat 5%nat _ eq_refl Bx) | exact Bx | lia | exact Vx].
-- apply (chunk_ok_val trasegs E m tb 40 4 _ cnt); [apply (Dat 6%nat _ eq_refl); clear - Bc; cbn in Bc; lia | exact Bc | lia | exact Vc].
-- apply (chunk_ok_val trasegs E m tb 44 4 _ T); [apply (Dat 7%nat _ eq_refl); clear - BT; cbn in BT; lia | exact BT | lia | exact VT].
+ apply pairwise_disjoint_of_extents. rewrite map_app. apply zpairwise_disjoint_app.
* unfold hk_stack, hk_ro, hk_rw, extent_of_region. cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U9.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. clear. repeat split; lia.
* cbn [map]. split; [|exact Held].
apply zall_disjoint_forall. intros b Hb. apply in_map_iff in Hb as (e & <- & He). destruct (Helx e He) as [_ Hd].
unfold zdisj, extent_of_region, hk_tbreg in Hd |- *. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val] in Hd |- *. fold E in Hd |- *. rewrite U32. clear - Hd. lia.
* intros a Ha. unfold hk_stack, hk_ro, hk_rw, extent_of_region in Ha. cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val In] in Ha. fold E in Ha. rewrite U9 in Ha.
cbn [map]. split.
{ unfold zdisj, extent_of_region, hk_tbreg. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U32.
clear - Ha Htbceil Hceil. repeat (destruct Ha as [<- | Ha]; [cbn [fst snd]; lia|]). destruct Ha. }
apply zall_disjoint_forall. intros b Hb. apply in_map_iff in Hb as (e & <- & He). destruct (Helx e He) as [Hc _].
unfold zdisj. fold E. set (xe := extent_of_region E e) in *. clearbody xe. clear - Ha Hc Hceil. repeat (destruct Ha as [<- | Ha]; [cbn [fst snd]; lia|]). destruct Ha.
+ split; [|split; [exact Hcds | exact Hals]].
cbn [f_atoms]. apply atoms_ok_app; [|exact Hxat].
cbn [hk_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite U9, U32, E25.
rewrite unsigned_lit_small by (unfold SB; lia). change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
clear - Hceil Hs47 Hal C1 Htb16 Htb4096 Htbceil. repeat split; lia.
- unfold sh_ok. apply Forall_cons; [|exact HSHx].
apply (shent_ok_of_block trasegs B LAWS lyc Sc W mem md E hk_Bx 32 tb CHT_SIZE 0 48 HAR Htb).
+ unfold U, hk_Bx. cbn [sv_denot]. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U32.
+ lia.
+ change (req_size CHT_SIZE) with 48. lia.
Qed.
Lemma hk_awr_ok : forall E tbw c56 c72 c160 c296 elems STK sp0 FP bl0 blc lyq own,
bv_unsigned (ew E 9) = s1v -> s1v = sp0 - 512 -> 512 <= STK ->
bv_unsigned (ew E 32) = tb -> (tbw = true -> forall a, tb <= a < tb + 48 -> awr_byte STK sp0 FP bl0 blc lyq own a) ->
awr_ok E elems STK sp0 FP bl0 blc lyq own ->
awr_ok E (hk_stack fmt c56 c72 c160 c296 ++ hk_tbreg tbw :: elems) STK sp0 FP bl0 blc lyq own.
Proof.
intros E tbw c56 c72 c160 c296 elems STK sp0 FP bl0 blc lyq own U9 Hs1 HSTK U32 Htbw Hel.
unfold hk_stack, hk_ro, hk_rw. cbn [app].
repeat first
[ apply awr_ok_cons_ro; [cbn [YQ0b.r_wlo YQ0b.r_whi]; lia|]
| eapply (awr_ok_cons_stack_off E _ _ STK sp0 FP bl0 blc lyq own 9%nat (-512));
[reflexivity | rewrite U9, Hs1; lia | cbn [YQ0b.r_wlo]; lia | cbn [YQ0b.r_whi]; lia |] ].
eapply (awr_ok_cons_gen E _ _ STK sp0 FP bl0 blc lyq own 32%nat tb); [reflexivity | exact U32 | | exact Hel].
unfold hk_tbreg. cbn [YQ0b.r_wlo YQ0b.r_whi]. intros a Ha. destruct tbw; [apply Htbw; [reflexivity | lia] | exfalso; lia].
Qed.
Lemma hk_frame_kept : forall E tbw c56 c72 c160 c296 elems (H : word -> bool) (m m' : word -> option byte),
frame_of E (hk_stack fmt c56 c72 c160 c296 ++ hk_tbreg tbw :: elems) (mrestrict H m) (mrestrict H m') ->
bv_unsigned (ew E 9) = s1v -> bv_unsigned (ew E 32) = tb ->
forall a, 0 <= a < 2 ^ 64 -> ~ (s1v <= a < s1v + 512 /\ wslot (a - s1v)) -> (tbw = true -> ~ (tb <= a < tb + 48)) -> ~ in_wrange E elems a ->
aview trasegs H m' a = aview trasegs H m a.
Proof.
intros E tbw c56 c72 c160 c296 elems H m m' HF U9 U32 a Ha Hns Hnt Hne. apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. intros (rr & Hin & Hr). apply in_app_iff in Hin. destruct Hin as [Hin | [<- | Hin]].
- unfold hk_stack, hk_ro, hk_rw in Hin. cbn [In] in Hin. unfold wslot in Hns.
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia|]). destruct Hin.
- unfold hk_tbreg in Hr. cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr. rewrite U32 in Hr.
destruct tbw; [apply Hnt; [reflexivity | lia] | lia].
- apply Hne. exists rr. split; [exact Hin | exact Hr].
Qed.
Lemma hk_slot_of_state : forall E ss ms (H : word -> bool) idx lo hi wlo whi cs off e v,
st_ok trasegs E ss (restrict H ms) -> nth_error (ss_mem ss) idx = Some (YQ0b.mkRegion (Some 9%nat) lo hi wlo whi cs) -> In (ck off e) cs ->
bv_unsigned (ew E 9) = s1v -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
val_mem trasegs (mrestrict H (ms_mem ms)) (s1v + off) 8 v.
Proof.
intros E ss ms H idx lo hi wlo whi cs off e v HS Hnth Hin U9 He Hv.
destruct (st_ok_mem_ok trasegs E ss _ HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hnth)) as HR. cbn [ms_mem restrict] in HR.
exact (field_of_region E _ 9 s1v cs lo hi wlo whi off 8%N e v HR U9 Hin He Hv ltac:(lia)).
Qed.
End HK.
