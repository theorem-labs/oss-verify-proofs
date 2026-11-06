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
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfx YCe9 YCi1 YCib YCia YCi8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c YI0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition CH_ARR : Z := 0x85268.
Definition CH_NEXT : Z := 0x85268.
Definition CH_BRET : Z := 0x852b0.
Definition CH_GPRET : Z := 0x851d4.
Definition LAY_CHF : layout_t := [(8, 8%N); (16, 8%N); (24, 8%N); (32, 8%N); (40, 8%N); (48, 8%N); (56, 8%N); (64, 8%N); (72, 8%N)].
Definition chf_vals (regs : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs 23); bv_unsigned (getr regs 22); bv_unsigned (getr regs 21); bv_unsigned (getr regs 20); bv_unsigned (getr regs 19);
bv_unsigned (getr regs 18); bv_unsigned (getr regs 9); bv_unsigned (getr regs 8); bv_unsigned (getr regs 1)].
Section CH.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ABCMP : abcmp_realizes trbsegs B A_bcmp_tra.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Definition ch_Bx : sv := SOff 32 0.
Definition ch_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma denot_of_U : forall E v z, U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Local Ltac rreg_by HS r v pf H :=
lazymatch type of HS with st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (H : getr rg r = v) by (refine (eq_trans (st_ok_restrict_reg segs Hh Ex ss ms r HS) _); change (sv_denot Ex e = v); exact pf) end.
Definition CH_KEPT : list (bv 5) := [3; 4; 24; 25; 26; 27]%bv.
Definition chl_mem : smem :=
[ YQ0b.mkRegion (Some 2%nat) 0 80 0 0 (obj_chunks_from LAY_CHF 32);
YQ0b.mkRegion (Some 41%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 42 0))] ].
Definition chl_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 1 (2^30) 0); (9%nat, mkAF 4096 140737479966720 0);
(18%nat, mkAF 4096 140737479966720 0); (19%nat, mkAF 4096 140737479966720 0); (20%nat, mkAF 0 (2^30) 0);
(21%nat, mkAF SB SB 0); (22%nat, mkAF 18446603336229584895 18446744073709547519 0); (23%nat, mkAF 1 1 0);
(41%nat, mkAF 4096 140737479966720 0); (42%nat, mkAF 0 255 0) ] []
[(SAlu ALU_ADD (SOff 9 0) (SOff 20 0), SOff 41 0)].
Definition ss_chl (pin : bool) (pc : Z) : sstate :=
mkSS pc (if pin then sr_set sr_atoms 10%bv (SOff 41 0) else sr_atoms) chl_mem None chl_facts.
Definition chl_Bx : sv := SOff 21 0.
Definition chl_SH : list shent := [ mkSHE 41 0 1 ].
Definition chl_extra (regs0 : bvmap 5 word) (uh ub : Z) : list word := map (Z_to_bv 64) (chf_vals regs0 ++ [uh; ub]).
Definition at_st ly S (W : world trbsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (rgb keys u T hj : Z)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
ajournal trbsegs B TCOLHASH_STK (spZ regs) [] ly S W mem md [] ly S W mem1 md1 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCOLHASH_STK <= a < spZ regs) ->
aview trbsegs (w_H W) mem1 a = aview trbsegs (w_H W) mem a) /\
obj_at trbsegs (mrestrict (w_H W) mem1) (spZ regs - 80) LAY_CHF (chf_vals regs) /\
getr regs1 2 = w64 (spZ regs - 80) /\ getr regs1 20 = w64 hj /\
getr regs1 8 = w64 T /\ getr regs1 9 = w64 u /\ getr regs1 18 = w64 keys /\ getr regs1 19 = w64 rgb /\ getr regs1 21 = w64 SB /\
getr regs1 22 = w64 (2 ^ 64 - 1 - u) /\ getr regs1 23 = w64 1 /\
(forall rr : bv 5, In rr CH_KEPT -> getr regs1 rr = getr regs rr).
Lemma u64_range8 : forall w : word, 0 <= bv_unsigned w < 2 ^ (8 * Z.of_N 8).
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in H. lia. Qed.
Lemma ch_seed : forall (pin : bool) pc ly S W (regs : bvmap 5 word) mem md ch (rgb keys u Nu T hj ub : Z) (regs1 : bvmap 5 word) mem1 md1,
afn_pre trbsegs B TCOLHASH_STK ly S W regs mem md ch ->
at_st ly S W regs mem md rgb keys u T hj regs1 mem1 md1 ->
In (u, Nu) (ablocks B ly S) -> T <= Nu -> 0 < T < 2 ^ 30 -> 0 <= hj < T ->
4096 <= rgb <= 140737479966720 -> 4096 <= keys <= 140737479966720 ->
mbyte trbsegs (mrestrict (w_H W) mem) (u + hj) = Some (Z_to_bv 8 ub) -> 0 <= ub < 256 ->
(pin = true -> getr regs1 10 = w64 (u + hj)) ->
let E := Ereg regs1 (chl_extra regs (u + hj) ub) in
st_ok trbsegs E (ss_chl pin pc) (restrict (w_H W) (mkst regs1 (Z_to_bv 64 pc) mem1 (seg_rom trbsegs)))
/\ sh_ok trbsegs chl_Bx chl_SH E (mrestrict (w_H W) mem1).
Proof.
intros pin pc ly S W regs mem md ch rgb keys u Nu T hj ub regs1 mem1 md1 HPRE HA Hu HNu RT Rhj Rrgb Rkeys Bu Rub G10 E.
destruct HA as (HJ1 & Hkept & Ofr & G2 & G20 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TCOLHASH_STK = 8272) by reflexivity.
pose proof (proj1 HJ1) as HAR1.
destruct (al_blocks _ _ LAWS ly S W mem md u Nu HAR Hu) as (_ & Hu4096 & Huceil & Huh_ia & _ & _ & HNu0).
pose proof (blk_off_img _ _ _ _ _ _ u Nu HAR Hu) as Huh_img.
pose proof (req_size_pos Nu ltac:(lia)) as [_ HrNu].
set (sp := spZ regs) in *.
assert (Hspr : 0 <= sp - 80 /\ sp < 2 ^ 64) by (clear - Hslo Hshi H47 Hceil C1 WS Hstk0; lia).
rewrite restrict_mkst_fx.
assert (HE : forall j (rr : bv 5), Z.of_nat j = bv_unsigned rr -> ew E j = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVF : forall j v, nth_error (chf_vals regs ++ [u + hj; ub]) j = Some v -> ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. unfold chl_extra. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hj. }
assert (E39 : ew E 41 = Z_to_bv 64 (u + hj)) by (exact (HVF 9%nat _ eq_refl)).
assert (E40 : ew E 42 = Z_to_bv 64 ub) by (exact (HVF 10%nat _ eq_refl)).
assert (E2 : ew E 2 = w64 (sp - 80)) by (rewrite (HE 2%nat 2%bv eq_refl); exact G2).
assert (E8 : ew E 8 = w64 T) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
assert (E9 : ew E 9 = w64 u) by (rewrite (HE 9%nat 9%bv eq_refl); exact G9).
assert (E18 : ew E 18 = w64 keys) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (E19 : ew E 19 = w64 rgb) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (E22 : ew E 22 = w64 (2 ^ 64 - 1 - u)) by (rewrite (HE 22%nat 22%bv eq_refl); exact G22).
assert (E23 : ew E 23 = w64 1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (E20 : ew E 20 = w64 hj) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E21 : ew E 21 = w64 SB) by (rewrite (HE 21%nat 21%bv eq_refl); exact G21).
assert (U2 : bv_unsigned (ew E 2) = sp - 80) by (rewrite E2; apply unsigned_lit_small; clear - Hspr; lia).
assert (U39 : bv_unsigned (ew E 41) = u + hj) by (rewrite E39; apply unsigned_lit_small; clear - Hu4096 Huceil HrNu HNu Rhj C1; lia).
assert (Bu1 : mbyte trbsegs (mrestrict (w_H W) mem1) (u + hj) = Some (Z_to_bv 8 ub)).
{ rewrite <- Bu. apply (mbyte_of_aview trbsegs). apply Hkept; [clear - Hu4096 Huceil HrNu HNu Rhj C1; lia|].
fold sp. clear - Huceil HrNu HNu Rhj Hceil Hslo WS. lia. }
split.
- unfold ss_chl. apply (entry_st_ok_full trbsegs).
+ destruct pin; [|apply regs_ok_Ereg]. apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |].
rewrite (G10 eq_refl). cbn [sv_denot]. fold E. rewrite U39, Z.add_0_r. reflexivity.
+ destruct pin; vm_compute; reflexivity.
+ unfold chl_mem. repeat apply Forall_cons; try apply Forall_nil.
* eapply (region_ok_obj_gen trbsegs _ _ 2 (sp - 80)); [exact U2 | clear - Hspr; lia | clear - Hspr; lia | exact Ofr | reflexivity | | intros j z Hj; destruct j; discriminate Hj | intros i Hi; lia].
intros j v Hj. apply HVF. rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence].
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E. rewrite U39.
split; [clear - Hu4096 Rhj; lia|]. split; [clear - Huceil HrNu HNu Rhj C1; lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val trbsegs E _ (u + hj) 0 1 _ ub); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. apply (val_mem_byte trbsegs); assumption.
+ apply pairwise_disjoint_of_extents. unfold chl_mem, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E. rewrite U2, U39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Huceil HrNu HNu Rhj Hceil Hslo WS Hstk0. subst sp. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [chl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
rewrite U2, U39, E8, E9, E18, E19, E20, E21, E22, E23, E40. unfold w64.
rewrite !unsigned_lit_small by (unfold SB; clear - Hu4096 Huceil HrNu HNu RT Rhj Rrgb Rkeys Rub C1; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
assert (Hal80 : (sp - 80) mod 16 = 0) by (clear - Hal16; subst sp; rewrite Zminus_mod, Hal16; reflexivity).
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 Hu4096 Huceil HrNu HNu RT Rhj Rrgb Rkeys Rub Hal80. clear.
unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
* cbn [chl_facts f_alias alias_ok]. split; [|exact I].
fold E. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 9 u E9) by (clear - Hu4096 Huceil HrNu HNu RT C1; lia). rewrite (U_atom E 20 hj E20) by (clear - Rhj RT; lia).
rewrite (U_atom E 41 (u + hj) E39) by (clear - Hu4096 Huceil HrNu HNu Rhj C1; lia).
apply zcanon_id. unfold M64. clear - Hu4096 Huceil HrNu HNu Rhj C1. lia.
- unfold sh_ok, chl_SH. constructor; [|constructor].
apply (shent_ok_of_range trbsegs (w_H W) mem1 E chl_Bx 41 (u + hj) 1 (u + hj) 0 1).
+ apply (range_addressable_of_block trbsegs B LAWS ly S W mem1 md1 u Nu _ _ HAR1 Hu); clear - HrNu HNu Rhj; lia.
+ unfold U, chl_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U39.
+ lia.
+ lia.
+ intros x Hx. revert Hx Huh_ia Huh_img Huceil Hu4096 HrNu HNu Rhj C1. clear. unfold off_img, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg. intros. lia.
Qed.
Lemma chl_ro_kept : forall E H (m m' : word -> option byte),
frame_of E chl_mem (mrestrict H m) (mrestrict H m') ->
forall a, 0 <= a < 2 ^ 64 -> aview trbsegs H m' a = aview trbsegs H m a.
Proof.
intros E H m m' HF a Ha. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). cbn [chl_mem In] in Hin.
destruct Hin as [<- | [<- | []]]; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; lia.
Qed.
Lemma av_byte : forall H (m : word -> option byte) a v,
mbyte trbsegs (mrestrict H m) a = Some (Z_to_bv 8 v) -> 0 <= v < 256 -> aview trbsegs H m a = Some v.
Proof.
intros H m a v Hb Hv. unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Definition ch_post ly S (W : world trbsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (r : Z)
: world trbsegs -> config -> Prop :=
apost_base B TCOLHASH_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' (_ : word -> option byte) (_ : Model) => ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 r).
Definition CH_SAME : list (bv 5) := [2; 8; 9; 18; 19; 21; 22; 23]%bv ++ CH_KEPT.
Lemma at_st_step : forall ly S W (regs : bvmap 5 word) mem md ch rgb keys u T hj hj' (regs1 : bvmap 5 word) mem1 md1 (regs2 : bvmap 5 word) mem2 md2,
afn_pre trbsegs B TCOLHASH_STK ly S W regs mem md ch ->
at_st ly S W regs mem md rgb keys u T hj regs1 mem1 md1 ->
ajournal trbsegs B TCOLHASH_STK (spZ regs) [] ly S W mem md [] ly S W mem2 md2 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCOLHASH_STK <= a < spZ regs - 80) ->
aview trbsegs (w_H W) mem2 a = aview trbsegs (w_H W) mem1 a) ->
(forall rr : bv 5, In rr CH_SAME -> getr regs2 rr = getr regs1 rr) -> getr regs2 20 = w64 hj' ->
at_st ly S W regs mem md rgb keys u T hj' regs2 mem2 md2.
Proof.
intros ly S W regs mem md ch rgb keys u T hj hj' regs1 mem1 md1 regs2 mem2 md2 HPRE HA HJ2 Hk2 Hsame H20.
destruct HA as (HJ1 & Hkept & Ofr & G2 & G20 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (asan_consts) as (C1 & _). assert (WS : TCOLHASH_STK = 8272) by reflexivity.
unfold at_st. split; [exact HJ2|]. split.
{ intros a Ha Hn. rewrite (Hk2 a Ha ltac:(clear - Hn; lia)). apply Hkept; assumption. }
split.
{ apply (rg_obj_at_blk_kept (w_H W) (w_H W) mem1 mem2 (spZ regs - 80) LAY_CHF _ 80 Ofr ltac:(vm_compute; reflexivity)).
intros i Hi. apply Hk2; [clear - Hi Hslo Hshi H47 Hceil C1 WS Hstk0; lia | clear - Hi; lia]. }
split; [rewrite (Hsame (2%bv : bv 5) (or_introl eq_refl)); exact G2|].
split; [exact H20|].
split; [rewrite (Hsame (8%bv : bv 5) (or_intror (or_introl eq_refl))); exact G8|].
split; [rewrite (Hsame (9%bv : bv 5) (or_intror (or_intror (or_introl eq_refl)))); exact G9|].
split; [rewrite (Hsame (18%bv : bv 5) (or_intror (or_intror (or_intror (or_introl eq_refl))))); exact G18|].
split; [rewrite (Hsame (19%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))); exact G19|].
split; [rewrite (Hsame (21%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))); exact G21|].
split; [rewrite (Hsame (22%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))); exact G22|].
split; [rewrite (Hsame (23%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))); exact G23|].
intros rr Hrr. rewrite (Hsame rr ltac:(unfold CH_SAME; apply in_or_app; right; exact Hrr)). apply GK. exact Hrr.
Qed.
Definition CH_TEST : Z := 0x85278.
Lemma ch_head : forall ly S W (regs : bvmap 5 word) mem md ch (rgb keys u Nu T hj : Z) (used : list Z) pc (regs1 : bvmap 5 word) mem1 md1
(Q : world trbsegs -> config -> Prop),
afn_pre trbsegs B TCOLHASH_STK ly S W regs mem md ch ->
In (u, Nu) (ablocks B ly S) -> T <= Nu -> 0 < T < 2 ^ 30 -> 0 <= hj < T ->
4096 <= rgb <= 140737479966720 -> 4096 <= keys <= 140737479966720 ->
arr8 trbsegs (mrestrict (w_H W) mem) u used -> zlen used = T ->
(pc = CH_ARR \/ pc = CH_NEXT) ->
at_st ly S W regs mem md rgb keys u T hj regs1 mem1 md1 -> getr regs1 10 = w64 (u + hj) ->
(forall regs' mem' md', at_st ly S W regs mem md rgb keys u T hj regs' mem' md' -> getr regs' 10 = w64 (u + hj) ->
SRr trbsegs W (mkCfg (mkst regs' (Z_to_bv 64 CH_TEST) mem' (seg_rom trbsegs)) md') Q) ->
SRr trbsegs W (mkCfg (mkst regs1 (Z_to_bv 64 pc) mem1 (seg_rom trbsegs)) md1) Q.
Proof.
intros ly S W regs mem md ch rgb keys u Nu T hj used pc regs1 mem1 md1 Q HPRE Hu HNu RT Rhj Rrgb Rkeys Hused LU Hpc HA G10s K.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
destruct (arr8_getz trbsegs _ u used hj Hused ltac:(lia)) as [Bu Rub].
pose proof HA as (HJ & Hkept & Ofr & G2 & G20 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK).
destruct Hpc as [-> | ->].
1: destruct (ch_seed true CH_ARR ly S W regs mem md ch rgb keys u Nu T hj _ regs1 mem1 md1 HPRE HA Hu HNu RT Rhj Rrgb Rkeys Bu Rub
(fun _ => G10s)) as [HS SHOK].
2: destruct (ch_seed true CH_NEXT ly S W regs mem md ch rgb keys u Nu T hj _ regs1 mem1 md1 HPRE HA Hu HNu RT Rhj Rrgb Rkeys Bu Rub
(fun _ => G10s)) as [HS SHOK].
all: set (E := Ereg regs1 (chl_extra regs (u + hj) (getz used hj))) in *.
all: assert (HAE : env_agree 32 (Ereg regs1 (chl_extra regs (u + hj) (getz used hj))) E) by (split; [intros n Hn; reflexivity | reflexivity]).
all: assert (E39 : ew E 41 = Z_to_bv 64 (u + hj))
by (subst E; unfold chl_extra; rewrite <- (app_nil_r (map _ _)); exact (Ereg_vals regs1 (chf_vals regs ++ [u + hj; getz used hj]) [] 9%nat _ eq_refl)).
all: aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan CH_TEST.
1, 3: (cbn [ss_mem ss_chl]; unfold chl_mem; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil).
all: lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (HAE' : env_agree 32 (Ereg regs1 (chl_extra regs (u + hj) (getz used hj))) Ex) by (env_agree_chain HAE) end.
all: pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs1 _ (20%bv :: CH_SAME) HS HAE' ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
all: rreg HS (10%bv : bv 5) R10.
all: rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ _ HS eq_refl); cbn [ss_pc].
all: apply K;
[ apply (at_st_step ly S W regs mem md ch rgb keys u T hj hj regs1 mem1 md1 _ _ _ HPRE HA HJ);
[ intros a Ha _; exact (chl_ro_kept _ _ _ _ HFr a Ha)
| intros rr Hrr; apply HKR; right; exact Hrr
| rewrite (HKR (20%bv : bv 5) (or_introl eq_refl)); exact G20 ]
| rewrite R10; rewrite ?ew_ewset_other by (cbv; lia); exact E39 ].
Qed.
Lemma ch_body : forall ly S W (regs : bvmap 5 word) mem md ch (img Nimg off keys Nh u Nu T : Z) (used kys : list Z) (c : colour) (r js : Z)
j (regs1 : bvmap 5 word) mem1 md1,
afn_pre trbsegs B TCOLHASH_STK ly S W regs mem md ch ->
In (img, Nimg) (ablocks B ly S) -> 0 <= off -> off + 3 <= Nimg ->
In (keys, Nh) (ablocks B ly S) -> 3 * T <= Nh -> In (u, Nu) (ablocks B ly S) -> T <= Nu ->
col3 trbsegs (mrestrict (w_H W) mem) (img + off) c ->
arr8 trbsegs (mrestrict (w_H W) mem) u used -> arr8 trbsegs (mrestrict (w_H W) mem) keys kys ->
zlen used = T -> zlen kys = 3 * T -> 0 < T < 2 ^ 30 ->
0 <= js < T -> r = cyc T (hash0 T c) js ->
(forall i, 0 <= i <= js -> slot_stop (HT0 T used kys) c (cyc T (hash0 T c) i) = (i =? js)) ->
0 <= j <= js ->
at_st ly S W regs mem md (img + off) keys u T (cyc T (hash0 T c) j) regs1 mem1 md1 ->
getr regs1 10 = w64 (u + cyc T (hash0 T c) j) ->
(forall regs' mem' md', j + 1 <= js -> at_st ly S W regs mem md (img + off) keys u T (cyc T (hash0 T c) (j + 1)) regs' mem' md' ->
getr regs' 10 = w64 (u + cyc T (hash0 T c) (j + 1)) ->
SRr trbsegs W (mkCfg (mkst regs' (Z_to_bv 64 CH_NEXT) mem' (seg_rom trbsegs)) md') (ch_post ly S W regs mem md r)) ->
SRr trbsegs W (mkCfg (mkst regs1 (Z_to_bv 64 CH_TEST) mem1 (seg_rom trbsegs)) md1) (ch_post ly S W regs mem md r).
Proof.
intros ly S W regs mem md ch img Nimg off keys Nh u Nu T used kys c r js j regs1 mem1 md1
HPRE Himg Hoff0 Hoff1 Hk HNh Hu HNu Hcol Hused Hkeys LU LK RT Hjs Hr Hstop Hj HA G10 K.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TCOLHASH_STK = 8272) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
set (rgb := img + off) in *. set (h0 := hash0 T c) in *. set (hj := cyc T h0 j) in *. set (sp := spZ regs) in *.
assert (Rhj : 0 <= hj < T) by (subst hj; apply cyc_range; lia).
destruct (arr8_getz trbsegs _ u used hj Hused ltac:(lia)) as [Bu Rub]. set (ub := getz used hj) in *.
destruct (al_blocks _ _ LAWS ly S W mem md img Nimg HAR Himg) as (_ & Hi4096 & Hiceil & _ & _ & _ & HNi0).
destruct (al_blocks _ _ LAWS ly S W mem md keys Nh HAR Hk) as (_ & Hk4096 & Hkceil & _ & _ & _ & HNh0).
destruct (al_blocks _ _ LAWS ly S W mem md u Nu HAR Hu) as (_ & Hu4096 & Huceil & _ & _ & _ & HNu0).
pose proof (req_size_pos Nimg ltac:(lia)) as [_ HrNi]. pose proof (req_size_pos Nh ltac:(lia)) as [_ HrNh]. pose proof (req_size_pos Nu ltac:(lia)) as [_ HrNu].
assert (Rrgb : 4096 <= rgb <= 140737479966720) by (subst rgb; clear - Hi4096 Hiceil Hoff0 Hoff1 HrNi C1; lia).
assert (Rkeys : 4096 <= keys <= 140737479966720) by (clear - Hk4096 Hkceil HrNh HNh RT C1; lia).
destruct (ch_seed true CH_TEST ly S W regs mem md ch rgb keys u Nu T hj ub regs1 mem1 md1 HPRE HA Hu HNu RT Rhj Rrgb Rkeys Bu Rub (fun _ => G10)) as [HS SHOK].
pose proof HA as (HJ & Hkept & Ofr & G2 & G20 & G8 & G9 & G18 & G19 & G21 & G22 & G23 & GK).
set (E := Ereg regs1 (chl_extra regs (u + hj) ub)) in *.
assert (HAE : env_agree 32 (Ereg regs1 (chl_extra regs (u + hj) ub)) E) by (split; [intros n Hn; reflexivity | reflexivity]).
assert (HE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HVFa : forall n v, nth_error (chf_vals regs ++ [u + hj; ub]) n = Some v -> ew E (32 + n) = Z_to_bv 64 v).
{ intros n v Hn. subst E. unfold chl_extra. rewrite <- (app_nil_r (map _ _)). apply Ereg_vals. exact Hn. }
assert (E40 : ew E 42 = Z_to_bv 64 ub) by (exact (HVFa 10%nat _ eq_refl)).
assert (E39 : ew E 41 = Z_to_bv 64 (u + hj)) by (exact (HVFa 9%nat _ eq_refl)).
assert (Hspr : 0 <= sp - 80 /\ sp < 2 ^ 64) by (subst sp; clear - Hslo Hshi H47 Hceil C1 WS Hstk0; lia).
pose proof (Hstop j Hj) as Hsj. fold hj in Hsj. rewrite slot_stop_HT0 in Hsj. fold ub in Hsj.
assert (EXIT : forall E' ss ms' md', st_ok trbsegs E' ss (restrict (w_H W) ms') -> env_agree 43 E E' -> ss_resv ss = None ->
clookup trbtbl_lib (ss_pc ss) = Some RET_WORD_r ->
sr_get (ss_regs ss) 1 = SOff 40 0 -> sr_get (ss_regs ss) 2 = SOff 2 80 ->
sr_get (ss_regs ss) 8 = SOff 39 0 -> sr_get (ss_regs ss) 9 = SOff 38 0 -> sr_get (ss_regs ss) 18 = SOff 37 0 ->
sr_get (ss_regs ss) 19 = SOff 36 0 -> sr_get (ss_regs ss) 20 = SOff 35 0 -> sr_get (ss_regs ss) 21 = SOff 34 0 ->
sr_get (ss_regs ss) 22 = SOff 33 0 -> sr_get (ss_regs ss) 23 = SOff 32 0 ->
sr_get (ss_regs ss) 10 = SOff 20 0 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) CH_KEPT = true ->
hj = r ->
ajournal trbsegs B TCOLHASH_STK sp [] ly S W mem md [] ly S W (ms_mem ms') md' 0 ->
SRr trbsegs W (mkCfg ms' md') (ch_post ly S W regs mem md r)).
{ intros E' ss ms' md' HS' [EA ED] Hrv Hpc Q1 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q10 QK Hhr HJ'.
assert (RG : forall (rr : bv 5) e, sr_get (ss_regs ss) rr = e -> getr (ms_regs ms') rr = sv_denot E' e).
{ intros rr e He. rewrite <- He. apply (st_ok_restrict_reg trbsegs (w_H W) E' ss ms' rr HS'). }
assert (FR : forall (rr : bv 5) k, nth_error (chf_vals regs) k = Some (bv_unsigned (getr regs rr)) ->
sr_get (ss_regs ss) rr = SOff (32 + k) 0 -> getr (ms_regs ms') rr = getr regs rr).
{ intros rr k Hnk Hq. assert (Hk7 : (k < 9)%nat) by (apply (proj1 (nth_error_Some (chf_vals regs) k)); congruence).
rewrite (RG _ _ Hq). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia.
rewrite (HVFa k (bv_unsigned (getr regs rr))); [apply Z_to_bv_bv_unsigned|].
rewrite nth_error_app1; [exact Hnk | exact Hk7]. }
assert (HAE' : env_agree 32 (Ereg regs1 (chl_extra regs (u + hj) ub)) E').
{ split; [intros n Hn; rewrite EA by lia; reflexivity | exact ED]. }
pose proof (regs_kept_of_st_ok trbsegs E' ss _ regs1 _ CH_KEPT HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
assert (R1' : getr (ms_regs ms') 1 = getr regs 1) by (exact (FR (1%bv : bv 5) 8%nat eq_refl Q1)).
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W E' ss ms' md' _ HS' Hrv Hpc).
intros mat'. unfold ch_post, apost_base. exists ly, S, (ms_regs ms'), (ms_mem ms'), (with_vm_backing (m_vm_lazy md') mat' md').
split; [rewrite R1', Hra; reflexivity|].
split; [apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ'|].
split.
{ intros q Hq. unfold acallee_saved in Hq.
assert (Hcase : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by (clear - Hq; lia).
clear Hq. repeat (destruct Hcase as [-> | Hcase]); [ | | | | | | | | | | | | | | subst q].
- assert (X : getr (ms_regs ms') (2%bv : bv 5) = getr regs (2%bv : bv 5)); [|exact X].
rewrite (RG _ _ Q2). cbn [sv_denot]. rewrite EA by lia. rewrite (HE 2%nat 2%bv eq_refl), G2. unfold w64.
transitivity (Z_to_bv 64 (spZ regs)); [|unfold spZ; apply Z_to_bv_bv_unsigned].
f_equal. rewrite unsigned_lit_small by (clear - Hspr; lia). subst sp. lia.
- exact (eq_trans (HKR (3%bv : bv 5) (or_introl eq_refl)) (GK _ (or_introl eq_refl))).
- exact (eq_trans (HKR (4%bv : bv 5) (or_intror (or_introl eq_refl))) (GK _ (or_intror (or_introl eq_refl)))).
- exact (FR (8%bv : bv 5) 7%nat eq_refl Q8).
- exact (FR (9%bv : bv 5) 6%nat eq_refl Q9).
- exact (FR (18%bv : bv 5) 5%nat eq_refl Q18).
- exact (FR (19%bv : bv 5) 4%nat eq_refl Q19).
- exact (FR (20%bv : bv 5) 3%nat eq_refl Q20).
- exact (FR (21%bv : bv 5) 2%nat eq_refl Q21).
- exact (FR (22%bv : bv 5) 1%nat eq_refl Q22).
- exact (FR (23%bv : bv 5) 0%nat eq_refl Q23).
- exact (eq_trans (HKR (24%bv : bv 5) (or_intror (or_intror (or_introl eq_refl)))) (GK _ (or_intror (or_intror (or_introl eq_refl))))).
- exact (eq_trans (HKR (25%bv : bv 5) (or_intror (or_intror (or_intror (or_introl eq_refl))))) (GK _ (or_intror (or_intror (or_intror (or_introl eq_refl)))))).
- exact (eq_trans (HKR (26%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) (GK _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))).
- exact (eq_trans (HKR (27%bv : bv 5) (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) (GK _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))). }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite (RG _ _ Q10). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia. rewrite (HE 20%nat 20%bv eq_refl), G20, Hhr. reflexivity. }
assert (HAE41 : env_agree 43 E E) by (apply env_agree_refl).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan A_bcmp_tra.
{ cbn [ss_mem ss_chl]. unfold chl_mem. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msA := msx) in * end.
srr_branch_with trbtbl_lib_ok HS.
-
rewrite branch_eq_U, (U_atom E 42 ub E40), U_lit in Hc by (clear - Rub; lia). apply Z.eqb_eq in Hc.
assert (Hjj : j = js) by (rewrite Hc in Hsj; cbn [Z.eqb orb] in Hsj; symmetry in Hsj; apply Z.eqb_eq in Hsj; exact Hsj).
aj_run_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 43 E Ex) by (env_agree_chain HAE41) end.
apply (EXIT _ _ _ _ HS HAEx); [reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | subst hj; rewrite Hjj; symmetry; exact Hr | exact HJ].
-
rewrite branch_eq_U, (U_atom E 42 ub E40), U_lit in Hc by (clear - Rub; lia). apply Z.eqb_neq in Hc.
assert (Hsj' : colour_eqb (col_at kys hj) c = (j =? js)).
{ destruct (Z.eqb_spec ub 0) as [X|_]; [contradiction|]. exact Hsj. }
clear Hsj.
assert (E18 : ew E 18 = w64 keys) by (rewrite (HE 18%nat 18%bv eq_refl); exact G18).
assert (E19 : ew E 19 = w64 rgb) by (rewrite (HE 19%nat 19%bv eq_refl); exact G19).
assert (E20 : ew E 20 = w64 hj) by (rewrite (HE 20%nat 20%bv eq_refl); exact G20).
assert (E8 : ew E 8 = w64 T) by (rewrite (HE 8%nat 8%bv eq_refl); exact G8).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan A_bcmp_tra.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2a; rename HG into HG2a; clear HF.
rename Hc into Hub.
srr_branch_with trbtbl_lib_ok HS.
{ exfalso. rewrite branch_ltu_U in Hc.
rewrite (U_add_mul3' E 20 18 hj keys E20 ltac:(clear - Rhj; lia) E18 ltac:(clear - Rkeys; lia) ltac:(clear - Rkeys Rhj RT; lia)) in Hc.
rewrite (U_atom E 18 keys E18) in Hc by (clear - Rkeys; lia).
destruct (Z.ltb_spec (keys + 3 * hj) keys) as [X|X]; [clear - X Rhj; lia | discriminate Hc]. }
clear Hc. rename Hub into Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan A_bcmp_tra.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2b; rename HG into HG2b; clear HF.
assert (E23 : ew E 23 = w64 1) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
rename Hc into Hub.
srr_branch_with trbtbl_lib_ok HS.
{ exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite (U_atom E 23 1 E23) in Hc by (clear; lia).
rewrite !U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc. rename Hub into Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan A_bcmp_tra.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2; rename HG into HG2; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msB := msx) in * end.
rreg HS (10%bv : bv 5) Ra0. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (keys + 3 * hj))
(denot_of_U _ _ _ (U_add_mul3' E 20 18 hj keys E20 ltac:(clear - Rhj; lia) E18 ltac:(clear - Rkeys; lia) ltac:(clear - Rkeys Rhj RT; lia))) Ra1.
assert (UspB : spZ (ms_regs msB) = sp + -80).
{ unfold spZ. rewrite Rsp, (HE 2%nat 2%bv eq_refl), G2. unfold w64. rewrite unsigned_lit_small by (clear - Hspr; lia). lia. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview trbsegs (w_H W) (ms_mem msB) a = aview trbsegs (w_H W) mem1 a).
{ intros a Ha. rewrite (chl_ro_kept _ _ _ _ HFr2 a Ha). rewrite (chl_ro_kept _ _ _ _ HFr2b a Ha). rewrite (chl_ro_kept _ _ _ _ HFr2a a Ha). exact (chl_ro_kept _ _ _ _ HFr1 a Ha). }
pose proof (proj1 HJ) as HARB.
destruct (al_blocks _ _ LAWS ly S W _ _ img Nimg HARB Himg) as (_ & _ & _ & _ & Hipres & _).
destruct (al_blocks _ _ LAWS ly S W _ _ keys Nh HARB Hk) as (_ & _ & _ & _ & Hkpres & _).
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msB HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ eapply (aj_bcmp_at trbsegs B LAWS Hsegs A_bcmp_tra ABCMP W (ms_regs msB) (ms_mem msB) TCOLHASH_STK sp [] ly S W mem md [] ly S _ 0
rgb (keys + 3 * hj) 3 (-80) (Z_to_bv 64 CH_BRET) HJ).
- rewrite Ra0. exact E19.
- exact Ra1.
- exact Ra2.
- clear; lia.
- clear - Rrgb; lia.
- clear - Rrgb; lia.
- clear - Rkeys Rhj; lia.
- clear - Rkeys Rhj RT; lia.
- exact UspB.
- reflexivity.
- clear; lia.
- rewrite WS, Hes. clear; lia.
- rewrite Rgp, (HE 3%nat 3%bv eq_refl), (GK (3%bv : bv 5) (or_introl eq_refl)). exact Hgp.
- rewrite Rtp, (HE 4%nat 4%bv eq_refl), (GK (4%bv : bv 5) (or_intror (or_introl eq_refl))). exact Htp.
- exact Rra.
- apply ret_ok_even. vm_compute. reflexivity.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (Hipres a ltac:(subst rgb; clear - Ha Hoff0 Hoff1 HrNi; lia))) |].
rewrite UspB, Hes. subst rgb sp. clear - Ha Hoff1 HrNi Hiceil Hceil Hslo WS. lia.
- intros a Ha. split; [apply (aview_some_of_apresent trbsegs); apply (proj1 (Hkpres a ltac:(clear - Ha Rhj HNh HrNh; lia))) |].
rewrite UspB, Hes. subst sp. clear - Ha Rhj HNh HrNh Hkceil Hceil Hslo WS. lia.
- intros a Ha. rewrite Hes. subst rgb sp. clear - Ha Hoff1 HrNi Hiceil Hceil Hslo WS. lia.
- intros a Ha. rewrite Hes. subst sp. clear - Ha Rhj HNh HrNh Hkceil Hceil Hslo WS. lia.
- apply (amem_range_of_block trbsegs B LAWS ly S W _ _ img Nimg _ _ HARB Himg); subst rgb; clear - Hoff0 Hoff1 HrNi; lia.
- apply (amem_range_of_block trbsegs B LAWS ly S W _ _ keys Nh _ _ HARB Hk); clear - Rhj HNh HrNh; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly S W _ _ img Nimg _ _ HARB Himg); subst rgb; clear - Hoff0 Hoff1 HrNi; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S W _ _ img Nimg _ _ HARB Himg); subst rgb; clear - Hoff0 Hoff1 HrNi; lia.
- apply (range_addressable_of_block trbsegs B LAWS ly S W _ _ keys Nh _ _ HARB Hk); clear - Rhj HNh HrNh; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS ly S W _ _ keys Nh _ _ HARB Hk); clear - Rhj HNh HrNh; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hout2 & Hpres2).
assert (AV : forall a bz, mbyte trbsegs (mrestrict (w_H W) mem) a = Some (Z_to_bv 8 bz) -> 0 <= bz < 256 -> 0 <= a -> a < alloc_ceiling ->
aview trbsegs (w_H W) (ms_mem msB) a = Some bz).
{ intros a bz Hb Rb Ha0 Ha1. rewrite (KA a ltac:(clear - Ha0 Ha1 C1; lia)).
rewrite (Hkept a ltac:(clear - Ha0 Ha1 C1; lia) ltac:(fold sp; subst sp; clear - Ha1 Hceil Hslo WS; lia)).
apply av_byte; assumption. }
destruct Hcol as (C0 & C1' & C2' & Cok). pose proof Cok as (Rr & Rg & Rb).
destruct (arr8_getz trbsegs _ keys kys (3 * hj) Hkeys ltac:(clear - Rhj LK; lia)) as [Bk0 Rk0].
destruct (arr8_getz trbsegs _ keys kys (3 * hj + 1) Hkeys ltac:(clear - Rhj LK; lia)) as [Bk1 Rk1].
destruct (arr8_getz trbsegs _ keys kys (3 * hj + 2) Hkeys ltac:(clear - Rhj LK; lia)) as [Bk2 Rk2].
assert (Hzero : v = w64 0 <-> col_at kys hj = c).
{ rewrite Hcmp. split.
- intros Q. pose proof (Q 0 ltac:(lia)) as Q0. pose proof (Q 1 ltac:(lia)) as Q1. pose proof (Q 2 ltac:(lia)) as Q2.
rewrite !Z.add_0_r in Q0.
rewrite (AV rgb (cR c) C0 Rr ltac:(clear - Rrgb; lia) ltac:(subst rgb; clear - Hoff1 HrNi Hiceil; lia)) in Q0.
rewrite (AV (rgb + 1) (cG c) C1' Rg ltac:(clear - Rrgb; lia) ltac:(subst rgb; clear - Hoff1 HrNi Hiceil; lia)) in Q1.
rewrite (AV (rgb + 2) (cB c) C2' Rb ltac:(clear - Rrgb; lia) ltac:(subst rgb; clear - Hoff1 HrNi Hiceil; lia)) in Q2.
rewrite (AV (keys + 3 * hj) _ Bk0 Rk0 ltac:(clear - Rkeys Rhj; lia) ltac:(clear - Rhj HNh HrNh Hkceil; lia)) in Q0.
replace (keys + 3 * hj + 1) with (keys + (3 * hj + 1)) in Q1 by lia. replace (keys + 3 * hj + 2) with (keys + (3 * hj + 2)) in Q2 by lia.
rewrite (AV (keys + (3 * hj + 1)) _ Bk1 Rk1 ltac:(clear - Rkeys Rhj; lia) ltac:(clear - Rhj HNh HrNh Hkceil; lia)) in Q1.
rewrite (AV (keys + (3 * hj + 2)) _ Bk2 Rk2 ltac:(clear - Rkeys Rhj; lia) ltac:(clear - Rhj HNh HrNh Hkceil; lia)) in Q2.
injection Q0 as Q0. injection Q1 as Q1. injection Q2 as Q2.
unfold col_at, mkcol. destruct c as [[cr cg] cb]. unfold cR, cG, cB in *. cbn [fst snd] in *. congruence.
- intros Hcc i Hi. assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
assert (Q0 : cR c = getz kys (3 * hj)) by (rewrite <- Hcc; reflexivity).
assert (Q1 : cG c = getz kys (3 * hj + 1)) by (rewrite <- Hcc; reflexivity).
assert (Q2 : cB c = getz kys (3 * hj + 2)) by (rewrite <- Hcc; reflexivity).
destruct Hi3 as [-> | [-> | ->]].
+ rewrite !Z.add_0_r.
rewrite (AV rgb (cR c) C0 Rr ltac:(clear - Rrgb; lia) ltac:(subst rgb; clear - Hoff1 HrNi Hiceil; lia)).
rewrite (AV (keys + 3 * hj) _ Bk0 Rk0 ltac:(clear - Rkeys Rhj; lia) ltac:(clear - Rhj HNh HrNh Hkceil; lia)). rewrite Q0. reflexivity.
+ rewrite (AV (rgb + 1) (cG c) C1' Rg ltac:(clear - Rrgb; lia) ltac:(subst rgb; clear - Hoff1 HrNi Hiceil; lia)).
replace (keys + 3 * hj + 1) with (keys + (3 * hj + 1)) by lia.
rewrite (AV (keys + (3 * hj + 1)) _ Bk1 Rk1 ltac:(clear - Rkeys Rhj; lia) ltac:(clear - Rhj HNh HrNh Hkceil; lia)). rewrite Q1. reflexivity.
+ rewrite (AV (rgb + 2) (cB c) C2' Rb ltac:(clear - Rrgb; lia) ltac:(subst rgb; clear - Hoff1 HrNi Hiceil; lia)).
replace (keys + 3 * hj + 2) with (keys + (3 * hj + 2)) by lia.
rewrite (AV (keys + (3 * hj + 2)) _ Bk2 Rk2 ltac:(clear - Rkeys Rhj; lia) ltac:(clear - Rhj HNh HrNh Hkceil; lia)). rewrite Q2. reflexivity. }
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 chl_Bx chl_SH ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ eapply region_kept_aview;
[ rewrite (HE 2%nat 2%bv eq_refl), G2; unfold w64; apply unsigned_lit_small; clear - Hspr; lia
| intros a Ha; cbn [ms_mem]; apply Hout2; [clear - Ha Hspr; lia | rewrite Hes; clear - Ha; lia]
| intros a Ha; apply Hpres2; exact Ha ]
| eapply region_kept_aview;
[ rewrite E39; apply unsigned_lit_small; clear - Hu4096 Huceil HrNu HNu Rhj C1; lia
| intros a Ha; cbn [ms_mem]; apply Hout2; [clear - Ha Hu4096 Huceil HrNu HNu Rhj C1; lia | rewrite Hes; subst sp; clear - Ha Huceil HrNu HNu Rhj Hceil Hslo WS; lia]
| intros a Ha; apply Hpres2; exact Ha ] ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS Hc. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E2 := havoc E 43 (map (getr regs2) CLOB)) in *.
assert (Hv' : ew E2 47 = v).
{ rewrite <- Hv. subst E2. etransitivity; [apply (ew_havoc_new E 43 _ 4%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (HAE2 : env_agree 43 E E2) by (subst E2; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (SHOK2 : sh_ok trbsegs chl_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
srr_branch_with trbtbl_lib_ok HS.
+
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hv' in Hc. apply bv_eqb_eq in Hc.
pose proof (proj1 Hzero Hc) as Hcc. rewrite Hcc, colour_eqb_refl in Hsj'. symmetry in Hsj'. apply Z.eqb_eq in Hsj'.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (HAEx : env_agree 43 E Ex) by (env_agree_chain HAE2) end.
apply (EXIT _ _ _ _ HS HAEx); [reflexivity | vm_compute; reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | subst hj; rewrite Hsj'; symmetry; exact Hr | exact HJ2].
+
cbn [branch_taken sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hv' in Hc.
assert (Hjs' : j + 1 <= js).
{ destruct (Z.eqb_spec j js) as [Ej|]; [|clear - Hj n; lia]. exfalso. apply (proj1 (colour_eqb_spec _ _)) in Hsj'.
apply Hzero in Hsj'. rewrite Hsj' in Hc. vm_compute in Hc. discriminate Hc. }
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_NEXT.
{ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr3.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (HAEx : env_agree 43 E Ex) by (env_agree_chain HAE2);
assert (HAE32 : env_agree 32 (Ereg regs1 (chl_extra regs (u + hj) ub)) Ex)
by (destruct HAEx as [AA DD]; split; [intros n0 Hn0; rewrite AA by lia; reflexivity | exact DD]);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (probe_next T hj))
(denot_of_U _ _ _ (U_sv_next Ex 20 8 hj T ltac:(rewrite (proj1 HAEx) by lia; exact E20) ltac:(rewrite (proj1 HAEx) by lia; exact E8) Rhj (proj2 RT))) R20;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (u + probe_next T hj))
(denot_of_U _ _ _ (U_u_next Ex 9 20 8 u hj T ltac:(rewrite (proj1 HAEx) by lia; rewrite (HE 9%nat 9%bv eq_refl); exact G9) ltac:(rewrite (proj1 HAEx) by lia; exact E20)
ltac:(rewrite (proj1 HAEx) by lia; exact E8) Rhj (proj2 RT) ltac:(clear - Hu4096; lia) ltac:(clear - Huceil HrNu HNu RT C1; lia))) R10n
end.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs1 _ CH_SAME HS HAE32 ltac:(vm_compute; reflexivity)) as HKR. cbn [ms_regs restrict] in HKR.
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ _ HS eq_refl). cbn [ss_pc].
apply K; [exact Hjs' | | rewrite R10n; subst hj; rewrite cyc_succ by (clear - RT; lia); reflexivity].
apply (at_st_step ly S W regs mem md ch rgb keys u T hj _ regs1 mem1 md1 _ _ _ HPRE HA HJ2).
* intros a Ha Hnb. rewrite (chl_ro_kept _ _ _ _ HFr3 a Ha).
rewrite (Hout2 a Ha ltac:(rewrite Hes; fold sp in Hnb; rewrite WS in Hnb; clear - Hnb; lia)). exact (KA a Ha).
* exact HKR.
* rewrite R20. subst hj. rewrite cyc_succ by (clear - RT; lia). reflexivity.
Qed.
Lemma ch_loop : forall ly S W (regs : bvmap 5 word) mem md ch (img Nimg off keys Nh u Nu T : Z) (used kys : list Z) (c : colour) (r js : Z),
afn_pre trbsegs B TCOLHASH_STK ly S W regs mem md ch ->
In (img, Nimg) (ablocks B ly S) -> 0 <= off -> off + 3 <= Nimg ->
In (keys, Nh) (ablocks B ly S) -> 3 * T <= Nh -> In (u, Nu) (ablocks B ly S) -> T <= Nu ->
col3 trbsegs (mrestrict (w_H W) mem) (img + off) c ->
arr8 trbsegs (mrestrict (w_H W) mem) u used -> arr8 trbsegs (mrestrict (w_H W) mem) keys kys ->
zlen used = T -> zlen kys = 3 * T -> 0 < T < 2 ^ 30 ->
0 <= js < T -> r = cyc T (hash0 T c) js ->
(forall i, 0 <= i <= js -> slot_stop (HT0 T used kys) c (cyc T (hash0 T c) i) = (i =? js)) ->
forall (n : nat) pc j (regs1 : bvmap 5 word) mem1 md1, js - j <= Z.of_nat n -> 0 <= j <= js -> (pc = CH_ARR \/ pc = CH_NEXT) ->
at_st ly S W regs mem md (img + off) keys u T (cyc T (hash0 T c) j) regs1 mem1 md1 ->
getr regs1 10 = w64 (u + cyc T (hash0 T c) j) ->
SRr trbsegs W (mkCfg (mkst regs1 (Z_to_bv 64 pc) mem1 (seg_rom trbsegs)) md1) (ch_post ly S W regs mem md r).
Proof.
intros ly S W regs mem md ch img Nimg off keys Nh u Nu T used kys c r js
HPRE Himg Hoff0 Hoff1 Hk HNh Hu HNu Hcol Hused Hkeys LU LK RT Hjs Hr Hstop.
pose proof HPRE as (HAR & _).
pose proof (asan_consts) as (C1 & _).
destruct (al_blocks _ _ LAWS ly S W mem md img Nimg HAR Himg) as (_ & Hi4096 & Hiceil & _ & _ & _ & HNi0).
destruct (al_blocks _ _ LAWS ly S W mem md keys Nh HAR Hk) as (_ & Hk4096 & Hkceil & _ & _ & _ & HNh0).
pose proof (req_size_pos Nimg ltac:(lia)) as [_ HrNi]. pose proof (req_size_pos Nh ltac:(lia)) as [_ HrNh].
assert (Rrgb : 4096 <= img + off <= 140737479966720) by (clear - Hi4096 Hiceil Hoff0 Hoff1 HrNi C1; lia).
assert (Rkeys : 4096 <= keys <= 140737479966720) by (clear - Hk4096 Hkceil HrNh HNh RT C1; lia).
induction n as [|n IH]; intros pc j regs1 mem1 md1 Hn Hj Hpc HA G10s.
- apply (ch_head ly S W regs mem md ch (img + off) keys u Nu T _ used pc regs1 mem1 md1 _ HPRE Hu HNu RT
ltac:(apply cyc_range; lia) Rrgb Rkeys Hused LU Hpc HA G10s).
intros regs' mem' md' HA' G10'.
apply (ch_body ly S W regs mem md ch img Nimg off keys Nh u Nu T used kys c r js j regs' mem' md'
HPRE Himg Hoff0 Hoff1 Hk HNh Hu HNu Hcol Hused Hkeys LU LK RT Hjs Hr Hstop Hj HA' G10').
intros regs'' mem'' md'' Hj' _ _. exfalso. cbn in Hn. lia.
- apply (ch_head ly S W regs mem md ch (img + off) keys u Nu T _ used pc regs1 mem1 md1 _ HPRE Hu HNu RT
ltac:(apply cyc_range; lia) Rrgb Rkeys Hused LU Hpc HA G10s).
intros regs' mem' md' HA' G10'.
apply (ch_body ly S W regs mem md ch img Nimg off keys Nh u Nu T used kys c r js j regs' mem' md'
HPRE Himg Hoff0 Hoff1 Hk HNh Hu HNu Hcol Hused Hkeys LU LK RT Hjs Hr Hstop Hj HA' G10').
intros regs'' mem'' md'' Hj' HA'' G10''.
apply (IH CH_NEXT (j + 1)); [rewrite Nat2Z.inj_succ in Hn; lia | lia | right; reflexivity | exact HA'' | exact G10''].
Qed.
Definition che_mem : smem := [ stack_region 80; got_region; bcell_region 32 ].
Definition che_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 0); (11%nat, mkAF 4096 140737479966720 0);
(12%nat, mkAF 4096 140737479966720 0); (13%nat, mkAF 1 (2^30) 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_che (fmt : Z) : sstate := mkSS A_col_hash (sr_set sr_atoms 14%bv (SLit fmt)) che_mem None che_facts.
Definition che_extra : list word := map (Z_to_bv 64) [SB].
Lemma ch_entry : forall ly S W (regs : bvmap 5 word) mem md ch (img Nimg off h Nh u Nu T fmt : Z),
afn_pre trbsegs B TCOLHASH_STK ly S W regs mem md ch ->
getr regs 10 = w64 (img + off) -> getr regs 11 = w64 h -> getr regs 12 = w64 u -> getr regs 13 = w64 T -> getr regs 14 = w64 fmt ->
In (img, Nimg) (ablocks B ly S) -> 0 <= off -> off + fmt <= Nimg -> (fmt = 3 \/ fmt = 4) ->
In (h, Nh) (ablocks B ly S) -> In (u, Nu) (ablocks B ly S) -> 0 < T < 2 ^ 30 ->
st_ok trbsegs (Ereg regs che_extra) (ss_che fmt) (restrict (w_H W) (mkst regs (Z_to_bv 64 A_col_hash) mem (seg_rom trbsegs))).
Proof.
intros ly S W regs mem md ch img Nimg off h Nh u Nu T fmt HPRE H10 H11 H12 H13 H14 Himg Hoff0 Hoff1 Rf Hh Hu RT.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCOLHASH_STK = 8272) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md img Nimg HAR Himg) as (_ & Hi4096 & Hiceil & _ & _ & _ & Hin0).
destruct (al_blocks _ _ LAWS ly S W mem md h Nh HAR Hh) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly S W mem md u Nu HAR Hu) as (_ & Hu4096 & Huceil & _).
pose proof (req_size_pos Nimg ltac:(lia)) as [_ HrNi]. pose proof (req_size_pos Nh ltac:(destruct (al_blocks _ _ LAWS ly S W mem md h Nh HAR Hh) as (_ & _ & _ & _ & _ & _ & X); lia)) as [HrNh0 HrNh].
pose proof (req_size_pos Nu ltac:(destruct (al_blocks _ _ LAWS ly S W mem md u Nu HAR Hu) as (_ & _ & _ & _ & _ & _ & X); lia)) as [HrNu0 HrNu].
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Ereg regs che_extra).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 (img + off)) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 h) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 u) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 T) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = img + off) by (rewrite E10; apply unsigned_lit_small; clear - Hi4096 Hiceil Hoff0 Hoff1 HrNi Rf C1; lia).
unfold ss_che. apply (entry_st_ok_full trbsegs); change (Ereg regs _) with E.
+ apply regs_ok_pin; [apply regs_ok_Ereg | intros HH0; discriminate HH0 |].
rewrite H14. cbn [sv_denot]. reflexivity.
+ destruct Rf as [-> | ->]; vm_compute; reflexivity.
+ unfold che_mem, stack_region, got_region, bcell_region. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite Usp.
split; [clear - Hslo Hceil C1 WS Hstk0; lia|]. split; [clear - Hshi H47; lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable trbsegs). apply Hpres. clear - Ho WS. lia.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_GOT_shadow.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xa3250) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xa3250 8 (SLit A_shadow_glob) A_shadow_glob); [reflexivity | unfold A_shadow_glob; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kgot).
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold A_shadow_glob.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. rewrite <- (Z.add_0_l 0xab278) at 1.
apply (chunk_ok_val trbsegs _ _ 0 0xab278 8 ch_Bx SB);
[cbn [sv_denot ch_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
exact (val_mem_of_rdword trbsegs (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold che_mem, stack_region, got_region, bcell_region, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite Usp. unfold A_GOT_shadow, A_shadow_glob.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear. unfold ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [che_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, E11, E12, E13, E32, !unsigned_lit_small by (unfold SB; clear - Hh4096 Hhceil Hu4096 Huceil HrNh0 HrNu0 RT C1; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hiceil Hi4096 Hoff0 Hoff1 HrNi Rf Hh4096 Hhceil Hu4096 Huceil HrNh0 HrNu0 RT. clear.
unfold SB, ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Lemma che_kept : forall E0 rs (H : word -> bool) (m m' : word -> option byte) sp,
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some 2%nat /\ -80 <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= 0)) ->
bv_unsigned (ew E0 2) = sp ->
forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 80 <= x < sp) -> aview trbsegs H m' x = aview trbsegs H m x.
Proof.
intros E0 rs H m m' sp HF Hrs Hsp x Hx Hnw. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). destruct (Hrs rr Hin) as [Hro | (Hb & Hlo & Hhi)]; [lia|].
rewrite Hb in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
Local Ltac che_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; cbn [ss_mem ss_che che_mem add_cond] in Hin; unfold stack_region, got_region, bcell_region in Hin; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction; unfold stack_region, got_region, bcell_region;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Definition chf_chunks : list YQ0b.chunk :=
[ YQ0b.mkChunk (-72) (CVal 8 (SOff 23 0)); YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0)); YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0));
YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0)); YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0));
YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0)); YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0)) ].
Lemma ch_lxor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
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
Let TGPV : tgpv_spec B := trb_getPixelVal B TL LAWS.
Theorem trb_col_hash : tcolhash_spec B.
Proof.
unfold tcolhash_spec.
intros ly S W regs mem md ch img Nimg off h Nh u Nu T fmt used keys c op r
HPRE H10 H11 H12 H13 H14 Himg Hoff0 Hoff1 Hh HNh Hu HNu Hpix Hused Hkeys LU LK RT Hprobe.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TCOLHASH_STK = 8272) by reflexivity.
assert (Rf : fmt = 3 \/ fmt = 4) by (destruct Hpix as [_ [[-> _] | (-> & _)]]; [left | right]; reflexivity).
pose proof (ch_entry ly S W regs mem md ch img Nimg off h Nh u Nu T fmt HPRE H10 H11 H12 H13 H14 Himg Hoff0 Hoff1 Rf Hh Hu RT) as HS.
assert (SHOK : sh_ok trbsegs ch_Bx [] (Ereg regs che_extra) (mrestrict (w_H W) mem)) by constructor.
pose proof (ajournal_init trbsegs B TCOLHASH_STK [] ly S W regs mem md ch HPRE) as HJ.
set (E := Ereg regs che_extra) in *.
assert (ER : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (ER 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_col_hash) with (Z_to_bv 64 A_col_hash).
destruct (al_blocks _ _ LAWS ly S W mem md img Nimg HAR Himg) as (_ & Hi4096 & Hiceil & _ & _ & _ & HNi0).
pose proof (req_size_pos Nimg ltac:(lia)) as [_ HrNi].
destruct (al_blocks _ _ LAWS ly S W mem md u Nu HAR Hu) as (_ & Hu4096 & Huceil & _ & _ & _ & HNu0).
pose proof (req_size_pos Nu ltac:(lia)) as [_ HrNu].
pose proof (hash0_range T c ltac:(clear - RT; lia)) as Rh0.
assert (Hoff1' : off + 3 <= Nimg) by (clear - Hoff1 Rf; lia).
pose proof Hpix as [Hcol _].
assert (E10 : ew E 10 = w64 (img + off)) by (rewrite (ER 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = w64 h) by (rewrite (ER 11%nat 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = w64 u) by (rewrite (ER 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = w64 T) by (rewrite (ER 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (ARRIVE : forall E' ss ms' md', st_ok trbsegs E' ss (restrict (w_H W) ms') -> env_agree 33 E E' ->
U E' (sv_hashx (SOff 37 0) 13) = hash0 T c -> op = true ->
ss_pc ss = CH_ARR -> ss_resv ss = None ->
sr_get (ss_regs ss) 10 = SAlu ALU_ADD (SOff 12 0) (sv_hashx (SOff 37 0) 13) ->
sr_get (ss_regs ss) 20 = SAlu ALU_ADD (sv_hashx (SOff 37 0) 13) (SLit 0) -> sr_get (ss_regs ss) 2 = SOff 2 (-80) ->
sr_get (ss_regs ss) 8 = SOff 13 0 -> sr_get (ss_regs ss) 9 = SOff 12 0 -> sr_get (ss_regs ss) 18 = SOff 11 0 ->
sr_get (ss_regs ss) 19 = SOff 10 0 -> sr_get (ss_regs ss) 21 = SOff 32 0 ->
sr_get (ss_regs ss) 22 = SAlu ALU_XOR (SOff 12 0) (SLit (-1)) -> sr_get (ss_regs ss) 23 = SLit 1 ->
forallb (fun rr : bv 5 => sv_eqb (sr_get (ss_regs ss) rr) (SOff (Z.to_nat (bv_unsigned rr)) 0)) CH_KEPT = true ->
nth_error (ss_mem ss) 0 = Some (YQ0b.mkRegion (Some 2%nat) (-80) 0 (-80) 0 chf_chunks) ->
ajournal trbsegs B TCOLHASH_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms') md' 0 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - TCOLHASH_STK <= x < spZ regs) ->
aview trbsegs (w_H W) (ms_mem ms') x = aview trbsegs (w_H W) mem x) ->
SRr trbsegs W (mkCfg ms' md')
(apost_base B TCOLHASH_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' (_ : word -> option byte) (_ : Model) =>
ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 (if op then r else 2 ^ 64 - 1)))).
{ intros E' ss ms' md' HS' [EA ED] HhU' Hop Hpc Hrv Q10 Q20 Q2 Q8 Q9 Q18 Q19 Q21 Q22 Q23 QK Hrg HJ' Hk'.
specialize (Hprobe Hop). destruct (probe_facts T used keys c r ltac:(lia) Hprobe) as (js & Hjs & Hr & Hstop).
assert (RG : forall (rr : bv 5) e, sr_get (ss_regs ss) rr = e -> getr (ms_regs ms') rr = sv_denot E' e).
{ intros rr e He. rewrite <- He. apply (st_ok_restrict_reg trbsegs (w_H W) E' ss ms' rr HS'). }
pose proof (st_ok_region_nth E' ss _ 0%nat _ HS' Hrg) as HRstk. cbn [ms_mem restrict] in HRstk.
assert (UspX : bv_unsigned (ew E' 2) = spZ regs) by (rewrite EA by lia; exact Usp).
assert (SL : forall od (rr : bv 5) n, Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
In (YQ0b.mkChunk od (CVal 8 (SOff n 0))) chf_chunks ->
val_mem trbsegs (mrestrict (w_H W) (ms_mem ms')) (spZ regs + od) 8 (bv_unsigned (getr regs rr))).
{ intros od rr n Hn Hn32 Hin.
apply (slot_of_region E' _ (spZ regs) chf_chunks (-80) 0 (-80) 0 od (SOff n 0) _ HRstk UspX Hin);
[ cbn [sv_denot]; rewrite EA by lia; rewrite (ER n rr Hn), Z.add_0_r; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs rr)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq ]. }
assert (HAE' : env_agree 32 (Ereg regs che_extra) E') by (split; [intros n Hn; rewrite EA by lia; reflexivity | exact ED]).
pose proof (regs_kept_of_st_ok trbsegs E' ss _ regs _ CH_KEPT HS' HAE' QK) as HKR. cbn [ms_regs restrict] in HKR.
assert (E12' : ew E' 12 = w64 u) by (rewrite EA by lia; exact E12).
assert (Ru : 0 <= u /\ u + T < 2 ^ 47) by (clear - Hu4096 Huceil HrNu HNu RT C1; lia).
rewrite (st_ok_restrict_mkst trbsegs (w_H W) E' ss ms' HS' Hrv), Hpc. rewrite Hop.
eapply (ch_loop ly S W regs mem md ch img Nimg off h Nh u Nu T used keys c r js
HPRE Himg Hoff0 Hoff1' Hh HNh Hu HNu Hcol Hused Hkeys LU LK RT Hjs Hr Hstop (Z.to_nat js) CH_ARR 0);
[clear - Hjs; lia | clear - Hjs; lia | left; reflexivity | |].
2: { rewrite cyc_0 by (apply hash0_range; clear - RT; lia). rewrite (RG _ _ Q10). apply denot_of_U.
rewrite U_SAlu. cbn [zalu_raw]. rewrite HhU', (U_atom E' 12 u E12') by (clear - Ru RT; lia).
apply zcanon_id. unfold M64. clear - Ru Rh0 RT. lia. }
unfold at_st. rewrite cyc_0 by (apply hash0_range; clear - RT; lia).
split; [exact HJ'|]. split; [exact Hk'|]. split.
{ cbn [obj_at LAY_CHF chf_vals]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N Pos.to_nat].
repeat split; try apply u64_range8.
- replace (spZ regs - 80 + 8) with (spZ regs + -72) by lia. apply (SL (-72) (23%bv : bv 5) 23%nat eq_refl ltac:(lia)). left. reflexivity.
- replace (spZ regs - 80 + 16) with (spZ regs + -64) by lia. apply (SL (-64) (22%bv : bv 5) 22%nat eq_refl ltac:(lia)). do 1 right. left. reflexivity.
- replace (spZ regs - 80 + 24) with (spZ regs + -56) by lia. apply (SL (-56) (21%bv : bv 5) 21%nat eq_refl ltac:(lia)). do 2 right. left. reflexivity.
- replace (spZ regs - 80 + 32) with (spZ regs + -48) by lia. apply (SL (-48) (20%bv : bv 5) 20%nat eq_refl ltac:(lia)). do 3 right. left. reflexivity.
- replace (spZ regs - 80 + 40) with (spZ regs + -40) by lia. apply (SL (-40) (19%bv : bv 5) 19%nat eq_refl ltac:(lia)). do 4 right. left. reflexivity.
- replace (spZ regs - 80 + 48) with (spZ regs + -32) by lia. apply (SL (-32) (18%bv : bv 5) 18%nat eq_refl ltac:(lia)). do 5 right. left. reflexivity.
- replace (spZ regs - 80 + 56) with (spZ regs + -24) by lia. apply (SL (-24) (9%bv : bv 5) 9%nat eq_refl ltac:(lia)). do 6 right. left. reflexivity.
- replace (spZ regs - 80 + 64) with (spZ regs + -16) by lia. apply (SL (-16) (8%bv : bv 5) 8%nat eq_refl ltac:(lia)). do 7 right. left. reflexivity.
- replace (spZ regs - 80 + 72) with (spZ regs + -8) by lia. apply (SL (-8) (1%bv : bv 5) 1%nat eq_refl ltac:(lia)). do 8 right. left. reflexivity. }
split. { rewrite (RG _ _ Q2). cbn [sv_denot]. rewrite EA by lia. rewrite (ER 2%nat 2%bv eq_refl). unfold w64, spZ. f_equal; lia. }
split. { rewrite (RG _ _ Q20). apply denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite HhU', U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. unfold M64. clear - Rh0 RT. lia. }
split. { rewrite (RG _ _ Q8). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia. exact E13. }
split. { rewrite (RG _ _ Q9). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia. exact E12. }
split. { rewrite (RG _ _ Q18). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia. exact E11. }
split. { rewrite (RG _ _ Q19). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia. exact E10. }
split. { rewrite (RG _ _ Q21). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, EA by lia. exact E32. }
split. { rewrite (RG _ _ Q22). apply denot_of_U. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E' 12 u E12'), U_SLit by (clear - Ru RT; lia).
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite ch_lxor_ones64 by (clear - Ru RT; lia). apply zcanon_id. unfold M64. clear - Ru RT. lia. }
split. { rewrite (RG _ _ Q23). reflexivity. }
exact HKR. }
destruct Rf as [-> | ->].
-
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan A_getPixelVal. { awr_ok_tac; exact Usp. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msC := msx) in * end.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 80 <= x < spZ regs) -> aview trbsegs (w_H W) (ms_mem msC) x = aview trbsegs (w_H W) mem x).
{ apply (che_kept _ _ _ _ _ _ HFr1); [che_rs_tac | exact Usp]. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
assert (Hspr : 0 <= spZ regs - 80 /\ spZ regs < 2 ^ 64) by (clear - Hslo Hshi H47 Hceil C1 WS Hstk0; lia).
assert (UspC : spZ (ms_regs msC) = spZ regs + -80).
{ unfold spZ at 1. rewrite Rsp. cbn [sv_denot]. rewrite (ER 2%nat 2%bv eq_refl). fold (spZ regs). rewrite unsigned_lit_small by (clear - Hspr; lia). reflexivity. }
assert (HpixC : pixel_at trbsegs (mrestrict (w_H W) (ms_mem msC)) (img + off) 3 c op).
{ assert (MB : forall a, img + off <= a < img + off + 3 -> mbyte trbsegs (mrestrict (w_H W) (ms_mem msC)) a = mbyte trbsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply (mbyte_of_aview trbsegs). apply KW1; [clear - Ha Hi4096 Hiceil Hoff0 Hoff1 HrNi C1; lia | clear - Ha Hoff1 HrNi Hiceil Hceil Hslo WS; lia]. }
destruct Hpix as [(C0 & C1' & C2' & Cok) Hfm]. split.
- split; [rewrite MB by (clear; lia); exact C0|]. split; [rewrite MB by (clear; lia); exact C1'|]. split; [rewrite MB by (clear; lia); exact C2' | exact Cok].
- destruct Hfm as [Hf3 | (Hf4 & a & Ca & Ra & Hopa)]; [left; exact Hf3 | right; split; [exact Hf4|]; exists a; split; [rewrite MB by (clear - Hf4; lia); exact Ca | split; [exact Ra | exact Hopa]]]. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msC HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 544908) with (w64 A_getPixelVal).
eapply SRr_bind.
{ eapply (TGPV TCOLHASH_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msC) _ 0 (ms_regs msC) img Nimg (img + off) 3 c op HJ).
- rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
- unfold raZ. rewrite Rra. cbn [sv_denot]. rewrite unsigned_lit_small by (clear; lia). clear; lia.
- rewrite UspC. replace (spZ regs + -80) with (spZ regs + (-5) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact Hal16.
- rewrite UspC, WS. unfold TGPV_STK. clear; lia.
- rewrite UspC. clear; lia.
- rewrite Ra0, (ER 10%nat 10%bv eq_refl). exact H10.
- rewrite Ra1. reflexivity.
- first [left; reflexivity | right; reflexivity].
- exact Himg.
- clear - Hoff0; lia.
- clear - Hoff1; lia.
- exact HpixC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hout2 & Hpres2).
rewrite Rra.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 ch_Bx [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ exact Usp
| intros a Ha; cbn [ms_mem]; apply Hout2; [clear - Ha Hspr; lia | rewrite UspC; unfold TGPV_STK; clear - Ha; lia]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E2 := havoc E 33 (map (getr regs2) CLOB)) in *.
assert (Hv' : ew E2 37 = w64 (pixel_word c op)).
{ rewrite <- Ha02. subst E2. etransitivity; [apply (ew_havoc_new E 33 _ 4%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (HAE2 : env_agree 33 E E2) by (subst E2; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (HAE49 : env_agree 49 E2 E2) by (apply env_agree_refl).
assert (SHOK2 : sh_ok trbsegs ch_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
pose proof Hpix as [(_ & _ & _ & Cok) _]. pose proof Cok as (Rr & Rg & Rb).
set (A := if op then 255 else 0).
assert (RA : 0 <= A < 256) by (subst A; destruct op; clear; lia).
assert (HpU : U E2 (SOff 37 0) = A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c).
{ rewrite (U_atom E2 37 (pixel_word c op) Hv') by (unfold pixel_word; destruct op; clear - Rr Rg Rb; lia). unfold pixel_word. subst A. destruct op; clear; lia. }
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite (proj1 HAE2) by lia; exact Usp).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr2; rename HG into HG2; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Usp3 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (proj1 (ltac:(env_agree_chain HAE2) : env_agree 33 E Ex)) by lia; exact Usp) end.
srr_branch_with trbtbl_lib_ok HS.
+
rewrite branch_ne_U, (U_pix_alpha E2 (SOff 37 0) A c Cok RA HpU), U_SLit in Hc.
assert (Hop : op = true) by (destruct op; [reflexivity | subst A; vm_compute in Hc; discriminate Hc]).
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr3; rename HG into HG3; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Usp4 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (proj1 (ltac:(env_agree_chain HAE2) : env_agree 33 E Ex)) by lia; exact Usp) end.
assert (E2_12 : ew E2 12 = w64 u) by (rewrite (proj1 HAE2) by lia; rewrite (ER 12%nat 12%bv eq_refl); exact H12).
assert (E2_13 : ew E2 13 = w64 T) by (rewrite (proj1 HAE2) by lia; rewrite (ER 13%nat 13%bv eq_refl); exact H13).
assert (HhU : U E2 (sv_hashx (SOff 37 0) 13) = hash0 T c) by (exact (U_hashx E2 (SOff 37 0) 13 A c T Cok RA HpU E2_13 RT)).
srr_branch_with trbtbl_lib_ok HS.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 37 0) 13) in Hc.
rewrite HhU, (U_atom E2 12 u E2_12) in Hc by (clear - Hu4096 Huceil HrNu HNu RT C1; lia).
rewrite zcanon_id in Hc by (unfold M64; clear - Rh0 Hu4096 Huceil HrNu HNu RT C1; lia).
destruct (Z.ltb_spec (hash0 T c + u) u) as [X|X]; [clear - X Rh0; lia | discriminate Hc]. }
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr4; rename HG into HG4; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Usp5 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (proj1 (ltac:(env_agree_chain HAE2) : env_agree 33 E Ex)) by lia; exact Usp) end.
srr_branch_with trbtbl_lib_ok HS.
{ exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 37 0) 13) in Hc.
rewrite HhU, (U_atom E2 12 u E2_12), !U_SLit in Hc by (clear - Hu4096 Huceil HrNu HNu RT C1; lia).
rewrite (zcanon_id (hash0 T c + u)) in Hc by (unfold M64; clear - Rh0 Hu4096 Huceil HrNu HNu RT C1; lia).
change (zcanon 1) with 1 in Hc. change (zcanon 0) with 0 in Hc.
replace (hash0 T c + u <? 1) with false in Hc by (symmetry; apply Z.ltb_ge; clear - Rh0 Hu4096; lia).
vm_compute in Hc. discriminate Hc. }
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr5; rename HG into HG5; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (HAEx : env_agree 33 E Ex) by (env_agree_chain HAE2);
assert (HAEx2 : env_agree 49 E2 Ex) by (env_agree_chain HAE49) end.
apply (ARRIVE _ _ _ _ HS HAEx);
[ apply (U_hashx _ (SOff 37 0) 13 A c T Cok RA);
[ rewrite <- HpU; unfold U; cbn [sv_denot]; first [reflexivity | rewrite (proj1 HAEx2) by lia; reflexivity]
| rewrite (proj1 HAEx) by lia; rewrite (ER 13%nat 13%bv eq_refl); exact H13 | exact RT ]
| exact Hop | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | reflexivity | exact HJ2 |].
intros x Hx Hnw.
assert (Hnw80 : ~ (spZ regs - 80 <= x < spZ regs)) by (clear - Hnw WS; lia).
rewrite (che_kept _ _ _ _ _ _ HFr5 ltac:(che_rs_tac) Usp5 x Hx Hnw80).
rewrite (che_kept _ _ _ _ _ _ HFr4 ltac:(che_rs_tac) Usp4 x Hx Hnw80).
rewrite (che_kept _ _ _ _ _ _ HFr3 ltac:(che_rs_tac) Usp3 x Hx Hnw80).
rewrite (che_kept _ _ _ _ _ _ HFr2 ltac:(che_rs_tac) Usp2 x Hx Hnw80).
rewrite (Hout2 x Hx ltac:(rewrite UspC; unfold TGPV_STK; clear - Hnw WS; lia)).
apply KW1; [exact Hx | exact Hnw80].
+
rewrite branch_ne_U, (U_pix_alpha E2 (SOff 37 0) A c Cok RA HpU), U_SLit in Hc.
assert (Hop : op = false) by (destruct op; [subst A; vm_compute in Hc; discriminate Hc | reflexivity]).
clear Hc.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan. { awr_ok_tac; exact Usp2. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (HAEx : env_agree 33 E Ex) by (env_agree_chain HAE2);
assert (HAE32 : env_agree 32 (Ereg regs che_extra) Ex)
by (destruct HAEx as [AA DD]; split; [intros n0 Hn0; rewrite AA by lia; reflexivity | exact DD]) end.
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rr _ ?m _) ?d) => exists ly, S, rr, m, d end.
split; [cbn [ms_regs]; rewrite R1; rewrite ?(proj1 HAEx) by lia; rewrite (ER 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs che_extra HS); [exact HAE32 | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite Hop. cbn [ms_regs]. rewrite R10. reflexivity.
-
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK ch_Bspan A_getPixelVal. { awr_ok_tac; exact Usp. }
rename HFr into HFr1; rename HG into HG1; clear HF.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => set (msC := msx) in * end.
assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 80 <= x < spZ regs) -> aview trbsegs (w_H W) (ms_mem msC) x = aview trbsegs (w_H W) mem x).
{ apply (che_kept _ _ _ _ _ _ HFr1); [che_rs_tac | exact Usp]. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp.
assert (Hspr : 0 <= spZ regs - 80 /\ spZ regs < 2 ^ 64) by (clear - Hslo Hshi H47 Hceil C1 WS Hstk0; lia).
assert (UspC : spZ (ms_regs msC) = spZ regs + -80).
{ unfold spZ at 1. rewrite Rsp. cbn [sv_denot]. rewrite (ER 2%nat 2%bv eq_refl). fold (spZ regs). rewrite unsigned_lit_small by (clear - Hspr; lia). reflexivity. }
assert (HpixC : pixel_at trbsegs (mrestrict (w_H W) (ms_mem msC)) (img + off) 4 c op).
{ assert (MB : forall a, img + off <= a < img + off + 4 -> mbyte trbsegs (mrestrict (w_H W) (ms_mem msC)) a = mbyte trbsegs (mrestrict (w_H W) mem) a).
{ intros a Ha. apply (mbyte_of_aview trbsegs). apply KW1; [clear - Ha Hi4096 Hiceil Hoff0 Hoff1 HrNi C1; lia | clear - Ha Hoff1 HrNi Hiceil Hceil Hslo WS; lia]. }
destruct Hpix as [(C0 & C1' & C2' & Cok) Hfm]. split.
- split; [rewrite MB by (clear; lia); exact C0|]. split; [rewrite MB by (clear; lia); exact C1'|]. split; [rewrite MB by (clear; lia); exact C2' | exact Cok].
- destruct Hfm as [Hf3 | (Hf4 & a & Ca & Ra & Hopa)]; [left; exact Hf3 | right; split; [exact Hf4|]; exists a; split; [rewrite MB by (clear - Hf4; lia); exact Ca | split; [exact Ra | exact Hopa]]]. }
rewrite (st_ok_restrict_mkst trbsegs (w_H W) _ _ msC HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 544908) with (w64 A_getPixelVal).
eapply SRr_bind.
{ eapply (TGPV TCOLHASH_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msC) _ 0 (ms_regs msC) img Nimg (img + off) 4 c op HJ).
- rewrite Rra. apply ret_ok_even. vm_compute. reflexivity.
- unfold raZ. rewrite Rra. cbn [sv_denot]. rewrite unsigned_lit_small by (clear; lia). clear; lia.
- rewrite UspC. replace (spZ regs + -80) with (spZ regs + (-5) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact Hal16.
- rewrite UspC, WS. unfold TGPV_STK. clear; lia.
- rewrite UspC. clear; lia.
- rewrite Ra0, (ER 10%nat 10%bv eq_refl). exact H10.
- rewrite Ra1. reflexivity.
- first [left; reflexivity | right; reflexivity].
- exact Himg.
- clear - Hoff0; lia.
- clear - Hoff1; lia.
- exact HpixC. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hout2 & Hpres2).
rewrite Rra.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K 0 ch_Bx [] ssx) in
jafter_call_keep HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ exact Usp
| intros a Ha; cbn [ms_mem]; apply Hout2; [clear - Ha Hspr; lia | rewrite UspC; unfold TGPV_STK; clear - Ha; lia]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E2 := havoc E 33 (map (getr regs2) CLOB)) in *.
assert (Hv' : ew E2 37 = w64 (pixel_word c op)).
{ rewrite <- Ha02. subst E2. etransitivity; [apply (ew_havoc_new E 33 _ 4%nat (Z_to_bv 64 0)); cbn; lia | reflexivity]. }
assert (HAE2 : env_agree 33 E E2) by (subst E2; apply env_agree_havoc_ge; [lia | apply env_agree_refl]).
assert (HAE49 : env_agree 49 E2 E2) by (apply env_agree_refl).
assert (SHOK2 : sh_ok trbsegs ch_Bx [] E2 (mrestrict (w_H W) mem2)) by constructor.
pose proof Hpix as [(_ & _ & _ & Cok) _]. pose proof Cok as (Rr & Rg & Rb).
set (A := if op then 255 else 0).
assert (RA : 0 <= A < 256) by (subst A; destruct op; clear; lia).
assert (HpU : U E2 (SOff 37 0) = A * 2 ^ 24 + cB c * 2 ^ 16 + cG c * 2 ^ 8 + cR c).
{ rewrite (U_atom E2 37 (pixel_word c op) Hv') by (unfold pixel_word; destruct op; clear - Rr Rg Rb; lia). unfold pixel_word. subst A. destruct op; clear; lia. }
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite (proj1 HAE2) by lia; exact Usp).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr2; rename HG into HG2; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Usp3 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (proj1 (ltac:(env_agree_chain HAE2) : env_agree 33 E Ex)) by lia; exact Usp) end.
srr_branch_with trbtbl_lib_ok HS.
+
rewrite branch_ne_U, (U_pix_alpha E2 (SOff 37 0) A c Cok RA HpU), U_SLit in Hc.
assert (Hop : op = true) by (destruct op; [reflexivity | subst A; vm_compute in Hc; discriminate Hc]).
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr3; rename HG into HG3; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Usp4 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (proj1 (ltac:(env_agree_chain HAE2) : env_agree 33 E Ex)) by lia; exact Usp) end.
assert (E2_12 : ew E2 12 = w64 u) by (rewrite (proj1 HAE2) by lia; rewrite (ER 12%nat 12%bv eq_refl); exact H12).
assert (E2_13 : ew E2 13 = w64 T) by (rewrite (proj1 HAE2) by lia; rewrite (ER 13%nat 13%bv eq_refl); exact H13).
assert (HhU : U E2 (sv_hashx (SOff 37 0) 13) = hash0 T c) by (exact (U_hashx E2 (SOff 37 0) 13 A c T Cok RA HpU E2_13 RT)).
srr_branch_with trbtbl_lib_ok HS.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 37 0) 13) in Hc.
rewrite HhU, (U_atom E2 12 u E2_12) in Hc by (clear - Hu4096 Huceil HrNu HNu RT C1; lia).
rewrite zcanon_id in Hc by (unfold M64; clear - Rh0 Hu4096 Huceil HrNu HNu RT C1; lia).
destruct (Z.ltb_spec (hash0 T c + u) u) as [X|X]; [clear - X Rh0; lia | discriminate Hc]. }
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr4; rename HG into HG4; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ => assert (Usp5 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite (proj1 (ltac:(env_agree_chain HAE2) : env_agree 33 E Ex)) by lia; exact Usp) end.
srr_branch_with trbtbl_lib_ok HS.
{ exfalso. rewrite branch_eq_U, U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
change (SMdw M_REMU _ (SOff 13 0)) with (sv_hashx (SOff 37 0) 13) in Hc.
rewrite HhU, (U_atom E2 12 u E2_12), !U_SLit in Hc by (clear - Hu4096 Huceil HrNu HNu RT C1; lia).
rewrite (zcanon_id (hash0 T c + u)) in Hc by (unfold M64; clear - Rh0 Hu4096 Huceil HrNu HNu RT C1; lia).
change (zcanon 1) with 1 in Hc. change (zcanon 0) with 0 in Hc.
replace (hash0 T c + u <? 1) with false in Hc by (symmetry; apply Z.ltb_ge; clear - Rh0 Hu4096; lia).
vm_compute in Hc. discriminate Hc. }
clear Hc.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan CH_ARR. { awr_ok_tac; exact Usp2. }
rename HFr into HFr5; rename HG into HG5; clear HF.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (HAEx : env_agree 33 E Ex) by (env_agree_chain HAE2);
assert (HAEx2 : env_agree 49 E2 Ex) by (env_agree_chain HAE49) end.
apply (ARRIVE _ _ _ _ HS HAEx);
[ apply (U_hashx _ (SOff 37 0) 13 A c T Cok RA);
[ rewrite <- HpU; unfold U; cbn [sv_denot]; first [reflexivity | rewrite (proj1 HAEx2) by lia; reflexivity]
| rewrite (proj1 HAEx) by lia; rewrite (ER 13%nat 13%bv eq_refl); exact H13 | exact RT ]
| exact Hop | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| vm_compute; reflexivity | reflexivity | exact HJ2 |].
intros x Hx Hnw.
assert (Hnw80 : ~ (spZ regs - 80 <= x < spZ regs)) by (clear - Hnw WS; lia).
rewrite (che_kept _ _ _ _ _ _ HFr5 ltac:(che_rs_tac) Usp5 x Hx Hnw80).
rewrite (che_kept _ _ _ _ _ _ HFr4 ltac:(che_rs_tac) Usp4 x Hx Hnw80).
rewrite (che_kept _ _ _ _ _ _ HFr3 ltac:(che_rs_tac) Usp3 x Hx Hnw80).
rewrite (che_kept _ _ _ _ _ _ HFr2 ltac:(che_rs_tac) Usp2 x Hx Hnw80).
rewrite (Hout2 x Hx ltac:(rewrite UspC; unfold TGPV_STK; clear - Hnw WS; lia)).
apply KW1; [exact Hx | exact Hnw80].
+
rewrite branch_ne_U, (U_pix_alpha E2 (SOff 37 0) A c Cok RA HpU), U_SLit in Hc.
assert (Hop : op = false) by (destruct op; [subst A; vm_compute in Hc; discriminate Hc | reflexivity]).
clear Hc.
aj_run_tok trbtbl_lib_ok HS HJ2 SHOK2 ch_Bspan. { awr_ok_tac; exact Usp2. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (HAEx : env_agree 33 E Ex) by (env_agree_chain HAE2);
assert (HAE32 : env_agree 32 (Ereg regs che_extra) Ex)
by (destruct HAEx as [AA DD]; split; [intros n0 Hn0; rewrite AA by lia; reflexivity | exact DD]) end.
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. lazymatch goal with |- apost_base _ _ _ _ _ _ _ _ _ _ _ _ (mkCfg (mkst ?rr _ ?m _) ?d) => exists ly, S, rr, m, d end.
split; [cbn [ms_regs]; rewrite R1; rewrite ?(proj1 HAEx) by lia; rewrite (ER 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs B LAWS Hsegs); exact HJ2|].
split; [eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs che_extra HS); [exact HAE32 | vm_compute; reflexivity]|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite Hop. cbn [ms_regs]. rewrite R10. reflexivity.
Qed.
End CH.
