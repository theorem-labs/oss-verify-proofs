(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC2o YC10 YC1b YC2u YC4r YC16 YC12 YC14 YC20 YC3q YC0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awr_a_rec Usp E32u Hing HTS :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
first
[ eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |] ]
| |- awr_ok _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPa, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
end
| fail 1 "awr_a: no rule for the head region" ];
awr_a_rec Usp E32u Hing HTS
end.
Ltac awr_a Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_a_rec Usp E32u Hing HTS.
Ltac af_join0 HS target :=
norm_ss HS;
let tg := eval red in target in
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let rs := eval cbn [ss_mem] in (ss_mem tg) in
pose proof (st_ok_submem trasegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in
let fa := eval cbn [ss_facts f_atoms] in (f_atoms (ss_facts tg)) in
let cs := eval cbn [ss_facts f_conds] in (f_conds (ss_facts tg)) in
let al := eval cbn [ss_facts f_alias] in (f_alias (ss_facts tg)) in
pose proof (st_ok_facts_incl3 trasegs Ex ssx msx fa cs al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS end;
norm_ss HS;
lazymatch type of HS with st_ok _ _ ?ssx _ => first [change ssx with target in HS | idtac "JOIN-MISMATCH" ssx tg; fail] end.
Ltac af_join HS target N deads := rn_join HS target N deads.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section h.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Lemma af_E_havoc : forall regs g s cfp lpal img fattr fgen delay nlp tidx E N vals,
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E -> (54 <= N)%nat ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx (havoc E N vals).
Proof.
intros regs g s cfp lpal img fattr fgen delay nlp tidx E N vals HE HN.
destruct HE as (EE & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53).
unfold af_E. rewrite !ew_havoc_old by lia.
split; [intros n r Hn; rewrite ew_havoc_old by (pose proof (bv_unsigned_in_range 5 r); change (bv_modulus 5) with 32 in *; lia); exact (EE n r Hn)|].
repeat (split; [assumption|]). assumption.
Qed.

Lemma af_frame_of_region : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) wlo whi,
region_ok trasegs E m (YQ0b.mkRegion (Some 2%nat) (-104) 0 wlo whi
[YQ0b.mkChunk (-104) (CVal 8 (SOff 27 0)); YQ0b.mkChunk (-96) (CVal 8 (SOff 26 0)); YQ0b.mkChunk (-88) (CVal 8 (SOff 25 0));
YQ0b.mkChunk (-80) (CVal 8 (SOff 24 0)); YQ0b.mkChunk (-72) (CVal 8 (SOff 23 0)); YQ0b.mkChunk (-64) (CVal 8 (SOff 22 0));
YQ0b.mkChunk (-56) (CVal 8 (SOff 21 0)); YQ0b.mkChunk (-48) (CVal 8 (SOff 20 0)); YQ0b.mkChunk (-40) (CVal 8 (SOff 19 0));
YQ0b.mkChunk (-32) (CVal 8 (SOff 18 0)); YQ0b.mkChunk (-24) (CVal 8 (SOff 9 0)); YQ0b.mkChunk (-16) (CVal 8 (SOff 8 0));
YQ0b.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
af_frame m sp0 regs.
Proof.
intros E m sp0 regs wlo whi HR Hsp HE j r Hj.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some af_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
do 13 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
let od' := eval vm_compute in od in change od with od';
let n := eval vm_compute in (Z.to_nat R) in
apply (field_of_region E m 2 sp0 _ (-104) 0 wlo whi od' 8 (SOff n 0) _ HR Hsp);
[ cbn; tauto
| cbn [sv_denot]; rewrite (HE n (Z_to_bv 5 R) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
| exact HRr
| cbn; lia ] end
| ]). cbn in Hj13. lia.
Qed.
Lemma af_side_kept : forall H (m m' : word -> option byte) g s1 (Zs : Z -> Prop),
af_side (mrestrict H m) g s1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview trasegs H m' a = aview trasegs H m a) ->
(forall i, 0 <= i < 48 -> 0 <= cg_raw s1 + i < 2 ^ 64 /\ ~ Zs (cg_raw s1 + i)) ->
(forall f i, In (Some f) (cg_frames s1) -> 0 <= i < 40 -> 0 <= fr_ptr f + i < 2 ^ 64 /\ ~ Zs (fr_ptr f + i)) ->
af_side (mrestrict H m') g s1.
Proof.
intros H m m' g s1 Zs [Hr Hf] UN Zr Zf. split.
- apply (obj_at_blk_kept H H m m' _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. destruct (Zr i Hi) as [Hb Hn]. exact (UN _ Hb Hn).
- intros f Hin. apply (obj_at_blk_kept H H m m' _ LAY_Frame _ 40 (Hf f Hin) lay_inside_Frame).
intros i Hi. destruct (Zf f i Hin Hi) as [Hb Hn]. exact (UN _ Hb Hn).
Qed.
Lemma af_frame_in_blocks : forall g s1 N f, In (Some f) (cg_frames s1) -> In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s1 N).
Proof.
intros g s1 N f Hin. unfold cgif_blocks. right. right. apply in_app_iff. right.
unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hin | left; reflexivity].
Qed.
Definition ZsA (g sp0 : Z) (a : Z) : Prop := (sp0 - 224 <= a < sp0) \/ (g + 88 <= a < g + 92).
Lemma af_sideZ : forall ly S W mem md g s1 N cb lya sp0,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> astk_ok TADDFRAME_STK lya sp0 ->
(forall i, 0 <= i < 48 -> 0 <= cg_raw s1 + i < 2 ^ 64 /\ ~ ZsA g sp0 (cg_raw s1 + i)) /\
(forall f i, In (Some f) (cg_frames s1) -> 0 <= i < 40 -> 0 <= fr_ptr f + i < 2 ^ 64 /\ ~ ZsA g sp0 (fr_ptr f + i)).
Proof.
intros ly S W mem md g s1 N cb lya sp0 HAR HP Hstk.
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). pose proof asan_consts as (C1 & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
assert (HP' : Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: ((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1)) ++ cb)) by exact HP.
assert (Hraw : In (cg_raw s1, RAW_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right. apply in_app_iff. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hraw) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (cg_raw s1, RAW_SIZE) _ HAR HP' ltac:(apply in_app_iff; left; left; reflexivity)) as HdGR.
unfold zdisjoint, block_rng in HdGR. cbn [fst snd] in HdGR. change (req_size CGIF_SIZE) with 96 in HdGR. change (req_size RAW_SIZE) with 48 in HdGR.
split.
- intros i Hi. unfold ZsA. split; [lia|]. lia.
- intros f i Hf Hi.
assert (Hft : In (fr_ptr f, FRAME_SIZE) (((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1)) ++ cb)).
{ apply in_app_iff. left. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf | left; reflexivity]. }
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right. exact Hft. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HP' Hft) as HdGF.
unfold zdisjoint, block_rng in HdGF. cbn [fst snd] in HdGF. change (req_size CGIF_SIZE) with 96 in HdGF. change (req_size FRAME_SIZE) with 40 in HdGF.
unfold ZsA. split; [lia|]. lia.
Qed.
Lemma U_zext32_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt false 32 (SOff n 0)) = v.
Proof.
intros E n v Hn Hv. rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_sltu1_and : forall E a m, 0 <= m < 2 ^ 64 ->
U E (SAlu ALU_SLTU (SAlu ALU_AND a (SLit m)) (SLit 1)) = (if Z.land (U E a) m =? 0 then 1 else 0).
Proof.
intros E a m Hm. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_and_lit E a m Hm), U_lit by lia.
pose proof (proj2 (Z.land_nonneg (U E a) m) ltac:(pose proof (U_range E a); lia)) as H0.
destruct (Z.ltb_spec (Z.land (U E a) m) 1); destruct (Z.eqb_spec (Z.land (U E a) m) 0); try lia; apply zcanon_id; unfold M64; lia.
Qed.
Lemma af_E_agree : forall regs g s cfp lpal img fattr fgen delay nlp tidx E E',
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E -> (forall n, (n < 54)%nat -> ew E' n = ew E n) ->
af_E regs g s cfp lpal img fattr fgen delay nlp tidx E'.
Proof.
intros regs g s cfp lpal img fattr fgen delay nlp tidx E E' HE HA.
destruct HE as (EE & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53).
unfold af_E. rewrite !HA by lia.
split; [intros n r Hn; rewrite HA by (pose proof (bv_unsigned_in_range 5 r); change (bv_modulus 5) with 32 in *; lia); exact (EE n r Hn)|].
repeat (split; [assumption|]). assumption.
Qed.
Lemma af_pre_agree : forall ly S W regs mem md g cfp s N fattr E E' ms1 md1,
af_pre B ly S W regs mem md g cfp s N fattr E ms1 md1 -> (forall n, (n < 68)%nat -> ew E' n = ew E n) ->
af_pre B ly S W regs mem md g cfp s N fattr E' ms1 md1.
Proof.
intros ly S W regs mem md g cfp s N fattr E E' ms1 md1 (H1 & H2 & H3 & H4 & H5 & H6 & H7) HA.
repeat (split; [assumption|]). split; [|exact H7]. rewrite HA by lia. exact H6.
Qed.
Lemma af_ptrs : forall ly S W mem md g s N cb i,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
(nth i (cg_frames s) None = None /\ frame_ptr (nth i (cg_frames s) None) = 0) \/
(exists f, nth i (cg_frames s) None = Some f /\ 4096 <= fr_ptr f /\ fr_ptr f + 40 <= alloc_ceiling).
Proof.
intros ly S W mem md g s N cb i HAR HP.
destruct (nth_in_or_default i (cg_frames s) None) as [Hin | Hd].
- destruct (nth i (cg_frames s) None) as [f|] eqn:Hn; [| left; split; reflexivity].
right. exists f. split; [reflexivity|].
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact (af_frame_in_blocks g s N f Hin). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & H4096 & Hceil & _). change (req_size FRAME_SIZE) with 40 in Hceil. lia.
- rewrite Hd. left. split; reflexivity.
Qed.
Lemma st_ok_respell : forall E ss ms (r : bv 5) (e' : sv),
st_ok trasegs E ss ms -> bv_eqb r 0 = false -> sv_denot E e' = sv_denot E (sr_get (ss_regs ss) r) ->
st_ok trasegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e') (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e' HS Hr He. apply (st_ok_regs trasegs); [exact HS|].
intros r0. destruct (decide (r0 = r)) as [-> | Hne]; [rewrite sr_get_set_same by exact Hr; exact He | rewrite sr_get_set_other by exact Hne; reflexivity].
Qed.
Lemma shadow_slot_step : forall E g o, ew E 32 = Z_to_bv 64 g -> ew E 38 = Z_to_bv 64 SB -> 0 <= g -> g + 96 <= alloc_ceiling -> 0 <= o -> o + 8 <= 96 -> g mod 8 = 0 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 (o + 8)) (SLit 3)) (SOff 38 0)) =
alu64 ALU_ADD (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 o) (SLit 3)) (SOff 38 0))) (Z_to_bv 64 1).
Proof.
intros E g o E32 E38 Hg0 Hg Ho0 Ho Hal. pose proof asan_consts as (C1 & _).
rewrite !(denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia). rewrite cl_alu64_addw. f_equal.
replace (g + (o + 8)) with ((g + o) + 1 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
End h.
End c.
Ltac side_win Usp E32u :=
let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u in Hrr; unfold ZsA; clear - Hrr; lia |]);
destruct Hin.
Ltac side_step HSD HGK HZr HZf HZg Usp E32u :=
lazymatch goal with HFr : frame_of _ _ (mrestrict ?Hh _) (mrestrict _ ?m') |- _ =>
lazymatch type of HZr with forall i, _ -> _ /\ ~ ?Zs _ =>
let UN := fresh "UN" in let HSD' := fresh "HSD" in let HGK' := fresh "HGK" in
pose proof (kept_of_frame _ _ _ _ _ Zs HFr ltac:(side_win Usp E32u)) as UN;
pose proof (af_side_kept _ _ _ _ _ Zs HSD UN HZr HZf) as HSD'; clear HSD; rename HSD' into HSD;
lazymatch type of HGK with forall i, _ -> _ -> mbyte _ _ (?g + i) = mbyte _ ?m0 (_ + i) =>
assert (HGK' : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte trasegs (mrestrict Hh m') (g + i) = mbyte trasegs m0 (g + i))
by (let i := fresh "i" in let Hi := fresh "Hi" in let Hn := fresh "Hn" in intros i Hi Hn; etransitivity; [| exact (HGK i Hi Hn)]; apply (mbyte_of_aview trasegs); apply UN; [|unfold ZsA]; clear - Hi Hn HZg; lia);
clear HGK UN; rename HGK' into HGK end end end.
Ltac cregA HS EEo :=
lazymatch goal with |- getr _ ?r = getr _ _ =>
let R := fresh "R" in rreg HS r R; rewrite R; clear R;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
apply EEo; reflexivity end.
Ltac hcA E40 E49 Rattr Rfattr Ucur Rcur H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_and_lit in H by (clear; lia);
rewrite ?(U_zext32_atom _ 40 _ E40 Rattr), ?(U_zext32_atom _ 49 _ E49 Rfattr) in H;
rewrite ?(cl_U_sext32 _ (SOff 37 0) _ Ucur Rcur) in H;
rewrite ?U_lit in H by (clear; lia);
try (apply (proj1 (Bool.negb_true_iff _)) in H); try (apply (proj1 (Bool.negb_false_iff _)) in H);
first [ apply (proj1 (Z.eqb_eq _ _)) in H | apply (proj1 (Z.eqb_neq _ _)) in H | idtac ].
Ltac agreeE_tac :=
let n := fresh "n" in let Hn := fresh "Hn" in
intros n Hn; repeat first [rewrite ew_havoc_old by lia | rewrite ew_ewset_other by lia]; reflexivity.
Ltac Unorm E HAE H :=
repeat (match type of H with context [U ?Ex _] =>
lazymatch Ex with E => fail | _ =>
let HAGx := fresh "HAG" in
assert (HAGx : env_agree 54 E Ex) by (env_agree_chain HAE);
rewrite !(U_agree 54 E _ _ HAGx) in H by (vm_compute; reflexivity); clear HAGx end end).
Ltac g_widen HS E32u HgP :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 32%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trasegs Ex ssx msx i r (set_window r 0 96) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trasegs Ex _ r 0 96 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
rewrite E32u; let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable trasegs); apply HgP; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac respell_shadow HS r o E32 E38 Hg0 Hgc Hal :=
lazymatch type of E32 with _ = Z_to_bv 64 ?g =>
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let HS3 := fresh "HS3" in let o8 := eval vm_compute in (o + 8) in
pose proof (st_ok_respell Ex ssx msx r (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 o8) (SLit 3)) (SOff 38 0)) HS eq_refl
ltac:(lazymatch goal with |- _ = sv_denot _ (sr_get ?a ?rr) => let v := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with v end;
change o8 with (o + 8);
etransitivity; [apply (shadow_slot_step Ex g o); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E38
| exact Hg0 | exact Hgc | clear; lia | clear; lia | exact Hal] |];
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end end.
Ltac g_field HRg HB32 off n HG :=
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch type of HB32 with _ = ?g =>
lazymatch cs with context [YQ0b.mkChunk off (CVal n ?e)] =>
lazymatch e with
| SLit ?z =>
let v := eval vm_compute in (z mod 2 ^ (8 * Z.of_N n)) in
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi off n e HRg HB32 ltac:(cbn; tauto) ltac:(cbn; lia)) as HG;
change (bv_unsigned (sv_denot Ex (SLit z)) mod 2 ^ (8 * Z.of_N n)) with v in HG
| SOff ?a 0 =>
match goal with Ea : ew _ a = Z_to_bv 64 ?v |- _ =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi off n e HRg HB32 ltac:(cbn; tauto) ltac:(cbn; lia)) as HG;
cbn [sv_denot] in HG; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in HG; rewrite ?ew_ewset_other in HG by lia; rewrite ?ew_havoc_old in HG by lia;
rewrite Ea, ?Z.add_0_r, ?Z_to_bv_bv_unsigned in HG; rewrite (unsigned_lit_small v) in HG by lia
end
| _ =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi off n e HRg HB32 ltac:(cbn; tauto) ltac:(cbn; lia)) as HG
end
end end end.
