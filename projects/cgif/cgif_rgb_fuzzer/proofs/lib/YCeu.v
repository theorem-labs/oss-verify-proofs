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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YCfy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCdv YCe9 YCfx YCex YCf8.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma aview_kept_ro : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) -> forall a, aview trbsegs H m' a = aview trbsegs H m a.
Proof.
intros E rs H m m' HF Hno a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E rs H m m' 0 HF ltac:(lia)); [intros x Hx; apply Hno | apply Z.mod_pos_bound; lia].
Qed.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy.
Definition cplp (p : Z) : Z := 18446744073709551615 - p.
Definition CPY_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 24; 28; 29; 30; 31]%bv.
Definition CPY_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 20; 21; 22; 23; 26; 27]%bv.
Lemma cpy_clob_cases : forall r : bv 5, reg_in r CPY_CLOB = false -> r = 0%bv \/ r = 25%bv \/ In r CPY_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | right; left; reflexivity | vm_compute in Hr; discriminate | right; right; cbv; tauto] |]). destruct Hin.
Qed.
Definition cpy_loc : YQ0b.region :=
YQ0b.mkRegion (Some 9%nat) 160 176 160 160 [YQ0b.mkChunk 160 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 168 (CVal 8 (SOff 32 0))].
Definition cpy_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, HPTR 0); (35%nat, HPTR 0);
(18%nat, mkAF 0 4294967295 0); (19%nat, mkAF 0 65534 0); (20%nat, mkAF 18446603336221196288 18446744073709551615 0);
(21%nat, mkAF 1 65535 0); (22%nat, mkAF 0 65534 0); (23%nat, mkAF 1 65535 0); (24%nat, mkAF 0 4294967295 0);
(26%nat, mkAF 1 65535 0); (27%nat, mkAF 1 65535 0) ] []
[ (SAlu ALU_ADD (SOff 24 0) (SOff 32 0), SOff 34 0); (SAlu ALU_ADD (SOff 22 0) (SOff 34 0), SOff 35 0) ].
Definition ss_cpy (pc : Z) : sstate := mkSS pc (sr_set sr_atoms 25 (SLit 1)) [cpy_loc] None cpy_facts.
Ltac ro_no :=
let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
intros a (rg & Hin & Hw); lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia|]); destruct Hin.
Lemma fl_cpy : forall (m : nat) (r : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos
(pt fimg N w h top left Wd Hd : Z),
h - r <= Z.of_nat m -> 0 <= r < h ->
1 <= w -> 0 <= left -> left + w <= Wd -> 1 <= h -> 0 <= top -> top + h <= Hd -> 1 <= Wd <= 65535 -> Hd <= 65535 -> Wd * Hd = N -> N <= 100000000 ->
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pt, w * h) (ablocks B lyc Sc) -> In (fimg, N) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pt, w * h) blc -> pt <= a < pt + w * h ->
awr_byte TFLUSH_STK sp0 FP (ablocks B ly S) blc lyq ownq a) ->
(pt + req_size (w * h) <= fimg \/ fimg + req_size N <= pt) ->
spZ regs = sp1 -> sp0 - 368 <= sp1 <= sp0 - 352 -> sp1 mod 16 = 0 -> getr regs 9 = Z_to_bv 64 sp1 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 18 = Z_to_bv 64 (r * w) -> getr regs 19 = Z_to_bv 64 r -> getr regs 20 = Z_to_bv 64 (cplp pt) -> getr regs 21 = Z_to_bv 64 w ->
getr regs 22 = Z_to_bv 64 left -> getr regs 23 = Z_to_bv 64 h -> getr regs 24 = Z_to_bv 64 ((top + r) * Wd) -> getr regs 25 = Z_to_bv 64 1 ->
getr regs 26 = Z_to_bv 64 w -> getr regs 27 = Z_to_bv 64 Wd ->
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 160) 8 pt -> val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg ->
SRr trbsegs W (mkCfg (mkst regs (Z_to_bv 64 0x882bc) memc (seg_rom trbsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 0x88314) mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
(forall q : bv 5, reg_in q CPY_CLOB = false -> getr regs' q = getr regs q) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pt <= a < pt + w * h) -> ~ (sp1 - ESTACK <= a < sp1) ->
aview trbsegs (w_H W) mem' a = aview trbsegs (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction m as [|m IH]; intros r W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt fimg N w h top left Wd Hd
Hm Hr Hw1 Hl0 Hlw Hh1 Ht0 Hth HWd HHd HN HNle HJ Hpt Himg Hpawr Hsep Hsp Hsp1 Hsp1al H9 Hgp Htp H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 V160 V168; [lia|].
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (FFS : TFLUSH_STK = 17440) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hw65 : w <= 65535) by (clear - Hlw HWd Hl0; lia). assert (Hh65 : h <= 65535) by (clear - Hth Ht0 HHd; lia).
assert (Hwh1 : 1 <= w * h) by (clear - Hw1 Hh1; nia).
assert (HN1 : 1 <= N) by (clear - HN HWd Hth Hh1 Ht0; nia).
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [lia | reflexivity]).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [lia | reflexivity]).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt (w * h) HAR Hpt) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR Hpt) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc fimg N HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih. rewrite HrqN in Hiceil, Hipres.
pose proof (blk_off_img _ _ _ _ _ _ fimg N HAR Himg) as Hih_img.
rewrite Hrq, HrqN in Hsep.
assert (Hrw : 0 <= r * w /\ r * w + w <= w * h) by (clear - Hr Hw1; nia).
assert (Hrow : 0 <= (top + r) * Wd /\ (top + r) * Wd + left + w <= N) by (clear - Hr Ht0 Hth HWd Hl0 Hlw HN; nia).
assert (Hrow32 : (top + r) * Wd < 2 ^ 32) by (clear - Hrow HNle Hl0 Hw1; lia).
assert (HwhM : w * h < 2 ^ 32) by (clear - Hw65 Hh65 Hw1 Hh1; nia).
set (rowp := fimg + (top + r) * Wd) in *.
remember (Ereg regs [Z_to_bv 64 fimg; Z_to_bv 64 pt; Z_to_bv 64 rowp; Z_to_bv 64 (rowp + left)]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 fimg; Z_to_bv 64 pt; Z_to_bv 64 rowp; Z_to_bv 64 (rowp + left)]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q) by (intros n q Hn; subst E; apply ew_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite H19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20. pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite H21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite H22 in E22. pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite H24 in E24. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite H26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 pt) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 rowp) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (rowp + left)) by (subst E; exact (ew_Ereg_extra regs _ 3)).
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok trbsegs E (ss_cpy 0x882bc) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x882bc) memc (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_cpy.
apply (rn_st_ok_any E 0x882bc _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite H25; cbn [sv_denot]; reflexivity].
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]; unfold region_ok, cpy_loc;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 160 8 _ pt); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I|]].
+ cbn [cpy_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E32, E33, E34, E35, E18, E19, E20, E21, E22, E23, E24, E26, E27, !unsigned_lit_small by (unfold cplp, rowp; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold cplp, rowp. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end].
+ cbn [cpy_facts f_alias alias_ok].
split; [rewrite (denot_add_atoms E 24 32 ((top + r) * Wd) fimg E24 E32) by lia; cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; unfold rowp; lia|].
split; [rewrite (denot_add_atoms E 22 34 left rowp E22 E34) by (unfold rowp; lia); cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; lia | exact I]. }
clear HE. pose proof HS as HS0.
aj_run trbtbl_lib_ok HS HJ; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
srr_branch_with trbtbl_lib_ok HS.
1: { exfalso. lazymatch goal with Hb : branch_taken BC_LTU _ _ = true |- _ =>
rewrite branch_ltu_U in Hb; rewrite (U_atom E 34 rowp E34), (U_atom E 32 fimg E32) in Hb by (unfold rowp; lia); apply Z.ltb_lt in Hb; unfold rowp in Hb; lia end. }
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
aj_run trbtbl_lib_ok HS HJ; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
srr_branch_with trbtbl_lib_ok HS.
1: { exfalso. lazymatch goal with Hb : branch_taken BC_LTU _ _ = true |- _ =>
rewrite branch_ltu_U in Hb; rewrite (U_atom E 35 (rowp + left) E35), (U_atom E 34 rowp E34) in Hb by (unfold rowp; lia); apply Z.ltb_lt in Hb; lia end. }
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => clear Hb end.
aj_run trbtbl_lib_ok HS HJ; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
assert (Da0 : sv_denot E (SAlu ALU_ADD (SOff 18 0) (SOff 33 0)) = Z_to_bv 64 (pt + r * w)) by (rewrite (denot_add_atoms E 18 33 (r * w) pt E18 E33) by lia; f_equal; lia).
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (pt + r * w)) Da0 Ra0.
rewrite E35 in Ra1. unfold rowp in Ra1.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (HAV3 : forall a, aview trbsegs (w_H W) (ms_mem msx) a = aview trbsegs (w_H W) memc a);
[ intros a; cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) a); cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) a); cbn [ms_mem];
exact (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) a) |];
assert (HPR3 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a);
[ intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply (apresent_grows _ _ _ _ HG1); exact Ha |] end.
cbn [ms_mem] in HAV3, HPR3.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ fimg N HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _). rewrite HrqN in Hipres1.
change (Z_to_bv 64 335988) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at trbsegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY W (ms_regs msX) (ms_mem msX) TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pt + r * w) (fimg + (top + r) * Wd + left) w (sp1 - sp0) _ HJ) end.
- exact Ra0.
- exact Ra1.
- rewrite Ra2, E26. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp, Usp. lia.
- rewrite Zminus_mod, Hsp1al, Hal16. reflexivity.
- lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- vm_compute. reflexivity.
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block trbsegs B LAWS lyc Sc W _ _ pt (w * h) _ _ HAR1 Hpt); rewrite ?Hrq; lia.
- apply (range_addressable_of_block trbsegs B LAWS lyc Sc W _ _ pt (w * h) _ _ HAR1 Hpt); rewrite ?Hrq; lia.
- intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS lyc Sc W _ _ pt (w * h) _ _ HAR1 Hpt); rewrite ?Hrq; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp, Usp; intro; lia].
apply (aview_some_of_apresent trbsegs). apply (proj1 (Hipres1 a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block trbsegs B LAWS lyc Sc W _ _ fimg N _ _ HAR1 Himg); rewrite ?HrqN; lia|]. split.
+ apply (range_addressable_of_block trbsegs B LAWS lyc Sc W _ _ fimg N _ _ HAR1 Himg); rewrite ?HrqN; lia.
+ intros _. apply (shadow_hull_vis_of_block trbsegs B LAWS lyc Sc W _ _ fimg N _ _ HAR1 Himg); rewrite ?HrqN; lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
jafter_call_keep HS 36%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q); [ cbn [ms_mem restrict] | specialize (HS2 HQ); clear HQ ] end.
{ lazymatch goal with |- Forall (region_kept _ ?Ev (mrestrict _ ?m0) _) _ =>
eapply (regions_kept_out2 Ev (w_H W) m0 mem2 (pt + r * w) (pt + r * w + w) (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0)) _ Hout2 Hpres2) end.
apply Forall_cons; [|apply Forall_nil]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E9, unsigned_lit_small by lia. unfold ESTACK. clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hpceil Hph Hrw Hwh1; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 36 _) as Eb eqn:HEb in HS.
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 fimg; Z_to_bv 64 pt; Z_to_bv 64 rowp; Z_to_bv 64 (rowp + left)]) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HEb.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 19%nat ltac:(lia)) as F19. rewrite E19 in F19.
pose proof (OLD 21%nat ltac:(lia)) as F21. rewrite E21 in F21. pose proof (OLD 23%nat ltac:(lia)) as F23. rewrite E23 in F23.
pose proof (OLD 24%nat ltac:(lia)) as F24. rewrite E24 in F24. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
aj_run trbtbl_lib_ok HS HJ2; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr4. rename HG into HG4. clear HF.
srr_branch_with trbtbl_lib_ok HS.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ =>
rewrite branch_ltu_U in Hb; rewrite (U_atom_off Eb 19 r 1 F19), (U_atom Eb 23 h F23) in Hb by lia; apply Z.ltb_lt in Hb; rename Hb into Hc end.
aj_run_to trbtbl_lib_ok HS HJ2 0x882bc; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ CPY_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 ((top + r) * Wd + Wd)) (denot_add_atoms Eb 24 27 ((top + r) * Wd) Wd F24 F27 ltac:(lia) ltac:(lia) ltac:(lia)) N24.
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (r * w + w)) (denot_add_atoms Eb 18 21 (r * w) w F18 F21 ltac:(lia) ltac:(lia) ltac:(lia)) N18.
rreg HS (19%bv : bv 5) N19. rewrite F19 in N19. rreg HS (25%bv : bv 5) N25.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
assert (HAV5 : forall a, 0 <= a < 2 ^ 64 -> ~ (pt <= a < pt + w * h) -> ~ (sp1 - ESTACK <= a < sp1) -> aview trbsegs (w_H W) (ms_mem msx) a = aview trbsegs (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr5 ltac:(ro_no) a); cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr4 ltac:(ro_no) a);
rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)); exact (HAV3 a) |];
assert (HPR5 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msx) a);
[ intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG5); apply (apresent_grows _ _ _ _ HG4); apply Hpres2; apply HPR3; exact Ha |];
assert (V160n : val_mem trbsegs (mrestrict (w_H W) (ms_mem msx)) (sp1 + 160) 8 pt);
[ intros kk Hkk; rewrite <- (V160 kk Hkk); apply (mbyte_of_aview trbsegs); apply HAV5; unfold ESTACK; clear - Hkk Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hpceil Hph Hwh1; lia |];
assert (V168n : val_mem trbsegs (mrestrict (w_H W) (ms_mem msx)) (sp1 + 168) 8 fimg);
[ intros kk Hkk; rewrite <- (V168 kk Hkk); apply (mbyte_of_aview trbsegs); apply HAV5; unfold ESTACK; clear - Hkk Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 Hpceil Hph Hwh1; lia |] end.
cbn [ms_mem] in HAV5, HPR5, V160n, V168n.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (r + 1) W (ms_regs msX) (ms_mem msX) _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt fimg N w h top left Wd Hd);
[ lia | lia | exact Hw1 | exact Hl0 | exact Hlw | exact Hh1 | exact Ht0 | exact Hth | exact HWd | exact HHd | exact HN | exact HNle
| exact HJ2 | exact Hpt | exact Himg | exact Hpawr | rewrite Hrq, HrqN; exact Hsep
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact Hsp1 | exact Hsp1al | rewrite (HK 9%bv ltac:(cbv; tauto)); exact H9
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite N18; f_equal; lia
| rewrite N19; cbn [sv_denot]; rewrite unsigned_lit_small by lia; f_equal; lia
| rewrite (HK 20%bv ltac:(cbv; tauto)); exact H20 | rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21
| rewrite (HK 22%bv ltac:(cbv; tauto)); exact H22 | rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23
| rewrite N24; f_equal; lia
| rewrite N25; reflexivity
| rewrite (HK 26%bv ltac:(cbv; tauto)); exact H26 | rewrite (HK 27%bv ltac:(cbv; tauto)); exact H27
| exact V160n | exact V168n ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros q Hq; rewrite (HK3 q Hq); destruct (cpy_clob_cases q Hq) as [-> | [-> | Hq']];
[ cbn [ms_regs]; rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity
| exact (HK q Hq')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HAV5 a Ha Hna Hnb).
+ intros a Ha. apply Hpres3. apply HPR5. exact Ha.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ =>
rewrite branch_ltu_U in Hb; rewrite (U_atom_off Eb 19 r 1 F19), (U_atom Eb 23 h F23) in Hb by lia; apply Z.ltb_ge in Hb; rename Hb into Hc end.
aj_run_to trbtbl_lib_ok HS HJ2 0x88314; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regs _ CPY_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg HS (25%bv : bv 5) N25.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ2|].
split; [intros q Hq; destruct (cpy_clob_cases q Hq) as [-> | [-> | Hq']];
[ cbn [ms_regs]; rewrite (st_ok_reg trbsegs _ _ _ 0%bv HS), (st_ok_reg trbsegs _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity
| exact (HK q Hq')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ _ _ _ _ HFr5 ltac:(ro_no) a). cbn [ms_mem]. rewrite (aview_kept_ro _ _ _ _ _ HFr4 ltac:(ro_no) a).
rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)). exact (HAV3 a).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG5). apply (apresent_grows _ _ _ _ HG4). apply Hpres2. apply HPR3. exact Ha.
Qed.
End c.
End b.
