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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC1z YC1y YC27 YC23 YC28 YC1w YC24 YC20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma fl_R5_aux : fl_from B ss_X (INV_X B) -> fl_from B ss_R5 (INV_R5 B).
Proof.
intros RX. fl_prelude.
pose proof HINV as (Hk3 & (res & E479 & Hres) & (pt & E451 & Hrpt & Hpt)).
unfold fl_FP in Hpt. cbn [c_ly c_S c_regs c_f c_s] in Hpt.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)).
{ intros x Hx. destruct Hpt as [(_ & HP3) | (_ & (n & _ & HP3 & _))]; (eapply Permutation_in; [apply Permutation_sym; exact HP3|]); [exact Hx | apply in_app_iff; left; exact Hx]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK FLBspan 0x53100.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi; lia). clear_frames.
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rreg HS (10%bv : bv 5) Ra0.
assert (Usp3 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp).
assert (Ugp : ew E 3 = getr regs 3) by (rewrite (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl)).
assert (Utp : ew E 4 = getr regs 4) by (rewrite (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl)).
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E70; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47; lia);
assert (EraX : raZ rg = 0x87a18) by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview trasegs (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem trasegs _ _ _ _ Vra Qra) (rdword_of_val_mem trasegs _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS; lia) Qal8
ltac:(clear - Htop32; lia) ltac:(clear - Hsp1; lia))
| ] end.
pose proof HJ3 as (_ & HLY3 & _ & _ & _ & _ & Hnev3 & _ & _ & _ & _ & _ & _ & Hpres3' & _).
assert (HEVc : vev S3 < VEV_MAX).
{ replace EV_RAWADD with 27 in Hk3 by reflexivity. rewrite HEV in Hev. clear - Hnev3 Hev Hk3. lia. }
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 340224 with (pc_wrap_free (as_code B)) by (rewrite HBcode; reflexivity).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
apply (SRr_bind trasegs _ _
(fun W4 c4 => exists ly4 S4 regs4 mem4 md4,
c4 = mkCfg (mkst regs4 (Z_to_bv 64 0x87a18) mem4 (seg_rom trasegs)) md4 /\
ajournal trasegs B TFLUSH_STK (spZ regs) [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s + 40, cg_raw s + 44)] ly S W mem md [(2, fpos)] ly4 S4 W4 mem4 md4 (k + 1) /\
aregs_preserved (ms_regs msX) regs4 /\ Permutation (ablocks B ly4 S4) (ablocks B ly S) /\ frames S4 = frames S3 /\
exists Er : Z -> Prop, acall_kept trasegs B ly3 S3 W3 (ms_mem msX) W4 mem4 (sp1 - ASTACK) sp1 Er /\
(forall a, F <= a < F + 256 -> ~ Er a) /\ (forall a, SB <= a < 17594333495296 -> ~ Er a) /\
(forall a, g <= a < g + 96 -> ~ Er a) /\ (forall a, fr_ptr f <= a < fr_ptr f + 40 -> ~ Er a))) end.
{ destruct Hpt as [(Hp0 & HP3) | (Hp1 & (n & Hn0 & HP3 & Haft))].
-
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (aj_free_null_at trasegs B LAWS tra_segs_low errno_low ML AFREE W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k (sp1 - spZ regs) (Z_to_bv 64 0x87a18) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3)
| ] end.
+ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E451, Hp0. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVc.
+ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x53244 by (rewrite HBcode; reflexivity). apply (tl_universe B TL).
apply (fl_trace_in 0x53244 0x87a18); [exact Hctx | exact EraX | left; split; reflexivity].
+ cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & HK).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
split; [eapply Permutation_trans; [exact HPerm4 | exact HP3]|]. split; [exact Hfrs4|].
exists (fun _ => False). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
repeat split; intros a _ Hn; exact Hn.
-
assert (Hpt3 : In (pt, n) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HP3|]; apply in_app_iff; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pt n HAR3 Hpt3) as (_ & _ & _ & Hph_ia & _ & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ pt n HAR3 Hpt3) as Hph_img.
pose proof (sep_block_frame trasegs _ LAWS ly3 S3 _ _ _ pt n 2 fpos HAR3 Hpt3 Hfin3) as HdFP.
unfold zdisjoint in HdFP; cbn [fst snd] in HdFP; change (fs_frame_bytes 2) with 256 in HdFP; rewrite EFA3 in HdFP. fold F in HdFP.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt n g CGIF_SIZE HAR3 HP3 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt n (fr_ptr f) FRAME_SIZE HAR3 HP3 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (aj_free_at trasegs B LAWS tra_segs_low errno_low ML AFREE W3 (ms_regs msX) (ms_mem msX) TFLUSH_STK (spZ regs) _ ly S W mem md [(2, fpos)]
ly3 S3 mdX k pt n (sp1 - spZ regs) (Z_to_bv 64 0x87a18) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 Hpt3)
| ] end.
+ rewrite Ra0, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite E451. reflexivity.
+ rewrite EspX. clear; lia.
+ rewrite Zminus_mod, Hsp1al16, Hal16. reflexivity.
+ clear - Hsp1; lia.
+ rewrite FFS. unfold ASTACK. clear - Hsp1; lia.
+ rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Ugp. exact Hgp.
+ rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side. rewrite Utp. exact Htp.
+ exact Rra.
+ apply ret_ok_even. vm_compute. reflexivity.
+ exact HEVc.
+ apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1); [rewrite EspX; clear - Hsp1 Hceil Hslo Hstk0 FFS C1; lia | exact Es0X | rewrite EraX; clear; lia].
+ replace (pc_free_ra0 (as_code B)) with 0x53244 by (rewrite HBcode; reflexivity). apply (tl_universe B TL).
apply (fl_trace_in 0x53244 0x87a18); [exact Hctx | exact EraX | left; split; reflexivity].
+ exact Haft.
+ cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl3 & Ebl4) & Hfrs4 & HK).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|]. split; [exact HJ4|]. split; [exact HP4|].
split; [rewrite Ebl4; apply Permutation_sym; apply (@Permutation_cons_app_inv _ _ l1 l2 (pt, n)); rewrite <- Ebl3;
apply Permutation_sym; eapply Permutation_trans; [exact HP3 | apply Permutation_app_comm]|].
split; [exact Hfrs4|].
exists (fun a => pt <= a < pt + req_size n). replace (spZ regs + (sp1 - spZ regs)) with sp1 in HK by (clear; lia). split; [exact HK|].
pose proof (req_size_pos n Hn0) as Hrq.
split; [intros a Ha Hx; clear - Ha Hx HdFP; lia|]. split; [intros a Ha Hx; clear - Ha Hx Hph_ia Hrq C3; unfold SB in Ha; zone_lia|].
split; [intros a Ha Hx; clear - Ha Hx HdPG; lia | intros a Ha Hx; clear - Ha Hx HdPC; lia]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPerm4 & Hfrs4 & Er & HK & HErF & HErLo & HErG & HErC).
clear Rra Rsp Rgp Rtp Rs0 Ra0 Vra Vs0 Hch1.
pose proof (proj1 HJ4) as HAR4.
assert (Hing4 : In (g, CGIF_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hing).
assert (Hcur4 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4|]; exact Hcur_in).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
assert (Hfin4 : In (2, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
assert (Hfrs4' : frames S4 = (2, fpos) :: frames S) by (rewrite Hfrs4; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4. change (256 / 8) with 32 in HFSpres4. rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
aconstsF HJ4 Kgot4 Kcell4 Kguar4 Kuar4.
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
reseat HS HJ4 HP4 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 88%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; exact (HErLo a ltac:(clear - Ha HF8lo HF8c HFceil C1; ceil; unfold SB in *; lia) Hn)
| intros a Ha; exfalso; clear - Ha; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 75%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; exact (HErF a ltac:(clear - Ha; lia) Hn)
| intros a Ha; apply (proj1 (HFpres4 a ltac:(clear - Ha; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 70%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear; lia | rewrite FFS; clear - Hsp1; lia | clear - Hsp1; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj trasegs _); [exact HK | exact HJ4 | evalE AG | clear - Hsp1; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion None ?a _ _ _ _) =>
first [ change a with A_GOT_shadow; apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot3 | exact Kgot4 | clear; lia]
| change a with A_shadow_glob; apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell3 | exact Kcell4 | clear; lia]
| change a with A_GOT_uar; apply (region_kept_val trasegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar3 | exact Kguar4 | clear; lia]
| change a with A_uar_glob; apply (region_kept_val trasegs _ _ _ A_uar_glob 4 1); [exact Kuar3 | exact Kuar4 | clear; lia] ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj trasegs _); [exact HK | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; exact (HErG a ltac:(clear - Ha; lia) Hn) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YQ0b.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 trasegs B LAWS); [exact HK | exact HAR4 | exact Hcur4 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; exact (HErC a ltac:(clear - Ha; lia) Hn) ] end
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
relowF HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS.
rreg HS (19%bv : bv 5) Q19.
lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
ra_join HS ss_X 520%nat fl_X_deads_bv ltac:(idtac; ra_join_val HS 520%nat 0%nat Q19 E520); fl_hand RX HS end.
split; [replace EV_RAWADD with 27 in Hk3 by reflexivity; rewrite HEV; clear - Hk3; lia|].
split; [exists res; split; [rewrite E520, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E479 | exact Hres]|].
cbn [c_ly c_S]. exact HPerm4.
Qed.
Lemma fl_R5 : fl_from B ss_X (INV_X B) -> fl_from B ss_R5 (INV_R5 B).
Proof. exact fl_R5_aux. Qed.
End c.
End b.
