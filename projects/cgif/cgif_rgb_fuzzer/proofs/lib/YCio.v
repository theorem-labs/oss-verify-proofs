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
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0a YQ0e YQ02 YQ0f YC02 YQ07 YQ08 YC03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz YCd2.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCfx YCe9 YCfu
YCi1 YCib YCia YChy YCji.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCip YCi7.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition trb_round_start : Z := 0x967f4.
Definition trb_round_count : nat := 40.
Definition trbtbl_round : ctable := Eval vm_compute in (build_table trbsegs trb_round_start trb_round_count TEmpty).
Lemma trbtbl_round_eq : trbtbl_round = build_table trbsegs trb_round_start trb_round_count TEmpty.
Proof. vm_cast_no_check (eq_refl trbtbl_round). Qed.
Lemma trbtbl_round_ok : table_ok trbsegs trbtbl_round.
Proof. rewrite trbtbl_round_eq. apply build_table_ok0. cbv. discriminate. Qed.
Definition RND_LO : Z := 0x10318.
Definition RND_HI : Z := 0x10388.
Definition rnd_rodata : YQ0b.region := YQ0b.mkRegion None RND_LO RND_HI 0 0 [YQ0b.mkChunk 0x10318 (CImg 8); YQ0b.mkChunk 0x10368 (CImg 8); YQ0b.mkChunk 0x10380 (CImg 8)].
Definition rnd_mem : smem := [ stack_region 16; rnd_rodata ].
Definition rnd_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4) ] [] [].
Definition ss_rnd : sstate := mkSS A_round sr_atoms rnd_mem None rnd_facts.
Definition rnd_Bx : sv := SLit SB.
Definition rnd_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition trb_rom_present (a : Z) : bool := match seg_rom trbsegs (Z_to_bv 64 a) with Some _ => true | None => false end.
Lemma rnd_rom_present : zallb trb_rom_present TRB_FPC_LO (Z.to_nat (TRB_FPC_HI - TRB_FPC_LO)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma trb_fpc_bytes : forall a, TRB_FPC_LO <= a < TRB_FPC_HI -> exists b, seg_rom trbsegs (Z_to_bv 64 a) = Some b.
Proof.
intros a Ha. pose proof (zallb_sound _ _ _ a rnd_rom_present ltac:(unfold TRB_FPC_LO, TRB_FPC_HI in *; cbn; lia)) as H.
unfold trb_rom_present in H. destruct (seg_rom trbsegs (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | discriminate].
Qed.
Lemma trb_fpc_in_ro : forall a, TRB_FPC_LO <= a < TRB_FPC_HI -> in_ro_tfa a.
Proof.
intros a Ha. left. exists (nth 0 trbsegs seg_dummy). split; [apply nth_In; vm_compute; lia|]. split; [vm_compute; reflexivity|].
match goal with |- ?lo <= a < ?hi => let l := eval vm_compute in lo in let h := eval vm_compute in hi in change (l <= a < h) end.
unfold TRB_FPC_LO, TRB_FPC_HI in Ha. lia.
Qed.
Lemma trb_fpc_addr_rng : forall a, trb_fpc_addr a -> TRB_FPC_LO <= a < TRB_FPC_HI.
Proof. intros a Ha. unfold trb_fpc_addr in Ha. unfold TRB_FPC_LO, TRB_FPC_HI. lia. Qed.
Lemma trb_fpc_mbyte : forall (B : asyms) (H : word -> bool) mem a, trb_fp_consts B -> arodata_ok B (aview trbsegs H mem) ->
trb_fpc_addr a ->
exists b, seg_rom trbsegs (Z_to_bv 64 a) = Some b /\ mbyte trbsegs (mrestrict H mem) a = Some b.
Proof.
intros B H mem a FPC HR Ha0. pose proof (trb_fpc_addr_rng a Ha0) as Ha. destruct (trb_fpc_bytes a Ha) as [b Hb]. exists b. split; [exact Hb|].
destruct (FPC a Ha0) as [Ho He]. pose proof (HR a (trb_fpc_in_ro a Ha) Ho He) as Hv. rewrite Hb in Hv. cbn [option_map] in Hv.
destruct (aview_byte trbsegs H mem _ _ Hv) as (b' & Hm & Hbv & _). rewrite Hm. f_equal. apply bv_eq. symmetry. exact Hbv.
Qed.
Section c. Context {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis FPC : trb_fp_consts B.
Lemma rnd_entry : forall (fy : FPState) W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k (o : Z),
ajournal trbsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 16 - o <= STK ->
arodata_ok B (aview trbsegs (w_H W) memc) ->
@st_ok trbsegs fy (Ereg regs []) ss_rnd (restrict (w_H W) (@mkst fy regs (Z_to_bv 64 A_round) memc (seg_rom trbsegs))).
Proof.
intros fy W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k o HJ Hsp' Hal Hneg Hbud HRO.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs []).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_rnd. apply (entry_st_ok_full trbsegs); change (Ereg regs _) with E.
+ apply regs_ok_Ereg.
+ vm_compute; reflexivity.
+ unfold rnd_mem, stack_region, rnd_rodata. repeat apply Forall_cons; try apply Forall_nil.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite Usp.
split; [clear - Hslo Hceil C1 Hstk0 Hsp' Hbud; lia|]. split; [clear - Hshi H47 Hsp' Hneg; lia|]. split; [|constructor].
intros q Hq. apply (apresent_writable trbsegs). apply Hpres. clear - Hq Hsp' Hneg Hbud. lia.
* unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. unfold RND_LO, RND_HI.
split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
destruct (trb_fpc_mbyte B (w_H W) memc (0x10318 + i) FPC HRO ltac:(unfold trb_fpc_addr; lia)) as (b & Hb & Hm).
exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb | exact Hm].
-- intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
destruct (trb_fpc_mbyte B (w_H W) memc (0x10368 + i) FPC HRO ltac:(unfold trb_fpc_addr; lia)) as (b & Hb & Hm).
exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb | exact Hm].
-- intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
destruct (trb_fpc_mbyte B (w_H W) memc (0x10380 + i) FPC HRO ltac:(unfold trb_fpc_addr; lia)) as (b & Hb & Hm).
exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb | exact Hm].
+ apply pairwise_disjoint_of_extents. unfold rnd_mem, stack_region, rnd_rodata, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite Usp. unfold RND_LO, RND_HI.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 Hstk0 Hsp' Hneg Hbud. clear. unfold ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [rnd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp. change (2 ^ 4) with 16.
assert (Hspal : spZ regs mod 16 = 0) by (rewrite Hsp', Z.add_mod, Hsp0al, Hal by lia; reflexivity).
revert Hslo Hshi H47 Hceil Hspal C1 C3 Hstk0 Hsp' Hneg Hbud. clear. unfold ASAN_CEIL. intros. repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Lemma rnd_kept : forall E0 rs (H : word -> bool) (m m' : word -> option byte) sp,
frame_of E0 rs (mrestrict H m) (mrestrict H m') ->
(forall rr, In rr rs -> YQ0b.r_whi rr <= YQ0b.r_wlo rr \/ (YQ0b.r_base rr = Some 2%nat /\ -16 <= YQ0b.r_wlo rr /\ YQ0b.r_whi rr <= 0)) ->
bv_unsigned (ew E0 2) = sp ->
forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 16 <= x < sp) -> aview trbsegs H m' x = aview trbsegs H m x.
Proof.
intros E0 rs H m m' sp HF Hrs Hsp x Hx Hnw. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros (rr & Hin & Hr). destruct (Hrs rr Hin) as [Hro | (Hb & Hlo & Hhi)]; [lia|].
rewrite Hb in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
Local Ltac rnd_rs_tac :=
let rr := fresh "rr" in let Hin := fresh "Hin" in
intros rr Hin; vm_compute in Hin;
repeat (destruct Hin as [<- | Hin]); try contradiction;
first [ left; cbn [YQ0b.r_wlo YQ0b.r_whi]; lia
| right; cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi]; repeat split; first [reflexivity | lia] ].
Local Ltac rnd_step HS HJ SHOK KE PR Usp Hsp' Hbud Hneg o regs W memc :=
aj_run_tokF trbtbl_round_ok HS HJ SHOK rnd_Bspan;
[ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyx ?ownx =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk s0 fp b0 bc lyx ownx) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat o);
[ reflexivity | rewrite Usp; exact Hsp' | cbn [YQ0b.r_wlo]; clear - Hbud; lia | cbn [YQ0b.r_whi]; clear - Hneg; lia
| apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] ]
| ];
[ lazymatch goal with
| HFrx : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2), HGx : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), HFx : frame_of _ _ ?m1 ?m2 |- _ =>
let KE2 := fresh "KE" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview trbsegs (w_H W) m2 a = aview trbsegs (w_H W) memc a)
by (intros a' Ha' Hn'; rewrite (rnd_kept _ _ _ _ _ _ HFrx ltac:(rnd_rs_tac) Usp a' Ha' Hn'); exact (KE a' Ha' Hn'));
clear KE; rename KE2 into KE;
let PR2 := fresh "PR" in
assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) m2 a) by (intros a' Ha'; exact (apresent_grows _ _ _ _ HGx (PR a' Ha')));
clear PR; rename PR2 into PR; clear HFx HFrx HGx end ].
Local Ltac rnd_leaf HS HJ KE PR Hx HEf HAE E1 Hraw Hwx Hsegs LAWSx regs :=
let Hfrm' := fresh "Hfrm'" in let HSL := fresh "HSL" in let R1 := fresh "R1" in
pose proof (st_okF_frm trbsegs _ _ _ HS) as Hfrm';
pose proof (st_okF_to_legacy trbsegs _ _ _ HS) as HSL;
rreg HSL (1%bv : bv 5) R1;
eapply (SRr_ret_at trbsegs trbtbl_round trbtbl_round_ok Hwx _ _ _ _ _ _ HSL eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat'" in intros mat'; split; [reflexivity|];
lazymatch type of HS with st_okF _ ?Ex ?ssx (restrict ?Hh ?msF) =>
exists (fp_of (restrict Hh msF)), (ms_regs msF), (ms_mem msF); eexists;
split; [ cbn [ms_regs]; rewrite R1; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite E1, Hraw; reflexivity |];
split; [ exact Hfrm' |];
split; [ cbn [fp_regs fp_of]; rewrite (st_okF_freg trbsegs Ex ssx (restrict Hh msF) 10%bv HS);
match goal with |- sv_denot _ ?v = _ => let v' := eval vm_compute in v in change v with v' end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?Hx;
unfold round_bits, round_exp, faddD, fsubD, fmulD, fabsD, fnegD, fltD, fleD, C2P52, CHALF, CMHALF, CONE;
repeat match goal with
| Hc : branch_taken _ _ _ = _ |- _ =>
cbn [sv_denot branch_taken] in Hc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?Hx in Hc;
first [ apply (proj1 (negb_true_iff _)) in Hc | apply (proj1 (negb_false_iff _)) in Hc | idtac ];
rewrite Hc; clear Hc
end;
reflexivity |];
split; [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [fp_regs fp_of];
exact (st_okF_fregs_kept trbsegs Ex ssx (restrict Hh msF) 32 _ FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) r Hr) |];
split; [ cbn [ms_mem]; apply (ajournal_materialize trbsegs _ LAWSx Hsegs); exact HJ |];
split; [ eapply (aregs_preserved_of_st_ok trbsegs _ _ _ _ regs [] HSL); [exact HAE | vm_compute; reflexivity] |];
split; [ exact KE | exact PR ]
end.
Local Ltac rnd_explore n HS HJ SHOK KE PR Usp Hsp' Hbud Hneg o regs W memc Hx HEf HAE E1 Hraw Hwx Hsegs LAWSx :=
lazymatch n with
| O => fail "rnd_explore: out of depth"
| S ?m =>
rnd_step HS HJ SHOK KE PR Usp Hsp' Hbud Hneg o regs W memc;
first [ lg_branchF trbtbl_round_ok HS;
[ rnd_explore m HS HJ SHOK KE PR Usp Hsp' Hbud Hneg o regs W memc Hx HEf HAE E1 Hraw Hwx Hsegs LAWSx
| rnd_explore m HS HJ SHOK KE PR Usp Hsp' Hbud Hneg o regs W memc Hx HEf HAE E1 Hraw Hwx Hsegs LAWSx ]
| rnd_leaf HS HJ KE PR Hx HEf HAE E1 Hraw Hwx Hsegs LAWSx regs ]
end.
Theorem trb_round : forall {fx : FPState}, tround_spec B.
Proof.
intros fx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hraw Hra4 Hal16 Hlo Hhi Hfrm HRO.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (o := spZ regs - sp0).
assert (Hsp' : spZ regs = sp0 + o) by (subst o; lia).
assert (Hneg : o <= 0) by (subst o; lia).
assert (Hal : o mod 16 = 0) by (subst o; rewrite Zminus_mod, Hal16, Hsp0al; reflexivity).
assert (Hbud : 16 - o <= STK) by (subst o; unfold TROUND_STK in Hlo; lia).
pose proof (rnd_entry fx W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k o HJ Hsp' Hal Hneg Hbud HRO) as HS0.
pose proof (st_ok_enterF trbsegs fx 32 (Ereg regs []) _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
set (E := ew_fregs (Ereg regs []) 32 (@fp_regs fx)) in *.
assert (SHOK : sh_ok trbsegs rnd_Bx [] E (mrestrict (w_H W) memc)) by constructor.
clear HS0.
assert (Hx : ew E 42 = reg_get (@fp_regs fx) 10) by exact (ew_fregs_at (Ereg regs []) 32 (@fp_regs fx) 10%bv).
assert (HEf : forall r : bv 5, ew E (32 + ridx r)%nat = reg_get (@fp_regs fx) r) by (intros r; apply ew_fregs_at).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_ew_fregs).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (proj1 HAE) by lia; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE) by lia; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> aview trbsegs (w_H W) memc a = aview trbsegs (w_H W) memc a) by reflexivity.
assert (PR : forall a, apresent (w_H W) memc a -> apresent (w_H W) memc a) by (intros a Ha; exact Ha).
unfold cfg_at. change (w64 A_round) with (Z_to_bv 64 A_round). unfold TROUND_STK.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_rnd] in HS.
clearbody E o.
rnd_explore 8%nat HS HJ SHOK KE PR Usp Hsp' Hbud Hneg o regs W memc Hx HEf HAE E1 Hraw Hwx Hsegs LAWS.
Qed.
End d.
End c.
