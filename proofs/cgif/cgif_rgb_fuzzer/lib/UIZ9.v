(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s YK0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0a YQ0e YQ02 YQ00 YQ07 YQ08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02 YI01 YI03
UI1e UI1i YI0x YI08 YI0c YI0f UI3h.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YCip.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition ROUND_STK : Z := 16.
Definition ro_region : YQ0b.region :=
YQ0b.mkRegion None SRC2_RO_LO SRC2_RO_HI 0 0 [YQ0b.mkChunk SRC2_RO_LO (CImg (SRC2_RO_HI - SRC2_RO_LO))].
Definition rnd_mem : smem := [ YQ0b.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [] ; ro_region ].
Definition ss_rnd : sstate :=
mkSS ubs2_A_round sr_atoms rnd_mem None (mkFacts [ (2%nat, mkAF (CEIL_MIN + 16) (2^63) 4) ] [] []).
Definition ubs2_rom_present (a : Z) : bool := match seg_rom ubs2segs (Z_to_bv 64 a) with Some _ => true | None => false end.
Lemma ubs2_ro_present : zallb ubs2_rom_present SRC2_RO_LO (Z.to_nat (SRC2_RO_HI - SRC2_RO_LO)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ro_bounds : 4096 <= SRC2_RO_LO /\ SRC2_RO_LO < SRC2_RO_HI /\ SRC2_RO_HI + 4096 <= CEIL_MIN.
Proof. repeat split; vm_compute; first [reflexivity | intro Hc; discriminate Hc]. Qed.
Lemma ro_region_ok : forall E mem, ubs2_rgb_rodata_ok mem -> region_ok ubs2segs E mem ro_region.
Proof.
intros E mem HRO. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
unfold region_ok, ro_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
intros i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len YQ0b.cv_len YQ0b.cbyte] in Hi |- *.
pose proof (zallb_sound _ _ _ (SRC2_RO_LO + i) ubs2_ro_present ltac:(lia)) as Hp.
unfold ubs2_rom_present in Hp.
destruct (seg_rom ubs2segs (Z_to_bv 64 (SRC2_RO_LO + i))) as [b|] eqn:Hb; [|discriminate Hp].
exists b. rewrite Z.add_0_l. unfold img_byte. split; [exact Hb|].
rewrite (HRO (SRC2_RO_LO + i) ltac:(lia)). exact Hb.
Qed.
Ltac wr_ok_eval :=
lazymatch goal with |- wr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc =>
let rs' := eval vm_compute in rs in change (wr_ok E rs' stk sp0 fp b0 bc) end.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Local Notation segs := ubs2segs.
Local Notation rom := (seg_rom ubs2segs).
Definition round_spec : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word),
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
YK0s.ret_ok (getr regs 1) -> spZ regs mod 16 = 0 ->
sp0 - STK <= spZ regs - ROUND_STK -> spZ regs <= sp0 ->
frm_zero fp_csr ->
ubs2_rgb_rodata_ok memc ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_round) memc rom) mdc)
(fun c' => exists (fx' : FPState) regs2 mem2,
c' = mkCfg (@mkst fx' regs2 (getr regs 1) mem2 rom) mdc /\ frm_zero (@fp_csr fx') /\
reg_get (@fp_regs fx') 10 = round_bits (reg_get (@fp_regs fx) 10) /\
fregs_preserved (@fp_regs fx) (@fp_regs fx') /\
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac mem2 mdc /\
regs_preserved regs regs2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ROUND_STK <= a < spZ regs) -> mbyte segs mem2 a = mbyte segs memc a)).
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma rnd_entry : forall (fy : FPState) (regs : bvmap 5 word) memc STK sp0 FP L A mem md Lc Ac mdc,
journal ubs2_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - 16 -> spZ regs <= sp0 ->
ubs2_rgb_rodata_ok memc ->
@st_ok segs fy (Ereg regs []) ss_rnd (@mkst fy regs (Z_to_bv 64 ubs2_A_round) memc rom).
Proof.
intros fy regs memc STK sp0 FP L A mem md Lc Ac mdc HJ Hal16 Hlo Hhi HRO.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
assert (HU2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold ss_rnd. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack segs _ memc 2 (spZ regs)); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ apply ro_region_ok. exact HRO.
- unfold rnd_mem, ro_region. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite HU2. repeat split. right. lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; lia.
Qed.
Local Ltac rnd_run HS HJ HU2 KE regs memc :=
jrunF LAWS ubs2tbl_ok HS HJ;
[ wr_ok_eval; eapply wr_ok_cons_win;
[ reflexivity | exact HU2 | cbn [r_wlo]; lia | cbn [r_whi]; lia | apply wr_ok_cons_ro; [cbn; lia | apply wr_ok_nil] ]
| lazymatch goal with
| HF : frame_of _ _ ?m1 ?m2, HG : mem_grows _ _ |- _ =>
let KE2 := fresh "KE" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> mbyte segs m2 a = mbyte segs memc a)
by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
intros a Ha Hn; mb_frame_g HF ltac:(exact Ha) ltac:(rewrite ?HU2; lia); exact (KE a Ha Hn));
clear KE HF HG; rename KE2 into KE
end ].
Local Ltac rnd_leaf HS HJ HU2 HEf Hx E1 KE Hra regs :=
let Hfrm' := fresh "Hfrm'" in
pose proof (st_okF_frm segs _ _ _ HS) as Hfrm';
let Hh := fresh "Hh" in let Hlz := fresh "Hlz" in
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)) as (Hh & Hlz & _);
lazymatch type of HS with st_okF _ ?E1x ?ss1 ?ms1 =>
eapply (SR_ret_at (fx:=(fp_of ms1)) segs ubs2tbl E1x ss1 ms1 _ _ ubs2tbl_ok);
[ exact Hh | exact Hlz | exact (st_okF_to_legacy segs E1x ss1 ms1 HS) | reflexivity | vm_compute; reflexivity | ];
exists (fp_of ms1), (ms_regs ms1), (ms_mem ms1);
split;
[ let Q1 := fresh "Q1" in
pose proof (st_okF_reg segs E1x _ _ 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite ?Z.add_0_r, E1, Z_to_bv_bv_unsigned in Q1; rewrite Q1, Hra; reflexivity |];
split; [ exact Hfrm' |];
split;
[ cbn [fp_regs fp_of]; rewrite (st_okF_freg segs E1x ss1 ms1 10%bv HS);
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
split;
[ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [fp_regs fp_of];
exact (st_okF_fregs_kept segs E1x ss1 ms1 32 _ FCALLEE_SAVED HS HEf ltac:(vm_compute; reflexivity) r Hr) |];
split; [ exact HJ |];
split;
[ apply regs_preserved_of_list;
exact (regs_kept_of_st_ok _ _ _ _ regs [] CALLEE_SAVED (st_okF_to_legacy segs _ _ _ HS)
ltac:(eassumption) ltac:(vm_compute; reflexivity)) |];
exact KE
end.
Local Ltac rnd_explore n HS HJ HU2 HEf Hx E1 KE Hra regs memc :=
lazymatch n with
| O => fail "rnd_explore: out of depth"
| S ?m =>
rnd_run HS HJ HU2 KE regs memc;
first [ jbranchF ubs2tbl HS;
[ rnd_explore m HS HJ HU2 HEf Hx E1 KE Hra regs memc
| rnd_explore m HS HJ HU2 HEf Hx E1 KE Hra regs memc ]
| rnd_leaf HS HJ HU2 HEf Hx E1 KE Hra regs ]
end.
Theorem ubs2_round : round_spec.
Proof.
intros STK sp0 FP L A mem md Lc Ac memc mdc regs HJ Hra Hal16 Hlo Hhi Hfrm HRO.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & H63 & Hstw) & _).
pose proof (proj1 alloc_ceiling_val) as Hac. pose proof ro_bounds as (Hb1 & Hb2 & Hb3).
unfold ROUND_STK in *.
pose proof (rnd_entry fx regs memc STK sp0 FP L A mem md Lc Ac mdc HJ Hal16 Hlo Hhi HRO) as HS0.
pose proof (st_ok_enterF segs fx 32 (Ereg regs []) _ _ HS0 ltac:(vm_compute; reflexivity) Hfrm) as HS.
clear HS0.
set (E := ew_fregs (Ereg regs []) 32 (@fp_regs fx)) in *.
assert (Hx : ew E 42 = reg_get (@fp_regs fx) 10) by exact (ew_fregs_at (Ereg regs []) 32 (@fp_regs fx) 10%bv).
assert (HEf : forall r : reg, ew E (32 + ridx r)%nat = reg_get (@fp_regs fx) r) by (intros r; apply ew_fregs_at).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_ew_fregs).
assert (HU2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite ew_fregs_low by lia; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite ew_fregs_low by lia; exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) -> mbyte segs memc a = mbyte segs memc a) by reflexivity.
change memc with (ms_mem (@mkst fx regs (Z_to_bv 64 ubs2_A_round) memc rom)) in HJ at 1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_rnd] in HS.
clearbody E.
rnd_explore 8%nat HS HJ HU2 HEf Hx E1 KE Hra regs memc.
Qed.
End S.
End c.
