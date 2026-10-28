(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m UO3n YI00 YI02 YI01 YI03 YI05
UI1e UI39 UI1i UI59 YI0x UI57 UI1h UI1g UI16
YI04 YI08 UI3d UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Ltac lit_range := lazymatch goal with |- (_ <= _ < _)%Z => vm_compute; split; [let HH := fresh in intros HH; discriminate HH | reflexivity] end.
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition rgbcfg_chunks : list YQ0b.chunk :=
[ mkChunk 0 (CVal 8 (SLit ubs2_A_writecb)); mkChunk 8 (CVal 8 (SLit 0)); mkChunk 16 (CVal 8 (SLit 0));
mkChunk 24 (CVal 4 (SOff 35 0)); mkChunk 28 (CVal 4 (SOff 36 0));
mkChunk 32 (CVal 2 (SOff 37 0)); mkChunk 34 (CVal 2 (SOff 38 0)); mkChunk 36 (CVal 2 (SOff 39 0)) ].
Definition ss_rgb_newgif : sstate :=
mkSS ubs2_A_cgif_rgb_newgif sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-24) 0 (-24) 0 [] ;
YQ0b.mkRegion (Some 10%nat) 0 RGBCONFIG_SIZE 0 0 rgbcfg_chunks ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + RGBNEWGIF_STK) (2^63) 4); (10%nat, mkAF CEIL_MIN (2^63 - RGBCONFIG_SIZE) 3);
(35%nat, mkAF 0 (2^32 - 1) 0); (36%nat, mkAF 0 (2^32 - 1) 0);
(37%nat, mkAF 0 65535 0); (38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0) ] [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis NEWGIF : newgif_spec API.
Theorem ubs2_rgb_newgif : rgb_newgif_spec API.
Proof.
intros L A regs mem md cfgp attr gen loops W H HPRE Hid Ha0 Hcal Hclo Hchi Hcfg Hcfgrd HWH.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HSTKv : RGBNEWGIF_STK = 9296) by reflexivity. assert (HNSv : NEWGIF_STK = 9216) by reflexivity.
assert (HCSv : CALLOC_STACK = 8224) by reflexivity.
assert (HRCv : RGBCONFIG_SIZE = 40) by reflexivity. assert (HRSv : RGB_SIZE = 64) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 3%nat attr eq_refl) as Rattr. pose proof (Rcfg 4%nat gen eq_refl) as Rgen.
pose proof (Rcfg 5%nat loops eq_refl) as Rloops. pose proof (Rcfg 6%nat W eq_refl) as RW. pose proof (Rcfg 7%nat H eq_refl) as RH.
cbn in Rattr, Rgen, Rloops, RW, RH.
set (cvals := [ubs2_A_writecb; 0; 0; attr; gen; loops; W; H]) in *.
set (E := Ereg regs (map (Z_to_bv 64) cvals ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HX35 : ew E 35 = Z_to_bv 64 attr) by (apply (HX 3%nat); reflexivity).
assert (HX36 : ew E 36 = Z_to_bv 64 gen) by (apply (HX 4%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 loops) by (apply (HX 5%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 W) by (apply (HX 6%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 H) by (apply (HX 7%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = cfgp) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
pose proof Hcfg as Hc. cbn [obj_at LAY_RgbConfig] in Hc. unfold field_ok in Hc. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hc.
destruct Hc as ((F0 & _) & (F1 & _) & (F2 & _) & (F3 & _) & (F4 & _) & (F5 & _) & (F6 & _) & (F7 & _) & _).
assert (HS : st_ok ubs2segs E ss_rgb_newgif (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_newgif) mem (seg_rom ubs2segs))).
{ unfold ss_rgb_newgif. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ mem 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold rgbcfg_chunks.
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ubs2_A_writecb); [reflexivity | unfold ubs2_A_writecb; lit_range | cbn; lia | exact F0]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lit_range | cbn; lia | exact F1]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lit_range | cbn; lia | exact F2]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ attr); [cbn [sv_denot]; rewrite Z.add_0_r, HX35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F3]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ gen); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F4]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ loops); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F5]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ W); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F6]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ H); [cbn [sv_denot]; rewrite Z.add_0_r, HX39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F7]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HX35, HX36, HX37, HX38, HX39, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
pose proof (journal_init ubs2_msyms MR RGBNEWGIF_STK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_cgif_rgb_newgif) mem (seg_rom ubs2segs))) in HJ.
fold sp0 in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
cbn [ms_mem mkst] in HF, HG.
assert (K00 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> mbyte ubs2segs (ms_mem ms) a = mbyte ubs2segs mem a).
{ intros a Ha Hna. mb_frame_with HF ltac:(exact Ha) ltac:(rewrite ?HU2, ?HU10; lia). reflexivity. }
clear HF.
eapply SR_bind.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset E _ _ RGBNEWGIF_STK sp0 [] L A mem md L A _ (sp0 - 72) 0 48);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regsz & memz & -> & HJz & Hdz & Hfrz & Houtz & Hgrz & Hzeroz). clear HJ Ma0 Ma1 Ma2 Mra.
assert (K0z : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> mbyte ubs2segs memz a = mbyte ubs2segs mem a).
{ intros a Ha Hna. rewrite <- (K00 a Ha Hna). unfold mbyte. rewrite (Houtz (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
clear K00.
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?pcm) _ _) _) _ =>
jafter_stretch HS 40%nat regsz memz MEMSET_CLOB pcm HS2 end.
specialize (HS2 Hfrz).
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ repeat (apply Forall_cons;
[ (eapply region_kept_outside; [exact Houtz | exact Hgrz | | | | cbn; lia | cbn; lia]);
cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite ?HU2, ?HU10; lia |]).
apply Forall_nil. }
clear HS Hfrz Hdz. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-72) (-24) (-72) (-24) [mkChunk (-72) (CZero 48)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst]. ew_havoc. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows ubs2segs (ms_mem ms) memz); [exact Hgrz|]. apply (writable_at_grows ubs2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -72 + i) with (sp0 - 72 + i) by lia. apply Hzeroz. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havoc. rewrite HU2, HU10. repeat split; lia. }
clear Hgrz Hzeroz Houtz HG.
jrun_to LAWS ubs2tbl_ok HS HJz ubs2_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
(jreg HS (10%bv:reg) as M10); (jreg HS (2%bv:reg) as M2); (jreg HS (4%bv:reg) as M4); (jreg HS (1%bv:reg) as M1).
rewrite HU2 in M2. replace (sp0 + -80) with (sp0 - 80) in M2 by lia. rewrite (HE 4%nat 4%bv eq_refl), Htp in M4.
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem a) end.
{ intros a Ha Hna. rewrite <- (K0z a Ha Hna). mb_frame_with HF ltac:(exact Ha) ltac:(ew_havoc; rewrite ?HU2, ?HU10; lia). reflexivity. }
clear HF K0z.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 64) (spc := sp0 - 80);
[ exact HS | reflexivity | reflexivity | exact HJz | exact Hid | exact M10 | lia
| exact M2 | lia | exact Hspm | lia | lia | exact M4 | exact M1 | apply ret_ok_even; vm_compute; reflexivity ]. }
clear M10 M2 M4 M1.
cbv beta. intros c' (L1 & A1 & regs1 & mem1 & md1 & p & -> & HJ1 & Hid1 & HP1 & Hr10 & Hres & Hkeep1 & Hhi1). clear HJz.
cbn [ms_regs ms_mem mkst] in HP1, Hr10, Hkeep1, Hhi1, HJ1.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep1, Hhi1.
assert (K1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - RGBNEWGIF_STK <= a < sp0) -> mbyte ubs2segs mem1 a = mbyte ubs2segs mem a).
{ intros a Ha Hna. rewrite (proj1 (Hhi1 a Ha ltac:(lia))). apply K0; lia. }
jafter_call_keep HS 46%nat regs1 mem1 HP1 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi1 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi1 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hhi1 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hatom); cbn [ms_regs mkst] in Hatom; rewrite Hr10 in Hatom; symmetry in Hatom.
destruct Hres as [[-> HBeq] | (Hpnz & Hp16 & (pb1 & pb2 & HBp & HBc) & Wp)].
{
pin_reg' HS (10%bv:reg) 0 Hr10.
jrun LAWS ubs2tbl_ok HS HJ1.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ1))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ1)))). }
lazymatch type of HS with st_ok _ _ _ ?msf => exists L1, A1, (ms_regs msf), (ms_mem msf), md1, 0 end.
split.
{ cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite !ew_havoc_old in Q1 by (cbv; lia); rewrite ?Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra; reflexivity end. }
split; [exact HJ1|].
split.
{ exact (regs_preserved_of_st_ok _ _ _ _ regs _ HS (env_agree_havoc_ge 32 46 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 40 _ _ _ ltac:(lia) (env_agree_refl _ _))) ltac:(vm_compute; reflexivity)). }
split; [reg_nowF HS ltac:(reflexivity)|].
left. split; [reflexivity|]. exists []. rewrite HBeq. apply Permutation_refl. }
assert (HBp1 : In (p, 64) (blocks L1 A1)) by (rewrite HBp; apply in_app_iff; right; left; reflexivity).
destruct (heap_blocks_range _ _ LAWS _ _ _ _ p 64 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) HBp1 ltac:(lia)) as (Rp0 & Rp1 & _).
assert (HB1 : Permutation (blocks L1 A1) ((p, 64) :: blocks L A)).
{ rewrite HBp, HBc. apply Permutation_sym. apply Permutation_middle. }
clear HBp HBc pb1 pb2.
add_fact' HS 50%nat (mkAF 4096 (CEIL_MAX - 64) 4); [| rewrite Hatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
assert (Wp' : wtok' RGBNEWGIF_STK sp0 [] (blocks L A) (p, 64)) by (intros blc i Hin Hi; apply (Wp blc i Hin Hi)).
jrun_to LAWS ubs2tbl_ok HS HJ1 ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (K1m : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - RGBNEWGIF_STK <= a < sp0) -> mbyte ubs2segs (ms_mem msx) a = mbyte ubs2segs mem a) end.
{ intros a Ha Hna. rewrite <- (K1 a Ha Hna). mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2, ?HU10; lia). reflexivity. }
clear HF K1.
(jreg HS (10%bv:reg) as Mm10); (jreg HS (11%bv:reg) as Mm11); (jreg HS (12%bv:reg) as Mm12); (jreg HS (1%bv:reg) as Mm1).
cbn [ms_regs mkst] in Mm10, Mm11, Mm12, Mm1. rewrite Hatom in Mm10.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset E1 ss1 ms1 _ _ _ _ _ _ _ _ _ _ p 0 64);
[ exact HS | reflexivity | reflexivity | exact HJ1 | exact Mm10 | exact Mm11 | exact Mm12 | exact Mm1
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia
| intros i Hi; apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 64 i (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) HBp1 Hi))
| intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ p 64); [exact Wp' | exact HBp1 | lia] ] end. }
clear Mm10 Mm11 Mm12 Mm1.
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Zp). clear HJ1. rename HJ2 into HJ1.
assert (K1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - RGBNEWGIF_STK <= a < sp0) -> mbyte ubs2segs mem2 a = mbyte ubs2segs mem a).
{ intros a Ha Hna. rewrite <- (K1m a Ha Hna). unfold mbyte. rewrite (Hout2 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia). reflexivity. }
clear K1m.
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?pcm) _ _) _) _ =>
jafter_stretch HS 62%nat regs2 mem2 MEMSET_CLOB pcm HS2 end.
specialize (HS2 Hfr2).
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ repeat (apply Forall_cons;
[ (eapply region_kept_outside; [exact Hout2 | exact Hgr2 | | | | cbn; lia | cbn; lia]);
cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite ?HU2, ?HU10; lia |]).
apply Forall_nil. }
clear HS Hfr2 Hgr2 Hd10. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 50%nat) 0 64 0 64 [mkChunk 0 (CZero 64)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havoc. rewrite Hatom, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. cbn [ms_mem mkst]. apply (present_writable ubs2_msyms).
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 64 o (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) HBp1 Ho)). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off ms_mem mkst]. intros i Hi.
rewrite Z.add_0_r. apply Zp. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
ew_havoc. rewrite Hatom. ew_havoc. rewrite HU2, HU10, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [lia|]. exact I. }
Ltac wr4 Hatom HU2 Wp' HBin :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 50); [reflexivity | ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ 64); [exact Wp' | exact HBin | lia]
| eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil ].
jrun_to LAWS ubs2tbl_ok HS HJ1 ubs2_A_cgif_newgif. { wr4 Hatom HU2 Wp' HBp1. }
cbn [ms_mem mkst] in HF.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hidx : obj_at ubs2segs (ms_mem msx) (sp0 - 72) LAY_Config [0; 0; RGB_GIFATTR; 0; W; H; 0; loops; ubs2_A_writecb; 0]) end.
{ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
assert (HU2' : bv_unsigned (ew E1 2) = sp0) by (ew_havoc; exact HU2);
pose proof (fun off len o n Hin => st_chunk_zero_val ubs2segs E1 ss1 ms1 1%nat _ 2%nat off len sp0 o n HS eq_refl eq_refl Hin HU2') as ZF;
pose proof (fun off n e v Hin => st_chunk_val ubs2segs E1 ss1 ms1 1%nat _ 2%nat off n e sp0 v HS eq_refl eq_refl Hin HU2') as VF;
pose proof (fun off n e m Hin => st_field_low ubs2segs E1 ss1 ms1 1%nat _ 2%nat sp0 off n e m HS eq_refl eq_refl Hin HU2') as LF;
assert (LW : U E1 (SExt true 16 (SOff 38 0)) mod 2 ^ 16 = W) by (apply U_sext16_low; [ew_havoc; exact HX38 | lia]);
assert (LH : U E1 (SExt true 16 (SOff 39 0)) mod 2 ^ 16 = H) by (apply U_sext16_low; [ew_havoc; exact HX39 | lia]);
assert (LL : U E1 (SExt true 16 (SOff 37 0)) mod 2 ^ 16 = loops) by (apply U_sext16_low; [ew_havoc; exact HX37 | lia])
end.
pose proof (LF (-48) 2%N (SExt true 16 (SOff 38 0)) (2 ^ 16) ltac:(cbv; auto 20) ltac:(cbn; lia) eq_refl) as FW. rewrite LW in FW.
pose proof (LF (-46) 2%N (SExt true 16 (SOff 39 0)) (2 ^ 16) ltac:(cbv; auto 20) ltac:(cbn; lia) eq_refl) as FH. rewrite LH in FH.
pose proof (LF (-42) 2%N (SExt true 16 (SOff 37 0)) (2 ^ 16) ltac:(cbv; auto 20) ltac:(cbn; lia) eq_refl) as FL. rewrite LL in FL.
unfold field_ok in FW, FH, FL. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in FW, FH, FL.
cbn [obj_at LAY_Config]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [replace (sp0 - 72 + 0) with (sp0 + -72) by lia; apply (ZF (-72) 8 (-72) 8%nat); [cbv; auto 20 | lia | cbn; lia] | lia] |].
split; [split; [replace (sp0 - 72 + 8) with (sp0 + -64) by lia; apply (VF (-64) 8%N (SLit 0) 0); [cbv; auto 20 | reflexivity | cbn; lia | cbn; lia] | lia] |].
split; [split; [replace (sp0 - 72 + 16) with (sp0 + -56) by lia; apply (VF (-56) 4%N (SLit 6) 6); [cbv; auto 20 | reflexivity | cbn; lia | cbn; lia] | unfold RGB_GIFATTR; lia] |].
split; [split; [replace (sp0 - 72 + 20) with (sp0 + -52) by lia; apply (ZF (-52) 4 (-52) 4%nat); [cbv; auto 20 | lia | cbn; lia] | lia] |].
split; [split; [replace (sp0 - 72 + 24) with (sp0 + -48) by lia; exact (proj1 FW) | lia] |].
split; [split; [replace (sp0 - 72 + 26) with (sp0 + -46) by lia; exact (proj1 FH) | lia] |].
split; [split; [replace (sp0 - 72 + 28) with (sp0 + -44) by lia; apply (ZF (-44) 2 (-44) 2%nat); [cbv; auto 20 | lia | cbn; lia] | lia] |].
split; [split; [replace (sp0 - 72 + 30) with (sp0 + -42) by lia; exact (proj1 FL) | lia] |].
split; [split; [replace (sp0 - 72 + 32) with (sp0 + -40) by lia; apply (VF (-40) 8%N (SLit ubs2_A_writecb) ubs2_A_writecb); [cbv; auto 20 | reflexivity | unfold ubs2_A_writecb; cbn; lia | cbn; lia] | unfold ubs2_A_writecb; lia] |].
split; [split; [replace (sp0 - 72 + 40) with (sp0 + -32) by lia; apply (VF (-32) 8%N (SLit 0) 0); [cbv; auto 20 | reflexivity | cbn; lia | cbn; lia] | lia] |].
exact I. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KC2 : forall i, 0 <= i < RGBCONFIG_SIZE -> mbyte ubs2segs (ms_mem msx) (cfgp + i) = mbyte ubs2segs mem (cfgp + i)) end.
{ intros i Hi. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
rewrite (mbyte_of_frame E1 rs m1 m2 _ HF); [| lia | intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite ?Hatom, ?HU2, ?HU10, ?unsigned_lit_small by lia; lia |]); destruct Hr ] end.
apply K1; lia. }
clear HF.
jreg HS (10%bv:reg) as Ha10. rewrite HU2 in Ha10.
jreg HS (2%bv:reg) as Ha2. rewrite HU2 in Ha2.
jreg HS (4%bv:reg) as Ha4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Ha4.
jreg HS (1%bv:reg) as Ha1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 80) by (unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia) end.
assert (Hsp8 : (sp0 - 72) mod 8 = 0).
{ replace (sp0 - 72) with ((sp0 - 80) + 1 * 8) by lia. rewrite Z.mod_add by lia.
rewrite <- (Z.mod_mod_divide (sp0 - 80) 16 8) by (exists 2; reflexivity). rewrite Hspm. reflexivity. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ1) as HH1.
eapply SR_bind.
{ eapply (jcall ubs2_msyms MR) with (STK1 := NEWGIF_STK) (FP1 := [])
(K := fun L4 A4 (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) => exists res,
getr regs4 10 = Z_to_bv 64 res /\
((res = 0 /\ exists leak, Permutation (blocks L4 A4) (leak ++ blocks L1 A1)) \/
(res <> 0 /\ exists s, cgif_at mem4 res s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = RGB_GIFATTR /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (blocks L4 A4) (cgif_blocks res s (W * H) ++ blocks L1 A1))));
[ exact HS | reflexivity | exact HJ1 | exact Ha1 | | apply ret_ok_even; vm_compute; reflexivity
| rewrite Hsp; exact Hspm | lia
| rewrite Hsp; lia | rewrite Hsp; lia | exact Ha4 | intros a Ha; exfalso; exact (inFP_nil a Ha) ].
intros HPRE1. eapply SR_mono.
{ eapply (NEWGIF _ _ _ _ _ (sp0 - 72) 0 0 RGB_GIFATTR 0 W H 0 loops (blocks L1 A1) HPRE1 Hid1);
[ rewrite Ha10; f_equal; lia | exact Hsp8 | rewrite Hsp; lia | lia | exact Hidx | exact HWH | reflexivity | apply Permutation_refl ]. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & res & -> & HJc4 & HP4 & Hres10 & ALT).
exists L4, A4, regs4, mem4, md4. split; [rewrite Ha1; reflexivity|]. split; [exact HJc4|]. split; [exact HP4|].
exists res. split; [exact Hres10|].
destruct ALT as [(Hres & Hleak) | (Hres & s & Hat & Hwf & Hfr & HWs & HHs & Hattr & Hcur & Hih & HB4)]; [left; auto | right].
split; [exact Hres|]. exists s. repeat (split; [assumption|]). exact HB4. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & res & Hr10g & ALT). clear HJ1.
cbn [ms_regs ms_mem mkst] in HJc4, HP4, Hr10g, HJ4, ALT.
pose proof HJc4 as (_ & _ & Hhi4 & Hblk4 & _). rewrite Hsp in Hhi4. change (ms_segs ubs2_msyms) with ubs2segs in Hhi4, Hblk4.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
assert (KC3 : forall i, 0 <= i < RGBCONFIG_SIZE -> mbyte ubs2segs mem4 (cfgp + i) = mbyte ubs2segs mem (cfgp + i)).
{ intros i Hi. rewrite (proj1 (Hhi4 (cfgp + i) ltac:(lia) ltac:(lia))). apply KC2. exact Hi. }
clear KC2.
assert (HXX : exists X, Permutation (blocks L4 A4) (X ++ blocks L1 A1)).
{ destruct ALT as [(_ & leak & Hl) | (_ & s & _ & _ & _ & _ & _ & _ & _ & _ & Hb)]; [exists leak; exact Hl | eexists; exact Hb]. }
destruct HXX as [X HB4X].
assert (Hp4 : In (p, 64) (blocks L4 A4)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB4X|]. apply in_app_iff. right. exact HBp1. }
jafter_call_keep HS 68%nat regs4 mem4 HP4 [0%nat; 2%nat; 3%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_live _ _ _ _ 50%nat p 64); [reflexivity | ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia | | | cbn; lia | cbn; lia].
+ intros i Hi. apply (Hblk4 p 64 i HBp1 Hp4 Hi). intros HF0. exact (inFP_nil _ HF0).
+ cbn [r_wlo r_whi]. intros i Hi. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 64 i HH4 Hp4 Hi)).
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
(jreg HS (10%bv:reg) as Hgatom); cbn [ms_regs mkst] in Hgatom; rewrite Hr10g in Hgatom; symmetry in Hgatom.
Ltac wr3 Hatom HU2 Wp' HBin :=
wr_norm;
eapply (wr_ok_cons_gen _ _ _ _ _ _ _ _ 50); [reflexivity | ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia | |];
[ cbn [r_wlo r_whi]; intros a Ha; eapply (wr_byte_of_wtok _ _ _ _ _ _ 64); [exact Wp' | exact HBin | lia]
| eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil ].
destruct ALT as [(-> & leak & Hleak) | (Hres & s & Hat & Hwf & Hfr & HWs & HHs & Hattr & Hcur & Hih & HB4)].
{
pin_reg' HS (10%bv:reg) 0 Hr10g.
jrun_to LAWS ubs2tbl_ok HS HJ4 ubs2_A_free. { wr3 Hatom HU2 Wp' Hp4. }
jreg HS (10%bv:reg) as Hq10. rewrite Hatom in Hq10.
jreg HS (2%bv:reg) as Hq2. rewrite HU2 in Hq2. replace (sp0 + -80) with (sp0 - 80) in Hq2 by lia.
jreg HS (4%bv:reg) as Hq4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hq4. jreg HS (1%bv:reg) as Hq1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := p) (n := 64) (spc := sp0 - 80);
[ exact HS | reflexivity | reflexivity | exact HJ4 | exact Hp4 | exact Hq10 | exact Hq2 | lia | exact Hspm | lia | lia
| exact Hq4 | exact Hq1 | apply ret_ok_even; vm_compute; reflexivity | ].
intros Hin i Hi. exfalso.
destruct (heap_sep_perm _ _ LAWS L1 A1 _ _ (p, 64) (blocks L A) (p, 64) HH1 HB1 Hin) as [H1|H1]; cbn [fst snd] in H1; lia. }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & _). clear HJ4.
jafter_call_keep HS 84%nat regs6 mem6 HP6 [1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havoc; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 10); [ew_havoc; exact HU10 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ6.
{ eapply wr_ok_cons_win; [reflexivity | ew_havoc; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ6))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ6)))). }
lazymatch type of HS with st_ok _ _ _ ?msf => exists L6, A6, (ms_regs msf), (ms_mem msf), md6, 0 end.
split.
{ cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite !ew_havoc_old in Q1 by (cbv; lia); rewrite ?Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra; reflexivity end. }
split; [exact HJ6|].
split.
{ exact (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 84 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 68 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 62 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 46 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 40 _ _ _ ltac:(lia) (env_agree_refl _ _))))))
ltac:(vm_compute; reflexivity)). }
split; [reg_nowF HS ltac:(reflexivity)|].
left. split; [reflexivity|]. exists leak.
eapply perm_after_rm1; [| exact Hrm6]. eapply Permutation_trans; [exact Hleak|].
eapply Permutation_trans; [apply Permutation_app_head; exact HB1|]. apply Permutation_sym. apply Permutation_middle. }
destruct (af_cgif_geom API L4 A4 mem4 md4 res s (W * H) (blocks L1 A1) HH4 HB4) as (_ & _ & (Hg0 & Hg1 & Hg16)).
assert (Gsep : forall b n, In (b, n) (cgif_blocks res s (W * H)) -> b + n <= p \/ p + 64 <= b).
{ intros b n Hbn. pose proof (heap_sep_app API L4 A4 mem4 md4 (cgif_blocks res s (W * H)) (blocks L1 A1) (b, n) (p, 64) HH4 HB4 Hbn HBp1) as Hs.
cbn [fst snd] in Hs. exact Hs. }
add_fact' HS 72%nat (mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4); [| rewrite Hgatom, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia].
jrun_to LAWS ubs2tbl_ok HS HJ4 ubs2_A_memcpy. { wr3 Hatom HU2 Wp' Hp4. }
cbn [ms_mem mkst] in HF.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
assert (HU44 : bv_unsigned (ew E1 50) = p) by (ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia);
pose proof (st_chunk_val ubs2segs E1 ss1 ms1 0%nat _ 50%nat 0 8%N (SOff 72 0) p res HS eq_refl eq_refl ltac:(cbv; auto 20) HU44
ltac:(cbn [sv_denot]; ew_havoc; rewrite Z.add_0_r, Hgatom, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Wg;
pose proof (st_chunk_zero_val ubs2segs E1 ss1 ms1 0%nat _ 50%nat 8 56 p 48 16%nat HS eq_refl eq_refl ltac:(cbv; auto 20) HU44 ltac:(lia) ltac:(cbn; lia)) as Z48
end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (KC : forall i, 0 <= i < RGBCONFIG_SIZE -> mbyte ubs2segs (ms_mem msx) (cfgp + i) = mbyte ubs2segs mem (cfgp + i)) end.
{ intros i Hi. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
rewrite (mbyte_of_frame E1 rs m1 m2 _ HF); [| lia | intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite ?Hatom, ?HU2, ?HU10, ?unsigned_lit_small by lia; lia |]); destruct Hr ] end.
apply KC3. exact Hi. }
jreg HS (10%bv:reg) as M0. rewrite Hatom in M0. rewrite unsigned_lit_small in M0 by lia.
jreg HS (11%bv:reg) as M1.
rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 10)), HU10 in M1.
jreg HS (12%bv:reg) as M2. jreg HS (1%bv:reg) as Mra.
pose proof Hcfg as Hc. cbn [obj_at LAY_RgbConfig] in Hc. unfold field_ok in Hc.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs2_memcpy) with (d := p + 8) (src := cfgp) (n := 40);
[ exact HS | reflexivity | reflexivity | exact HJ4 | exact M0 | exact M1 | exact M2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
replace (p + 8 + i) with (p + (8 + i)) by lia. apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 64 (8 + i) HH4 Hp4 ltac:(lia))).
- intros i Hi. rewrite (KC i ltac:(lia)). apply Hcfgrd. lia.
- intros a Ha. eapply (wr_byte_of_wtok _ _ _ _ _ _ 64); [exact Wp' | exact Hp4 | lia]. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & Hd10 & Hfr5 & Hout5 & Hgr5 & Hcpy5). clear HJ4.
cbn [ms_regs ms_mem mkst] in Hfr5, Hout5, Hgr5, Hcpy5, HJ5.
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?pc5) _ _) _) _ =>
jafter_stretch_keep HS 84%nat regs5 mem5 MEMCPY_CLOB pc5 [1%nat; 2%nat] HS2 end.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr5. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU2; lia
| cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havoc; rewrite HU10; lia | cbn [r_base r_hi base_val]; ew_havoc; rewrite HU10; lia
| cbn [r_base r_lo r_hi base_val]; ew_havoc; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
assert (K5g : forall k, (k < 8)%nat -> mbyte ubs2segs mem5 (p + 0 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte res 8 k))).
{ intros k Hk. unfold mbyte. rewrite (Hout5 (Z_to_bv 64 (p + 0 + Z.of_nat k))) by (rewrite unsigned_lit_small by lia; lia). apply (Wg k Hk). }
assert (K5z : forall i, 48 <= i < 64 -> mbyte ubs2segs mem5 (p + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold mbyte. rewrite (Hout5 (Z_to_bv 64 (p + i))) by (rewrite unsigned_lit_small by lia; lia).
pose proof (Z48 (Z.to_nat (i - 48)) ltac:(lia)) as Zi. replace (p + 48 + Z.of_nat (Z.to_nat (i - 48))) with (p + i) in Zi by lia.
unfold mbyte in Zi. rewrite Zi. f_equal. f_equal. unfold le_byte. rewrite Z.shiftr_0_l. reflexivity. }
assert (K5c : obj_at ubs2segs mem5 (p + 8) LAY_RgbConfig cvals).
{ eapply (obj_at_copy ubs2segs mem mem5 cfgp (p + 8) LAY_RgbConfig cvals RGBCONFIG_SIZE Hcfg lay_inside_RgbConfig).
intros i Hi. rewrite (Hcpy5 i ltac:(lia)). apply KC. exact Hi. }
assert (Kcg5 : forall b n i, In (b, n) (cgif_blocks res s (W * H)) -> 0 <= i < n -> mbyte ubs2segs mem5 (b + i) = mbyte ubs2segs mem4 (b + i)).
{ intros b n i Hbn Hi. pose proof (Gsep b n Hbn) as Gs.
assert (Hbin : In (b, n) (blocks L4 A4)) by (eapply Permutation_in; [apply Permutation_sym; exact HB4 | apply in_app_iff; left; exact Hbn]).
destruct (blocks_range _ _ LAWS L4 A4 mem4 md4 b n HH4 Hbin) as [Rb0 Rb1].
lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
transitivity (mbyte ubs2segs m2 (b + i));
[ unfold mbyte; rewrite (Hout5 (Z_to_bv 64 (b + i))) by (rewrite unsigned_lit_small by lia; lia); reflexivity
| rewrite (mbyte_of_frame E1 rs m1 m2 _ HF); [reflexivity | lia | intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite ?Hatom, ?HU2, ?HU10, ?unsigned_lit_small by lia; lia |]); destruct Hr ] ] end. }
clear HF.
lazymatch type of HS with st_ok _ ?Ef _ _ => assert (Hatom5 : ew Ef 50 = Z_to_bv 64 p) by (ew_havoc; exact Hatom) end.
add_region HS (YQ0b.mkRegion (Some 50%nat) 0 64 60 64 []).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val ms_mem mkst]. ew_havoc. rewrite Hatom, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (present_writable ubs2_msyms). eapply (present_grows _ _ _ Hgr5).
repeat match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end.
apply (proj1 (heap_blocks _ _ LAWS _ _ _ _ p 64 o HH4 Hp4 ltac:(lia))). }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. rewrite Hatom5. ew_havoc. rewrite HU2, HU10, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. exact I. }
jrun LAWS ubs2tbl_ok HS HJ5. { wr3 Hatom HU2 Wp' Hp4. }
cbn [ms_mem mkst] in HF.
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5)))). }
lazymatch type of HS with st_ok _ _ _ ?msf => exists L4, A4, (ms_regs msf), (ms_mem msf), md4, p end.
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (p + 60 <= a < p + 64) -> ~ (sp0 - 32 <= a < sp0) -> mbyte ubs2segs (ms_mem msf) a = mbyte ubs2segs mem5 a);
[ intros a Ha Hn1 Hn2; lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 =>
rewrite (mbyte_of_frame E1 rs m1 m2 _ HF); [reflexivity | exact Ha | intros r Hr; cbv [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val]; ew_havoc; rewrite ?Hatom, ?HU2, ?HU10, ?unsigned_lit_small by lia; lia |]); destruct Hr ] end
| ];
assert (HU44f : bv_unsigned (ew Ef 50) = p) by (ew_havoc; rewrite Hatom; apply unsigned_lit_small; lia);
pose proof (st_region_chunks ubs2segs Ef ssf msf 0%nat _ 50%nat p HS eq_refl eq_refl HU44f) as HCf; cbn [r_chunks] in HCf
end.
split.
{ cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
rewrite !ew_havoc_old in Q1 by (cbv; lia); rewrite ?Z.add_0_r, (HE 1%nat 1%bv eq_refl), Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra; reflexivity end. }
split; [exact HJ5|].
split.
{ exact (regs_preserved_of_st_ok _ _ _ _ regs _ HS
(env_agree_havoc_ge 32 84 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 68 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 62 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 46 _ _ _ ltac:(lia) (env_agree_havoc_ge 32 40 _ _ _ ltac:(lia) (env_agree_refl _ _))))))
ltac:(vm_compute; reflexivity)). }
split; [reg_nowF HS ltac:(ew_havoc; rewrite Hatom, Z_to_bv_bv_unsigned; reflexivity)|].
right. split; [exact Hpnz|]. split; [exact Hp16|]. exists res, s.
split.
{
pose proof (obj_at_range _ _ _ _ _ K5c) as Rc5.
cbn [obj_at LAY_Rgb]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
assert (FLD : forall off n v, obj_at ubs2segs mem5 (p + 8) LAY_RgbConfig cvals ->
(forall j, nth_error LAY_RgbConfig j = Some (off - 8, n) -> nth_error cvals j = Some v ->
val_mem ubs2segs mem5 (p + 8 + (off - 8)) (N.to_nat n) v /\ 0 <= v < 2 ^ (8 * Z.of_N n)) ->
True) by (intros; exact I).
clear FLD.
pose proof K5c as C5. cbn [obj_at LAY_RgbConfig] in C5. unfold field_ok in C5. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in C5.
destruct C5 as ((C0 & R0) & (C1 & R1) & (C2 & R2) & (C3 & R3) & (C4 & R4) & (C5a & R5) & (C6 & R6) & (C7 & R7) & _).
Ltac xfer KF C lo :=
intros k Hk; rewrite KF; [apply C; exact Hk | lia | lia | lia].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); apply (K5g k Hk) | clear - Hg0 Hg1 Hac HGSv; lia] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 8 + Z.of_nat k) with (p + 8 + 0 + Z.of_nat k) by lia; apply (C0 k Hk) | exact R0] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 16 + Z.of_nat k) with (p + 8 + 8 + Z.of_nat k) by lia; apply (C1 k Hk) | exact R1] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 24 + Z.of_nat k) with (p + 8 + 16 + Z.of_nat k) by lia; apply (C2 k Hk) | exact R2] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 32 + Z.of_nat k) with (p + 8 + 24 + Z.of_nat k) by lia; apply (C3 k Hk) | exact R3] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 36 + Z.of_nat k) with (p + 8 + 28 + Z.of_nat k) by lia; apply (C4 k Hk) | exact R4] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 40 + Z.of_nat k) with (p + 8 + 32 + Z.of_nat k) by lia; apply (C5a k Hk) | exact R5] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 42 + Z.of_nat k) with (p + 8 + 34 + Z.of_nat k) by lia; apply (C6 k Hk) | exact R6] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 44 + Z.of_nat k) with (p + 8 + 36 + Z.of_nat k) by lia; apply (C7 k Hk) | exact R7] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 48 + Z.of_nat k) with (p + (48 + Z.of_nat k)) by lia; rewrite (K5z (48 + Z.of_nat k)) by (cbn in Hk; lia); f_equal; f_equal; unfold le_byte; rewrite Z.shiftr_0_l; reflexivity | lia] |].
split; [split; [intros k Hk; rewrite KF by (cbn in Hk; lia); replace (p + 56 + Z.of_nat k) with (p + (56 + Z.of_nat k)) by lia; rewrite (K5z (56 + Z.of_nat k)) by (cbn in Hk; lia); f_equal; f_equal; unfold le_byte; rewrite Z.shiftr_0_l; reflexivity | lia] |].
split; [split; [| unfold R_PENDING; lia] | exact I].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
eapply (st_chunk_val ubs2segs Ef ssf msf 0%nat _ 50%nat 60 4%N (SLit 6) p R_PENDING HS eq_refl eq_refl ltac:(cbv; auto 20) HU44f eq_refl ltac:(unfold R_PENDING; cbn; lia) ltac:(cbn; lia)) end. }
split.
{
eapply (cgif_at_kept mem4 _ res s (W * H) (cgif_blocks res s (W * H) ++ []) []); [apply Permutation_refl | exact Hat |].
intros b n k Hb Hk. rewrite app_nil_r in Hb. pose proof (Gsep b n Hb) as Gs.
assert (Hbin : In (b, n) (blocks L4 A4)) by (eapply Permutation_in; [apply Permutation_sym; exact HB4 | apply in_app_iff; left; exact Hb]).
destruct (blocks_range _ _ LAWS L4 A4 mem4 md4 b n HH4 Hbin) as [Rb0 Rb1].
rewrite KF by lia. apply (Kcg5 b n k Hb Hk). }
split; [exact Hwf|]. split; [exact Hfr|]. split; [exact HWs|]. split; [exact HHs|]. split; [exact Hattr|]. split; [exact Hcur|]. split; [exact Hih|].
eapply Permutation_trans; [exact HB4|]. eapply Permutation_trans; [apply Permutation_app_head; exact HB1|]. apply Permutation_sym. apply Permutation_middle.
Qed.
End S.
End f.
