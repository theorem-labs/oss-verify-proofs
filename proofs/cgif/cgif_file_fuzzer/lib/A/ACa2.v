(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACam ACai ACaj ACak ACal ACan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7x YC7y YCbi YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 AC9y AC9m AC9n AC9o AC9p AC9q AC9w AC9t AC9u AC9v AC9x AC9r AC9s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac fs_pair_tac2 :=
lazymatch goal with |- _ + ?Fv / 8 + _ <= _ \/ _ <= _ + _ / 8 + _ =>
let HFce := lazymatch goal with H : Fv + _ <= alloc_ceiling |- _ => H end in
let HC1 := lazymatch goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let HF8 := lazymatch goal with H : Fv / 8 = 4 * (Fv / 32) |- _ => H end in
let HFq := lazymatch goal with H : Fv = 32 * (Fv / 32) |- _ => H end in
let HF8lo := lazymatch goal with H : _ <= Fv / 8 |- _ => H end in
match goal with Hin : in_app _ _ |- _ =>
let H := fresh "Hia" in pose proof Hin as H; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, RAW_SIZE, CGIF_SIZE in H;
try (change (req_size 48) with 48 in H); try (change (req_size 96) with 96 in H);
let H4 := fresh "H4" in let Hlow := fresh "Hlow" in let Hhi := fresh "Hhi" in let Hce2 := fresh "Hce2" in
destruct H as [H4 [Hlow | [Hhi Hce2]]];
[ solve [ right; try (match goal with Hflo : frame_addr _ _ _ <= ?c |- _ => match goal with Hfhi : c + _ <= frame_addr _ _ _ + _ |- _ => revert Hflo Hfhi end end);
revert Hlow HF8 HFq HF8lo; clear; intros; lia ]
| solve [ left; try (match goal with Hflo : frame_addr _ _ _ <= ?c |- _ => match goal with Hfhi : c + _ <= frame_addr _ _ _ + _ |- _ => revert Hflo Hfhi end end);
revert Hhi HFce HC1 HF8 HFq HF8lo; clear; intros; lia ] ]
end end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XNa : YC7y.xnums.
Let XN : xnums := XNa.
Hypothesis HXM : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xm_lzw XN N idl + 2 * mo_free MT <= xm_rawadd XN N.
Hypothesis HXN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xn_lzw XN N idl + 2 * mo_free MT <= xn_rawadd XN N.
Hypothesis HXMN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> 0 <= xn_lzw XN N idl <= xm_lzw XN N idl.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Variable wfn : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis WFNX : twcbF_spec SEGS KS B wfn.
Variable CTXL : list (list Z).
Hypothesis TLZWX : tlzw_specX SEGS B MT XN (BASE + AF_asan3_LZW_GenerateStream) CTXL pa_relro_lo pa_relro_hi.
Hypothesis HCTXL1 : forall l, In l CTX -> In ((BASE + 0xaf4) :: l) CTXL.
Hypothesis HCTXL2 : forall l, In l CTX -> In ((BASE + 0xd94) :: l) CTXL.
Hypothesis HTR : forall (pcf ra : Z) (regsT regs : bvmap 5 word) ch,
In (raZ regs :: spine ch) CTX -> raZ regsT = ra ->
((pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0xda0) \/ (pcf = pc_free_ra0 (as_code B) /\ ra = BASE + 0x10ac) \/
(pcf = pc_malloc_ra0 (as_code B) /\ ra = BASE + 0xb08)) ->
In (call_trace0 pcf regsT ((spZ regs, raZ regs, s0Z regs) :: ch)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Local Notation code := (as_code B).
Theorem pb_cgif_raw_addframeX : trawadd_specX SEGS KS B MT XNa (BASE + AF_asan3_cgif_raw_addframe) CTX wfn pa_relro_lo pa_relro_hi.
Proof.
unfold trawadd_specX.
intros ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx pf path hw lct img fattr w h top left delay slct disp tidx Nimg rest Sg IMG LCT
HPRE Hal32 Hctx Hroom HROD H10 H11 HFO Hcfg Hraw Hsg Mgw Rhw Mgf Rctx Mg80 Hpf0 HSINK HSmax Hw Hh HnP HnPN HPerm HlctX HIMG HIMGlen Hev Hlive MOK.
change YC20.TRAWADD_STK with TRAWADD_STK in *.
assert (Hlct : 0 < slct <= 256 -> exists Nl rest', Permutation ((pf, FILE_BLOCK) :: rest) ((lct, Nl) :: rest') /\ 3 * slct <= Nl).
{ intros Hs. destruct (HlctX Hs) as (Nl & rest' & HP & HN & _ & _). exists Nl, ((pf, FILE_BLOCK) :: rest').
split; [| exact HN]. eapply Permutation_trans; [apply perm_skip; exact HP | apply perm_swap]. }
assert (Hinf : In (pf, FILE_BLOCK) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; right; right; left; reflexivity).
assert (RXX : ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389)) by (eapply ra_XX; eassumption).
assert (RX1X : ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359)) by (eapply ra_X1X; eassumption).
assert (RHX : ra_fromX1 KS MT XN B CTX ss_G3X (INV_G3X KS MT XN B)) by (eapply ra_HX; eassumption).
assert (RGX : ra_fromX1 KS MT XN B CTX ss_G2X (INV_G2X KS MT XN B)) by (eapply ra_GX; eassumption).
assert (RT0X : ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B)) by (eapply ra_T0X; eassumption).
assert (RTfX : ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B)) by (eapply ra_TfX; eassumption).
assert (RMX : ra_fromX0 KS MT XN B CTX ss_MX (INV_MX MT XN B)) by (eapply ra_MX; eassumption).
assert (RLX : ra_fromX0 KS MT XN B CTX ss_LX (INV_LX MT XN B)) by (eapply ra_LX; eassumption).
assert (RIX : ra_fromX0 KS MT XN B CTX ss_IX (INV_IX MT B)) by (eapply ra_IX; eassumption).
assert (RPX : ra_fromX0 KS MT XN B CTX ss_PX (INV_PX MT B)) by (eapply ra_PX; eassumption).
assert (RFX : ra_fromX0 KS MT XN B CTX ss_FX (INV_FX MT B)) by (eapply ra_FX; eassumption).
assert (REX : ra_fromX0 KS MT XN B CTX ss_EX (INV_EX MT B)) by (eapply AC9p.ra_EX; eassumption).
assert (RDX : ra_fromX0 KS MT XN B CTX ss_DX (INV_DX MT B)) by (eapply ra_DX; eassumption).
assert (RCX : ra_fromX0 KS MT XN B CTX ss_CX (INV_CX MT B)) by (eapply ra_CX; eassumption).
assert (RB8X : ra_fromX0 KS MT XN B CTX ss_B8X (INV_B8X MT B)) by (eapply ra_B8X; eassumption).
assert (RA2X : ra_fromX0 KS MT XN B CTX ss_A2X (INV_0X MT B 1)) by (eapply ra_A2X; eassumption).
clear RXX RX1X RHX RGX RT0X RTfX RMX RLX RIX RPX RFX REX RDX RCX RB8X.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ra_entryX B TL LAWS TLF wfn hw Rwfn Rhw HGOT9 W ly S regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg ((pf, FILE_BLOCK) :: rest) pf
HPRE Hal32 HROD H10 H11 HFO Hcfg Hraw Hsg Mgw Mgf Rctx Mg80 Hw Hh HnP HnPN HPerm Hinf) as HS.
pose proof (ajournal_init SEGS B TRAWADD_STK [(raw + 40, raw + 44)] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWADD_STK = 17040) by reflexivity.
assert (HEV : EV_RAWADD = 27) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity. assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
assert (Hraw_in : In (raw, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md raw RAW_SIZE HAR Hraw_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ raw RAW_SIZE HAR Hraw_in) as Hrh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrpres, Hrh_img.
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
remember (Eimg (Ereg regs (ra_extraX g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw (as_uar_cell B) pf))) as E eqn:HE.     assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 raw) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 cfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall j, (j < 25)%nat -> ew E (32 + j) = nth j (ra_extraX g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw (as_uar_cell B) pf) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45. pose proof (EX 14%nat ltac:(lia)) as E46. pose proof (EX 15%nat ltac:(lia)) as E47.
pose proof (EX 16%nat ltac:(lia)) as E48. pose proof (EX 17%nat ltac:(lia)) as E49. pose proof (EX 18%nat ltac:(lia)) as E50. pose proof (EX 19%nat ltac:(lia)) as E51.
pose proof (EX 20%nat ltac:(lia)) as E52. pose proof (EX 21%nat ltac:(lia)) as E53. pose proof (EX 22%nat ltac:(lia)) as E54. pose proof (EX 23%nat ltac:(lia)) as E55.
pose proof (EX 24%nat ltac:(lia)) as E56.
cbn [Nat.add nth ra_extraX ra_extra map app] in E56. cbn [Nat.add nth ra_extraX ra_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45, E46, E47, E48, E49, E50, E51, E52, E53, E54, E55.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ra_extraX g gct rattr Wd Hd sgct loops rcur lct img fattr w h top left delay slct disp tidx ctx wfn hw (as_uar_cell B) pf)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (Hchne : ch <> []) by (intros Hn; pose proof (HDEEP _ Hctx) as Hdeep; rewrite Hn in Hdeep; cbn in Hdeep; clear - Hdeep; lia).
img_factsA E. img_hull_factsA.
unfold cfg_at. change (w64 (BASE + AF_asan3_cgif_raw_addframe)) with (Z_to_bv 64 (BASE + AF_asan3_cgif_raw_addframe)).
shok_auto SHOK RABx E (mrestrict (w_H W) mem).
paj_run_tok RUN HS HJ SHOK RABspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyx ?own => let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc lyx own) end.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0); [reflexivity | cbn [ew]; rewrite Usp; lia | cbn; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia|]).
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat); [reflexivity | cbn [ew]; rewrite E10; apply unsigned_lit_small; lia | | ];
[ cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split; [exists (raw + 40, raw + 44); split; [left; reflexivity | cbn [fst snd]; clear - Ha; lia] | exists raw, RAW_SIZE; split; [exact Hraw_in | change (req_size RAW_SIZE) with 48; lia]]
| repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ]. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?Usp, ?E10 in Hrg; rewrite ?unsigned_lit_small in Hrg by lia; lia|]);
destruct Hin | ] end.
clear HF HFr HG.
aconstsA HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm1 B TLF).
pose proof (count_cid_le_length 1 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX) TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [] ly S _ 0 (-320) _ HJ) end.
- unfold spZ. rewrite R2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite R3, E3. exact Hgp. - rewrite R4, E4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 1) with 8192. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & _ & (fS2 & ES2)).
rewrite Hes in HK. replace (spZ regs + -320 - 4096) with (spZ regs - 4416) in HK by lia. replace (spZ regs + -320) with (spZ regs - 320) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconstsA HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFapp_img.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 1) with 128 in *.
set (F := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (1, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 1) with 128 in HdFC. fold F in HdFC.
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 g CGIF_SIZE 1 fpos HAR2 ltac:(rewrite Eab; exact Hing) Hfin2) as HdFG.
unfold zdisjoint in HdFG. cbn [fst snd] in HdFG. change (req_size CGIF_SIZE) with 96 in HdFG. change (fs_frame_bytes 1) with 128 in HdFG. fold F in HdFG.
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 raw RAW_SIZE 1 fpos HAR2 ltac:(rewrite Eab; exact Hraw_in) Hfin2) as HdFR.
unfold zdisjoint in HdFR. cbn [fst snd] in HdFR. change (req_size RAW_SIZE) with 48 in HdFR. change (fs_frame_bytes 1) with 128 in HdFR. fold F in HdFR.
Local Ltac keptRA HK HJx AG Usp E10 E11 E32 Hfin Hraw Hraw2 Hing Kg Kg2 Kc Kc2 Kgu Kgu2 Ku Ku2 Vg Vg2 :=
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJx | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 2%nat) by lia; exact Usp
| lia | unfold TRAWADD_STK, LZW_TSTK, ASTACK; lia | lia | lia | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kg | exact Kg2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kc | exact Kc2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgu | exact Kgu2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 55%nat) _ _ _ _ _) =>
apply (region_kept_val_at Ex _ _ 55%nat (as_uar_cell B) 4 1); [evalE AG | exact Ku | exact Ku2 | lia]
| |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 250%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 9) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe));
[exact (H (A_OBJ 9) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Vg | exact Vg2 | lia]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj SEGS B); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 11%nat) by lia; rewrite E11; apply unsigned_lit_small; lia
| exact Hfin | lia | lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact HK | exact (proj1 HJx) | exact Hraw2 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia
| exact Hraw | lia | change (req_size RAW_SIZE) with 48; lia | lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 32%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS B); [exact HK | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?(AG 32%nat) by lia; rewrite E32; apply unsigned_lit_small; lia
| exact Hing | lia | change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | intros a Ha Hn; first [exact Hn | rqs Hn; zone_lia]]
end.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (Hraw2 : In (raw, RAW_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hraw_in).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7; 8]%nat AG
ltac:(idtac; first [keptRA HK HJ2 AG Usp E10 E11 E32 Hfin Hraw_in Hraw2 Hing Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2 | match goal with |- ?g => idtac "KEPTFAIL" g end]).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 | st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3  end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) | st_ok _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEv; exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)))  end.
clear HEv.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia)    .
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
destruct (FFL ly S2 W mem2 md2 1 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 40 529 F SB RF ltac:(lia) E40 E529)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS;
let addF lo hi cs cks :=
let HS3 := fresh "HS3" in
lazymatch goal with |- _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) lo hi lo hi cs) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | cks ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end in
addF 58 128 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))]
ltac:(apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | change (fs_frame_bytes 1) with 128 in Hflag; replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)]);
addF 49 58 (@nil YP09.chunk) ltac:(apply Forall_nil);
addF 0 49 (@nil YP09.chunk) ltac:(apply Forall_nil) | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_add_alias SEGS Ev _ _ _ _ HS (shadow_decl_ok Ev 516 40 529 F SB RF ltac:(lia) E40 E529)) as HS3;
clear HS; rename HS3 into HS;
let addF lo hi cs cks :=
let HS3 := fresh "HS3" in
lazymatch goal with |- _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 516%nat) lo hi lo hi cs) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))) | cks ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite RF; evalE AG; unfold CGIF_SIZE;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end in
addF 58 128 [YP09.mkChunk 120 (CVal 8 (SOff 528 0))]
ltac:(apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F 120 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | change (fs_frame_bytes 1) with 128 in Hflag; replace (F + 120) with (F + 128 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)]);
addF 49 58 (@nil YP09.chunk) ltac:(apply Forall_nil);
addF 0 49 (@nil YP09.chunk) ltac:(apply Forall_nil)  end.
assert (ZS : forall j, 0 <= j < 2 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (128 / 8) with 16. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv _ =>
let rs2 := eval vm_compute in (ss_mem ssv) in
assert (DJ : all_disjoint Ev (fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) rs2) by
( cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 1 / 8) with 16; rewrite E529, RF; evalE AG; unfold CGIF_SIZE, SB; repeat split; first [fs_pair_tac2 | zone_lia]);
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 1 0 16 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 1 / 8) with 16; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (128 / 8) with 16; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_nil ])
DJ) as HS3;
clear HS DJ; rename HS3 into HS end.
norm_ss HS.
paj_run_to_sh RUNTOP HS HJ2 0x84c. { awrRA AG fpos F EFA0. }
upd_aboveW HUP2 HFr AG. rename HUP2 into HUP. clear HF HFr HG.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (E11' : ew Ev 11 = Z_to_bv 64 cfp) by (rewrite (AG 11%nat) by lia; exact E11);
assert (E10' : ew Ev 10 = Z_to_bv 64 raw) by (rewrite (AG 10%nat) by lia; exact E10) end.
fs_roA HS. reshok_bx HS 40%nat.
assert (Hrapp : raw + req_size RAW_SIZE <= kLowShadowBeg \/ kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL) by exact (proj2 Hrh_ia).
paj_run_tok RUN HS HJ2 SHOK RABspan.
all: try (oblFAX HJ2 E11' E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: try (obl_blk HJ2 E10' E40 Hraw2).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA0.
clear_frames.
rebaseE HS AG HEv. clear HEv.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (RA2X (mkRACX ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg ((pf, FILE_BLOCK) :: rest) cid pos fpos wfn hw (as_uar_cell B) E)
(mkRAXX pf Sg IMG LCT) Ev 0 _ _ Wg msF mdF) | st_ok _ ?Ev _ _ =>
eapply (RA2X (mkRACX ly S W regs mem md ch raw g cfp gct rattr Wd Hd sgct loops rcur ctx lct img fattr w h top left delay slct disp tidx Nimg ((pf, FILE_BLOCK) :: rest) cid pos fpos wfn hw (as_uar_cell B) E)
(mkRAXX pf Sg IMG LCT) Ev 0 _ _ Wg msF mdF)  end end.
- unfold ra_baseX, ra_vals. cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_raw c_g c_cfp c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_Nimg c_rest c_cid c_pos c_fpos c_wfn c_hw c_uar c_E0 x_pf x_Sg x_IMG x_LCT].
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (clear - Rctx; lia); try (clear - Rwfn Rhw; lia).
+ intros j Hj. rewrite (EX j ltac:(clear - Hj; lia)). change (Z_to_bv 64 0) with ((Z_to_bv 64) 0). unfold ra_extraX, ra_extra. cbn [map app].
do 25 (try (destruct j as [|j]; [reflexivity|])). exfalso; clear - Hj; lia.
+
change 56%nat with (32 + 24)%nat. rewrite (EX 24%nat ltac:(clear; lia)). unfold ra_extraX, ra_extra. cbn [map app nth]. reflexivity.
+   left; reflexivity.
+   intros Hs. destruct (HlctX Hs) as (Nl & rest' & _ & _ & HG & HL). split; [exact HG | exact HL].
+
intros Hs. destruct (HlctX Hs) as (Nl & rest' & HP & HN & _ & _).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (pf, FILE_BLOCK) (lct, Nl) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest') HAR
ltac:(eapply Permutation_trans; [exact HPerm|];
eapply Permutation_trans; [do 4 apply perm_skip; exact HP|];
eapply Permutation_trans; [apply perm_skip; apply perm_skip; apply perm_swap|];
eapply Permutation_trans; [apply perm_skip; apply perm_swap|];
eapply Permutation_trans; [apply perm_swap|];
eapply Permutation_trans; [apply perm_skip; apply perm_skip; apply perm_skip; apply perm_swap|];
eapply Permutation_trans; [apply perm_skip; apply perm_skip; apply perm_swap|];
apply perm_skip; apply perm_swap)) as HdPL.
unfold zdisjoint, block_rng in HdPL. cbn [fst snd] in HdPL. change (req_size FILE_BLOCK) with 1264 in HdPL.
pose proof (req_size_pos Nl ltac:(clear - HN Hs; lia)) as [_ Hq]. unfold FILE_BLOCK. clear - HdPL Hq HN. lia.
- unfold ACa3.ra_EX. split; [| exact E56]. unfold ACai.ra_E, ACai.ra_F, ACai.ra_FL, ACai.ra_vals. cbn [c_ly c_fpos c_E0 c_g c_gct c_rattr c_Wd c_Hd c_sgct c_loops c_rcur c_ctx c_lct c_img c_fattr
c_w c_h c_top c_left c_delay c_slct c_disp c_tidx c_wfn c_hw c_uar]. fold F FL.
split; [exact AG|]. split; [|split; [exact RF | split; [exact E528 | split; [exact E529 | assumption]]]].
intros j Hj. do 24 (try (destruct j as [|j]; [first [assumption | lia] |])). lia.
- cbn [c_regs c_raw c_ly c_S c_W c_mem c_md c_fpos]. exact HJ2.
- cbn [c_S c_fpos]. exact Hfrs2.
- split; [split; [lia | cbn [c_ly c_S]; exact Eab]|].
cbn [c_S]. rewrite ES2. apply (mo_le_set_fs_r MT MLAWF). exact (mle_start MT S MLAW).
- lazymatch goal with |- st_ok_pi _ _ ?Ev ?ssT _ => lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
let fa := eval vm_compute in (f_atoms (ss_facts ssT)) in let al := eval vm_compute in (f_alias (ss_facts ssT)) in
exact (st_ok_pi_facts_incl Ev ssx _ fa al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)) end end.
Qed.
End e.
End d.
End b.
