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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbe.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbd ACbg.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YC7k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba ACb5 ACas ACat ACar ACaq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
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
Hypothesis AMALLOC : amalloc_realizes SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Hypothesis ASM2 : astack_malloc_realizes SEGS B 2.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis WFNX : twcbF_spec SEGS K B wfn.
Hypothesis HGOT7 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_asan3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Hypothesis HUM : forall c, In c CTX ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun ra => if ra =? pc_malloc_ra0 (as_code B) then [] else [ra]) ((BASE + 0x168) :: c))) (as_universe B).
Local Notation code := (as_code B).
Theorem pb_rawnewX :
forall ly S W (regs : bvmap 5 word) mem md ch (cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg : Z) rest (Sg GCT : list Z),
afn_pre SEGS B TRAWNEW_STK ly S W regs mem md ch -> spZ regs mod 32 = 0 ->
In (raZ regs :: spine ch) CTX -> Z.of_nat (length (frames S)) <= 8 ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 cfgp ->
afobj SEGS B ly S W mem cfgp 40 ->
obj_at SEGS (mrestrict (w_H W) mem) cfgp LAY_RawConfig [wfn; g; pgct; rattr; Wd; Hd; sgct; loops] ->
Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: rest) ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 56) 8 hw ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (g + 80) 8 pf -> pf <> 0 ->
asink_at SEGS K (mrestrict (w_H W) mem) md pf Sg -> Z.of_nat (length Sg) + HDR_OUT <= SINK_MAX ->
(sgct <> 0 -> In (pga, Npg) rest /\ Z_to_bv 64 pga = Z_to_bv 64 pgct /\ 3 * sgct <= Npg /\
garr8 SEGS (mrestrict (w_H W) mem) pga GCT /\ 3 * sgct <= Z.of_nat (length GCT)) ->
st_nev S + EV_RAWNEW <= EV_MAX -> blocks_bytes S + 2 ^ 16 <= LIVE_MAX ->
mo_ok MT S (mo_malloc MT RAW_SIZE) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_asan3_cgif_raw_newgif) regs mem md)
(rn_postX K MT B wfn regs ly S W mem md g pgct rattr Wd Hd sgct loops pf Sg GCT).
Proof.
intros ly S W regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest Sg GCT HPRE Hal32 Hctx Hroom HROD H10 HFO Hcfg HPerm Mgw Mgf Rctx Mg80 Hpf0 HSINK HSmax HGCT Hev Hlive MOK.
assert (Hinf : In (pf, FILE_BLOCK) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
assert (Hsg16 : 0 <= sgct <= 65535).
{ pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32. lia. }
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (rn_entryX B TL LAWS TLF wfn hw Rwfn Rhw HGOT7 W ly S regs mem md ch cfgp g pgct rattr Wd Hd sgct loops ctx pf _ HPRE Hal32 HROD H10 HFO Hcfg HPerm Mgw Mgf Rctx Mg80 Hinf Hsg16) as HS.
pose proof (ajournal_init SEGS B TRAWNEW_STK (asink_fp pf) ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (FFS : TRAWNEW_STK = 16576) by reflexivity.
assert (HEV : EV_RAWNEW = 4) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hfin) as Hfhigh_img.
assert (EFA0 : forall c p, frame_addr ly c p = frame_addr ly c p) by reflexivity. assert (EFL0 : forall c p, flag_addr ly c p = flag_addr ly c p) by reflexivity.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS ly S W mem md g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, Hgh_img.
destruct (al_blocks _ _ LAWS ly S W mem md pf FILE_BLOCK HAR Hinf) as (Hp16 & Hp4096 & Hpceil & Hp_ia & _ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ pf FILE_BLOCK HAR Hinf) as Hph_img. change (req_size FILE_BLOCK) with 1264 in Hpceil, Hph_img, Hp_ia. unfold off_img in Hph_img.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md pf FILE_BLOCK cid pos HAR Hinf Hfin) as HdPC.
unfold zdisjoint in HdPC. cbn [fst snd] in HdPC. change (req_size FILE_BLOCK) with 1264 in HdPC.
assert (XF : xfacts (pf + 1264 <= alloc_ceiling /\ 4096 <= pf /\ alloc_ceiling + TRAWNEW_STK <= spZ regs /\ TRAWNEW_STK = 16576 /\ 140735332483072 <= alloc_ceiling <= 140737479966720 /\ (pf + 1264 <= 65536 \/ 6270976 <= pf) /\ (pf + 1264 <= cfgp \/ cfgp + 40 <= pf) /\ 4096 <= cfgp))
by (apply xfacts_i; clear - Hpceil Hp4096 Hceil Hslo FFS C1 Hph_img HdPC Hflo Hfhi Hf4096; lia).
clear HdPC Hph_img. change (in_app pf 1264) with (xfacts (in_app pf 1264)) in Hp_ia.
remember (Eimg (Ereg regs (rn_extraX g pgct rattr Wd Hd sgct loops ctx wfn hw (as_uar_cell B) pf))) as E eqn:HE.     assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 cfgp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (rn_extraX g pgct rattr Wd Hd sgct loops ctx wfn hw (as_uar_cell B) pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37. pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39. pose proof (EX 8%nat ltac:(lia)) as E40.
pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42. pose proof (EX 11%nat ltac:(lia)) as E43.
pose proof (EX 12%nat ltac:(lia)) as E44. pose proof (EX 13%nat ltac:(lia)) as E45.
cbn [Nat.add nth rn_extraX rn_extra map app] in E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (rn_extraX g pgct rattr Wd Hd sgct loops ctx wfn hw (as_uar_cell B) pf)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
clear HE.
assert (Hchne : ch <> []).
{ intros ->. pose proof (HDEEP _ Hctx) as HL. cbn in HL. lia. }
assert (Htop32 : spZ regs + 16 <= s0Z regs /\ s0Z regs < ly_top ly - 16).
{ destruct Hch as [[_ Hnil] | (H1 & H2 & _)]; [exfalso; exact (Hchne Hnil) | lia]. }
img_facts E. img_hull_facts.
unfold cfg_at. change (w64 (BASE + AF_asan3_cgif_raw_newgif)) with (Z_to_bv 64 (BASE + AF_asan3_cgif_raw_newgif)).
shok_auto SHOK RBx E (mrestrict (w_H W) mem).
paj_run_tok RUN HS HJ SHOK RBspan. { awr_ok_tac. exact Usp. }
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ (ms_mem ?msX)) =>
assert (HUP : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) mem a);
[ eapply (aview_kept_frame Ef rs _ _ _ (spZ regs) HFr); [lia|];
intros a Ha (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; rewrite ?Usp in Hrg; lia|]);
match goal with |- ?g => match type of Hin with ?t => idtac "HUPLEFT" t end end; destruct Hin | ] end.
xsink_stretch HFr HSINK.
clear HF HFr HG.
aconsts HROD HJ Kgot0 Kcell0 Kguar0 Kuar0 Vgr0.
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm2 B TLF).
pose proof (count_cid_le_length 2 (frames S)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 2 ASM2 ltac:(lia) W (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [] ly S _ 0 (-192) _ HJ) end.
- unfold spZ. rewrite R2, E2. fold (spZ regs). rewrite unsigned_lit_small by lia. lia.
- reflexivity. - lia. - rewrite FFS, Hes; lia.
- rewrite R3, E3. exact Hgp. - rewrite R4, E4. exact Htp.
- exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
- change (fs_frames 2) with 4096. lia. }
cbv beta. clear R2 R3 R4 R1 HJ SHOK.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJt2 & (fS2 & ES2)).
assert (Hinf2 : In (pf, FILE_BLOCK) (ablocks B ly S2)) by (rewrite Eab; exact Hinf).
xsink_sub HJt2 HSINK Hinf Hinf2. clear HJt2.
rewrite Hes in HK. replace (spZ regs + -192 - 4096) with (spZ regs - 4288) in HK by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK by lia.
assert (HUP2 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. rewrite <- (HUP a Ha). pose proof HK as (K1 & _). apply K1; lia. }
clear HUP.
aconsts HROD HJ2 Kgot2 Kcell2 Kguar2 Kuar2 Vgr2.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (2, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
assert (HfinS2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFapp_img.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin2) as HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
set (F := frame_addr ly 2 fpos) in *. set (FL := flag_addr ly 2 fpos) in *.
destruct (in_split _ _ Hfin) as (fl1 & fl2 & Efl).
pose proof (sep_frames_pos SEGS B LAWS ly S2 W mem2 md2 (2, fpos) (cid, pos) [] fl1 fl2 HAR2 ltac:(rewrite Hfrs2, Efl; reflexivity)) as HdFC.
unfold zdisjoint, frame_rng in HdFC. cbn [fst snd] in HdFC. change (fs_frame_bytes 2) with 256 in HdFC. fold F in HdFC.
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 g CGIF_SIZE 2 fpos HAR2 ltac:(rewrite Eab; exact Hing) Hfin2) as HdFG.
unfold zdisjoint in HdFG. cbn [fst snd] in HdFG. change (req_size CGIF_SIZE) with 96 in HdFG. change (fs_frame_bytes 2) with 256 in HdFG. fold F in HdFG.
pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 pf FILE_BLOCK 2 fpos HAR2 Hinf2 Hfin2) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (req_size FILE_BLOCK) with 1264 in HdPF. change (fs_frame_bytes 2) with 256 in HdPF. fold F in HdPF.
pose proof HFhigh_img as HFoff. unfold off_img in HFoff. change (fs_frame_bytes 2) with 256 in HFoff. fold F in HFoff.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; keptR HK HJ2 AG Usp E10 E32 Hfin Hing Kgot0 Kgot2 Kcell0 Kcell2 Kguar0 Kguar2 Kuar0 Kuar2 Vgr0 Vgr2).
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
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
lazymatch type of XF with xfacts ?P => assert (XF2 : xfacts (P /\ (pf + 1264 <= F \/ F + 256 <= pf) /\ 4096 <= F /\ F + 256 <= alloc_ceiling /\ (F + 256 <= 65536 \/ 6270976 <= F) /\ 512 <= F / 8 < 17592186044416))
by (apply xfacts_i; split; [exact XF | clear - HdPF HF4096 HFceil HFoff HF8lo HF8hi; lia]); clear XF HFoff HdPF; rename XF2 into XF end.
destruct (FFL ly S2 W mem2 md2 2 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng). fold FL in HFLpres, HFLown, HFLrng.
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
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS (shadow_decl_ok Ev 516 35 529 F SB RF ltac:(lia) E35 E529)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 2 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2) with 256; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F (256 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (256 - 8)) with (F + 256 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2) with 256;
rewrite RF; evalE AG;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
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
pose proof (st_ok_add_alias SEGS Ev _ _ _ _ HS (shadow_decl_ok Ev 516 35 529 F SB RF ltac:(lia) E35 E529)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 516 528 2 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2) with 256; rewrite RF, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Ev _ F (256 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (256 - 8)) with (F + 256 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2) with 256;
rewrite RF; evalE AG;
repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
assert (ZS : forall j, 0 <= j < 4 -> val_mem SEGS (mrestrict (w_H W) mem2) (SB + F / 8 + 8 * j) 8 0).
{ intros j Hj. apply val_mem_zero8. intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
replace (SB + F / 8 + 8 * j + i) with (SB + F / 8 + (8 * j + i)) by lia. apply Hz. change (256 / 8) with 32. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 2 0 32 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2 / 8) with 32; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (256 / 8) with 32; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 16 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32;
rewrite E529, RF; evalE AG; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 2 0 32 [YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 8 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 2 / 8) with 32; rewrite E529, unsigned_lit_small by (unfold SB; lia); split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres;
replace (SB + F / 8 + o) with (SB + F / 8 + o) by lia; apply (proj1 (HFSpres o ltac:(change (256 / 8) with 32; lia)))
| apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside | rewrite Z.add_0_r; replace (SB + F / 8) with (SB + F / 8 + 8 * 0) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 8 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 8) with (SB + F / 8 + 8 * 1) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 16 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 16) with (SB + F / 8 + 8 * 2) by lia; apply ZS; lia]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ (SB + F / 8) 24 8 _ 0); [reflexivity | zside | zside | replace (SB + F / 8 + 24) with (SB + F / 8 + 8 * 3) by lia; apply ZS; lia]|];
apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 2 / 8) with 32;
rewrite E529, RF; evalE AG; unfold SB; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
paj_run_to_sh RUNTOP HS HJ2 0x148. { awrR AG fpos F EFA0. }
upd_above HUP2 HFr AG. rename HUP2 into HUP.
xsink_stretch HFr HSINK.
clear HF HFr HG.
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (E10' : ew Ev 10 = Z_to_bv 64 cfgp) by (rewrite (AG 10%nat) by lia; exact E10) end.
fs_ro HS. reshok_bx HS 35%nat.
paj_run_tok RUN HS HJ2 SHOK RBspan; [oblFX HJ2 E10' E35 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal | awrR AG fpos F EFA0 |].
upd_above HUP HFr AG. xsink_stretch HFr HSINK. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RBspan.
-
paj_run_to_tok RUNTO HS HJ2 SHOK RBspan 0x618; [awrR AG fpos F EFA0|]. xsink_stretch HFr HSINK. clear HF.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hing).
exitRX RET RUNF HS HJ2 AG fpos F cfgp g E528 E529 Hfin2 HfinS2 Hing2 EE Hra HEV EFA0 EFL0.
exists 0. split; [reflexivity|].
split.
{ unfold stack_free_state. apply (mo_le_set_fs_r MT MLAWF). rewrite ES2. apply (mo_le_set_fs_r MT MLAWF).
exact (mle_weaken MT S S 0 _ MLAW (mle_start MT S MLAW) (mo_malloc_nonneg MT MLAW RAW_SIZE ltac:(unfold RAW_SIZE; lia))). }
left. split; [reflexivity|]. split.
{
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E38 in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
destruct (Z.ltb_spec 256 sgct); [lia | discriminate Hc]. }
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly S2); rewrite Eab; apply Permutation_refl|].
lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => exact H end.
-
assert (Hsg : sgct <= 256).
{ pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'. destruct Hc' as (_ & _ & _ & _ & _ & _ & [_ R32] & _). cbn [fst snd N.to_nat Z.of_N] in R32.
change (2 ^ (8 * 2)) with 65536 in R32.
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hc.
rewrite ?ew_ewset_other in Hc by lia. rewrite E38 in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia.
destruct (Z.ltb_spec 256 sgct); [discriminate Hc | lia]. }
paj_run_tok RUN HS HJ2 SHOK RBspan; [awrR AG fpos F EFA0|].
upd_above HUP HFr AG. xsink_stretch HFr HSINK. clear HF HFr HG.
assert (HMM : MALLOC_MAX = 2 ^ 28) by reflexivity.
clear Kgot2 Kcell2 Kguar2 Kuar2 Vgr2. aconsts HROD HJ2 KgotB KcellB KguarB KuarB VgrB.
prreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp. prreg HS (8%bv : bv 5) Rs0.
assert (Qceil : alloc_ceiling <= spZ regs) by lia. assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D; rewrite Hal32, Z.add_0_r in D; rewrite D; replace (32 * (spZ regs / 32)) with ((4 * (spZ regs / 32)) * 8) by lia; apply Z_mod_mult).
assert (Qtop : spZ regs < ly_top ly - 16) by lia. assert (Qtop64 : ly_top ly <= 2 ^ 64) by lia. assert (Qsp : spZ regs - 192 + 16 <= spZ regs) by lia.
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 2 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msX) 2 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly (aview SEGS (w_H W) (ms_mem msX)) (spZ regs - 192) (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ (spZ regs - 192) Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 Qceil Qal8 Qtop Qsp)
| ]  end.
pmkst HS.
ppcs.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)]
ly S2 _ 0 48 (-192) (Z_to_bv 64 (BASE + 0x168)) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ2) end.
- exact Ra0.
- rewrite HMM. lia.
- rewrite Hbb2. unfold LIVE_MAX in *. lia.
- unfold spZ. rewrite Rsp. evalE AG.
- reflexivity.
- lia.
- rewrite FFS. unfold ASTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite Hnev2. rewrite HEV in Hev. unfold EV_MAX in *. lia.
- apply (achain_chain_pre ly _ (spZ regs - 192) (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp; evalE AG
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia ].
- rewrite call_trace_of_spine. cbn [spine map fst snd]. fold (spine ch). unfold raZ at 1. rewrite Rra, unsigned_lit_small by lia.
exact (HUM (raZ regs :: spine ch) Hctx).
-   rewrite ES2. apply (mo_ok_set_fs MT MLAWF). exact MOK. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Ha03 & Hfrs3 & Hres4096 & Eab3 & HK3 & MLE3 & HJt3).
assert (Hinf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; exact Hinf2).
xsink_sub HJt3 HSINK Hinf2 Hinf3. clear HJt3.
clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1 HUP Vra Vs0 Qceil Qal8 Qtop Qtop64 Qsp Qra Qs0.
unfold ASTACK in HK3. replace (spZ regs + -192 - 16384) with (spZ regs - 16576) in HK3 by lia. replace (spZ regs + -192) with (spZ regs - 192) in HK3 by lia.
pose proof (proj1 HJ3) as HAR3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR (proj1 (proj2 HJ3))) as (_ & EFA3 & _).
assert (EFL3 : forall c p, flag_addr ly3 c p = flag_addr ly c p) by (intros c p; unfold flag_addr; pose proof (EFA3 c p) as X; unfold frame_addr in X; lia).
assert (Hfin3 : In (2, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
assert (HfinS3 : In (cid, pos) (frames S3)) by (rewrite Hfrs3; exact HfinS2).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin3) as (_ & _ & HFpres3 & HFSpres3). change (fs_frame_bytes 2) with 256 in HFpres3, HFSpres3.
change (256 / 8) with 32 in HFSpres3. rewrite !EFA3 in HFpres3, HFSpres3. fold F in HFpres3, HFSpres3.
idtac.
assert (Hres_in : In (res, 48) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; left; rewrite Eab; exact Hing).
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly S2)) by (rewrite Eab; exact Hing).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 HAR3 Hres_in) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & Hrpres & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ res 48 HAR3 Hres_in) as Hrh_img.
change (req_size 48) with 48 in Hrceil, Hrpres, Hrh_img.
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 48 HJ2 HAR3 Eab3 ltac:(lia)) as Tres.
assert (Ares : forall blc lyq ownq i, In (res, 48) blc -> 0 <= i < 48 -> awr_byte TRAWNEW_STK (spZ regs) (asink_fp pf) (ablocks B ly S) blc lyq ownq (res + i)).
{ intros blc lyq ownq i Hbl Hi. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res 48 blc i lyq ownq HJ2 HAR3 Eab3 ltac:(lia) Hbl ltac:(change (req_size 48) with 48; lia)). }
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ res 48 2 fpos HAR3 Hres_in Hfin3) as HdRF.
unfold zdisjoint in HdRF. cbn [fst snd] in HdRF. change (req_size 48) with 48 in HdRF. change (fs_frame_bytes 2) with 256 in HdRF. rewrite EFA3 in HdRF. fold F in HdRF.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ res 48 cid pos HAR3 Hres_in HfinS3) as HdRC.
unfold zdisjoint in HdRC. cbn [fst snd] in HdRC. change (req_size 48) with 48 in HdRC. rewrite EFA3 in HdRC.
pose proof (sep_blocks SEGS B LAWS ly3 S3 _ _ _ g CGIF_SIZE res 48 HAR3 Hing3 Hres_in ltac:(unfold CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG. cbn [fst snd] in HdRG. change (req_size 48) with 48 in HdRG. change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_blocks SEGS B LAWS ly3 S3 _ _ _ pf FILE_BLOCK res 48 HAR3 Hinf3 Hres_in ltac:(unfold FILE_BLOCK; intros X; injection X; lia)) as HdPR.
unfold zdisjoint in HdPR. cbn [fst snd] in HdPR. change (req_size 48) with 48 in HdPR. change (req_size FILE_BLOCK) with 1264 in HdPR.
pose proof Hrh_img as HRoff. unfold off_img in HRoff.
lazymatch type of XF with xfacts ?P => assert (XF2 : xfacts (P /\ (pf + 1264 <= res \/ res + 48 <= pf) /\ 4096 <= res /\ res + 48 <= alloc_ceiling /\ (res + 48 <= 65536 \/ 6270976 <= res)))
by (apply xfacts_i; split; [exact XF | clear - HdPR Hr4096 Hrceil HRoff; lia]); clear XF HRoff HdPR; rename XF2 into XF end.
assert (HErF : forall a, F <= a < F + 256 -> ~ (res <= a < res + req_size 48)) by (change (req_size 48) with 48; intros a Ha; lia).
reseat HS HJ3 HP3 [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]%nat AG
ltac:(idtac; first [ keptR HK3 HJ3 AG Usp E10 E32 HfinS2 Hing2 KgotB Kgot3 KcellB Kcell3 KguarB Kguar3 KuarB Kuar3 VgrB Vgr3
| keptF HK3 AG RF E529 Hfin2 HFpres3 HFSpres3 HErF F
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
prreg HS (10%bv : bv 5) Rres. cbn [ms_regs] in Rres. rewrite Ha03 in Rres. symmetry in Rres. unfold w64 in Rres.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_pi_add_fact Ex _ _ nx (HPTR 4) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia; change (2 ^ 4) with 16; lia)) as HS3;
clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some nx) 0 48 0 48 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Rres, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrpres (res + o) ltac:(lia))))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rres; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32; evalE AG;
unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 35%nat.
paj_run_tok RUN HS HJ3 SHOK RBspan.
{ lazymatch type of Rres with ew _ ?nx = _ =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ nx); [reflexivity | evalE AG | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; replace a with (res + (a - res)) by lia; apply Ares; [exact Hres_in | lia] |] end.
awrR AG fpos F EFA3. }
xsink_stretch HFr HSINK. clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ3) HfinS3) as (_ & _ & HCpres3 & _). rewrite EFA3 in HCpres3.
assert (Qcs : cfgp + 40 <= spZ regs - 192 - ESTACK) by (unfold ESTACK; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY _ (ms_regs msX) (ms_mem msX) TRAWNEW_STK (spZ regs) (asink_fp pf) ly S W mem md [(2, fpos)]
ly3 S3 _ _ res cfgp 40 (-192) (Z_to_bv 64 (BASE + 0x17c)) HJ3) end.
- rewrite Ra0. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Rres. reflexivity.
- rewrite Ra1. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 10%nat) by lia. rewrite E10. reflexivity.
- exact Ra2.
- lia. - lia. - lia.
- unfold spZ at 1. rewrite Rsp. evalE AG.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 3%nat) by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 4%nat) by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [replace a with (res + (a - res)) by lia; apply Ares; [exact Hres_in | lia] | unfold ESTACK; lia].
- apply (amem_range_of_block SEGS B LAWS ly3 S3 _ _ _ res 48 _ _ (proj1 HJ3) Hres_in); change (req_size 48) with 48; lia.
- apply (range_addressable_of_block SEGS B LAWS ly3 S3 _ _ _ res 48 _ _ (proj1 HJ3) Hres_in); change (req_size 48) with 48; lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 _ _ _ res 48 _ _ (proj1 HJ3) Hres_in); change (req_size 48) with 48; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ; rewrite Rsp; evalE AG].
apply (aview_some_of_apresent SEGS). apply (proj1 (HCpres3 a ltac:(lia))). }
split; [clear - HdRC Hflo Hfhi; lia|]. split; [apply (amem_range_sub_app _ _ _ _ Hfhigh Hfceil Hflo Hfhi); clear; lia|]. split.
+ eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ3 | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| xFP | exact HAR | exact HRA].
+ intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 _ _ _ cid pos cfgp 40 (proj1 HJ3) HfinS3); [rewrite EFA3; exact Hflo | rewrite EFA3; exact Hfhi | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HSM4).
xsink_intrin Hfr4 HSM4 HSINK. clear HSM4.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'.
destruct Hc' as ([V0 _] & [V8 R8] & [V16 R16] & [V24 R24] & [V28 R28] & [V30 R30] & [V32 R32] & [V34 R34] & _).
cbn [fst snd N.to_nat Z.of_N] in V0, V8, V16, V24, V28, V30, V32, V34, R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in R8, R16. change (2 ^ (8 * 4)) with (2 ^ 32) in R24. change (2 ^ (8 * 2)) with 65536 in R28, R30, R32, R34.
lazymatch type of Heff with forall i, _ -> aview _ _ _ _ = aview _ _ ?memT _ =>
let cmove off w v V Vr :=
pose proof (val_mem_moved SEGS (w_H W3) (w_H W3) memT mem4 (cfgp + off) (res + off) w v
ltac:(intros k Hk; replace (res + off + k) with (res + (off + k)) by lia; replace (cfgp + off + k) with (cfgp + (off + k)) by lia;
apply Heff; cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; lia)
(val_mem_entry_frame SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (cfgp + off) w v HJ3 Hfin
ltac:(lia) ltac:(cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add]; lia) ltac:(xFP) V)) as Vr in
cmove 0 8%nat wfn V0 W0;
cmove 8 8%nat g V8 W8; cmove 16 8%nat pgct V16 W16; cmove 24 4%nat rattr V24 W24;
cmove 28 2%nat Wd V28 W28; cmove 30 2%nat Hd V30 W30; cmove 32 2%nat sgct V32 W32; cmove 34 2%nat loops V34 W34 end.
rewrite Z.add_0_r in W0.
aconsts HROD HJ4 Kgot4 Kcell4 Kguar4 Kuar4 Vgr4.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res 48 (proj1 HJ4) Hres_in) as (_ & _ & _ & _ & Hrpres4 & _). change (req_size 48) with 48 in Hrpres4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ4) Hfin3) as (_ & _ & HFpres4 & HFSpres4). change (fs_frame_bytes 2) with 256 in HFpres4, HFSpres4.
change (256 / 8) with 32 in HFSpres4. rewrite !EFA3 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
clear Kgot3 Kcell3 Kguar3 Kuar3 Vgr3. aconsts HROD HJ3 Kgot3 Kcell3 Kguar3 Kuar3 Vgr3.
reseat HS HJ4 HP4 [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]%nat AG
ltac:(idtac; first [ keptI Hfr4 Hpres4 AG Kgot3 Kgot4 Kcell3 Kcell4 Kguar3 Kguar4 Kuar3 Kuar4 Vgr3 Vgr4
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of Rres with ew _ ?nx = _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some nx) 0 48 40 48
[YP09.mkChunk 0 (CVal 8 (SOff 41 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
YP09.mkChunk 24 (CVal 4 (SOff 34 0)); YP09.mkChunk 28 (CVal 2 (SOff 36 0)); YP09.mkChunk 30 (CVal 2 (SOff 37 0));
YP09.mkChunk 32 (CVal 2 (SOff 38 0)); YP09.mkChunk 34 (CVal 2 (SOff 39 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrpres4 (res + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 0 8 _ wfn); [ckv E41 | zside | zside | rewrite Z.add_0_r; exact W0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 8 8 _ g); [ckv E32 | zside | zside | exact W8]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 16 8 _ pgct); [ckv E33 | zside | zside | exact W16]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 24 4 _ rattr); [ckv E34 | zside | zside | exact W24]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 28 2 _ Wd); [ckv E36 | zside | zside | exact W28]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 30 2 _ Hd); [ckv E37 | zside | zside | exact W30]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 32 2 _ sgct); [ckv E38 | zside | zside | exact W32]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 34 2 _ loops); [ckv E39 | zside | zside | exact W34]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rres; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32; evalE AG;
unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end | st_ok _ ?Ev _ _ =>
lazymatch type of Rres with ew _ ?nx = _ =>
let ckv HE := cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
try rewrite (AG 32%nat) by lia; rewrite HE; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity in
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some nx) 0 48 40 48
[YP09.mkChunk 0 (CVal 8 (SOff 41 0)); YP09.mkChunk 8 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
YP09.mkChunk 24 (CVal 4 (SOff 34 0)); YP09.mkChunk 28 (CVal 2 (SOff 36 0)); YP09.mkChunk 30 (CVal 2 (SOff 37 0));
YP09.mkChunk 32 (CVal 2 (SOff 38 0)); YP09.mkChunk 34 (CVal 2 (SOff 39 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hrpres4 (res + o) ltac:(lia)))|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 0 8 _ wfn); [ckv E41 | zside | zside | rewrite Z.add_0_r; exact W0]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 8 8 _ g); [ckv E32 | zside | zside | exact W8]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 16 8 _ pgct); [ckv E33 | zside | zside | exact W16]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 24 4 _ rattr); [ckv E34 | zside | zside | exact W24]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 28 2 _ Wd); [ckv E36 | zside | zside | exact W28]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 30 2 _ Hd); [ckv E37 | zside | zside | exact W30]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 32 2 _ sgct); [ckv E38 | zside | zside | exact W32]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ res 34 2 _ loops); [ckv E39 | zside | zside | exact W34]|];
apply Forall_nil)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Rres; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32; evalE AG;
unfold CGIF_SIZE; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end  end.
norm_ss HS. clear W0 W8 W16 W24 W28 W30 W32 W34 Heff.
pose proof (rn_XX B TL LAWS ML ASF FFL TLF wfn hw Rwfn Rhw K AIL MT MLAWF HGOT7) as PXX.
pose proof (rn_DX B TL LAWS TLF wfn hw Rwfn Rhw K AIL MT WFNX HGOT7 PXX) as PDX.
pose proof (rn_GX B TL LAWS TLF wfn hw Rwfn Rhw K AIL MT WFNX HGOT7 PDX) as PGX.
pose proof (rn_CX B TL LAWS TLF wfn hw Rwfn Rhw K AIL MT WFNX HGOT7 PDX PGX) as PCX.
pose proof (rn_BX B TL LAWS AMEMSET TLF wfn hw Rwfn Rhw K AIL MT HGOT7 PCX) as PBX.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msv) =>
change ssx with ss_BX in HS;
eapply (PBX ly S W regs mem md _ cfgp g pgct rattr Wd Hd sgct loops ctx pf pga Npg rest cid pos E Ev W3 ly3 S3 msv _ _ fpos res Sg GCT);
[ exact HPRE | exact Hchne | exact Hal32 | exact HROD
| split; [exact Hfin | split; [exact Hcid0 | split; [exact Hfal | split; [exact Hflo | split; [exact Hfhi | split; [exact Hcal | exact HRA]]]]]]
| exact Hcfg | exact HPerm | exact Hev
| split; [exact EE | split; [exact E10 | split; [exact E32 | exact Usp]]]
| split; [| split; [exact E44 | exact E45]]; split; [exact AG | repeat (split; [eassumption|]); eassumption]
| split; [exact HJ4 | split; [clear; lia | split; [rewrite Hfrs3, Hfrs2; reflexivity | split; [rewrite Eab3, Eab; apply Permutation_app_tail; apply Permutation_refl | split; [exact Hres4096 | split; [exact Tres | split; [exact Ares | split; [| ]]]]]]]]
| exact Hsg | exact HSmax | exact HGCT | exact HS ] end.
{   unfold PRE_C. rewrite app_nil_r. exact HSINK. }
{   rewrite ES2 in MLE3. exact (mo_le_set_fs_l MT MLAWF _ _ _ _ MLE3). }
Qed.
End e.
End d.
End b.
