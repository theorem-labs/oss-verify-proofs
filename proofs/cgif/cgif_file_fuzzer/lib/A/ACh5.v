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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC81 YC4b YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp AC8h ACh9 AChc ACh8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0c YC5d YC7z YC7x YC21 YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh7 ACh6 ACh4 ACh1 ACh2 ACh3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Section i.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Variable CTX : list (list Z).
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AFM : afile_meter SEGS B MT.
Variable XN : xnums.
Hypothesis HXM : forall N, cl_msum MT XN N <= xm_close XN N.
Hypothesis HXN : forall N, cl_msum MT XN N <= xn_close XN N.
Hypothesis HXF0 : forall N, 0 <= xn_flush XN N.
Hypothesis HXMF0 : forall N, 0 <= xm_flush XN N.
Hypothesis HXMF : forall N, xn_flush XN N + xm_flush XN N <= xm_close XN N.
Hypothesis HUfc : In [pc_free_ra0 (as_code B); BASE + 0x73c] (as_universe B).
Hypothesis HUff1 : In [pc_free_ra0 (as_code B); BASE + 0x2ad0] (as_universe B).
Hypothesis HUff2 : In [pc_free_ra0 (as_code B); BASE + 0x2b08] (as_universe B).
Hypothesis HUrfc : In [pc_free_ra0 (as_code B); BASE + CL_RET_FREECGIF] (as_universe B).
Hypothesis HUrff : In [pc_free_ra0 (as_code B); BASE + CL_RET_FREEFRAME] (as_universe B).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Variable rctrace : list Z.
Hypothesis HUrc : In rctrace (as_universe B).
Hypothesis RAWCLOSEX : forall hw, 0 <= hw < 2 ^ 64 -> trawclose_specX SEGS K B MT (SIGMA AS_cgif_raw_close) rctrace WFN_ADDR hw.
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_spec SEGS B K (SIGMA AS_fclose) ra_fc1 ra_fc2 pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Variable CTXfl : list (list Z).
Hypothesis HCTXfl : In [BASE + CL_RET_FLUSH] CTXfl.
Hypothesis FLUSHX : tflush_specX SEGS K B MT XN (BASE + A_flushFrame) CTXfl WFN_ADDR pa_relro_lo pa_relro_hi.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Section k.
Variable hw path pf : Z.
Lemma regsA_okX : forall (regs : bvmap 5 word) g s1,
getr regs 10 = w64 g -> 4096 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs (cl_extraX regs g s1 pf))) regsA regs.
Proof.
intros regs g s1 H10 Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs (cl_extraX regs g s1 pf))). assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 0); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity | rewrite E32; exact H10 ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cl_frame_of_region0 : forall E (m : word -> option byte) sp0 (regs : bvmap 5 word) wlo whi,
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-80) 0 wlo whi [YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) ->
cl_frame SEGS m sp0 regs.
Proof.
intros E m sp0 regs wlo whi HR Hsp HE j r Hj.
assert (Hj9 : (j < 9)%nat) by (apply (proj1 (nth_error_Some cl_saved j)); rewrite Hj; discriminate).
pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia. change 8%nat with (N.to_nat 8).
do 9 (destruct j as [|j];
[ cbn in Hj; injection Hj as <-;
lazymatch goal with |- val_mem _ _ (_ + ?od) _ (bv_unsigned (getr _ (Z_to_bv 5 ?R))) =>
let od' := eval vm_compute in od in change od with od';
let n := eval vm_compute in (Z.to_nat R) in
apply (field_of_region E m 2 sp0 _ (-80) 0 wlo whi od' 8 (SOff n 0) _ HR Hsp);
[ cbn; tauto
| cbn [sv_denot]; rewrite (HE n (Z_to_bv 5 R) eq_refl), Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
| exact HRr
| cbn; lia ] end
| ]). cbn in Hj9. lia.
Qed.
Ltac awr_clAX Usp E32u Hing HTS :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite HTS; lia | cbn; lia |];
apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | exact E32u | exact Hing | cbn [YP09.r_wlo]; lia
| cbn [YP09.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; unfold FPcX, FPc, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| apply awr_ok_nil ] end.
Lemma cl_A_okX : CL_B_stmtX B hw CTX path pf K MT XN -> CL_IT1_stmtX B hw CTX path pf K MT XN ->
forall ly S W regs mem md ch g s N aM rest GPAL gs,
cl_cxX B hw CTX path pf ly S W regs mem md ch g s N rest -> cl_xent pf K MT XN ly S W mem md s N aM GPAL gs ->
SRr SEGS W (cfg_at SEGS (BASE + A_cgif_close) regs mem md) (cl_postX B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs (2 * EV_FLUSH + 16)).
Proof.
intros CLB IT1 ly S W regs mem md ch g s N aM rest GPAL gs CX XE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof HREL as ((HRC & HOCC) & HSINK & HLIVE).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (ajournal_init SEGS B TCLOSE_STK (FPcX g s N pf) ly S W regs mem md ch HPRE) as HJ.
assert (HTS : TCLOSE_STK = 17520) by reflexivity. assert (HEVF : EV_FLUSH = 35) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen.
assert (HOK : cl_obj_ok g s s N) by (split; [exact HWF | repeat split; reflexivity]).
assert (Hinpf : In (pf, FILE_BLOCK) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR Hinpf) as (_ & Hpf4096 & Hpfceil & _). change (req_size FILE_BLOCK) with 1264 in Hpfceil.
assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_blocks SEGS B LAWS ly S W mem md g CGIF_SIZE pf FILE_BLOCK HAR Hing Hinpf ltac:(unfold CGIF_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
destruct (cl_seed_entryX B LAWS TL hw path pf A_cgif_close regsA W regs regs mem ly S md ly sp0 g s HAR Hing Hstk Hpres
ltac:(unfold sp0, spZ; lia) (regsA_okX regs g s H10 Hgh Hgceil) (proj1 HT)) as [HS SHOK].
unfold cfg_at. change (mkst regs (Z_to_bv 64 A_cgif_close) mem (seg_rom SEGS)) with (mkst regs (Z_to_bv 64 A_cgif_close) mem (seg_rom SEGS)) in *.
set (E := Eimg (Ereg regs (cl_extraX regs g s pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s) (proj1 HT) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_tok RUN HS HJ SHOK RBspanC.
{ awr_clAX Usp E32u Hing HTS. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
pose proof (U_atom E 37 (cg_cur s) E37 ltac:(clear - Rcur; lia)) as Ucur.
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
rewrite branch_ne_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity. rewrite (cl_U_sext32 E (SOff 37 0) (cg_cur s) Ucur Rcur) in Hc.
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_B.
{ awr_clAX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20; prreg HS (18%bv : bv 5) Q18.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
assert (HVK : cl_vkept (mrestrict (w_H W) mem) (mrestrict (w_H W) m2) s N)
by exact (cl_vkept_stretchA B LAWS ly S W mem md _ g s N _ (sp0 - 80) sp0 HAR HPerm ltac:(clear - Hceil Hslo HTS C1; lia) UN) end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W) _) g (cl_set_cur s (cg_cur s)))
by (eapply (xcgif_at_stretchXA B LAWS hw path pf ly S W mem md _ g s s N ((pf, FILE_BLOCK) :: rest) (cg_cur s) HAR HPerm HOK HT); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a) by (clear - Ha Hna Hceil Hslo HTS C1; lia); apply UN1; clear - Ha Hna Hceil Hslo HTS C1; lia).
assert (Hcne : YO07.s_cur gs <> YO07.C_OK).
{ rewrite <- HRC. unfold rc_int, YO07.C_OK. destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); cbn [negb] in Hc;
[destruct (Z.eqb_spec (cg_cur s) 0); [discriminate Hc | assumption] | clear - Rcur H; lia]. }
pose proof (close_gif_dead (gcfg_of s GPAL) gs Hcne) as ECG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N aM rest GPAL gs ly S W rg mm mdq 0 (cl_set_cur s (cg_cur s)) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [lia|]. split.
{ exact (cl_frame_of_region0 E _ sp0 regs _ _ HR0 Usp EEo). }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s N _ HOK) | exact HPerm].
+ clear - HEVF. lia.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. cbn [sv_denot]. rewrite Usp. unfold sp0, spZ. reflexivity.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Hgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Htp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); reflexivity end).
+ rewrite Q20. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. exact E38.
+
split; [| split; [| split; [| reflexivity]]].
* rewrite ECG. apply (asink_at_kept_mm SEGS K (mrestrict (w_H W) mem) _ md _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp Hpfceil Hceil Hslo HTS C1; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi Hceil Hslo HTS C1; lia ].
* apply (mle_weaken MT S S 0 _ MLAW (mle_start MT S MLAW)). unfold cl_macc_b. pose proof (HXF0 N) as H0. clear - H0. lia.
* rewrite ECG. unfold CLOSE_OUT, FRAME_OUT in HLEN. clear - HLEN HN0. lia.
-
rewrite branch_ne_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity. rewrite (cl_U_sext32 E (SOff 37 0) (cg_cur s) Ucur Rcur) in Hc.
assert (Hcur0 : cg_cur s = 0).
{ destruct (Z.ltb_spec (cg_cur s) (2 ^ 31)); cbn [negb] in Hc;
[destruct (Z.eqb_spec (cg_cur s) 0); [assumption | discriminate Hc] | destruct (Z.eqb_spec (cg_cur s - 2 ^ 32 + 2 ^ 64) 0); [clear - Rcur e; lia | discriminate Hc]]. }
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_IT.
{ awr_clAX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20; prreg HS (18%bv : bv 5) Q18; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (10%bv : bv 5) Q10.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 80 <= a < sp0 \/ g + 88 <= a < g + 92) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna));
assert (HVK : cl_vkept (mrestrict (w_H W) mem) (mrestrict (w_H W) m2) s N)
by exact (cl_vkept_stretchA B LAWS ly S W mem md _ g s N _ (sp0 - 80) sp0 HAR HPerm ltac:(clear - Hceil Hslo HTS C1; lia) UN) end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : xcgif_at SEGS WFN_ADDR path hw pf (mrestrict (w_H W) _) g (cl_set_cur s (cg_cur s)))
by (eapply (xcgif_at_stretchXA B LAWS hw path pf ly S W mem md _ g s s N ((pf, FILE_BLOCK) :: rest) (cg_cur s) HAR HPerm HOK HT); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a) by (clear - Ha Hna Hceil Hslo HTS C1; lia); apply UN1; clear - Ha Hna Hceil Hslo HTS C1; lia).
assert (Hcok : YO07.s_cur gs = YO07.C_OK) by (rewrite <- HRC, Hcur0; reflexivity).
pose proof (HLIVE (or_introl Hcok)) as XL0.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (IT1 ly S W regs mem md ch g s N aM rest GPAL gs ly S W rg mm mdq 0 (cl_set_cur s (cg_cur s)) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [lia|]. split.
{ exact (cl_frame_of_region0 E _ sp0 regs _ _ HR0 Usp EEo). }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s N _ HOK) | exact HPerm].
+ clear - HEVF. lia.
+ cbn [cg_cur cl_set_cur]. exact Hcur0.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. cbn [sv_denot]. rewrite Usp. unfold sp0, spZ. reflexivity.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Hgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Htp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H W) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H W) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); reflexivity end).
+ rewrite Q20. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. exact E38.
+ rewrite Q18. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q21. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q22. rewrite ?E32u, ?E32, ?E38; lazymatch goal with |- _ = w64 (?sb + ?y / 8) => first [apply (cl_shx_eqX' _ y sb) | apply (cl_shx_eqX _ y sb)]; lia end.
+ rewrite Q23. apply bv_eq. vm_compute. reflexivity.
+
split; [| split; [| split; [| reflexivity]]].
* apply (asink_at_kept_mm SEGS K (mrestrict (w_H W) mem) _ md _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp Hpfceil Hceil Hslo HTS C1; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; pose proof Hgh_img as Hgi; unfold off_img in Hgi; clear - Hr Hgi Hceil Hslo HTS C1; lia ].
* exact (mle_start MT S MLAW).
* exact HLEN.
+ exact Hcok.
+ apply (proj2 (af_xlive_set_cur SEGS _ s N GPAL gs (cg_cur s))). exact (af_xlive_vkept _ _ s N GPAL gs HVK XL0).
Qed.
End k.
Theorem pb_cgif_closeX : tclose_specX SEGS K B MT XN (BASE + A_cgif_close) CTX WFN_ADDR pa_relro_lo pa_relro_hi.
Proof.
unfold tclose_specX. intros ly S W regs mem md ch g s N f path hw aM rest GPAL gs HPRE Hctx Hfr7 HROD H10 HT HWF Hf0 HPerm HREL HLEN HAM Hev Hlive HMOK.
assert (CX : cl_cxX B hw CTX path f ly S W regs mem md ch g s N rest).
{ split; [exact HPRE|]. split; [exact Hctx|]. split; [exact Hfr7|]. split; [exact HROD|]. split; [exact H10|].
split; [exact HT|]. split; [exact HWF|]. split; [exact HPerm|]. split; [exact Hev | exact Hlive]. }
assert (XE : cl_xent f K MT XN ly S W mem md s N aM GPAL gs) by (split; [exact Hf0 | split; [exact HREL | split; [exact HLEN | split; [exact HAM | exact HMOK]]]]).
assert (Rhw : 0 <= hw < 2 ^ 64) by (pose proof (obj_at_nth SEGS _ _ _ _ 11 (56, 8%N) hw (proj1 HT) eq_refl eq_refl) as [_ R]; cbn in R; lia).
assert (FR0 : CL_FR_stmtX B hw CTX path f K MT XN 0) by (apply cl_FR0X; assumption).
assert (CLB : CL_B_stmtX B hw CTX path f K MT XN)
by (apply (cl_BX_of_FR0 B LAWS TL hw CTX path f K AIL MT MLAW XN HXM AFM rctrace HUrc (RAWCLOSEX hw Rhw) ra_fc1 ra_fc2 AFCLOSE HUfc1 HUfc2 FR0)).
assert (IT1 : CL_IT1_stmtX B hw CTX path f K MT XN) by (apply cl_IT1X with (CTXfl := CTXfl); assumption).
eapply SRr_mono; [exact (cl_A_okX hw path f CLB IT1 ly S W regs mem md ch g s N aM rest GPAL gs CX XE)|].
intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ & HP & HK). unfold apost_base.
exists ly', S', regs', mem', md'. split; [reflexivity|]. split; [| split; [exact HP | exact HK]].
exact HJ.
Qed.
End i.
End h.
End c.
