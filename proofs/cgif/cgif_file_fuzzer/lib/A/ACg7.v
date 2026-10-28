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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgv ACgu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo ACg8 ACga.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section h.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis HXNUM : af_xnums MT XN.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_SMX : AF_RET_stmtX K MT XN B -> AF_SM_stmtX K MT XN B.
Proof.
intros PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 f GPAL IMG LPAL gs gsF HD CX HEB HPB Hn HS SHOK XSM.
pose proof (af_xf_in _ XSM) as XSMm. clear XSM.
af_B_namesX LAWS CX HEB HPB Hn.
assert (XREL1 : af_xrel K (mrestrict (w_H W) (ms_mem ms1)) md1 s N img lpa fattr nlp GPAL IMG LPAL gs)
by (exact (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF (conj XREL0 (conj XIMG0 (conj XIMGL XLPAL0))))).
pose proof (af_liftN B LAWS ly S W regs mem md ch g s N _ _ _ _ _ _ _ HPRE HJ) as HJb. clear HJ. rename HJb into HJ. clear XIMGL.
destruct Hih as [Hih | Hih]; rewrite Hih in HS, SHOK, Hn; [change (Z.to_nat 1) with 1%nat in Hn | change (Z.to_nat 2) with 2%nat in Hn];
[change (33 + Z.to_nat 1)%nat with 34%nat in HS, SHOK | change (33 + Z.to_nat 2)%nat with 35%nat in HS, SHOK]; cbn [Z.mul Pos.mul] in HS.
-
assert (B34 : bv_unsigned (ew E 34) = fr_ptr f) by (rewrite E34, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 1 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ) Hfb) as (_ & _ & _ & _ & HhP & _).
change (req_size FRAME_SIZE) with 40 in HhP.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 0 rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx 0 r (set_window r 24 26) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r 24 26 (st_ok_pi_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite B34;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (fun Hq => proj1 (HhP (fr_ptr f + o) Hq)); clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 0 rs got_regionP) in
pose proof (ast_ok_set_region SEGS Ex ssx msx 0 r (set_window r 24 26) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r 24 26 (st_ok_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite B34;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (fun Hq => proj1 (HhP (fr_ptr f + o) Hq)); clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_RET; [awr_bX Usp E32u Hing HTS 34%nat B34 Hfb Hfq |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => ZsA g sp0 a \/ (fr_ptr f + 24 <= a < fr_ptr f + 26)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u, ?B34 in Hrr; unfold ZsA; clear - Hrr; lia |]);
destruct Hin)) as UN.
cbv beta in UN. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rh := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rh HS ltac:(vm_compute; reflexivity)) as HRh;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_pi_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRh, HR1, HRg | st_ok _ ?Ex ?ssx ?msx =>
let rh := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rh HS ltac:(vm_compute; reflexivity)) as HRh;
pose proof (st_ok_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRh, HR1, HRg  end.
lazymatch type of HRh with region_ok _ ?Ex _ (YP09.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 24 (CVal 2 ?e)] =>
pose proof (field_of_region_any Ex _ 34 (fr_ptr f) cs lo hi wlo whi 24 2 e HRh ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact B34) ltac:(cbn; tauto) ltac:(cbn; clear; lia)) as Vd;
set (d' := bv_unsigned (sv_denot Ex e) mod 2 ^ (8 * Z.of_N 2)) in Vd end end.
assert (Rd' : 0 <= d' < 2 ^ (8 * Z.of_N 2)) by (subst d'; apply Z.mod_pos_bound; clear; cbn; lia).
set (f' := set_fr_delay f d').
assert (Hf' : frame_vals f' = list_set (frame_vals f) 4 d') by reflexivity.
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
destruct (af_xfoot_unz B LAWS ly S W mem md g s N (@nil (Z * Z)) _ ly sp0 (fun a => ZsA g sp0 a \/ (fr_ptr f + 24 <= a < fr_ptr f + 26)) HAR HPerm Hstk
ltac:(intros a [[Ha | Ha] | Ha];
[ left; clear - Ha HTS; lia
| right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]
| right; exists (fr_ptr f), FRAME_SIZE; split; [apply in_app_iff; left; exact (af_wblocks_frame g s f HfIn) | change (req_size FRAME_SIZE) with 40; clear - Ha; lia] ])) as [XZb XZi].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdq) _ =>
pose proof (af_xrel_unz B K AIL (w_H W) (ms_mem ms1) _ md1 mdq s N img lpa fattr nlp GPAL IMG LPAL gs _ _ UN XZb XZi
ltac:(right; apply in_app_iff; right; exact Hpfr) (or_introl eq_refl)
ltac:(intros Hz; right; apply in_app_iff; left; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity])
HWF eq_refl eq_refl XREL1) as XREL2 end.
clear XZb XZi.
assert (Xd : d' = delay + fr_delay f).
{ destruct (af_xf_out _ XSMm) as (XLV & Xq & Xfd & _).
pose proof (proj1 (cgif_relA_split SEGS K _ _ s pf N GPAL gs) (proj1 XREL2)) as (_ & _ & XL).
pose proof (proj2 (proj1 (af_xlive_iff SEGS _ s N GPAL gs) (XL XLV)) (Z.to_nat (cg_ihead s)) ltac:(rewrite Hih; cbv; lia) I) as XR.
rewrite Xq in XR. rewrite Hih in XR. change (Z.to_nat 1) with 1%nat in XR. rewrite Hn in XR. cbn [oframe_relbA] in XR. destruct XR as (_ & _ & XRd & _).
pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdl]. cbn [snd] in Rdl. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rdl.
pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) (fr_delay f) (proj2 HSD f HfIn) eq_refl eq_refl) as [_ Rfd]. cbn [snd] in Rfd. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rfd.
subst d'. lazymatch goal with |- bv_unsigned (sv_denot ?Ex ?e) mod _ = _ => change (bv_unsigned (sv_denot Ex e)) with (U Ex e) end.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext.
lazymatch goal with |- context [U ?Ex (SOff 72 0)] =>
rewrite (U_atom Ex 72 (fr_delay f) ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E72)), (U_atom Ex 51 delay ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E51)) by (clear - Rdl Rfd; lia) end.
change (Z.of_N 16) with 16. change (2 ^ (8 * Z.of_N 2)) with 65536. change (2 ^ 16) with 65536.
rewrite (Z.mod_small delay 65536) by (clear - Rdl; lia). rewrite zcanon_id by (unfold M64; clear - Rdl Rfd; lia).
rewrite Z.mod_small by (rewrite XRd; clear - Xfd Rdl Rfd XRd; lia). clear; lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 (upd_frame s 1 f') GPAL IMG LPAL gs gsF CX) end.
{
split; [exact HJ|]. split; [clear; lia|].
split; [lazymatch type of HR1 with region_ok _ ?Ex _ _ =>
let Uspx := fresh "Uspx" in let EEx := fresh "EEx" in
assert (EEx : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Ex n = getr regs rr)
by (let n := fresh "n" in let rr := fresh "rr" in let Hn := fresh "Hn" in intros n rr Hn;
pose proof (bv_unsigned_in_range 5 rr); change (bv_modulus 5) with 32 in *;
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact (EEo n rr Hn));
assert (Uspx : bv_unsigned (ew Ex 2) = sp0) by (rewrite (EEx 2%nat 2%bv eq_refl); rewrite <- (EEo 2%nat 2%bv eq_refl); exact Usp);
exact (af_frame_of_region Ex _ _ _ _ _ HR1 Uspx EEx) end|].
split.
{ pose proof HSD as [Hsr Hsf]. split; [|split].
- rewrite (xcgif_vals_upd_frame path hw pf s 1 f f' Hfne eq_refl).
lazymatch goal with |- obj_at _ _ _ _ (xcgif_vals path hw pf ?sx) => rewrite <- (cl_set_cur_same sx) end.
apply (obj_cgif_setcurX SEGS path hw pf _ _ g s (cg_cur s) (proj1 HT)).
+ intros ii Hii Hnc. etransitivity; [| exact (HGK ii Hii Hnc)]. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii HZg; lia | unfold ZsA; clear - Hii Hnc HZg Dgh; lia].
+ exact Vc.
+ exact Rcur.
- rewrite traw_vals_upd_frame. change (cg_raw (upd_frame s 1 f')) with (cg_raw s).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hsr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hnz].
assert (Hinr2 : In (cg_raw s, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr2 Hfb ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as Drh.
unfold zdisjoint in Drh. cbn [fst snd] in Drh. change (req_size RAW_SIZE) with 48 in Drh. change (req_size FRAME_SIZE) with 40 in Drh.
apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Drh Hii; lia].
- apply (tframes_at_upd _ _ s 1 (Some f) f' Hsf Hfne).
+ change (fr_ptr f') with (fr_ptr f). rewrite Hf'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS _ mF (fr_ptr f) LAY_Frame 40 (frame_vals f) (list_set (frame_vals f) 4 d') [4]%nat [(24, 26)] (Hsf f HfIn) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros jj Hjj Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview SEGS). destruct (HZf f jj HfIn Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hjj Hw Hnz; lia]. }
{ intros j' fj v' Hj' Hfj Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hfj. injection Hfj as <-. cbn in Hv'. injection Hv' as <-.
split; [exact Vd | exact Rd']. }
{ intros j' Hj'. rewrite YI5v.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ intros j x Hjx Hne jj Hjj.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s N _ _ _ _ _ HAR HPerm Hlen Hjx Hfne Hne) as Dff.
assert (Hxi : In (Some x) (cg_frames s)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview SEGS). destruct (HZf x jj Hxi Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Dff Hjj; lia]. }
split.
{ apply (af_obj_ok_upd_frame s s N 1 f f'); [| exact Hfne |].
- split; [exact HWF|]. repeat split.
- apply (frame_wf_fields (cg_attr s) f f'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))) f HfIn) | reflexivity | reflexivity]. }
rewrite (cgif_blocks_upd_frame g s N 1 f f' Hfne (frame_blocks_set_fr_delay N f d')). split; [exact HPerm | intros b Hb; left; exact Hb]. }
{ change EV_ADDFRAME with (12 + (8 + EV_RAWADD)). change (12 + (8 + EV_RAWADD)) with 47. clear. lia. }
{ unfold af_regs_ret. change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite Usp; unfold w64; f_equal; clear; lia
| rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp
| rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| exact E32 | exact E38 | rewrite E32u; reflexivity
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]). }
{
destruct (af_xsm_ret K _ _ s N 1%nat f d' delay GPAL gs gsF HD (proj1 XREL2) HWF Hih ltac:(clear; lia) Hn (af_xf_out _ XSMm) Xd) as [XA XB].
exact (conj XA (conj XB (af_xmtr00 MT XN MLAW S N HXNUM HN1))). }
-
assert (B35 : bv_unsigned (ew E 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 2 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ) Hfb) as (_ & _ & _ & _ & HhP & _).
change (req_size FRAME_SIZE) with 40 in HhP.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 0 rs got_regionP) in
pose proof (ast_ok_pi_set_region Ex ssx msx 0 r (set_window r 24 26) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r 24 26 (st_ok_pi_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite B35;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (fun Hq => proj1 (HhP (fr_ptr f + o) Hq)); clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 0 rs got_regionP) in
pose proof (ast_ok_set_region SEGS Ex ssx msx 0 r (set_window r 24 26) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow SEGS Ex _ r 24 26 (st_ok_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite B35;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (fun Hq => proj1 (HhP (fr_ptr f + o) Hq)); clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_RET; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => ZsA g sp0 a \/ (fr_ptr f + 24 <= a < fr_ptr f + 26)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u, ?B35 in Hrr; unfold ZsA; clear - Hrr; lia |]);
destruct Hin)) as UN.
cbv beta in UN. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rh := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rh HS ltac:(vm_compute; reflexivity)) as HRh;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_pi_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRh, HR1, HRg | st_ok _ ?Ex ?ssx ?msx =>
let rh := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rh HS ltac:(vm_compute; reflexivity)) as HRh;
pose proof (st_ok_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRh, HR1, HRg  end.
lazymatch type of HRh with region_ok _ ?Ex _ (YP09.mkRegion (Some 35%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 24 (CVal 2 ?e)] =>
pose proof (field_of_region_any Ex _ 35 (fr_ptr f) cs lo hi wlo whi 24 2 e HRh ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact B35) ltac:(cbn; tauto) ltac:(cbn; clear; lia)) as Vd;
set (d' := bv_unsigned (sv_denot Ex e) mod 2 ^ (8 * Z.of_N 2)) in Vd end end.
assert (Rd' : 0 <= d' < 2 ^ (8 * Z.of_N 2)) by (subst d'; apply Z.mod_pos_bound; clear; cbn; lia).
set (f' := set_fr_delay f d').
assert (Hf' : frame_vals f' = list_set (frame_vals f) 4 d') by reflexivity.
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
destruct (af_xfoot_unz B LAWS ly S W mem md g s N (@nil (Z * Z)) _ ly sp0 (fun a => ZsA g sp0 a \/ (fr_ptr f + 24 <= a < fr_ptr f + 26)) HAR HPerm Hstk
ltac:(intros a [[Ha | Ha] | Ha];
[ left; clear - Ha HTS; lia
| right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]
| right; exists (fr_ptr f), FRAME_SIZE; split; [apply in_app_iff; left; exact (af_wblocks_frame g s f HfIn) | change (req_size FRAME_SIZE) with 40; clear - Ha; lia] ])) as [XZb XZi].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ _ _) ?mdq) _ =>
pose proof (af_xrel_unz B K AIL (w_H W) (ms_mem ms1) _ md1 mdq s N img lpa fattr nlp GPAL IMG LPAL gs _ _ UN XZb XZi
ltac:(right; apply in_app_iff; right; exact Hpfr) (or_introl eq_refl)
ltac:(intros Hz; right; apply in_app_iff; left; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity])
HWF eq_refl eq_refl XREL1) as XREL2 end.
clear XZb XZi.
assert (Xd : d' = delay + fr_delay f).
{ destruct (af_xf_out _ XSMm) as (XLV & Xq & Xfd & _).
pose proof (proj1 (cgif_relA_split SEGS K _ _ s pf N GPAL gs) (proj1 XREL2)) as (_ & _ & XL).
pose proof (proj2 (proj1 (af_xlive_iff SEGS _ s N GPAL gs) (XL XLV)) (Z.to_nat (cg_ihead s)) ltac:(rewrite Hih; cbv; lia) I) as XR.
rewrite Xq in XR. rewrite Hih in XR. change (Z.to_nat 2) with 2%nat in XR. rewrite Hn in XR. cbn [oframe_relbA] in XR. destruct XR as (_ & _ & XRd & _).
pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdl]. cbn [snd] in Rdl. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rdl.
pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) (fr_delay f) (proj2 HSD f HfIn) eq_refl eq_refl) as [_ Rfd]. cbn [snd] in Rfd. change (2 ^ (8 * Z.of_N 2)) with 65536 in Rfd.
subst d'. lazymatch goal with |- bv_unsigned (sv_denot ?Ex ?e) mod _ = _ => change (bv_unsigned (sv_denot Ex e)) with (U Ex e) end.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext.
lazymatch goal with |- context [U ?Ex (SOff 72 0)] =>
rewrite (U_atom Ex 72 (fr_delay f) ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E72)), (U_atom Ex 51 delay ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E51)) by (clear - Rdl Rfd; lia) end.
change (Z.of_N 16) with 16. change (2 ^ (8 * Z.of_N 2)) with 65536. change (2 ^ 16) with 65536.
rewrite (Z.mod_small delay 65536) by (clear - Rdl; lia). rewrite zcanon_id by (unfold M64; clear - Rdl Rfd; lia).
rewrite Z.mod_small by (rewrite XRd; clear - Xfd Rdl Rfd XRd; lia). clear; lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 (upd_frame s 2 f') GPAL IMG LPAL gs gsF CX) end.
{
split; [exact HJ|]. split; [clear; lia|].
split; [lazymatch type of HR1 with region_ok _ ?Ex _ _ =>
let Uspx := fresh "Uspx" in let EEx := fresh "EEx" in
assert (EEx : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Ex n = getr regs rr)
by (let n := fresh "n" in let rr := fresh "rr" in let Hn := fresh "Hn" in intros n rr Hn;
pose proof (bv_unsigned_in_range 5 rr); change (bv_modulus 5) with 32 in *;
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact (EEo n rr Hn));
assert (Uspx : bv_unsigned (ew Ex 2) = sp0) by (rewrite (EEx 2%nat 2%bv eq_refl); rewrite <- (EEo 2%nat 2%bv eq_refl); exact Usp);
exact (af_frame_of_region Ex _ _ _ _ _ HR1 Uspx EEx) end|].
split.
{ pose proof HSD as [Hsr Hsf]. split; [|split].
- rewrite (xcgif_vals_upd_frame path hw pf s 2 f f' Hfne eq_refl).
lazymatch goal with |- obj_at _ _ _ _ (xcgif_vals path hw pf ?sx) => rewrite <- (cl_set_cur_same sx) end.
apply (obj_cgif_setcurX SEGS path hw pf _ _ g s (cg_cur s) (proj1 HT)).
+ intros ii Hii Hnc. etransitivity; [| exact (HGK ii Hii Hnc)]. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii HZg; lia | unfold ZsA; clear - Hii Hnc HZg Dgh; lia].
+ exact Vc.
+ exact Rcur.
- rewrite traw_vals_upd_frame. change (cg_raw (upd_frame s 2 f')) with (cg_raw s).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hsr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hnz].
assert (Hinr2 : In (cg_raw s, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr2 Hfb ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as Drh.
unfold zdisjoint in Drh. cbn [fst snd] in Drh. change (req_size RAW_SIZE) with 48 in Drh. change (req_size FRAME_SIZE) with 40 in Drh.
apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Drh Hii; lia].
- apply (tframes_at_upd _ _ s 2 (Some f) f' Hsf Hfne).
+ change (fr_ptr f') with (fr_ptr f). rewrite Hf'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS _ mF (fr_ptr f) LAY_Frame 40 (frame_vals f) (list_set (frame_vals f) 4 d') [4]%nat [(24, 26)] (Hsf f HfIn) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros jj Hjj Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview SEGS). destruct (HZf f jj HfIn Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hjj Hw Hnz; lia]. }
{ intros j' fj v' Hj' Hfj Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hfj. injection Hfj as <-. cbn in Hv'. injection Hv' as <-.
split; [exact Vd | exact Rd']. }
{ intros j' Hj'. rewrite YI5v.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ intros j x Hjx Hne jj Hjj.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s N _ _ _ _ _ HAR HPerm Hlen Hjx Hfne Hne) as Dff.
assert (Hxi : In (Some x) (cg_frames s)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview SEGS). destruct (HZf x jj Hxi Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Dff Hjj; lia]. }
split.
{ apply (af_obj_ok_upd_frame s s N 2 f f'); [| exact Hfne |].
- split; [exact HWF|]. repeat split.
- apply (frame_wf_fields (cg_attr s) f f'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))) f HfIn) | reflexivity | reflexivity]. }
rewrite (cgif_blocks_upd_frame g s N 2 f f' Hfne (frame_blocks_set_fr_delay N f d')). split; [exact HPerm | intros b Hb; left; exact Hb]. }
{ change EV_ADDFRAME with (12 + (8 + EV_RAWADD)). change (12 + (8 + EV_RAWADD)) with 47. clear. lia. }
{ unfold af_regs_ret. change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite Usp; unfold w64; f_equal; clear; lia
| rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp
| rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| exact E32 | exact E38 | rewrite E32u; reflexivity
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]). }
{
destruct (af_xsm_ret K _ _ s N 2%nat f d' delay GPAL gs gsF HD (proj1 XREL2) HWF Hih ltac:(clear; lia) Hn (af_xf_out _ XSMm) Xd) as [XA XB].
exact (conj XA (conj XB (af_xmtr00 MT XN MLAW S N HXNUM HN1))). }
Qed.
End h.
End d.
End c.
