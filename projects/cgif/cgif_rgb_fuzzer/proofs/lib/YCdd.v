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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI1h YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCfs YCfu YCe1 YCfq YCe4 YCe0 YCgv YCdq YCdu YCdf YCds YCdp YCdm YCde.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma af_SM : AF_RET_stmt B -> AF_SM_stmt B.
Proof.
intros PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 f CX HEB HPB Hn HS SHOK.
af_B_names LAWS CX HEB HPB Hn.
destruct Hih as [Hih | Hih]; rewrite Hih in HS, SHOK, Hn; [change (Z.to_nat 1) with 1%nat in Hn | change (Z.to_nat 2) with 2%nat in Hn];
[change (33 + Z.to_nat 1)%nat with 34%nat in HS, SHOK | change (33 + Z.to_nat 2)%nat with 35%nat in HS, SHOK]; cbn [Z.mul Pos.mul] in HS.
-
assert (B34 : bv_unsigned (ew E 34) = fr_ptr f) by (rewrite E34, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 1 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ) Hfb) as (_ & _ & _ & _ & HhP & _).
change (req_size FRAME_SIZE) with 40 in HhP.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 0 rs got_region) in
pose proof (ast_ok_set_region trbsegs Ex ssx msx 0 r (set_window r 24 26) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 24 26 (st_ok_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; rewrite B34;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable trbsegs); apply (fun Hq => proj1 (HhP (fr_ptr f + o) Hq)); clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_RET; [awr_b Usp E32u Hing HTS 34%nat B34 Hfb Hfq |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => ZsA g sp0 a \/ (fr_ptr f + 24 <= a < fr_ptr f + 26)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u, ?B34 in Hrr; unfold ZsA; clear - Hrr; lia |]);
destruct Hin)) as UN.
cbv beta in UN. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rh := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rh HS ltac:(vm_compute; reflexivity)) as HRh;
pose proof (st_ok_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRh, HR1, HRg end.
lazymatch type of HRh with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk 24 (CVal 2 ?e)] =>
pose proof (field_of_region_any Ex _ 34 (fr_ptr f) cs lo hi wlo whi 24 2 e HRh ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact B34) ltac:(cbn; tauto) ltac:(cbn; clear; lia)) as Vd;
set (d' := bv_unsigned (sv_denot Ex e) mod 2 ^ (8 * Z.of_N 2)) in Vd end end.
assert (Rd' : 0 <= d' < 2 ^ (8 * Z.of_N 2)) by (subst d'; apply Z.mod_pos_bound; clear; cbn; lia).
set (f' := set_fr_delay f d').
assert (Hf' : frame_vals f' = list_set (frame_vals f) 4 d') by reflexivity.
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc end.
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 (upd_frame s 1 f') CX) end.
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
- rewrite (tcgif_vals_upd_frame s 1 f f' Hfne eq_refl).
lazymatch goal with |- obj_at _ _ _ _ (tcgif_vals ?sx) => rewrite <- (cl_set_cur_same sx) end.
apply (obj_cgif_setcur _ _ g s (cg_cur s) (proj1 HT)).
+ intros ii Hii Hnc. etransitivity; [| exact (HGK ii Hii Hnc)]. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii HZg; lia | unfold ZsA; clear - Hii Hnc HZg Dgh; lia].
+ exact Vc.
+ exact Rcur.
- rewrite traw_vals_upd_frame. change (cg_raw (upd_frame s 1 f')) with (cg_raw s).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hsr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hnz].
assert (Hinr2 : In (cg_raw s, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
pose proof (sep_blocks trbsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr2 Hfb ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as Drh.
unfold zdisjoint in Drh. cbn [fst snd] in Drh. change (req_size RAW_SIZE) with 48 in Drh. change (req_size FRAME_SIZE) with 40 in Drh.
apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Drh Hii; lia].
- apply (tframes_at_upd _ _ s 1 (Some f) f' Hsf Hfne).
+ change (fr_ptr f') with (fr_ptr f). rewrite Hf'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs _ mF (fr_ptr f) LAY_Frame 40 (frame_vals f) (list_set (frame_vals f) 4 d') [4]%nat [(24, 26)] (Hsf f HfIn) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros jj Hjj Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trbsegs). destruct (HZf f jj HfIn Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hjj Hw Hnz; lia]. }
{ intros j' fj v' Hj' Hfj Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hfj. injection Hfj as <-. cbn in Hv'. injection Hv' as <-.
split; [exact Vd | exact Rd']. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ intros j x Hjx Hne jj Hjj.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s N _ _ _ _ _ HAR HPerm Hlen Hjx Hfne Hne) as Dff.
assert (Hxi : In (Some x) (cg_frames s)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trbsegs). destruct (HZf x jj Hxi Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Dff Hjj; lia]. }
split.
{ apply (af_obj_ok_upd_frame s s N 1 f f'); [| exact Hfne |].
- split; [exact HWF|]. repeat split.
- apply (frame_wf_fields (cg_attr s) f f'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))) f HfIn) | reflexivity | reflexivity]. }
rewrite (cgif_blocks_upd_frame g s N 1 f f' Hfne (frame_blocks_set_fr_delay N f d')). split; [exact HPerm | intros b Hb; left; exact Hb]. }
{ change EV_ADDFRAME with (12 + (8 + EV_RAWADD)). change (12 + (8 + EV_RAWADD)) with 47. clear. lia. }
{ unfold af_regs_ret. change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite Usp; unfold w64; f_equal; clear; lia
| rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp
| rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| exact E32 | exact E38 | rewrite E32u; reflexivity
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]). }
-
assert (B35 : bv_unsigned (ew E 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 2 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ) Hfb) as (_ & _ & _ & _ & HhP & _).
change (req_size FRAME_SIZE) with 40 in HhP.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let r := eval vm_compute in (nth 0 rs got_region) in
pose proof (ast_ok_set_region trbsegs Ex ssx msx 0 r (set_window r 24 26) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 24 26 (st_ok_region_nth Ex ssx msx 0 r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; rewrite B35;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable trbsegs); apply (fun Hq => proj1 (HhP (fr_ptr f + o) Hq)); clear - Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_RET; [awr_b Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => ZsA g sp0 a \/ (fr_ptr f + 24 <= a < fr_ptr f + 26)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?Usp, ?E32u, ?B35 in Hrr; unfold ZsA; clear - Hrr; lia |]);
destruct Hin)) as UN.
cbv beta in UN. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rh := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rh HS ltac:(vm_compute; reflexivity)) as HRh;
pose proof (st_ok_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRh, HR1, HRg end.
lazymatch type of HRh with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 35%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk 24 (CVal 2 ?e)] =>
pose proof (field_of_region_any Ex _ 35 (fr_ptr f) cs lo hi wlo whi 24 2 e HRh ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact B35) ltac:(cbn; tauto) ltac:(cbn; clear; lia)) as Vd;
set (d' := bv_unsigned (sv_denot Ex e) mod 2 ^ (8 * Z.of_N 2)) in Vd end end.
assert (Rd' : 0 <= d' < 2 ^ (8 * Z.of_N 2)) by (subst d'; apply Z.mod_pos_bound; clear; cbn; lia).
set (f' := set_fr_delay f d').
assert (Hf' : frame_vals f' = list_set (frame_vals f) 4 d') by reflexivity.
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SOff 37 0) (cg_cur s) HRg ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; clear; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc end.
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly S W rg mm mdq 0 (upd_frame s 2 f') CX) end.
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
- rewrite (tcgif_vals_upd_frame s 2 f f' Hfne eq_refl).
lazymatch goal with |- obj_at _ _ _ _ (tcgif_vals ?sx) => rewrite <- (cl_set_cur_same sx) end.
apply (obj_cgif_setcur _ _ g s (cg_cur s) (proj1 HT)).
+ intros ii Hii Hnc. etransitivity; [| exact (HGK ii Hii Hnc)]. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii HZg; lia | unfold ZsA; clear - Hii Hnc HZg Dgh; lia].
+ exact Vc.
+ exact Rcur.
- rewrite traw_vals_upd_frame. change (cg_raw (upd_frame s 2 f')) with (cg_raw s).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hsr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hnz].
assert (Hinr2 : In (cg_raw s, RAW_SIZE) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm|]; right; left; reflexivity).
pose proof (sep_blocks trbsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr2 Hfb ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as Drh.
unfold zdisjoint in Drh. cbn [fst snd] in Drh. change (req_size RAW_SIZE) with 48 in Drh. change (req_size FRAME_SIZE) with 40 in Drh.
apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Drh Hii; lia].
- apply (tframes_at_upd _ _ s 2 (Some f) f' Hsf Hfne).
+ change (fr_ptr f') with (fr_ptr f). rewrite Hf'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs _ mF (fr_ptr f) LAY_Frame 40 (frame_vals f) (list_set (frame_vals f) 4 d') [4]%nat [(24, 26)] (Hsf f HfIn) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros jj Hjj Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trbsegs). destruct (HZf f jj HfIn Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hjj Hw Hnz; lia]. }
{ intros j' fj v' Hj' Hfj Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hfj. injection Hfj as <-. cbn in Hv'. injection Hv' as <-.
split; [exact Vd | exact Rd']. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ intros j x Hjx Hne jj Hjj.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s N _ _ _ _ _ HAR HPerm Hlen Hjx Hfne Hne) as Dff.
assert (Hxi : In (Some x) (cg_frames s)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trbsegs). destruct (HZf x jj Hxi Hjj) as [Hb Hnz]. apply UN; [exact Hb | unfold ZsA in Hnz |- *; clear - Hnz Dff Hjj; lia]. }
split.
{ apply (af_obj_ok_upd_frame s s N 2 f f'); [| exact Hfne |].
- split; [exact HWF|]. repeat split.
- apply (frame_wf_fields (cg_attr s) f f'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF)))))) f HfIn) | reflexivity | reflexivity]. }
rewrite (cgif_blocks_upd_frame g s N 2 f f' Hfne (frame_blocks_set_fr_delay N f d')). split; [exact HPerm | intros b Hb; left; exact Hb]. }
{ change EV_ADDFRAME with (12 + (8 + EV_RAWADD)). change (12 + (8 + EV_RAWADD)) with 47. clear. lia. }
{ unfold af_regs_ret. change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite Usp; unfold w64; f_equal; clear; lia
| rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp
| rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| exact E32 | exact E38 | rewrite E32u; reflexivity
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]). }
Qed.
End d.
End c.
