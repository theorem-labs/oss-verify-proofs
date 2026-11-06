(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YCcz YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCrs YCru YCro YCrb YChy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac fs_rwF0 HS E88 Hp :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 88%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_set_region trbsegs Ex ssx msx i r (set_window r 0 8) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow trbsegs Ex _ r 0 8 (st_ok_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YQ0b.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E88, unsigned_lit_small by (unfold SB; lia);
intros o Ho; apply (apresent_writable trbsegs); unfold shadow_addr in Hp; rewrite <- SB_SHADOW_OFF in Hp;
apply (proj1 (Hp o ltac:(clear - Ho; lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac add_flag_regionRF HS AG E87 Hp HFLrng HFLown HnoF HnoD :=
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trbsegs Ev _ _ (YQ0b.mkRegion (Some 87%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E87, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trbsegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoF fl); [lia | exact HFLown] | apply (HnoD fl); [lia | exact HFLown] | match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac wrangeRF AG fpos F EFA EFL Hown :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; lia
| left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
| left; right; right; right; eexists; eexists; split; [right; exact Hown | left; unfold in_zr; cbn [fst snd]; rewrite ?EFA; lia]
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeRF" ]
| ]);
destruct Hin.
Lemma rf_EPI_aux : True -> rf_from B ss_EPI (INV_EPI B).
Proof.
intros _. rf_prelude.
destruct HINV as (Hkk & res & cur2 & img & fmt & E400 & E390 & E391 & E392 & Hcur2 & HRES).
assert (HBb3 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly3 S3)).
{ intros b m Hb. destruct HRES as [(_ & P & _) | [(_ & P) | (_ & _ & _ & P & _)]];
(eapply Permutation_in; [apply Permutation_sym; exact P|]); [exact Hb | exact Hb | right; exact Hb]. }
destruct (FFL _ _ _ _ _ 0 fpos (proj1 HJ3) Hfin0) as (HFLpres' & HFLown' & HFLrng'). rewrite ?EFL3 in HFLpres'. rewrite ?EFL3 in HFLown'. rewrite ?EFL3 in HFLrng'. fold FL in HFLpres', HFLown', HFLrng'.
assert (HnoF : forall a, F <= a < F + 64 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HF0pres3 a Ha))).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR3 Hfin3) as (_ & _ & HFpres3 & HFSpres3). rewrite !EFA3 in HFpres3, HFSpres3.
assert (HnoD : forall a, dst <= a < dst + 12 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a ltac:(clear - Ha Hdst1 Hdst2; lia)))).
assert (HFLB : forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> b + i <> FL).
{ intros b m i Hb Hi Heq. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3 (HBb3 b m Hb)) as (_ & _ & _ & _ & Hbp & _).
apply (proj2 (Hbp (b + i) ltac:(clear - Hi; lia))). rewrite Heq. exact HFLown'. }
assert (HFLF : forall c p a, In (c, p) (frames Sc) -> (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> a <> FL).
{ intros c p a Hcp Ha Heq. destruct (al_frames _ _ LAWS _ _ _ _ _ c p HAR3 ltac:(rewrite Hfrs3; right; exact Hcp)) as (_ & _ & Hp1 & Hp2). rewrite !EFA3 in Hp1, Hp2.
destruct Ha as [Ha | Ha]; unfold in_zr, frame_rng in Ha; cbn [fst snd] in Ha.
- apply (proj2 (Hp1 a Ha)). rewrite Heq. exact HFLown'.
- apply (proj2 (Hp2 (a - shadow_addr (frame_addr lyc c p)) ltac:(clear - Ha; lia))). replace (shadow_addr (frame_addr lyc c p) + (a - shadow_addr (frame_addr lyc c p))) with a by (clear; lia). rewrite Heq. exact HFLown'. }
fs_rwF0 HS E88 HF0Spres3.
add_flag_regionRF HS AG E87 HFLpres' HFLrng' HFLown' HnoF HnoD.
aj_run_flag_sh trbtbl_lib_ok HS HJ3; [clear; lia | wrangeRF AG fpos F EFA3 EFL3 Hown | flag0 E87 EFL3 |].
lazymatch goal with HFr : frame_of _ _ (mrestrict (w_H _) _) (mrestrict (w_H _) _) |- _ =>
unrunB HFr (fun a => spZ regs - TRRFC_STK <= a < spZ regs \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24 \/
((in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8)) \/ a = FL)) AG F UNx end.
destruct HFLrng' as (_ & HFL4096 & _ & HFLc).
pose proof (rfc_kept_stepE _ _ _ _ _ _ _ _ _ _ _ _ (fun a => (in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8)) \/ a = FL)
HKEPT HSEP UNx ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)
ltac:(intros a [Ha | ->]; [revert Ha; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64; fold F; unfold SB; clear - HFceil HF8hi C1; lia
| exact HFLc])
ltac:(intros b m i Hb Hi [Hx | Hx]; [exact (HFSB b m i Hb Hi Hx) | exact (HFLB b m i Hb Hi Hx)])
ltac:(intros c p a Hcp Ha [Hx | Hx]; [exact (HFSF c p a Hcp Ha Hx) | exact (HFLF c p a Hcp Ha Hx)])) as KEPTx.
clear UNx. clear_frames.
pose proof HJ3 as (HARx & _ & _ & _ & _ & Hfrsx & _).
assert (Hfrx : forall Sx, frames Sx = own ++ frames S -> frames Sx = frames Sc) by (intros Sx Hx; rewrite Hx, Hfrs; reflexivity).
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
rf_stream_words2 HS B10 E33 E34 Vp Vn. rf_stream_cur HS B10 390%nat E390 Vc.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
assert (HinX : In (cid, pos) (own ++ frames S)) by (apply in_app_iff; left; exact Hown).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Wx ?mx ?mdx _ =>
assert (HPX : forall a, dst + 12 <= a < dst + 22 -> apresent (w_H Wx) mx a)
by (intros a Ha; destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HARx ltac:(rewrite Hfrsx; exact HinX)) as (_ & _ & Hp & _);
apply (proj1 (Hp a ltac:(rewrite !EFA3; clear - Ha Hdst1 Hdst2; lia)))) end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msN) =>
assert (OBJ : (res = 2 ^ 64 - 1 \/ res = 1) -> 0 <= img < 2 ^ 64 -> 0 <= fmt < 2 ^ 32 ->
exists fattr fgen delay, obj_at trbsegs (mrestrict (w_H W3) (ms_mem msN)) dst LAY_RgbFrameConfig [img; fmt; fattr; fgen; delay]) end.
{ intros _ Rimg Rfmt.
rf_obj_atB HS B11 img ltac:(rewrite sv_denot_SOff0; exact E391) fmt ltac:(rewrite sv_denot_SOff0; exact E392) HPX OBJ0. exact OBJ0. }
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold rf_post.
cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_lyc x_Sc x_W x_memc x_mdc x_k x_regs x_Bb x_st x_dst x_N x_pdata x_nb x_cur x_cid x_pos x_ch x_fpos x_sp1 x_E0].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md' res' cur', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx, res, cur2 end end.
split.
{ rewrite Rra. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (AG 1%nat) by lia.
rewrite (EE 1%nat 1%bv eq_refl). rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
rewrite Hra. reflexivity. }
split; [cbn [ms_mem]; apply (ajournal_materialize trbsegs _ LAWS trb_segs_low); eapply (ajournal_mono_k trbsegs); [exact HJ3 | exact Hkk]|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
split; [exact (Hfrx _ Hfrsx)|].
split; [apply (jbud_mono Sc _ (kk - k)); [first [exact HJB | match goal with |- ?g => idtac "EPI-JBUD" g end] | clear - Hkk; lia]|].
split; [rewrite Ra0; evalE AG|].
destruct KEPTx as (K1 & K2 & K3).
split; [exact K1|]. split; [exact K2|]. split; [exact K3|].
split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [exact Hcur2|].
unfold rf_result. cbn [x_Bb x_dst x_N x_FP x_ly x_S x_STK x_sp0 x_own].
unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly3 S3).
destruct HRES as [(Hr & P & Hi0 & Hf0) | [(Hr & P) | (Hr & Hfmt & Rimg & P & Tk & Aw)]].
- left. split; [exact Hr|]. split; [exact P|]. subst img fmt. apply OBJ; [left; exact Hr | clear; lia | clear; lia].
- right. left. split; [exact Hr | exact P].
- right. right. split; [exact Hr|]. destruct (OBJ ltac:(right; exact Hr) Rimg ltac:(clear - Hfmt; lia)) as (fattr & fgen & delay & OBJ1).
exists img, fmt, fattr, fgen, delay. split; [exact Hfmt|]. split; [exact OBJ1|]. split; [exact P|]. split; [exact Tk|].
intros blc i Hin Hi. exact (Aw blc i _ Hin Hi).
Qed.
Lemma rf_EPI : rf_from B ss_EPI (INV_EPI B).
Proof. exact (rf_EPI_aux I). Qed.
End e.
End d.
