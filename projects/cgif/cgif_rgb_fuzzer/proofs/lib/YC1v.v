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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20 YI1k YI16 YI1h.
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
Lemma tcgif_vals_flush_upd : forall s i gen rc f,
nth_error (cg_frames s) i = Some (Some f) -> tcgif_vals (flush_upd s i gen rc) = tcgif_vals s.
Proof.
intros s i gen rc f Hf. unfold tcgif_vals. rewrite (cg_frames_flush_upd s i gen rc f Hf). cbn -[list_set nth].
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some (set_fr_gen f gen))) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
rewrite (nth_error_nth _ _ None Hf). reflexivity.
- rewrite nth_list_set_other by (clear - Hne; lia). reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma traw_vals_flush_upd : forall g s i gen rc, traw_vals g (flush_upd s i gen rc) = list_set (traw_vals g s) 8 rc.
Proof. intros. reflexivity. Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Ltac add_flag_regionFL HS AG E87 Hp HFLrng HFLown HnoG HnoC HnoF :=
let Qceil := match goal with H : alloc_ceiling <= ly_stk_lo _ |- _ => H end in
let Qslo := match goal with H : ly_stk_lo _ + _ <= spZ _ |- _ => H end in
let QC1 := match goal with H : _ <= alloc_ceiling <= _ |- _ => H end in
let QC3 := match goal with H : kHighMemBeg = _ |- _ => H end in
let QFFS := match goal with H : TFLUSH_STK = _ |- _ => H end in
let QFq := match goal with H : ?Fr = 32 * (?Fr / 32) |- _ => H end in
let QF8 := match goal with H : ?Fr / 8 = 4 * (?Fr / 32) |- _ => H end in
let QFceil := match goal with H : ?Fr + 256 <= alloc_ceiling |- _ => H | _ => QFq end in
let QF8lo := match goal with H : 512 <= ?Fr / 8 |- _ => H | _ => QFq end in
let QF8hi := match goal with H : ?Fr / 8 < 17592186044416 |- _ => H | _ => QFq end in
let Qsp1 := match goal with H : spZ _ - 400 <= _ <= spZ _ - 384 |- _ => H | _ => QFq end in
lazymatch type of HS with st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region trasegs Ev _ _ (YQ0b.mkRegion (Some 87%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E87, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable trasegs); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [clear - HFLrng Qceil Qslo Qsp1 QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi; zone_lia |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoG fl); [lia | exact HFLown] | apply (HnoC fl); [lia | exact HFLown] | apply (HnoF fl); [lia | exact HFLown]
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac wrangeFL AG fpos F EFA EFL Hcur3 :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
first [ exfalso; clear - Hr; lia
| right; clear - Hr; lia
| left; left; lazymatch goal with Hsp1 : _ <= ?sp1 <= _, FFS : TFLUSH_STK = _ |- _ => clear - Hr Hsp1 FFS; lia end
| left; right; right; right; exists 2, fpos; split; [left; reflexivity|];
first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 2) with 256; rewrite ?EFA; fold F; clear - Hr; lia
| right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 2 / 8) with 32; rewrite ?EFA; fold F; unfold SB; clear - Hr; lia ]
|
left; right; left; split;
[ eexists; split; [left; reflexivity | cbn [fst snd]; clear - Hr; lia]
| lazymatch type of Hcur3 with In (?cur, _) _ => exists cur, FRAME_SIZE; split; [exact Hcur3 | change (req_size FRAME_SIZE) with 40; clear - Hr; lia] end ]
| match goal with |- ?g => match type of Hr with ?t => idtac "WRFAIL" t g end end; fail 2 "wrangeFL" ]
| ]);
destruct Hin.
Lemma fl_X_aux : True -> fl_from B ss_X (INV_X B).
Proof.
intros _. fl_prelude.
pose proof HINV as (Hk3 & (r & E520 & Hr) & HPerm3). cbn [c_ly c_S] in HPerm3.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hcur_in).
assert (Hraw3 : In (cg_raw s, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
fl_blocks3 Hing3 Hcur3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ3) Hfin3) as (HFLpres' & HFLown' & HFLrng'). rewrite ?EFL3 in HFLpres'. rewrite ?EFL3 in HFLown'. rewrite ?EFL3 in HFLrng'. fold FL in HFLpres', HFLown', HFLrng'.
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (Hgpres3 a Ha))).
assert (HnoC : forall a, fr_ptr f <= a < fr_ptr f + 40 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (Hcpres3 a Ha))).
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
fs_rwF HS E88 HFSpres3.
add_flag_regionFL HS AG E87 HFLpres' HFLrng' HFLown' HnoG HnoC HnoF.
aj_run_flag_sh tratbl_lib_ok HS HJ3; [clear; lia | wrangeFL AG fpos F EFA3 EFL3 Hcur3 | flag0 E87 EFL3 |].
rreg HS (1%bv : bv 5) Rra. rreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx_tfa Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold fl_post, apost_base. cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_g c_s c_N c_i c_f c_rest c_fpos c_sp1 c_E0].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end.
split; [rewrite Rra; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS tra_segs_low); exact HJ3 | clear - Hk3; lia]|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
rewrite Ra0.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF ?WF (ms_mem ?msF) _ _ =>
assert (HrawF : In (cg_raw s, RAW_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hraw3);
assert (HcurF : In (fr_ptr f, FRAME_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hcur3);
assert (HingF : In (g, CGIF_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hing3);
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE (proj1 HJ3) HrawF) as (_ & _ & _ & _ & HrpresF & _); change (req_size RAW_SIZE) with 48 in HrpresF;
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ3) HcurF) as (_ & _ & _ & _ & HcpresF & _); change (req_size FRAME_SIZE) with 40 in HcpresF;
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC;
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; change (req_size FRAME_SIZE) with 40 in HdRC;
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H WF) (ms_mem msF)) (cg_raw s) LAY_Raw 48 (traw_vals g s) 8 40
Oraw ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview trasegs); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (cg_raw s) RAW_SIZE j Hraw_in HrawF ltac:(change (req_size RAW_SIZE) with 48; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj HdRC; lia | clear - Ha Hj Hnj; lia])
ltac:(intros j Hj; destruct (proj1 (HrpresF (cg_raw s + 40 + j) ltac:(clear - Hj; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (rcF & HrcF & OrawF);
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H WF) (ms_mem msF)) (fr_ptr f) LAY_Frame 40 (frame_vals f) 3 20
Oc ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview trasegs); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (fr_ptr f) FRAME_SIZE j Hcur_in HcurF ltac:(change (req_size FRAME_SIZE) with 40; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj Hnj; lia | clear - Ha Hj HdRC; lia])
ltac:(intros j Hj; destruct (proj1 (HcpresF (fr_ptr f + 20 + j) ltac:(clear - Hj; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (genF & HgenF & OcurF)
end.
lazymatch type of Ra0 with _ = ?v => exists (bv_unsigned v) end. exists genF, rcF.
split; [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; clear - Hrg; lia end|].
split; [|split; [apply (cgif_wf_flush_upd s N i genF rcF f Hf HWF) | unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); eapply Permutation_trans; [exact HPerm3 | exact HPerm]]].
split; [|split].
- rewrite (tcgif_vals_flush_upd s i genF rcF f Hf).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF _ _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hing | unfold ablocks; rewrite blocks_stack_free_state; exact Hing3 | exact Og | vm_compute; reflexivity |] end.
change (req_size CGIF_SIZE) with 96. intros j Hj (rr & Hrr & Ha). cbn [In] in Hrr.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG.
unbox. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha; [clear - Ha Hj HdGC; lia | clear - Ha Hj HdRG; lia].
- rewrite cg_raw_flush_upd, traw_vals_flush_upd. exact OrawF.
- intros x Hx. apply (In_frames_flush_upd s i genF rcF f x Hf) in Hx as [-> | (Hxin & jx & Hjx & Hne)].
+ rewrite frame_vals_set_fr_gen, fr_ptr_set_fr_gen. exact OcurF.
+
destruct (fl_blocks_in B ly S g s N jx x rest HPerm Hjx) as (_ & _ & Hxblk & _).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF _ _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hxblk | unfold ablocks; rewrite blocks_stack_free_state; eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hxblk
| exact (Ofr x Hxin) | vm_compute; reflexivity |] end.
change (req_size FRAME_SIZE) with 40. intros j Hj.
destruct (cgif_two_frames g s N rest i jx f x Hf Hjx ltac:(clear - Hne; intros E; apply Hne; symmetry; exact E)) as (l & Hl).
pose proof (sep_blocks_perm trasegs B LAWS ly S W mem md _ _ l HAR (Permutation_trans HPerm Hl)) as Hs. unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. change (req_size FRAME_SIZE) with 40 in Hs.
pose proof (sep_blocks trasegs _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr x) FRAME_SIZE HAR Hraw_in Hxblk ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRX.
unfold zdisjoint in HdRX; cbn [fst snd] in HdRX; change (req_size RAW_SIZE) with 48 in HdRX; change (req_size FRAME_SIZE) with 40 in HdRX.
apply fl_fp_out_frame; [clear - Hs; lia | clear - HdRX; lia | exact Hj].
Qed.
Lemma fl_X : fl_from B ss_X (INV_X B).
Proof. exact (fl_X_aux I). Qed.
End d.
End c.
