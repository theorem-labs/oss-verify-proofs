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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x YI5s YI5v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACkc ACj4 ACj9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACii ACi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YC6g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Lemma tcgif_vals_flush_upd : forall hw s i gen rc f,
nth_error (cg_frames s) i = Some (Some f) -> tcgif_vals hw (flush_upd s i gen rc) = tcgif_vals hw s.
Proof.
intros hw s i gen rc f Hf. unfold tcgif_vals. rewrite (cg_frames_flush_upd s i gen rc f Hf). cbn -[list_set nth].
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some (set_fr_gen f gen))) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
rewrite (nth_error_nth _ _ None Hf). reflexivity.
- rewrite nth_list_set_other by (clear - Hne; lia). reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma xcgif_vals_flush_upd : forall path hw pf s i gen rc f,
nth_error (cg_frames s) i = Some (Some f) -> xcgif_vals path hw pf (flush_upd s i gen rc) = xcgif_vals path hw pf s.
Proof.
intros path hw pf s i gen rc f Hf. unfold xcgif_vals. rewrite (cg_frames_flush_upd s i gen rc f Hf). cbn -[list_set nth].
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some (set_fr_gen f gen))) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hf; discriminate).
rewrite (nth_error_nth _ _ None Hf). reflexivity.
- rewrite nth_list_set_other by (clear - Hne; lia). reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma traw_vals_flush_upd : forall wfn g s i gen rc, traw_vals wfn g (flush_upd s i gen rc) = list_set (traw_vals wfn g s) 8 rc.
Proof. intros. reflexivity. Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section m.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis TLF : PALibF B.
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Variable wfn : Z.
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Ltac add_flag_regionFL HS AG E528 Hp HFLrng HFLown HnoG HnoC HnoF :=
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
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [lazymatch goal with QH1 : 65536 <= ?xa /\ ?xa + 8 <= _, QH2 : 65536 <= ?xb /\ ?xb + 8 <= _, QH3 : 65536 <= ?xc /\ ?xc + 8 <= _, QH4 : 65536 <= ?xd /\ ?xd + 8 <= _ |- _ =>
clear - HFLrng Qceil Qslo Qsp1 QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi QH1 QH2 QH3 QH4; zone_lia end |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoG fl); [lia | exact HFLown] | apply (HnoC fl); [lia | exact HFLown] | apply (HnoF fl); [lia | exact HFLown]
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS | st_ok _ ?Ev _ _ =>
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 528%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E528, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); lazymatch goal with |- apresent _ _ (?fl + ?oo) => replace (fl + oo) with fl by lia end; exact Hp)
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; evalE AG;
repeat split; first [lazymatch goal with QH1 : 65536 <= ?xa /\ ?xa + 8 <= _, QH2 : 65536 <= ?xb /\ ?xb + 8 <= _, QH3 : 65536 <= ?xc /\ ?xc + 8 <= _, QH4 : 65536 <= ?xd /\ ?xd + 8 <= _ |- _ =>
clear - HFLrng Qceil Qslo Qsp1 QC1 QC3 QFFS QFq QF8 QFceil QF8lo QF8hi QH1 QH2 QH3 QH4; zone_lia end |
lazymatch goal with |- ?fl + 1 <= ?x + ?l \/ ?x + ?h <= ?fl + 0 =>
destruct (Z_lt_ge_dec fl (x + l)); [left; lia|]; destruct (Z_lt_ge_dec fl (x + h)); [exfalso | right; lia];
first [apply (HnoG fl); [lia | exact HFLown] | apply (HnoC fl); [lia | exact HFLown] | apply (HnoF fl); [lia | exact HFLown]
| match goal with |- ?g => idtac "DISJFAIL" g end] end
| match goal with |- ?g => idtac "DISJ?" g end ])) as HS3;
clear HS; rename HS3 into HS; norm_ss HS  end.
Ltac wrangeFL AG fpos F EFA EFL Hcur3 :=
let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros a (r & Hin & Hr); rewrite ?EFA, ?EFL;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; revert Hr; evalE AG; intros Hr;
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
Lemma fl_XX_aux : True -> fl_fromX1 KS MT XN B CTX wfn ss_X (INV_XX KS MT XN B).
Proof.
intros _. fl_preludeX.
pose proof HINV as (Hk3 & (r & E961 & Hr & ((code & bytes & HFL & Hcode & Vrc & HSINK3 & HLEN3) & (acc & MLE3 & HaccM & HaccN))) & HPerm3 & E621X & _). cbn [c_ly c_S] in HPerm3.
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hcur_in).
assert (Hraw3 : In (cg_raw s, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
pose proof (sep_block_frame SEGS _ LAWS ly3 S3 _ _ _ (cg_raw s) RAW_SIZE 2 fpos HAR3 Hraw3 Hfin3) as XdFR.
unfold zdisjoint in XdFR; cbn [fst snd] in XdFR; change (req_size RAW_SIZE) with 48 in XdFR; change (fs_frame_bytes 2) with 256 in XdFR; rewrite EFA3 in XdFR. fold F in XdFR.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as XdRC.
unfold zdisjoint in XdRC. cbn [fst snd] in XdRC. change (req_size RAW_SIZE) with 48 in XdRC. change (req_size FRAME_SIZE) with 40 in XdRC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
destruct (FFL _ _ _ _ _ 2 fpos (proj1 HJ3) Hfin3) as (HFLpres' & HFLown' & HFLrng'). rewrite ?EFL3 in HFLpres'. rewrite ?EFL3 in HFLown'. rewrite ?EFL3 in HFLrng'. fold FL in HFLpres', HFLown', HFLrng'.
assert (HnoG : forall a, g <= a < g + 96 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (Hgpres3 a Ha))).
assert (HnoC : forall a, fr_ptr f <= a < fr_ptr f + 40 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (Hcpres3 a Ha))).
assert (HnoF : forall a, F <= a < F + 256 -> ~ aowned B ly3 S3 a) by (intros a Ha; exact (proj2 (HFpres3 a Ha))).
pose proof (proj2 (proj1 HFLrng')) as HFLni.
assert (HnoP : forall x, pf <= x < pf + 1264 -> ~ aowned B ly3 S3 x).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR3 Hpf3) as (_ & _ & _ & _ & HPp & _). change (req_size FILE_BLOCK) with 1264 in HPp. intros x Hx. exact (proj2 (HPp x Hx)). }
assert (HnoR : forall x, cg_raw s <= x < cg_raw s + 48 -> ~ aowned B ly3 S3 x).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR3 Hraw3) as (_ & _ & _ & _ & HRp & _). change (req_size RAW_SIZE) with 48 in HRp. intros x Hx. exact (proj2 (HRp x Hx)). }
pose proof (xfacts_i _ Hrh_ia) as XRia.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE pf FILE_BLOCK HAR Hraw_in Hpf_in ltac:(unfold RAW_SIZE, FILE_BLOCK; intros X; injection X; lia)) as XdRP.
unfold zdisjoint in XdRP; cbn [fst snd] in XdRP; change (req_size RAW_SIZE) with 48 in XdRP; change (req_size FILE_BLOCK) with 1264 in XdRP.
fs_rwF HS E529 HFSpres3.
add_flag_regionFL HS AG E528 HFLpres' HFLrng' HFLown' HnoG HnoC HnoF.
paj_run_flag_sh RUNF HS HJ3; [clear; lia | wrangeFL AG fpos F EFA3 EFL3 Hcur3 | flag0 E528 EFL3 |].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => xsink_stretchF HFr HSINK3 end. xval_stretchF Vrc.
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0.
lazymatch goal with |- SRr _ ?Wx _ _ =>
eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end.
intros mat'. unfold fl_postX, apost_base. cbn [c_ly c_S c_W c_regs c_mem c_md c_ch c_g c_s c_N c_i c_f c_rest c_fpos c_sp1 c_wfn c_hw c_uar c_E0 x_path x_pf x_Sg x_GPAL x_cur x_bef].
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx _ _ _ _ =>
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyx, Sx, rg, mm, mdx end end.
split; [rewrite Rra; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
split; [cbn [ms_mem]; eapply (ajournal_mono_k SEGS _); [apply (ajournal_materialize SEGS _ LAWS pa_segs_low); exact HJ3 | clear - Hk3 Hob241 Hob242 Hob253 Huar; lia]|].
split; [apply aregs_preserved_eqs; creg HS AG EE|].
rewrite Ra0.
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF ?WF (ms_mem ?msF) _ _ =>
assert (HrawF : In (cg_raw s, RAW_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hraw3);
assert (HcurF : In (fr_ptr f, FRAME_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hcur3);
assert (HingF : In (g, CGIF_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hing3);
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE (proj1 HJ3) HrawF) as (_ & _ & _ & _ & HrpresF & _); change (req_size RAW_SIZE) with 48 in HrpresF;
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ3) HcurF) as (_ & _ & _ & _ & HcpresF & _); change (req_size FRAME_SIZE) with 40 in HcpresF;
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC;
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; change (req_size FRAME_SIZE) with 40 in HdRC;
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H WF) (ms_mem msF)) (cg_raw s) LAY_Raw 48 (traw_vals wfn g s) 8 40
Oraw ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview SEGS); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (cg_raw s) RAW_SIZE j Hraw_in HrawF ltac:(change (req_size RAW_SIZE) with 48; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | [<- | [<- | [<- | []]]]]; try unfold sink_token in Ha; cbn [fst snd] in Ha; [clear - Ha Hj HdRC Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hj Hnj Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hj XdRP; unfold FILE_BLOCK in Ha; lia | clear - Ha Hj Hr4096; lia])
ltac:(intros j Hj; destruct (proj1 (HrpresF (cg_raw s + 40 + j) ltac:(clear - Hj Hob241 Hob242 Hob253 Huar; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (rcF & HrcF & OrawF);
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H WF) (ms_mem msF)) (fr_ptr f) LAY_Frame 40 (frame_vals f) 3 20
Oc ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview SEGS); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (fr_ptr f) FRAME_SIZE j Hcur_in HcurF ltac:(change (req_size FRAME_SIZE) with 40; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | [<- | [<- | [<- | []]]]]; try unfold sink_token in Ha; cbn [fst snd] in Ha; [clear - Ha Hj Hnj Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hj HdRC Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hj XF; unfold xfacts in XF; unfold FILE_BLOCK in Ha; lia | clear - Ha Hj XF; unfold xfacts in XF; lia])
ltac:(intros j Hj; destruct (proj1 (HcpresF (fr_ptr f + 20 + j) ltac:(clear - Hj Hob241 Hob242 Hob253 Huar; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (genF & HgenF & OcurF)
end.
assert (XrcF : rcF = code mod 2 ^ 32).
{ destruct (obj_at_nth SEGS _ _ _ _ 8%nat (40, 4%N) rcF OrawF eq_refl eq_refl) as [VrcF _].
cbn [fst snd] in VrcF. change (N.to_nat 4) with 4%nat in VrcF.
apply (YC6g.val_mem4_inj SEGS _ (cg_raw s + 40) rcF (code mod 2 ^ 32) VrcF Vrc HrcF).
apply Z.mod_pos_bound. clear; lia. }
assert (XgenF : genF = YI0f.fl_gen3 (gcfg_of s GPAL) cur bef).
{ pose proof HCUR as (_ & XCg & _). cbn in XCg.
pose proof (fl_gen3_range (gcfg_of s GPAL) cur bef ltac:(rewrite <- XCg; clear - Q3; lia)) as G3R.
destruct (obj_at_nth SEGS _ _ _ _ 3%nat (20, 4%N) genF OcurF eq_refl eq_refl) as [VgenF _].
cbn [fst snd] in VgenF. change (N.to_nat 4) with 4%nat in VgenF.
refine (YC6g.val_mem4_inj SEGS _ (fr_ptr f + 20) genF (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) VgenF _ HgenF ltac:(clear - G3R Q3 XCg; lia)).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 11%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRcur; cbn [ms_mem restrict] in HRcur;
lazymatch type of HRcur with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
exact (field_of_region Ex _ 11 (fr_ptr f) cs lo hi wlo whi 20 4%N (SOff 621 0) (YI0f.fl_gen3 (gcfg_of s GPAL) cur bef) HRcur
ltac:(rewrite E11n; apply unsigned_lit_small; clear - Hc4096 Hcceil C1; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E621X)
ltac:(cbn; clear - G3R Q3 XCg; lia) ltac:(cbn; lia)) end end. }
lazymatch type of Ra0 with _ = ?v => exists (bv_unsigned v) end. exists rcF. rewrite <- XgenF.
split; [unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (bv_unsigned_in_range 64 v) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; clear - Hrg Hob241 Hob242 Hob253 Huar; lia end|].
split; [|split; [apply (cgif_wf_flush_upd s N i genF rcF f Hf HWF) | split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); eapply Permutation_trans; [exact HPerm3 | exact HPerm]|]]].
2: {
split.
- exists code, bytes. split; [exact HFL|]. split; [rewrite Z_to_bv_bv_unsigned, E961; exact Hcode|]. split; [exact XrcF|]. split; [cbn [ms_mem]; exact HSINK3 | exact HLEN3].
- apply (mle_weaken MT S _ acc _ MLAW); [| clear - HaccN; lia]. first [exact MLE3 | eapply (mo_le_set_fs_r MT MLAWF); exact MLE3]. }
split; [|split].
- rewrite (xcgif_vals_flush_upd path hw pf s i genF rcF f Hf).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF _ _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hing | unfold ablocks; rewrite blocks_stack_free_state; exact Hing3 | exact Og | vm_compute; reflexivity |] end.
change (req_size CGIF_SIZE) with 96. intros j Hj (rr & Hrr & Ha). cbn [In] in Hrr.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG.
unbox. destruct Hrr as [<- | [<- | [<- | [<- | []]]]]; try unfold sink_token in Ha; cbn [fst snd] in Ha; [clear - Ha Hj HdGC Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hj HdRG Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hj XF; unfold xfacts in XF; unfold FILE_BLOCK in Ha; lia | clear - Ha Hj XF; unfold xfacts in XF; lia].
- rewrite cg_raw_flush_upd, traw_vals_flush_upd. exact OrawF.
- intros x Hx. apply (In_frames_flush_upd s i genF rcF f x Hf) in Hx as [-> | (Hxin & jx & Hjx & Hne)].
+ rewrite frame_vals_set_fr_gen, fr_ptr_set_fr_gen. exact OcurF.
+
destruct (fl_blocks_in B ly S g s N jx x rest HPerm Hjx) as (_ & _ & Hxblk & _).
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF _ _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hxblk | unfold ablocks; rewrite blocks_stack_free_state; eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hxblk
| exact (Ofr x Hxin) | vm_compute; reflexivity |] end.
change (req_size FRAME_SIZE) with 40. intros j Hj.
destruct (cgif_two_frames g s N rest i jx f x Hf Hjx ltac:(clear - Hne Hob241 Hob242 Hob253 Huar; intros E; apply Hne; symmetry; exact E)) as (l & Hl).
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md _ _ l HAR (Permutation_trans HPerm Hl)) as Hs. unfold zdisjoint, block_rng in Hs. cbn [fst snd] in Hs. change (req_size FRAME_SIZE) with 40 in Hs.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr x) FRAME_SIZE HAR Hraw_in Hxblk ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRX.
unfold zdisjoint in HdRX; cbn [fst snd] in HdRX; change (req_size RAW_SIZE) with 48 in HdRX; change (req_size FRAME_SIZE) with 40 in HdRX.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ pf FILE_BLOCK (fr_ptr x) FRAME_SIZE HAR Hpf_in Hxblk ltac:(unfold FILE_BLOCK, FRAME_SIZE; intros X; injection X; lia)) as XdPX.
unfold zdisjoint in XdPX; cbn [fst snd] in XdPX; change (req_size FILE_BLOCK) with 1264 in XdPX; change (req_size FRAME_SIZE) with 40 in XdPX.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr x) FRAME_SIZE HAR Hxblk) as (_ & Hx4096 & _).
intros (r0 & Hr0 & Ha0). cbn [In asink_fp] in Hr0. destruct Hr0 as [<- | [<- | [<- | [<- | []]]]]; try unfold sink_token in Ha0; cbn [fst snd] in Ha0; unfold FILE_BLOCK in *; clear - Ha0 Hj Hs HdRX XdPX Hx4096; lia.
Qed.
Lemma fl_XX : fl_fromX1 KS MT XN B CTX wfn ss_X (INV_XX KS MT XN B).
Proof. exact (fl_XX_aux I). Qed.
End m.
End e.
End d.
