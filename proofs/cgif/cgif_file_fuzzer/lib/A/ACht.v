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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YI5x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCkd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACkc ACj4 ACj9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACj0 ACja ACj6 ACjb ACiy ACj7 ACj3 ACj5 AChd ACjc ACjd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YC5d YC7z YC7y YC7x YC85 YC88 YC7l YC87.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AChz ACid ACie ACig ACi0 ACih ACi4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACik ACil ACi9 ACia.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Ltac hc_atom H n v En rtac :=
lazymatch type of H with context [U ?E' (SOff n 0)] =>
rewrite (U_atom E' n v ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact En)) in H by rtac end.
Fixpoint trim_base (rs : smem) (n : nat) (lo hi : Z) : smem :=
match rs with
| [] => []
| r :: t => match YP09.r_base r with
| Some b => if Nat.eqb b n then trim_region r lo hi :: t else r :: trim_base t n lo hi
| None => r :: trim_base t n lo hi end end.
Lemma extent_disjoint_sym : forall E a b, extent_disjoint E a b -> extent_disjoint E b a.
Proof. intros E a b [H|H]; [right | left]; exact H. Qed.
Lemma all_disjoint_app : forall E r l1 l2, all_disjoint E r (l1 ++ l2) <-> all_disjoint E r l1 /\ all_disjoint E r l2.
Proof.
intros E r l1 l2. induction l1 as [|x l1 IH]; cbn; [tauto|]. rewrite IH. tauto.
Qed.
Lemma pairwise_disjoint_remove : forall E l1 x l2, pairwise_disjoint E (l1 ++ x :: l2) -> pairwise_disjoint E (l1 ++ l2) /\ all_disjoint E x l2 /\ (forall y, In y l1 -> extent_disjoint E y x).
Proof.
intros E l1 x l2. induction l1 as [|y l1 IH]; cbn; intros H.
- destruct H as [Hx Hp]. repeat split; try assumption. intros z [].
- destruct H as [Hy Hp]. apply all_disjoint_app in Hy as [Hy1 [Hyx Hy2]]. destruct (IH Hp) as (P1 & P2 & P3).
split; [split; [apply all_disjoint_app; split; assumption | exact P1]|]. split; [exact P2|].
intros z [<- | Hz]; [exact Hyx | exact (P3 z Hz)].
Qed.
Lemma pairwise_disjoint_insert : forall E l1 x l2, pairwise_disjoint E (l1 ++ l2) -> all_disjoint E x (l1 ++ l2) -> pairwise_disjoint E (l1 ++ x :: l2).
Proof.
intros E l1 x l2. induction l1 as [|y l1 IH]; cbn; intros Hp Hx.
- split; [exact Hx | exact Hp].
- destruct Hp as [Hy Hp]. destruct Hx as [Hxy Hx]. apply all_disjoint_app in Hy as [Hy1 Hy2].
split; [apply all_disjoint_app; split; [exact Hy1 | cbn; split; [apply extent_disjoint_sym; exact Hxy | exact Hy2]] | exact (IH Hp Hx)].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma ast_ok_replace_region0 : forall E ss ms l1 r r' l2,
st_ok SEGS E ss ms -> ss_mem ss = l1 ++ r :: l2 ->
regions_wf (l1 ++ r' :: l2) = true -> region_ok SEGS E (ms_mem ms) r' -> all_disjoint E r' (l1 ++ l2) ->
st_ok SEGS E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ r' :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 r r' l2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hrs Hwf' Hr' Hd.
rewrite Hrs in Hok, Hpd.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
split; [exact Hwf'|]. split.
- apply Forall_app in Hok as [Ha Hb]. inversion Hb; subst. apply Forall_app. split; [exact Ha | constructor; assumption].
- destruct (pairwise_disjoint_remove E l1 r l2 Hpd) as (P1 & _ & _). exact (pairwise_disjoint_insert E l1 r' l2 P1 Hd).
Qed.
Lemma ast_ok_replace_region : forall E ss ms l1 r r' l2,
st_ok_pi SEGS VAL E ss ms -> ss_mem ss = l1 ++ r :: l2 ->
regions_wf (l1 ++ r' :: l2) = true -> region_ok SEGS E (ms_mem ms) r' -> all_disjoint E r' (l1 ++ l2) ->
st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (ss_regs ss) (l1 ++ r' :: l2) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms l1 r r' l2 HS Hrs Hwf' Hr' Hd. destruct ss as [pc0 sr0 fr0 sm0 rv0 fs0].
exact (ast_ok_replace_region0 E _ ms l1 r r' l2 HS Hrs Hwf' Hr' Hd).
Qed.
Lemma denot_mul_add : forall E nh nw na h w a, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w -> ew E na = Z_to_bv 64 a ->
0 <= h < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= a < 2 ^ 16 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff nh 0) (SOff nw 0)) (SOff na 0)) = Z_to_bv 64 (h * w + a).
Proof.
intros E nh nw na h w a Hh Hw Ha Rh Rw Ra. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (h * w <= (2 ^ 16 - 1) * (2 ^ 16 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E nh h Hh), (U_atom E nw w Hw), (U_atom E na a Ha) by lia.
rewrite (zcanon_id (h * w)) by (rewrite M64_val; lia). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_and_ffff : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 -> sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 65535)) = Z_to_bv 64 x.
Proof.
intros E n x Hn Rx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_sll48 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 16 -> sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 48)) = Z_to_bv 64 (x * 2 ^ 48).
Proof.
intros E n x Hn Rx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia. apply zcanon_id. rewrite M64_val. change (2 ^ 48) with 281474976710656 in *. lia.
Qed.
Lemma region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.
Lemma fl_gpal_block : forall (B : asyms) ly S g s N rest,
Permutation (ablocks B ly S) (cgif_blocks g s N ++ rest) -> Z.land (cg_attr s) 4 = 0 -> In (cg_pal s, 3 * cg_ngp s) (ablocks B ly S).
Proof.
intros B ly S g s N rest HP Ha. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left.
unfold cgif_blocks. right. right. apply in_app_iff. left. unfold pal_blocks. rewrite (proj2 (Z.eqb_eq _ _) Ha). left. reflexivity.
Qed.
Section q.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
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
Ltac upd_aboveF HUP HFr AG ltac :=
let HUP' := fresh "HUP" in
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msX)) =>
lazymatch type of HUP with forall a, ?lo <= a < _ -> aview ?sg ?Hh _ a = aview _ ?Hw ?me a =>
assert (HUP' : forall a, lo <= a < 2 ^ 64 -> aview sg Hh (ms_mem msX) a = aview sg Hw me a);
[ let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; rewrite <- (HUP a Ha); eapply (aview_kept_frame Ef rs _ _ _ lo HFr); [lia| |exact Ha];
let b := fresh "b" in let Hb := fresh "Hb" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros b Hb (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; first [ ltac Hb Hrg | revert Hrg; evalE AG; intros Hrg; ltac Hb Hrg ] |]);
destruct Hin
| clear HUP; rename HUP' into HUP ] end end.
Ltac bef_EB :=
let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; do 9 (try (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [Nat.add]; assumption|])); destruct j; discriminate Hj.
Lemma fl_T3X_aux : fl_fromX0 KS MT XN B CTX wfn ss_R (INV_RX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T3 (INV_T3X MT B).
Proof.
intros RR. fl_preludeX.
pose proof HINV as ((gen & E621 & Rgen) & E625 & (fb & Hfb & EB) & (pt & w & h & top & left & E801 & E683 & E684 & E681 & E685 & Hw1 & Hl0 & Hlw & Hh1 & Ht0 & Hth & Hk2 & Htb & (XD & XI0 & XLEN & XMLE)) & E621X & XF1 & (tv & E741x & Rtv & Xtv)).
cbn [c_i c_s] in Hfb. pose proof Htb as Htb0. unfold fl_tmpblkX, fl_FP0 in Htb. cbn [c_ly c_S c_regs c_f c_s] in Htb.
destruct Htb as (Hnh & Hpce & Hn16 & Eab3 & Ares & Tres).
xpt_facts Htb0 XPT.
assert (XI : pt <> 0 -> garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) pt (xtmp (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur bef))) by (intros _; exact XI0).
pose proof (EB 0%nat _ eq_refl) as E651. pose proof (EB 1%nat _ eq_refl) as E652. pose proof (EB 2%nat _ eq_refl) as E653.
pose proof (EB 3%nat _ eq_refl) as E654. pose proof (EB 4%nat _ eq_refl) as E655. pose proof (EB 5%nat _ eq_refl) as E656.
pose proof (EB 6%nat _ eq_refl) as E657. pose proof (EB 7%nat _ eq_refl) as E658. pose proof (EB 8%nat _ eq_refl) as E659.
cbn [Nat.add] in E651, E652, E653, E654, E655, E656, E657, E658, E659.
rewrite Hfb in E12. cbn [frame_ptr] in E12.
assert (E741 : ew E 741 = Z_to_bv 64 (bv_unsigned (ew E 741))) by (symmetry; apply Z_to_bv_bv_unsigned).
assert (Hwh0 : 1 <= w * h) by (clear - Hw1 Hh1 Hob241 Hob242 Hob253 Huar; nia).
assert (Hwh : w * h <= N) by (rewrite HN; apply Z.mul_le_mono_nonneg; clear - Hw1 Hh1 Hlw Hl0 Hth Ht0 Hob241 Hob242 Hob253 Huar; lia).
destruct (fl_bef_in s i fb Hi Hlen3 Hfb) as [Hfbe Hfbi].
destruct (fl_bef_blocks B ly S g s N rest fb HPerm Hfbi) as (Hbef_in & Hbimg_in & Hblpal).
destruct (al_blocks _ _ LAWS ly S W mem md (fr_ptr fb) FRAME_SIZE HAR Hbef_in) as (Hb16 & Hb4096 & Hbceil & [Hbh1 Hbh2] & _ & _). change (req_size FRAME_SIZE) with 40 in Hbceil, Hbh2.
destruct (al_blocks _ _ LAWS ly S W mem md (fr_img fb) N HAR Hbimg_in) as (Hbi16 & Hbi4096 & Hbiceil & Hbih_ia & _ & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hbimg_in) as Hbih_img.
assert (Hsub3 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly3 S3)) by (intros x Hx; rewrite Eab3; apply in_app_iff; left; exact Hx).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hing).
assert (Hcur3 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hcur_in).
assert (Himg3 : In (fr_img f, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Himg_in).
assert (Hbef3 : In (fr_ptr fb, FRAME_SIZE) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbef_in).
assert (Hbimg3 : In (fr_img fb, N) (ablocks B ly3 S3)) by (apply Hsub3; exact Hbimg_in).
assert (Hpt3 : In (pt, w * h) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_app_iff; right; left; reflexivity).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (apply Hsub3; exact Hpf_in).
fl_blocks3X Hing3 Hcur3 Hpf3. fold F in HdFG, HdFC.
relowF HS AG E10 E11 E32 E10n E11n E32n.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E12) | st_ok _ ?Ev _ _ => assert (E12n : ew Ev 12 = Z_to_bv 64 (fr_ptr fb)) by (rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E12)  end.
reshok HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ3 SHOK FLBspan 0x21f4.
all: try (oblG HJ3 E12n E32n Hbef3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia). clear_frames.
lazymatch type of AG with forall n, _ -> ew ?Ebase n = _ => assert (Usp3 : bv_unsigned (ew Ebase 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
prreg HS (@BV 5 1 I) Rra. prreg HS (@BV 5 2 I) Rsp. prreg HS (@BV 5 3 I) Rgp. prreg HS (@BV 5 4 I) Rtp. prreg HS (@BV 5 8 I) Rs0.
prreg HS (@BV 5 6 I) Rr6. prreg HS (@BV 5 9 I) Rr9. prreg HS (@BV 5 14 I) Rr15. prreg HS (@BV 5 19 I) Rr19. prreg HS (@BV 5 18 I) Rr24.
prreg HS (@BV 5 21 I) Rr21. prreg HS (@BV 5 22 I) Rr22. prreg HS (@BV 5 26 I) Rr26. prreg HS (@BV 5 27 I) Rr27.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F240 : ew Ev 681 = Z_to_bv 64 top) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E681);
assert (F242 : ew Ev 679 = Z_to_bv 64 w) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E683);
assert (F243 : ew Ev 684 = Z_to_bv 64 h) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E684);
assert (F244 : ew Ev 680 = Z_to_bv 64 left) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E685);
assert (F40 : ew Ev 40 = Z_to_bv 64 (cg_W s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40);
assert (F360 : ew Ev 801 = Z_to_bv 64 pt) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E801);
assert (F211 : ew Ev 652 = Z_to_bv 64 (fr_img fb)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652);
rreg_by HS (@BV 5 24 I) (Z_to_bv 64 (top * cg_W s + left)) (denot_mul_add Ev 681 40 680 top (cg_W s) left F240 F40 F244 ltac:(clear - Ht0 Hth Hh1 R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - R7 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hl0 Hlw Hw1 R7 Hob241 Hob242 Hob253 Huar; lia)) Rr18;
rreg_by HS (@BV 5 20 I) (Z_to_bv 64 w) (denot_and_ffff Ev 679 w F242 ltac:(clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia)) Rr20 | st_ok _ ?Ev _ _ =>
assert (F240 : ew Ev 681 = Z_to_bv 64 top) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E681);
assert (F242 : ew Ev 679 = Z_to_bv 64 w) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E683);
assert (F243 : ew Ev 684 = Z_to_bv 64 h) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E684);
assert (F244 : ew Ev 680 = Z_to_bv 64 left) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E685);
assert (F40 : ew Ev 40 = Z_to_bv 64 (cg_W s)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E40);
assert (F360 : ew Ev 801 = Z_to_bv 64 pt) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E801);
assert (F211 : ew Ev 652 = Z_to_bv 64 (fr_img fb)) by (rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652);
rreg_by HS (@BV 5 24 I) (Z_to_bv 64 (top * cg_W s + left)) (denot_mul_add Ev 681 40 680 top (cg_W s) left F240 F40 F244 ltac:(clear - Ht0 Hth Hh1 R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - R7 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hl0 Hlw Hw1 R7 Hob241 Hob242 Hob253 Huar; lia)) Rr18;
rreg_by HS (@BV 5 20 I) (Z_to_bv 64 w) (denot_and_ffff Ev 679 w F242 ltac:(clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia)) Rr20 end.
lazymatch type of Rsp with getr ?rg 2 = _ =>
assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia);
assert (Es0X : s0Z rg = spZ regs) by (unfold s0Z; rewrite Rs0, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact Usp3) end.
assert (Qtop64 : ly_top ly <= 2 ^ 64) by (clear - Htop2 H47 Htop Hshi Hob241 Hob242 Hob253 Huar; lia).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qal8 : spZ regs mod 8 = 0) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ] | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
let rh := eval vm_compute in (nth ih rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat (@BV 5 1 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat (@BV 5 8 I) eq_refl), Z.add_0_r; reflexivity)
ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
clear HRstk;
assert (Hch1 : achain ly3 (aview SEGS (w_H W3) (ms_mem msX)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch));
[ apply (achain_ly_top ly); [pose proof (proj1 (proj2 HJ3)) as LY; destruct LY as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|];
replace (spZ regs - 8) with (spZ regs + -8) in Vra by lia; replace (spZ regs - 16) with (spZ regs + -16) in Vs0 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch Qtop64 HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs0 Qs0) Hra4 ltac:(clear - Hceil Hslo Hstk0 FFS Hob241 Hob242 Hob253 Huar; lia) Qal8
ltac:(clear - Htop32 Hob241 Hob242 Hob253 Huar; lia) ltac:(clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia))
| ]  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 60 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 232 (SOff 741 0) (bv_unsigned (ew Ex 741)) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 741)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) V232;
slot 240 (SOff 32 0) SB ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E32n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold SB; cbn; lia) V240;
slot 248 (SOff 12 0) (fr_ptr fb) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E12n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hbh1 Hbh2 C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V248;
slot 272 (SOff 516 0) F ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V272;
slot 176 (SAlu ALU_SLL (SOff 679 0) (SLit 48)) (w * 2 ^ 48) ltac:(apply (denot_sll48 Ex 679 w F242); clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) ltac:(cbn [Z.of_N Z.mul]; change (2 ^ 48) with 281474976710656; clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) V176;
slot 184 (SAlu ALU_AND (SOff 684 0) (SLit 65535)) h ltac:(apply (denot_and_ffff Ex 684 h F243); clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(cbn [Z.of_N Z.mul]; clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia) V184;
slot 192 (SAlu ALU_AND (SOff 679 0) (SLit 65535)) w ltac:(apply (denot_and_ffff Ex 679 w F242); clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) ltac:(cbn [Z.of_N Z.mul]; clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) V192;
slot 200 (SOff 40 0) (cg_W s) ltac:(cbn [sv_denot]; rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R7 Hob241 Hob242 Hob253 Huar; lia) V200 end;
clear HRloc | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let il := idx_of_base rs 60%nat in let il := eval vm_compute in il in
let rl := eval vm_compute in (nth il rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) il rl HS ltac:(vm_compute; reflexivity)) as HRloc; cbn [ms_mem restrict] in HRloc;
lazymatch type of HRloc with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
let slot off e v dtac rtac Hn :=
pose proof (field_of_region Ex _ 60 sp1 cs lo hi wlo whi off 8%N e v HRloc
ltac:(rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E60; apply unsigned_lit_small; clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia)
ltac:(cbn; tauto) ltac:(dtac) ltac:(rtac) ltac:(cbn; lia)) as Hn in
slot 232 (SOff 741 0) (bv_unsigned (ew Ex 741)) ltac:(cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (ew Ex 741)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) V232;
slot 240 (SOff 32 0) SB ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E32n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(unfold SB; cbn; lia) V240;
slot 248 (SOff 12 0) (fr_ptr fb) ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E12n, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - Hbh1 Hbh2 C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia) V248;
slot 272 (SOff 516 0) F ltac:(cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; lia) V272;
slot 176 (SAlu ALU_SLL (SOff 679 0) (SLit 48)) (w * 2 ^ 48) ltac:(apply (denot_sll48 Ex 679 w F242); clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) ltac:(cbn [Z.of_N Z.mul]; change (2 ^ 48) with 281474976710656; clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) V176;
slot 184 (SAlu ALU_AND (SOff 684 0) (SLit 65535)) h ltac:(apply (denot_and_ffff Ex 684 h F243); clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia) ltac:(cbn [Z.of_N Z.mul]; clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia) V184;
slot 192 (SAlu ALU_AND (SOff 679 0) (SLit 65535)) w ltac:(apply (denot_and_ffff Ex 679 w F242); clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) ltac:(cbn [Z.of_N Z.mul]; clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia) V192;
slot 200 (SOff 40 0) (cg_W s) ltac:(cbn [sv_denot]; rewrite F40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn [Z.of_N Z.mul]; clear - R7 Hob241 Hob242 Hob253 Huar; lia) V200 end;
clear HRloc  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V232, V240, V248, V272, V176, V184, V192, V200.
assert (HPerm3 : Permutation (ablocks B ly3 S3) (ablocks B ly S ++ [(pt, w * h)])) by (rewrite Eab3; apply Permutation_refl).
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) g CGIF_SIZE HAR3 HPerm3 Hing) as HdPG. change (req_size CGIF_SIZE) with 96 in HdPG.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) (fr_ptr f) FRAME_SIZE HAR3 HPerm3 Hcur_in) as HdPC. change (req_size FRAME_SIZE) with 40 in HdPC.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) (fr_ptr fb) FRAME_SIZE HAR3 HPerm3 Hbef_in) as HdPB. change (req_size FRAME_SIZE) with 40 in HdPB.
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) (fr_img fb) N HAR3 HPerm3 Hbimg_in) as HdPI.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 _ _ _ pt (w * h) 2 fpos HAR3 Hpt3 Hfin3) as HdPF.
unfold zdisjoint in HdPF. cbn [fst snd] in HdPF. change (fs_frame_bytes 2) with 256 in HdPF. rewrite EFA3 in HdPF. fold F in HdPF.
pose proof (fl_bef_sep B LAWS ly S W mem md g s N rest i f fb HAR HPerm Hf Hfbe Hi) as HdCB.
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [exfalso; clear - Hwh0 e Hob241 Hob242 Hob253 Huar; lia | reflexivity]).
rewrite Hrq in HdPG, HdPC, HdPB, HdPI, HdPF.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE g CGIF_SIZE HAR Hraw_in Hing ltac:(unfold RAW_SIZE, CGIF_SIZE; intros X; injection X; lia)) as HdRG.
unfold zdisjoint in HdRG; cbn [fst snd] in HdRG; change (req_size RAW_SIZE) with 48 in HdRG; change (req_size CGIF_SIZE) with 96 in HdRG.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr fb) FRAME_SIZE HAR Hraw_in Hbef_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRB.
unfold zdisjoint in HdRB; cbn [fst snd] in HdRB; change (req_size RAW_SIZE) with 48 in HdRB; change (req_size FRAME_SIZE) with 40 in HdRB.
pose proof (sep_blocks SEGS _ LAWS ly S _ _ _ (cg_raw s) RAW_SIZE (fr_ptr f) FRAME_SIZE HAR Hraw_in Hcur_in ltac:(unfold RAW_SIZE, FRAME_SIZE; intros X; injection X; lia)) as HdRC.
unfold zdisjoint in HdRC; cbn [fst snd] in HdRC; change (req_size RAW_SIZE) with 48 in HdRC; change (req_size FRAME_SIZE) with 40 in HdRC.
assert (Og3 : obj_at SEGS (mrestrict (w_H W3) (ms_mem ms)) g LAY_CGIF (xcgif_vals path hw pf s)).
{ lazymatch goal with |- obj_at _ (mrestrict _ (ms_mem ?msX)) _ _ _ =>
eapply (aj_obj_kept B); [exact HJ3 | exact Hing | exact Hing3 | exact Og | vm_compute; reflexivity |] end.
change (req_size CGIF_SIZE) with 96. intros j Hj (rr & Hrr & Ha). cbn [In] in Hrr.
unbox. destruct Hrr as [<- | []]; cbn [fst snd] in Ha; clear - Ha Hj HdGC Hob241 Hob242 Hob253 Huar; lia. }
assert (Ob3 : obj_at SEGS (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr fb) LAY_Frame (frame_vals fb)).
{ eapply (aj_obj_kept B); [exact HJ3 | exact Hbef_in | exact Hbef3 | exact (Ofr fb Hfbi) | vm_compute; reflexivity |].
change (req_size FRAME_SIZE) with 40. intros j Hj. apply fl_fp0_out_frame; [clear - HdCB Hob241 Hob242 Hob253 Huar; lia | exact Hj]. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE (proj1 HJ3) Hcur3) as (_ & _ & _ & _ & HcpresX & _). change (req_size FRAME_SIZE) with 40 in HcpresX.
destruct (obj_at_hole4 (mrestrict (w_H W) mem) (mrestrict (w_H W3) (ms_mem ms)) (fr_ptr f) LAY_Frame 40 (frame_vals f) 3 20
Oc ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity) ltac:(cbn; lia)
ltac:(intros j Hj Hnj; apply (mbyte_of_aview SEGS); pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _);
apply (F2 (fr_ptr f) FRAME_SIZE j Hcur_in Hcur3 ltac:(change (req_size FRAME_SIZE) with 40; exact Hj));
intros (rr & Hrr & Ha); cbn [In] in Hrr; destruct Hrr as [<- | []]; cbn [fst snd] in Ha; clear - Ha Hj Hnj Hob241 Hob242 Hob253 Huar; lia)
ltac:(intros j Hj; destruct (proj1 (HcpresX (fr_ptr f + 20 + j) ltac:(clear - Hj Hob241 Hob242 Hob253 Huar; lia))) as [Hh [b Hb]];
unfold mbyte, mrestrict; cbn [ms_mem]; rewrite Hh; cbn; rewrite Hb; eexists; reflexivity))
as (genC & HgenC & Oc3).
destruct (fl_bef_blocks B ly S g s N rest f HPerm Hfi) as (_ & _ & Hclpal).
pose proof (Hfwf f Hfi) as [Hfgp _]. pose proof (Hfwf fb Hfbi) as [Hbgp _].
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HCTX : tin_ctx B W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 [(fr_ptr f + 20, fr_ptr f + 24)] ly S W mem md ly3 S3 k fpos
((spZ regs, raZ regs, s0Z regs) :: ch) pt (w * h) (fr_img fb) N g (fr_ptr f) (fr_ptr fb) (bv_unsigned (ew E 741))
(xcgif_vals path hw pf s) (list_set (frame_vals f) 3 genC) (frame_vals fb)
(cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb)) end.
{ split; [exact HJ3|]. split; [exact Hpt3|].
split; [intros blc lyq ownq a Hbl Ha; replace a with (pt + (a - pt)) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); apply (Ares blc lyq ownq (a - pt) Hbl); clear - Ha Hob241 Hob242 Hob253 Huar; lia|].
split; [exact Hbimg3|]. split; [clear - HNle Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - HdPI Hrq Hob241 Hob242 Hob253 Huar; lia|].
split; [exact Hing3|]. split; [exact Hcur3|]. split; [exact Hbef3|]. split; [clear - HdCB Hob241 Hob242 Hob253 Huar; lia|].
split; [clear - HdPG Hrq Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - HdPC Hrq Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - HdPB Hrq Hob241 Hob242 Hob253 Huar; lia|].
split; [exact Og3|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Oc3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Ob3|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros Ha1; exists (3 * fr_nlp f); split; [apply Hsub3; apply Hclpal; exact Ha1 | clear; lia]|].
split; [intros Ha1; exists (3 * fr_nlp fb); split; [apply Hsub3; apply Hblpal; exact Ha1 | clear; lia]|].
split; [intros Hor; exists (3 * cg_ngp s); split; [apply Hsub3; apply (fl_gpal_block B ly S g s N rest HPerm); destruct Hor as [H0 | H0]; [exact (Hfgp H0) | exact (Hbgp H0)] | clear; lia]|].
split; [exact EspX|]. split; [exact Hsp1|]. split; [exact Hsp1al16|].
split; [rewrite Rr9, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E60|].
split; [rewrite Rgp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 3%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite (EE 3%nat (@BV 5 3 I) eq_refl); exact Hgp|].
split; [rewrite Rtp, ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 4%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite (EE 4%nat (@BV 5 4 I) eq_refl); exact Htp|].
split; [rewrite Es0X; exact Hch1|]. split; [exact Es0X|].
split; [exact V232|]. split; [pose proof (bv_unsigned_in_range 64 (ew E 741)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq|].
split; [exact V240|]. split; [exact V248|].
split; [rewrite Rr26, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E652|]. split; [exact Rr27|].
split; [rewrite Rr21, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E10n | rewrite Rr22, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E11n]. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
assert (HOUT : tout_ctx W3 (ms_mem msX) sp1 w h top left (cg_W s) N) end.
{ split; [clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia|]. split; [clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia|]. split; [exact Ht0|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [clear - R7 Hob241 Hob242 Hob253 Huar; lia|].
split; [rewrite HN, (Z.mul_comm (cg_W s) (cg_H s)); apply Z.mul_le_mono_nonneg_r; clear - Hth R7 Hob241 Hob242 Hob253 Huar; lia|].
split; [exact V176|]. split; [exact V184|]. split; [exact V192 | exact V200]. }
assert (HF8c : 8 * (F / 8) <= F) by (apply Z.mul_div_le; clear; lia).
clear Kgot3 Kcell3 Kguar3 Kuar3. aconstsF HJ3 Kgot3 Kcell3 Kguar3 Kuar3.
pmkst HS.
pose proof HCUR as (XCa & _ & _ & XCn & XCct & _ & _ & XCimg & XClen & XClp).
rewrite Hfb in HBEF. destruct bef as [b|]; [|destruct HBEF].
pose proof HBEF as (XBa & _ & _ & XBn & XBct & _ & _ & XBimg & XBlen & XBlp).
destruct (cur_obj_tail g s N rest i f Hf) as (ctail & HPct & Tgp & _ & Tlp & Tfr).
pose proof (Permutation_trans HPerm HPct) as HPc.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
assert (XJ : forall p sz L, In (p, sz) (ablocks B ly S) -> In (p, sz) ctail -> Z.of_nat (length L) <= req_size sz ->
garr8 SEGS (mrestrict (w_H W) mem) p L -> garr8 SEGS (mrestrict (w_H W3) (ms_mem msX)) p L) end.
{ intros p sz L Hin Hct HL HG.
eapply (garr8_journal_block_x SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p sz p L HJ3);
[ exact Hin | apply Hsub3; exact Hin | clear; lia | clear - HL; lia
| intros a Ha; apply (fp0_off_tail B LAWS ly S W mem md f ctail p sz HAR HPc Hct); clear - Ha HL; lia
| exact HG ]. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
assert (XBIMG : garr8 SEGS (mrestrict (w_H W3) (ms_mem msX)) (fr_img fb) (YO07.f_img b)) end.
{ apply (XJ _ N _ Hbimg_in); [apply (Tfr (i - 1)%nat fb ltac:(clear - Hi; lia) Hfbe); right; left; reflexivity | rewrite XBlen; pose proof (req_size_pos' N ltac:(clear - HW1 HH1 HN; nia)) as [_ HrN]; exact HrN | exact XBimg]. }
assert (XL46 : forall a, Z.land a 4 <> 0 -> Z.land a 6 <> 0).
{ intros a Ha H6. apply Ha. replace 4 with (Z.land 6 4) by reflexivity. rewrite Z.land_assoc, H6. reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
assert (XDI : tout_XD B W3 (ms_mem msX) ly3 S3 sp1 pt (w * h) (YO07.cmp_pixel (gcfg_of s GPAL) cur b)
(cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb)) end.
{ lazymatch goal with |- tout_XD _ _ ?mX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
apply (tout_XD_model B W3 mX ly3 S3 sp1 pt (w * h) (gcfg_of s GPAL) cur b);
[ exact XCa | intros Hz; exact (XCct (XL46 _ Hz)) | exact XCn | exact XBa | intros Hz; exact (XBct (XL46 _ Hz)) | exact XBn | reflexivity | | | ] end.
- intros Hz. destruct (XClp Hz) as [G0 L0]. pose proof (req_size_pos' (3 * fr_nlp f) ltac:(clear - L0; lia)) as [_ Hrl].
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) _ _ HAR3 HPerm3 (Hclpal Hz)) as Hd. rewrite Hrq in Hd.
split; [apply (XJ _ _ _ (Hclpal Hz) (Tlp Hz)); [rewrite L0; exact Hrl | exact G0]|]. split; [rewrite L0; clear; lia|].
exists (3 * fr_nlp f). split; [apply Hsub3; exact (Hclpal Hz)|]. split; [rewrite L0; exact Hrl|]. rewrite L0. clear - Hd Hrl. lia.
- intros Hz. destruct (XBlp Hz) as [G0 L0]. pose proof (req_size_pos' (3 * fr_nlp fb) ltac:(clear - L0; lia)) as [_ Hrl].
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) _ _ HAR3 HPerm3 (Hblpal Hz)) as Hd. rewrite Hrq in Hd.
assert (Hct : In (fr_lpal fb, 3 * fr_nlp fb) ctail).
{ apply (Tfr (i - 1)%nat fb ltac:(clear - Hi; lia) Hfbe). unfold frame_blocks. right. right. destruct (Z.eqb_spec (Z.land (fr_attr fb) 1) 0); [exfalso; exact (Hz e) | left; reflexivity]. }
split; [apply (XJ _ _ _ (Hblpal Hz) Hct); [rewrite L0; exact Hrl | exact G0]|]. split; [rewrite L0; clear; lia|].
exists (3 * fr_nlp fb). split; [apply Hsub3; exact (Hblpal Hz)|]. split; [rewrite L0; exact Hrl|]. rewrite L0. clear - Hd Hrl. lia.
- intros Hor. assert (Hg4 : Z.land (cg_attr s) 4 = 0) by (destruct Hor as [H0 | H0]; [exact (Hfgp H0) | exact (Hbgp H0)]).
destruct (HGPAL Hg4) as [G0 L0]. pose proof (fl_gpal_block B ly S g s N rest HPerm Hg4) as Hgin.
pose proof (req_size_pos' (3 * cg_ngp s) ltac:(clear - L0; lia)) as [_ Hrl].
pose proof (sep_tmp_entry B LAWS _ _ _ _ _ _ pt (w * h) _ _ HAR3 HPerm3 Hgin) as Hd. rewrite Hrq in Hd.
cbn [gcfg_of YO07.g_gpal YO07.g_ngp].
split; [apply (XJ _ _ _ Hgin (Tgp Hg4)); [rewrite L0; exact Hrl | exact G0]|]. split; [rewrite L0; clear; lia|].
exists (3 * cg_ngp s). split; [apply Hsub3; exact Hgin|]. split; [rewrite L0; exact Hrl|]. rewrite L0. clear - Hd Hrl. lia. }
eapply SRr_bind.
{ pose proof (fl_toutX B LAWS TCMP (Z.to_nat h)) as TOUT. unfold tout_stmtX in TOUT.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (TOUT 0 W3 (ms_regs msX) (ms_mem msX) mdX (spZ regs) sp1 _ ly S W mem md ly3 S3 k fpos _ pt w h top left (cg_W s) (fr_img fb) N g (fr_ptr f) (fr_ptr fb) (bv_unsigned (ew E 741))
(xcgif_vals path hw pf s) (list_set (frame_vals f) 3 genC) (frame_vals fb) (cg_pal s) (cg_ngp s) (fr_lpal f) (fr_attr f) (fr_nlp f) (fr_ctidx f) (fr_lpal fb) (fr_attr fb) (fr_nlp fb) (fr_ctidx fb) (YO07.cmp_pixel (gcfg_of s GPAL) cur b)) end;
[ rewrite Z2Nat.id by (clear - Hh1 Hob241 Hob242 Hob253 Huar; lia); clear; lia | clear - Hh1 Hob241 Hob242 Hob253 Huar; lia | exact HCTX | exact HOUT | exact XDI
| first [rewrite Rr6, ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E32n | match goal with |- ?g => idtac "TO6" g end]
| first [exact Rr15 | rewrite Rr15; reflexivity | match goal with |- ?g => idtac "TO15" g end]
| first [rewrite Rr18; f_equal; clear; lia | match goal with |- ?g => idtac "TO18" g end]
| first [replace (pt + 0 * w) with pt by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite Rr19; first [exact E801 | exact F360 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E801] | match goal with |- ?g => idtac "TO19" g end]
| first [replace (pt + 0 * w) with pt by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite Rr24; first [exact E801 | exact F360 | rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E801] | match goal with |- ?g => idtac "TO24" g end]
| first [exact Rr20 | match goal with |- ?g => idtac "TO20" g end] ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HK5 & H65 & K5 & X5 & XV5).
assert (Hnz : pt <> 0) by (clear - Hnh; lia).
assert (XF1m : YO07.flag (YI0f.fl_gen3 (gcfg_of s GPAL) cur (Some b)) 1 = true) by exact XF1.
assert (XDm : YI0f.fl_dims (gcfg_of s GPAL) cur (Some b) = (w, h, top, left)) by exact XD.
assert (XLENm : Z.of_nat (length (YI0f.fl_tmp (gcfg_of s GPAL) cur (Some b))) = w * h) by exact XLEN.
assert (E741u : bv_unsigned (ew E 741) = tv) by (rewrite E741x; apply unsigned_lit_small; exact Rtv).
assert (XtvM : tv mod 256 = YI0f.fl_tOpt (gcfg_of s GPAL) cur) by exact Xtv.
destruct (window_specZ (cg_W s) (cg_H s) (YO07.f_img b) w h top left ltac:(clear - HW1; lia) ltac:(clear - HH1; lia) ltac:(rewrite XBlen; exact HN)
Hw1 Hl0 Hlw Hh1 Ht0 Hth) as [XWL _].
assert (XG5 : garr8 SEGS (mrestrict (w_H W3) mem5) pt (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur (Some b)))).
{ unfold ximg, xG. cbn [c_s x_GPAL x_cur x_bef]. rewrite (fl_img_trans _ cur b w h top left XF1m XDm), <- XtvM, <- E741u.
exact (toutV_garr8 _ _ (w_H W3) _ mem5 pt (fr_img fb) w h top left (cg_W s) (cg_H s) _ _ (XI Hnz) XLENm XBIMG ltac:(rewrite XBlen; exact HN)
ltac:(clear - HW1; lia) ltac:(clear - HH1; lia) Hw1 Hl0 Hlw Hh1 Ht0 Hth XV5). }
assert (XLEN5 : Z.of_nat (length (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur (Some b)))) = w * h).
{ unfold ximg, xG. cbn [c_s x_GPAL x_cur x_bef]. rewrite (fl_img_trans _ cur b w h top left XF1m XDm).
apply length_mark; [exact XLENm | exact XWL]. }
clear XI XLEN. assert (XI : pt <> 0 -> garr8 SEGS (mrestrict (w_H W3) mem5) pt (ximg (mkFLCX ly S W regs mem md ch g s N i f rest fpos sp1 wfn hw (as_uar_cell B) E0) (mkFLXX path pf Sg GPAL cur (Some b)))) by (intros _; exact XG5).
clear XG5.
clear Rra Rsp Rgp Rtp Rs0 Rr6 Rr9 Rr15 Rr19 Rr24 Rr21 Rr22 Rr26 Rr27 Rr18 Rr20 Vra Vs0 V176 V184 V192 V200 HCTX HOUT.
pose proof (proj1 HJ5) as HAR5.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR5 Hfin3) as (_ & _ & HFpres5 & HFSpres5).
change (fs_frame_bytes 2) with 256 in HFpres5, HFSpres5. change (256 / 8) with 32 in HFSpres5. rewrite !EFA3 in HFpres5, HFSpres5. fold F in HFpres5, HFSpres5.
aconstsF HJ5 Kgot5 Kcell5 Kguar5 Kuar5.
assert (HSpres5 : forall a, spZ regs - TFLUSH_STK <= a < spZ regs -> apresent (w_H W3) mem5 a) by (pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _); exact HSp).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let rs' := eval vm_compute in (trim_base (ss_mem ssx) 60 0 208) in
pose proof (st_ok_pi_submem Ev ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let rs' := eval vm_compute in (trim_base (ss_mem ssx) 60 0 208) in
pose proof (st_ok_submem SEGS Ev ssx (restrict (w_H W3) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H W3) mem5) TOUT_CLOB 0x22cc [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat HS2 | st_ok _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_keep_hi HS kk regs5 (mrestrict (w_H W3) mem5) TOUT_CLOB 0x22cc [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11]%nat HS2  end.
lazymatch type of HS2 with _ -> ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil
| specialize (HS2 HK5 HQ); clear HQ ] end.
all: try (idtac; first
[ lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact K5 | evalE AG | exact Hfin3
| right; unfold shadow_addr; rewrite EFA3, <- SB_SHADOW_OFF; fold F; change (fs_frame_bytes 2 / 8) with 32; unfold SB; clear; lia
| intros a Ha Hn; clear - Ha Hn Hnh HF8lo HF8c HFceil C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold SB in *; zone_lia
| intros a Ha; exfalso; clear - Ha Hob241 Hob242 Hob253 Huar; unfold SB in *; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj SEGS _); [exact K5 | evalE AG | exact Hfin3
| left; rewrite EFA3; fold F; change (fs_frame_bytes 2) with 256; clear; lia
| intros a Ha Hn; clear - Ha Hn HdPF Hob241 Hob242 Hob253 Huar; lia
| intros a Ha; apply (proj1 (HFpres5 a ltac:(clear - Ha Hob241 Hob242 Hob253 Huar; lia))) ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 60%nat) _ _ _ _ _) =>
eapply region_kept_eq; [evalE AG | intros a Ha; apply X5; clear - Ha Hob241 Hob242 Hob253 Huar; lia | intros a Ha; apply HSpres5; rewrite FFS; clear - Ha Hsp1 Hob241 Hob242 Hob253 Huar; lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 2%nat) _ _ _ _ _) =>
eapply (region_kept_stack_aj SEGS _); [exact K5 | exact HJ5 | evalE AG | clear - Hsp1 Hob241 Hob242 Hob253 Huar; lia | rewrite FFS; clear; lia | clear; lia | clear; lia | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (pa_val (A_OBJ 0)) 8 (pa_val (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kgot3 | exact Kgot5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) =>
let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (pa_val (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kcell3 | exact Kcell5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 242%nat) _ _ _ _ _) =>
let H := rnHEI Ex in let Bv := rnB in apply (region_kept_val_at Ex _ _ (A_OBJ 1) (pa_val (A_OBJ 1)) 8 (as_uar_cell Bv));
[exact (H (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact Kguar3 | exact Kguar5 | lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 59%nat) _ _ _ _ _) =>
let AGx := lazymatch goal with A : forall n, (n < 33)%nat -> ew _ n = ew _ n |- _ => A end in
let Bv := rnB in apply (region_kept_val_at Ex _ _ 59%nat (as_uar_cell Bv) 4 1); [evalE AGx | exact Kuar3 | exact Kuar5 | lia] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 10%nat) _ _ _ _ _) =>
eapply (region_kept_block_aj SEGS _); [exact K5 | evalE AG | exact Hing3 | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPG Hob241 Hob242 Hob253 Huar; lia ] end
| lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _) =>
eapply (region_kept_block_ajw2 SEGS B LAWS); [exact K5 | exact HAR5 | exact Hcur3 | evalE AG | exact Hcur3 | clear; lia | change (req_size FRAME_SIZE) with 40; clear; lia | clear; lia | clear; lia
| intros a Ha Hn; clear - Ha Hn HdPC Hob241 Hob242 Hob253 Huar; lia ] end
| match goal with |- region_kept _ _ _ _ ?r => idtac "KEPTFAIL" r end ]).
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. rebaseE HS AG HEv. clear HEv.
assert (HUP5 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W3) mem5 a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof K5 as (K51 & _). rewrite (K51 a) by (first [clear - Ha Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | clear - Ha Hsp1 Hob241 Hob242 Hob253 Huar; lia]). apply HUP. exact Ha. }
clear HUP. rename HUP5 into HUP.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?rt :: ?l2 =>
lazymatch rt with YP09.mkRegion (Some 60%nat) 0 208 0 208 ?cst =>
pose proof (st_ok_pi_region_nth Ev ssx msv 2 rt HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict mkst] in HRt;
unfold region_ok in HRt; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in HRt;
destruct HRt as (HRt1 & HRt2 & HRt3 & HRt4);
pose proof (ast_ok_replace_region Ev ssx msv [r0; r1] rt
(YP09.mkRegion (Some 60%nat) 0 280 0 280 (cst ++ [YP09.mkChunk 232 (CVal 8 (SOff 741 0)); YP09.mkChunk 240 (CVal 8 (SOff 32 0));
YP09.mkChunk 248 (CVal 8 (SOff 12 0)); YP09.mkChunk 272 (CVal 8 (SOff 516 0))])) l2
HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
lazymatch goal with |- context [base_val ?Ex (Some 60%nat)] =>
replace (base_val Ex (Some 60%nat)) with sp1 in HRt4 |- * by (cbn [base_val]; symmetry; evalE AG) end;
split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia|]; split; [clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply HSpres5; rewrite FFS; clear - Ho Hsp1 Hob241 Hob242 Hob253 Huar; lia|];
apply Forall_app; split; [exact HRt4|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 232 8 _ (bv_unsigned (ew E 741)));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E741, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (ew E 741)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V232] ]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 240 8 _ SB);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V240] ]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 248 8 _ (fr_ptr fb));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hbh1 Hbh2 C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V248] ]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 272 8 _ F);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V272] ]|];
apply Forall_nil)
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32;
unfold CGIF_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil Hob241 Hob242 Hob253 Huar;
repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end | st_ok _ ?Ev ?ssx ?msv =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with ?r0 :: ?r1 :: ?rt :: ?l2 =>
lazymatch rt with YP09.mkRegion (Some 60%nat) 0 208 0 208 ?cst =>
pose proof (st_ok_region_nth Ev ssx msv 2 rt HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict mkst] in HRt;
unfold region_ok in HRt; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in HRt;
destruct HRt as (HRt1 & HRt2 & HRt3 & HRt4);
pose proof (ast_ok_replace_region Ev ssx msv [r0; r1] rt
(YP09.mkRegion (Some 60%nat) 0 280 0 280 (cst ++ [YP09.mkChunk 232 (CVal 8 (SOff 741 0)); YP09.mkChunk 240 (CVal 8 (SOff 32 0));
YP09.mkChunk 248 (CVal 8 (SOff 12 0)); YP09.mkChunk 272 (CVal 8 (SOff 516 0))])) l2
HS eq_refl ltac:(vm_compute; reflexivity)
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
lazymatch goal with |- context [base_val ?Ex (Some 60%nat)] =>
replace (base_val Ex (Some 60%nat)) with sp1 in HRt4 |- * by (cbn [base_val]; symmetry; evalE AG) end;
split; [clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia|]; split; [clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply HSpres5; rewrite FFS; clear - Ho Hsp1 Hob241 Hob242 Hob253 Huar; lia|];
apply Forall_app; split; [exact HRt4|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 232 8 _ (bv_unsigned (ew E 741)));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite E741, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (ew E 741)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V232] ]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 240 8 _ SB);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V240] ]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 248 8 _ (fr_ptr fb));
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 12%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - Hbh1 Hbh2 C1 C3 Hob241 Hob242 Hob253 Huar; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V248] ]|];
apply Forall_cons; [apply (chunk_ok_val SEGS Ev _ sp1 272 8 _ F);
[cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite RF, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| clear - HF4096 HFceil C1 Hob241 Hob242 Hob253 Huar; zside | zside
| eapply val_mem_keptK; [exact K5 | clear - Hsp1 Hceil Hslo Hstk0 FFS C1 Hob241 Hob242 Hob253 Huar; lia | cbn [Z.of_nat]; clear - Hsp1 Hshi H47 Hob241 Hob242 Hob253 Huar; lia | left; cbn [Z.of_nat]; clear; lia | exact V272] ]|];
apply Forall_nil)
ltac:(cbn [all_disjoint app]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; change (fs_frame_bytes 2) with 256; change (fs_frame_bytes 2 / 8) with 32;
unfold CGIF_SIZE, SB;
clear - Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C2 C3 HF4096 HFceil HFhigh HF8lo HF8hi HF8c Hgh Hgceil Hcrh Hcceil Hob241 Hob242 Hob253 Huar;
repeat split; first [zone_lia | match goal with |- ?g => idtac "DISJ-FAIL" g end])) as HS3;
clear HS; rename HS3 into HS end end  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv 6%bv (SOff 32 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite H65; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev ?ssx ?msv =>
pose proof (st_ok_pin_rege Ev ssx msv 6%bv (SOff 32 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite H65; cbn [sv_denot]; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; rewrite (AG 32%nat) by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
relowF HS AG E10 E11 E32 E10n E11n E32n. reshok HS. clear_frames.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ5 SHOK FLBspan 0x22f0.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrFL AG fpos F EFA3.
xpt_stretch.
upd_aboveF HUP HFr AG ltac:(fun Hb Hrg => clear - Hb Hrg Hsp1 HFceil Hceil Hslo Hstk0 FFS C1 Hgceil Hcceil HF8hi Hob241 Hob242 Hob253 Huar; lia). clear_frames.
rebase_goal.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
prreg HS (23%bv : bv 5) Q23; prreg HS (27%bv : bv 5) Q27;
add_atom HS 839%nat (sv_denot Ev (SOff 679 0)) E839;
rechunk_off HS 60%nat 168 (SOff 839 0) ltac:(rewrite sv_denot_SOff0, E839; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 840%nat (sv_denot Ev (SOff 680 0)) E840;
rechunk_off HS 60%nat 144 (SOff 840 0) ltac:(rewrite sv_denot_SOff0, E840; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 841%nat (sv_denot Ev (SOff 681 0)) E841;
rechunk_off HS 60%nat 152 (SOff 841 0) ltac:(rewrite sv_denot_SOff0, E841; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ ?Ev _ _ |- _ =>
add_atom HS 842%nat (sv_denot Ev (SOff 741 0)) E842;
rechunk_off HS 60%nat 232 (SOff 842 0) ltac:(rewrite sv_denot_SOff0, E842; cbn [sv_denot]; rewrite ?ew_havoc_old by lia; reflexivity) end.
lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
ra_join HS ss_R 843%nat fl_R_deads_bv ltac:(idtac;
ra_join_val HS 843%nat 0%nat Q23 E843; ra_join_val HS 843%nat 2%nat Q27 E845;
ra_join_fact HS 839%nat (mkAF 1 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E839; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E683, unsigned_lit_small by (clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia); clear - Hw1 Hlw Hl0 R7 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 840%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E840; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E685, unsigned_lit_small by (clear - Hl0 Hlw Hw1 R7 Hob241 Hob242 Hob253 Huar; lia); clear - Hl0 Hlw Hw1 R7 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 841%nat (mkAF 0 65535 0) ltac:(rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E841; rewrite Z.pow_0_r, Z.mod_1_r; rewrite sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E681, unsigned_lit_small by (clear - Ht0 Hth Hh1 R8 Hob241 Hob242 Hob253 Huar; lia); clear - Ht0 Hth Hh1 R8 Hob241 Hob242 Hob253 Huar; lia);
ra_join_fact HS 845%nat (mkAF 1 65535 0) ltac:(rewrite E845; rewrite Z.pow_0_r, Z.mod_1_r; rewrite E684, unsigned_lit_small by (clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia); clear - Hh1 Hth Ht0 R8 Hob241 Hob242 Hob253 Huar; lia));
fl_handX RR HS end.
split; [exists gen; split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption | exact Rgen]|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); assumption|].
split; [| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E621X].
exists pt, w, h, top, left, (bv_unsigned (ew E 741)). cbn [c_s c_ly c_S].
split; [rewrite E843; exact E801|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E839, sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E683|].
split; [rewrite E845; exact E684|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E841, sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E681|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E840, sv_denot_SOff0; rewrite ?ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); exact E685|].
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO Hob241 Hob242 Hob253 Huar; lia); rewrite E842, sv_denot_SOff0; rewrite ?ew_ewset_other, ?ew_havoc_old by nat_side; exact E741|].
split; [clear - Hnh Hpce Hwh0 Hob241 Hob242 Hob253 Huar; ceil; lia|].
split; [exact Hw1|]. split; [exact Hl0|]. split; [exact Hlw|]. split; [exact Hh1|]. split; [exact Ht0|]. split; [exact Hth|].
split; [pose proof (bv_unsigned_in_range 64 (ew E 741)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq|].
split. { right. split; [clear - Hnh Hob241 Hob242 Hob253 Huar; lia|]. split; [exact Hk2 | exact Htb0]. }
split; [exact XD|].
split; [rewrite E741u; unfold xtidx, xG; cbn [c_s x_GPAL x_cur x_bef]; rewrite (fl_tidx_trans _ cur b XF1m); exact XtvM|].
split; [exact XI|]. split; [intros Hp0; exfalso; exact (Hnz Hp0)|]. split; [exact XLEN5|].
unfold xmacc. rewrite (proj2 (Z.eqb_neq pt 0) Hnz). exact XMLE.
Qed.
Lemma fl_T3X : fl_fromX0 KS MT XN B CTX wfn ss_R (INV_RX MT B) -> fl_fromX0 KS MT XN B CTX wfn ss_T3 (INV_T3X MT B).
Proof. exact fl_T3X_aux. Qed.
End q.
End l.
End d.
