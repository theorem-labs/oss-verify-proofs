(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the proofs of lib/A/PresetPinvA.v's statements, made from the proofs of
   proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v, AD1v.v:31-71, AD1w.v:181-197 and AD2k.v:58-173 with FINV replaced by
   PINV (lib/A/PresetCfnA.v). Nothing here proves a function (rule 24: composition / driver layer of a port).
   The image facts are decided by vm_compute over the cell list PINV_IVS: the cells lie in the image hull, avoid the
   unit's owned statics, errno and the driver's write windows, and the start-up certificate knows each of them at its
   image value. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetPinvAPf.v, with its module paths and module names changed; 93 of its 267 lines of code are new or changed and 53 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the proofs of lib/A/PresetPinvA.v's statements, made from the proofs of
   proofs/cgif/cgif_file_fuzzer/lib/A/AD1u.v, AD1v.v:31-71, AD1w.v:181-197 and AD2k.v:58-173 with FINV replaced by
   PINV (lib/A/PresetCfnA.v). Nothing here proves a function (rule 24: composition / driver layer of a port).
   The image facts are decided by vm_compute over the cell list PINV_IVS: the cells lie in the image hull, avoid the
   unit's owned statics, errno and the driver's write windows, and the start-up certificate knows each of them at its
   image value. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AD2i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AD1y AD1v AD1w AD2f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PresetCfnA PresetPinvA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

Local Notation segs := tfibsegs.

(* ---------------------------------------------------------------------- *)
(* 1. The cell facts (donor AD1u.v:91-125), decided over PINV_IVS. *)
Lemma PINV_IVS_img : forallb (fun iv => (YImgTop.IMG_LO <=? fst iv) && (snd iv <=? YImgTop.IMG_TOP))%bool PINV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PINV_IVS_unowned : forallb (fun iv => forallb (AD1y.ext_avoids (fst iv) (snd iv)) Tfib_owned_static) PINV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PINV_IVS_drvw : forallb (fun d => pinv_ivs_avoid (fst d) (snd d)) AD1y.DRV_IVS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PINV_IVS_errno : pinv_ivs_avoid TFIB_ERRNO (TFIB_ERRNO + 4) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem finv_img_range_pinv_A_holds : finv_img_range_pinv_A.
Proof.
intros a Hf. destruct (pinv_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) PINV_IVS_img (l, h) Hin) as X. cbn [fst snd] in X. apply andb_prop in X as [X1 X2].
apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

(* The image bounds of a cell, as numerals for lia (from the generated names YImgTop.IMG_LO / IMG_TOP). *)
Ltac img_bounds a Ha := let R := fresh "R" in
pose proof (finv_img_range_pinv_A_holds a Ha) as R; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in R.

Theorem finv_img_img_pinv_A_holds : finv_img_img_pinv_A.
Proof. intros a Ha. apply AD1y.in_img_hull. img_bounds a Ha. lia. Qed.

Theorem finv_img_not_owned_pinv_A_holds : finv_img_not_owned_pinv_A.
Proof.
intros B HB a Ha. destruct (pinv_img_ivs a Ha) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) PINV_IVS_unowned (l, h) Hin) as X. cbn [fst snd] in X.
rewrite (ts_owned B HB). exact (AD1y.ext_avoids_sound l h _ a X Hlh).
Qed.

Theorem finv_img_not_drvw_pinv_A_holds : finv_img_not_drvw_pinv_A.
Proof.
intros a Ha Hw. unfold AD1y.DRVW in Hw. apply existsb_exists in Hw as (d & Hd & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (forallb_forall _ _) PINV_IVS_drvw d Hd) as X. exact (pinv_ivs_avoid_sound (fst d) (snd d) a X ltac:(lia) Ha).
Qed.

Theorem finv_img_not_errno_pinv_A_holds : finv_img_not_errno_pinv_A.
Proof. intros B HB a Ha He. rewrite (ts_errno B HB) in He. exact (pinv_ivs_avoid_sound _ _ a PINV_IVS_errno He Ha). Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The frame lemmas. *)
Theorem finv_frame_pinv_A_holds : finv_frame_pinv_A.
Proof. intros H H' mem mem' cnt ran Hfr. exact (pinv_frame_view segs H H' mem mem' cnt ran Hfr). Qed.

Theorem finv_aview_pinv_A_holds : finv_aview_pinv_A.
Proof. intros H H' mem mem' cnt ran Hfr. apply pinv_frame. intros a Ha. exact (Hfr a Ha). Qed.

Theorem finv_stretch_pinv_A_holds : finv_stretch_pinv_A.
Proof.
intros H E rs m m' usp cnt ran HF Hok E0 Husp HFI. apply (finv_frame_pinv_A_holds H H m m' cnt ran); [|exact HFI].
intros a Ha. img_bounds a Ha.
unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. intros Hw.
apply (AD1y.in_wrange_drv E rs) in Hw; [|exact Hok]. rewrite E0 in Hw. rewrite u64_lit in Hw by lia.
destruct Hw as [Hw|Hw]; [unfold sp_window_lo in Husp; lia | exact (finv_img_not_drvw_pinv_A_holds a Ha Hw)].
Qed.

Theorem finv_off_pinv_A_holds : finv_off_pinv_A.
Proof.
intros H mem mem' X1 X2 cnt ran Hfr HX HF. apply (finv_aview_pinv_A_holds H H mem mem' cnt ran); [|exact HF].
intros a Ha. destruct (HX a Ha) as [H1 H2]. apply Hfr; [|exact H1|exact H2].
img_bounds a Ha. lia.
Qed.

Theorem finv_avoids_stack_pinv_A_holds : finv_avoids_stack_pinv_A.
Proof. intros lo hi a H24 Ha Hr. img_bounds a Ha. lia. Qed.

Theorem finv_avoids_img_pinv_A_holds : finv_avoids_img_pinv_A.
Proof. intros lo hi a Hc Ha Hr. exact (pinv_ivs_avoid_sound lo hi a Hc Hr Ha). Qed.

Theorem finv_fp_u64_pinv_A_holds : finv_fp_u64_pinv_A.
Proof. intros a Ha. img_bounds a Ha. lia. Qed.

Theorem finv_img_write_pinv_A_holds : finv_img_write_pinv_A.
Proof.
intros H m m' lo hi cnt ran Hout Hc HF. apply (finv_frame_pinv_A_holds H H m m' cnt ran); [|exact HF].
intros a Ha. pose proof (finv_fp_u64_pinv_A_holds a Ha) as Hr.
pose proof (finv_avoids_img_pinv_A_holds lo hi a Hc Ha) as Hna.
unfold mbyte, mrestrict. rewrite (Hout (Z_to_bv 64 a)) by (rewrite u64_lit by exact Hr; lia). reflexivity.
Qed.

Theorem finv_run_pinv_A_holds : finv_run_pinv_A.
Proof. exact finv_stretch_pinv_A_holds. Qed.

Theorem finv_printf_pinv_A_holds : finv_printf_pinv_A.
Proof.
intros H mem mem' usp splo cnt ran Ulo Hsplo Hfr HFI.
apply (finv_off_pinv_A_holds H mem mem' (fun a => splo - PF_STK <= a < splo) STDOUT_MUT cnt ran Hfr); [|exact HFI].
intros a Ha. split.
- apply (finv_avoids_stack_pinv_A_holds (splo - PF_STK) splo a); [unfold sp_window_lo, PF_STK in *; lia | exact Ha].
- intros [Hso | Hso]; revert Hso.
+ apply (finv_avoids_img_pinv_A_holds STDOUT_LO STDOUT_HI a); [vm_compute; reflexivity | exact Ha].
+ apply (finv_avoids_img_pinv_A_holds SOBUF_LO SOBUF_HI a); [vm_compute; reflexivity | exact Ha].
Qed.

(* Over ARcf. *)
Theorem finv_avoids_block_pinv_A_holds : finv_avoids_block_pinv_A.
Proof.
intros fx rc ci cp B ARL ly S Hp W mem md p n a HAR Hin Ha Hpa.
exact (proj2 (alc_client_img _ _ ARL ly S Hp W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa)))))
(finv_img_img_pinv_A_holds a Ha)).
Qed.

Theorem finv_acall_post_pinv_A_holds : finv_acall_post_pinv_A.
Proof.
intros fx rc ci cp B HB ARL stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' cnt ran HAR HP HE Hlo Hhi H24 HFI.
destruct HP as (HAR' & Hle & Hwle & Hregs & Hio & Hfr & Hpres).
apply (finv_aview_pinv_A_holds (w_H W) (w_H W') mem mem' cnt ran); [|exact HFI].
intros a Ha. img_bounds a Ha.
pose proof (finv_img_img_pinv_A_holds a Ha) as Hi. pose proof (finv_img_not_owned_pinv_A_holds B HB a Ha) as Hns.
apply Hfr; [lia | | | |].
- intros Ho. exact (Hns (proj1 (alc_owned_image _ _ ARL ly S Hp W mem md a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (alc_owned_image _ _ ARL ly' S' Hp W' mem' md' a HAR' Hi) Ho)).
- unfold ascratch. intros [Hsc | Her]; [lia | exact (finv_img_not_errno_pinv_A_holds B HB a Ha Her)].
- intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | [(p & n & Hin & Hpa) | Hno]].
+ exact (proj2 (alc_client_img _ _ ARL ly S Hp W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
+ exact (proj2 (alc_client_img _ _ ARL ly' S' Hp W' mem' md' a HAR' (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
+ exact (Hno Hi).
Qed.

Theorem finv_site_pinv_A_holds : finv_site_pinv_A.
Proof.
intros fx rc ci cp B HB ARL stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' usp cnt ran HAR HP HE
(_ & Hlo & Hhi & HCT) Ulo Uhi Hsp Hstk HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
apply (finv_acall_post_pinv_A_holds fx rc ci cp B HB ARL stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' cnt ran
HAR HP HE); [| | | exact HFI].
- rewrite Hlo. unfold ASAN_CEIL, stack_max_size in *. lia.
- rewrite Hhi. unfold kHighMemEnd, sp_window_hi in *. lia.
- unfold sp_window_lo in *. lia.
Qed.

(* the same under the re-hide: finv_acall_post_pinv_A_holds' proof at the primed post, whose one more frame exception
   (the set the call may hide) lies above kLowMemEnd (YGcfRehidePost.dead_shadow_new_not_low), off the ledger cells *)
Theorem finv_site_pinv_rh_A_holds : finv_site_pinv_rh_A.
Proof.
intros fx rc ci cp B HB ARL stk ly S Hp W regs mem md E ly' S' W' regs' mem' md' usp cnt ran HAR HP HE
(_ & Hlo & Hhi & HCT) Ulo Uhi Hsp Hstk HFI.
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
assert (H24 : 2 ^ 24 <= spZ regs - stk) by (unfold sp_window_lo in *; lia).
destruct HP as (HAR' & Hle & Hwle & Hregs & Hio & Hfr & Hpres).
apply (finv_aview_pinv_A_holds (w_H W) (w_H W') mem mem' cnt ran); [|exact HFI].
intros a Ha. img_bounds a Ha.
pose proof (finv_img_img_pinv_A_holds a Ha) as Hi. pose proof (finv_img_not_owned_pinv_A_holds B HB a Ha) as Hns.
apply Hfr; [lia | | | | |].
- intros Ho. exact (Hns (proj1 (alc_owned_image _ _ ARL ly S Hp W mem md a HAR Hi) Ho)).
- intros Ho. exact (Hns (proj1 (alc_owned_image _ _ ARL ly' S' Hp W' mem' md' a HAR' Hi) Ho)).
- unfold ascratch. intros [Hsc | Her]; [lia | exact (finv_img_not_errno_pinv_A_holds B HB a Ha Her)].
- intros Ea. destruct (HE a Ea) as [(p & n & Hin & Hpa) | [(p & n & Hin & Hpa) | Hno]].
+ exact (proj2 (alc_client_img _ _ ARL ly S Hp W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
+ exact (proj2 (alc_client_img _ _ ARL ly' S' Hp W' mem' md' a HAR' (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa))))) Hi).
+ exact (Hno Hi).
- intros X. pose proof (YGcfRehidePost.dead_shadow_new_not_low ly S S' a X) as NL. unfold kLowMemEnd in NL. lia.
Qed.

Theorem finv_icpt_pinv_A_holds : finv_icpt_pinv_A.
Proof.
intros fx rc ci cp B HB ARL ly S Hp W mem md mem' P lo hi usp cnt ran HAR _ Ulo Uhi Hfr Hl Hh HP HFI.
apply (finv_off_pinv_A_holds (w_H W) mem mem' P (fun a => lo <= a < hi) cnt ran Hfr); [|exact HFI].
intros a Ha. split.
- intros HPa. destruct (HP a HPa) as (p0 & n0 & Hin & Hpa).
exact (finv_avoids_block_pinv_A_holds fx rc ci cp B ARL ly S Hp W mem md p0 n0 a HAR Hin Ha Hpa).
- apply (finv_avoids_stack_pinv_A_holds lo hi a); [unfold sp_window_lo in *; lia | exact Ha].
Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The start-up handoff (donor AD2k.v:58-70, 113-174). The start-up certificate knows each PINV cell at its start
      value: kn_read (lib/Reusable/YA0j.v:23) reads it as the literal of PINV_CELLS, whatever form the certificate
      gives it (KImg for the image bytes, KZero for .bss, KWord). ho_read_byte turns that into the bytes of the
      start-up reader, and AD2i.v's MR -> m1 transfer into the bytes of the start-up world.
      The cells are the interface's ONE list PINV_IVS (lib/A/PresetCfnA.v), each with its width; the start value is
      the image value: g_fail_at = SIZE_MAX and, on the #102 pins, g_most = SIZE_MAX (both .data: alloc.c
      `g_fail_at = SIZE_MAX, g_most = SIZE_MAX`; A' 0xa65c0 / 0xa65e0 hold ff x 8), every other cell 0 (.bss,
      g_own_ran_out included). A re-pin regenerates PINV_IVS only. *)
Definition cell_start (a : Z) : Z := if (a =? G_FAIL_AT) || (a =? G_MOST) then SIZE_MAX else 0.
Definition PINV_CELLS : list (Z * nat * Z) :=
map (fun iv => (fst iv, Z.to_nat (snd iv - fst iv), cell_start (fst iv))) PINV_IVS.
(* A cell is known when the certificate holds it as image bytes (KImg, inside the image hull) or reads it as its
   literal start value. *)
Definition cell_known (ch : acs) (c : Z * nat * Z) : bool :=
let '(a, n, v) := c in
((kn_img ch a (Z.of_nat n) && (YImgTop.IMG_LO <=? a) && (a + Z.of_nat n <=? YImgTop.IMG_TOP))
|| match kn_read TSEGS ch (ELit 0) a n with Some e => expr_eqb e (ELit v) | None => false end)%bool.
(* The image bytes of each cell are its start value (decided over the image segments). *)
Definition img_cell_ok (c : Z * nat * Z) : bool :=
let '(a, n, v) := c in
forallb (fun k => match seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) with
| Some b => (bv_unsigned b =? le_byte v n k) | None => false end) (seq 0 n).
Lemma PINV_CELLS_img : forallb img_cell_ok PINV_CELLS = true.
Proof. vm_compute. reflexivity. Qed.
Definition pinv_check (ch : acs) : bool := forallb (cell_known ch) PINV_CELLS.
Lemma pinv_check_all : forallb pinv_check HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma PINV_CELLS_ok : forallb (fun c => let '(a, n, v) := c in
((0 <=? a) && (0 <=? v) && (v <? 2 ^ (8 * Z.of_nat n)) && (v <? 2 ^ 64))%bool) PINV_CELLS = true.
Proof. vm_compute. reflexivity. Qed.
Ltac in_cells := unfold PINV_CELLS, PINV_IVS, cell_start; vm_compute; repeat (first [left; reflexivity | right]).

Section c. Context {fx : YK11.FPState}.
Section e.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Let MRm1 := AD2i.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model.

(* AD2k.v:71-82, with the image bounds by their generated names. *)
Lemma pinv_img_byte : forall a len, kn_img ch a len = true -> forall i, a <= i < a + len ->
YImgTop.IMG_LO <= a -> a + len <= YImgTop.IMG_TOP ->
mbyte tfibsegs (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL) i = seg_rom tfibsegs (Z_to_bv 64 i) /\
seg_rom tfibsegs (Z_to_bv 64 i) <> None.
Proof.
intros a len H i Hi Hlo Hhi. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hlo, Hhi. unfold kn_img in H. apply existsb_exists in H as (K & HK & HKb).
destruct K as [| | |lo hi| | | | | |]; try discriminate HKb. apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
pose proof (Hnone i ltac:(lia)) as X.
pose proof (tfib_rom_all i ltac:(lia)) as Hrom. change AB1v.tfibsegs with tfibsegs in Hrom.
split; [|exact Hrom].
destruct (seg_rom tfibsegs (Z_to_bv 64 i)) as [b|] eqn:Hs; [|exfalso; exact (Hrom eq_refl)].
change tfibsegs with TSEGS. apply MRm1. unfold mbyte. rewrite X. exact Hs.
Qed.

Lemma cell_rd : forall a n v, In (a, n, v) PINV_CELLS -> forall k, (k < n)%nat ->
aview tfibsegs (AD2i.H1 sp rdraw inp ch E model) FULL (a + Z.of_nat k) = Some (le_byte v n k).
Proof.
intros a n v Hin k Hkn.
pose proof (proj1 (forallb_forall _ _) pinv_check_all ch (HS_tfib_In h ch Hch)) as K. unfold pinv_check in K.
pose proof (proj1 (forallb_forall _ _) K _ Hin) as Hk. unfold cell_known in Hk. cbn beta iota in Hk.
pose proof (proj1 (forallb_forall _ _) PINV_CELLS_ok _ Hin) as Hok. cbn beta iota in Hok.
apply andb_prop in Hok as [Hok Hv64]. apply andb_prop in Hok as [Hok Hvn]. apply andb_prop in Hok as [Ha Hv0].
apply Z.leb_le in Ha. apply Z.leb_le in Hv0. apply Z.ltb_lt in Hvn. apply Z.ltb_lt in Hv64.
apply orb_prop in Hk as [Hk | Hk].
{ apply andb_prop in Hk as [Hk Hhi]. apply andb_prop in Hk as [Hk Hlo]. apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
pose proof (proj1 (forallb_forall _ _) PINV_CELLS_img _ Hin) as Hi. cbn beta iota in Hi.
pose proof (proj1 (forallb_forall _ _) Hi k (proj2 (in_seq n 0 k) ltac:(lia))) as Hb. cbn beta in Hb.
unfold aview. rewrite (proj1 (pinv_img_byte a (Z.of_nat n) Hk (a + Z.of_nat k) ltac:(lia) Hlo Hhi)).
revert Hb. destruct (seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; intros Hb; [|discriminate Hb].
apply Z.eqb_eq in Hb. cbn [option_map]. rewrite Hb. reflexivity. }
destruct (kn_read TSEGS ch (ELit 0) a n) as [e|] eqn:Hr; [|discriminate Hk]. apply expr_eqb_eq in Hk. subst e.
pose proof (ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (ELit 0) a n (ELit v) Hr k Hkn) as X.
rewrite uE_litv in X by lia. rewrite uE_litv in X by lia. rewrite Z.add_0_l in X.
destruct (AD2i.hreader_mbyte sp rdraw inp ch E FULL model _ _ X) as (b & Hb & Hbu).
unfold aview. change tfibsegs with TSEGS. rewrite (MRm1 _ _ Hb). cbn [option_map]. f_equal. rewrite Hbu.
unfold le_byte. rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat n))) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Theorem pinv_handoff_at : PINV (aview tfibsegs (AD2i.H1 sp rdraw inp ch E model) FULL) 0 0.
Proof.
unfold PINV, ledger_rest, pinv_stdio, rd64, rd32, rd8.
split; [split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]] | split; [|split; [|split]]].
- intros k Hk. exact (cell_rd G_LIVE 8 0 ltac:(in_cells) k Hk).
- exists 0. split; [lia|]. intros k Hk. exact (cell_rd G_PEAK 8 0 ltac:(in_cells) k Hk).
- lia.
- intros k Hk. exact (cell_rd G_COUNT 8 0 ltac:(in_cells) k Hk).
- intros k Hk. exact (cell_rd G_FAIL_AT 8 SIZE_MAX ltac:(in_cells) k Hk).
- left. reflexivity.
- intros k Hk. exact (cell_rd G_RAN_OUT 1 0 ltac:(in_cells) k Hk).
(* #102: the two new ledger cells at their start values (PresetCfnA.v ledger_rest) *)
- exists SIZE_MAX. split; [unfold SIZE_MAX; lia|]. intros k Hk. exact (cell_rd G_MOST 8 SIZE_MAX ltac:(in_cells) k Hk).
- exists 0. split; [left; reflexivity|]. intros k Hk. exact (cell_rd G_OWN_RAN_OUT 1 0 ltac:(in_cells) k Hk).
- pose proof (cell_rd A_THREADED 1 0 ltac:(in_cells) 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
rewrite Z.add_0_r in X. rewrite X. reflexivity.
- pose proof (cell_rd A_NEED_LOCKS 1 0 ltac:(in_cells) 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
rewrite Z.add_0_r in X. rewrite X. reflexivity.
- intros k Hk. exact (cell_rd A_OFL_LOCK 4 0 ltac:(in_cells) k Hk).
- intros k Hk. exact (cell_rd A_OFL_HEAD 8 0 ltac:(in_cells) k Hk).
Qed.
End e.
End c.

Theorem tfib_finv_handoff_pinv_A_holds : tfib_finv_handoff_pinv_A.
Proof.
intros fx rc sp rdraw brk inp Hsp Hva h ch E R FULL model H8 Hch HC.
exact (pinv_handoff_at sp rdraw brk inp Hsp Hva h ch E R FULL model Hch HC).
Qed.
