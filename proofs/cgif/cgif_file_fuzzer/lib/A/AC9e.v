(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbw YCbx.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC81 YC4b YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AC93 AC9g AC95 AC91 AC99 AC92 AC9b AC9c AC9d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_SW_RET : Z := 0x1d44.
Lemma val_mem_zero2 : forall H (m : word -> option byte) a,
(forall i, 0 <= i < 2 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 2 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA AS_asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Hypothesis HUL : forall t, In t (lzw_traces (as_code B) BASE) -> In t (as_universe B).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma mbyte_zero_of_aview : forall H (m : word -> option byte) a,
aview SEGS H m a = Some 0 -> mbyte SEGS (mrestrict H m) a = Some (Z_to_bv 8 0).
Proof.
intros H m a Hz. destruct (aview_byte SEGS H m a 0 Hz) as (b & Hb & Hv & _). rewrite Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Z.mod_0_l by (vm_compute; discriminate). lia.
Qed.
Lemma U_sw_dest : forall E tm mp idl,
ew E 57 = Z_to_bv 64 tm -> ew E 35 = Z_to_bv 64 mp -> ew E 25 = Z_to_bv 64 idl ->
1 <= mp <= 2048 -> 0 <= idl <= 256 -> 0 <= tm -> tm + 2 * ((mp - 1) * idl) < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SLL (SMdw M_MUL (SOff 35 (-1)) (SOff 25 0)) (SLit 1))) = tm + 2 * ((mp - 1) * idl).
Proof.
intros E tm mp idl H1 H35 H25 Hmp Hidl Htm Hhi.
assert (Hp : 0 <= (mp - 1) * idl <= 2047 * 256) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg; lia]).
apply (U_add_small E); [apply (U_atom E 57 tm H1); lia | | lia | lia | lia].
apply (U_sll1_small E); [apply (U_mulw_row E 35 25 mp idl H35 H25); lia | lia | lia].
Qed.
Lemma tmiss_sw : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q c,
tmiss_hyps B cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c -> la_dp X < 4096 -> nth (Z.to_nat q) (la_LM X) 0 = 0 ->
nth (Z.to_nat q) (la_LI X) 0 <> 0 -> z_gp cx = as_gp B -> z_tp cx = as_tp B ->
SRr SEGS W7 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)) mdT)
(tmiss_tail_post B cx lyc Sc W memc mdc ly7 S7 W7 memT X s1).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q c
(HCX & HRG & HSEP & (HBg & HBi & HBt) & HTOK & HJ & HFC & HG & HSL & HSS & HFR & HT & HI & HPRE & Hs1 & Hq & Hc & HCpix & HS48) Hdp HLM HLI Hzgp Hztp.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
destruct (tmiss_seed B LAWS cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c
HCX HRG HSEP (conj HBg (conj HBi HBt)) HJ HFC HG HSL HSS HFR HT HI HPRE Hs1 Hq Hc HCpix HS48)
as (E & more & HE0 & HS & HENV & Hmap & Hsw & Hfirst & _). assert (HEI : img_env VAL A_LIM E) by (rewrite HE0; apply Eimg_env).
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
assert (Hmc : mc_of dp vLM vLI = MC_sw).
{ unfold mc_of. replace (dp =? 4096) with false by (symmetry; apply Z.eqb_neq; lia).
fold vLM in HLM. fold vLI in HLI. rewrite (proj2 (Z.eqb_eq _ _) HLM). replace (vLI =? 0) with false by (symmetry; apply Z.eqb_neq; exact HLI). reflexivity. }
rewrite Hmc in HS, HENV, Hmap, Hsw, Hfirst. cbn [tmiss_J is_map is_sw is_first] in HENV, Hmap, Hsw, Hfirst.
destruct HENV as (HE2 & HE8 & HE27 & HE25 & HE53 & HE54 & HE56 & HE55 & HE57 & HE59 & HE58 & HE32 & HE33 & HE34 & HE35 & HE37 & HE23 & HE15 & HE71 & HE72 & HE73 &
HE60 & HE64 & HE65 & HE66 & HE68 & HE69 & HE3 & HE4 & HE70 & HE5 & HE24).
specialize (Hsw eq_refl). destruct Hsw as (Hrow0 & _ & HJsz & Hrow1 & _ & _ & _). clear Hmap Hfirst.
remember ((mp - 1) * z_idl cx + c) as J eqn:HJdef.
miss_prep B cx HCX HRG HBt HTOK HJ.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp' & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
destruct (LI_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI. fold vLI in HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM. fold vLM in HvLM.
destruct HT as (ATI & ALM & ALI & ATM).
unfold z_tisz, z_tmsz in *.
Local Ltac tm_sep HSEP :=
match goal with
| |- context [z_ctx _] => septac HSEP 5%nat 6%nat
| |- context [z_ld _] => septac HSEP 0%nat 5%nat
| |- context [z_li _] => septac HSEP 4%nat 5%nat
| |- context [z_lm _] => septac HSEP 2%nat 5%nat
| |- context [z_lc _] => septac HSEP 3%nat 5%nat
| |- context [z_ti _] => septac HSEP 1%nat 5%nat
| |- context [z_img _] => septac HSEP 5%nat 7%nat
| _ => idtac
end; lia.
assert (Hrow2 : 2 * ((mp - 1) * z_idl cx) + 2 * z_idl cx <= 4098 * z_idl cx) by lia.
set (m := mrestrict (w_H W7) memT) in *.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 (BASE + PC_MISS)) memT (seg_rom SEGS))) in HJ.
unfold ss_tmiss in HS. cbn [is_sw is_map is_first is_full tmiss_regions tmiss_facts tmiss_conds tmiss_alias app orb] in HS.
paj_run_tok RUN HS HJ SHOK Bspan; try (oblk HJ HBld HE60 HE27 (z_ld cx + 2 * lp)); try (oblk HJ HBg HE8 HE27 (z_ctx cx));
try (oblk HJ HBi HE70 HE27 (z_img cx + s1)); try (oblk HJ HBlm HE65 HE27 (z_lm cx + 2 * q)); try (oblk HJ HBli HE64 HE27 (z_li cx + 2 * q)).
{ awr_tmp 8%nat (z_ctx cx) HE8 Actx HBg.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 65%nat (z_lm cx + 2 * q) HE65 Alm HBlm. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
hout HFr E m [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (z_lm cx + 2 * q, z_lm cx + 2 * q + 2); (0, 0); (0, 0)].
rename Hout into Hout1. clear HF.
remember ((mp - 1) * z_idl cx) as P eqn:HPdef.
rregU HS (10%bv : bv 5) (z_tm cx + 2 * P)
ltac:(rewrite HPdef; apply (U_sw_dest _ (z_tm cx) mp (z_idl cx)); [eatom AG HE57 | eatom AG HE35 | eatom AG HE25 | lia | lia | lia | lia]) Ra0.
prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
idtac.
try match goal with H : mem_grows _ _ |- _ => clear H end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS_asan_memset) AMEMSET _ (ms_regs msX) (ms_mem msX) _ _ _ lyc Sc W memc mdc _
ly7 S7 _ 7 (z_tm cx + 2 * P) 0 (2 * z_idl cx) (-320) (Z_to_bv 64 (BASE + A_SW_RET)) HJ) end.
- exact Ra0.
- rewrite Ra1. reflexivity.
- rewrite Ra2, HE37. reflexivity.
- lia.
- lia.
- lia.
- unfold spZ. rewrite Rsp, HE2, unsigned_lit_small by lia. lia.
- reflexivity.
- lia.
- unfold ESTACK. lia.
- rewrite Rgp, HE3, Hzgp. reflexivity.
- rewrite Rtp, HE4, Hztp. reflexivity.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [replace a with (z_tm cx + (a - z_tm cx)) by lia; apply Atm; [exact HBtm | lia] | unfold ESTACK; lia].
- eapply (amem_range_of_block SEGS B LAWS ly7 S7 _ _ _ (z_tm cx) (4098 * z_idl cx) _ _ (proj1 HJ) HBtm); lia.
- eapply (range_addressable_of_block SEGS B LAWS ly7 S7 _ _ _ (z_tm cx) (4098 * z_idl cx) _ _ (proj1 HJ) HBtm); lia.
- intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS ly7 S7 _ _ _ (z_tm cx) (4098 * z_idl cx) _ _ (proj1 HJ) HBtm); lia.
- exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr & Hpres2).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6]%nat AG
ltac:(eapply region_kept_aview;
[ cbn [ew ewset Nat.eqb]; repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- context [ew ?Ex ?n] => rewrite H end;
rewrite unsigned_lit_small by lia; reflexivity
| intros a Ha; cbn in Ha; apply Hfr; [lia | revert Ha; tm_sep HSEP | unfold ESTACK; lia]
| exact Hpres2 ]).
lazymatch type of AG with forall n, _ -> ew ?Ev n = _ =>
assert (HEv2 : ew Ev 2 = Z_to_bv 64 (z_sp cx - 320)) by (rewrite (AG 2%nat) by lia; exact HE2);
assert (HEv8 : ew Ev 8 = Z_to_bv 64 (z_ctx cx)) by (rewrite (AG 8%nat) by lia; exact HE8);
assert (HEv20 : ew Ev 27 = Z_to_bv 64 SB) by (rewrite (AG 27%nat) by lia; exact HE27);
assert (HEv25 : ew Ev 25 = Z_to_bv 64 (z_idl cx)) by (rewrite (AG 25%nat) by lia; exact HE25);
assert (HEv24 : ew Ev 23 = Z_to_bv 64 s1) by (rewrite (AG 23%nat) by lia; exact HE23)
end.
clear HE2 HE8 HE27 HE25 HE23.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_tm cx) _ (proj1 HJ2) HBtm) as (_ & _ & _ & _ & Htmpres2 & _).
assert (Vz : val_mem SEGS (mrestrict (w_H W7) mem2) (z_tm cx + 2 * J) 2 0).
{ apply val_mem_zero2. intros i Hi. replace (z_tm cx + 2 * J + i) with (z_tm cx + 2 * P + (2 * c + i)) by lia.
rewrite (Heff (2 * c + i)) by lia. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 68%nat) 0 2 0 2 [YP09.mkChunk 0 (CVal 2 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite HE68, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Htmpres2 (z_tm cx + 2 * J + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ex _ (z_tm cx + 2 * J) 0 2 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vz])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HE68, HEv8, HEv2, HE60, HE64, HE65, HE66, HE70, !unsigned_lit_small by lia; repeat split; tm_sep HSEP)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 67%nat) 0 2 0 2 [YP09.mkChunk 0 (CVal 2 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite HE67, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Htmpres2 (z_tm cx + 2 * J + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ex _ (z_tm cx + 2 * J) 0 2 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vz])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite HE67, HEv8, HEv2, HE60, HEv16, HEv12, HEv11, !unsigned_lit_small by lia; repeat split; tm_sep HSEP)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS. reshok_bx HS 27%nat.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 565432) mem2 (seg_rom SEGS))) in HJ2.
paj_run_to_tok RUNTO HS HJ2 SHOK Bspan PC_HEAD; try (oblk HJ2 HBtm HE68 HEv20 (z_tm cx + 2 * J)); try (oblk HJ2 HBlm HE65 HEv20 (z_lm cx + 2 * q));
try (oblk HJ2 HBg HEv8 HEv20 (z_ctx cx)).
{ awr_tmp 68%nat (z_tm cx + 2 * J) HE68 Atm HBtm.
awr_tmp 8%nat (z_ctx cx) HEv8 Actx HBg.
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (-320)); [reflexivity | cbn [ew ewset Nat.eqb]; rewrite HEv2; rewrite unsigned_lit_small by lia; lia | cbn; lia | cbn; lia |].
awr_tmp 60%nat (z_ld cx + 2 * lp) HE60 Ald HBld. apply awr_ok_cons_ro; [cbn; lia|].
awr_tmp 65%nat (z_lm cx + 2 * q) HE65 Alm HBlm. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- exists regs' mem' md' X', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ =>
exists rg, mm, mdx, (mkLA TI (updn LM (Z.to_nat q) mp) LI (updn (zero_range TM (Z.to_nat P) (Z.to_nat (z_idl cx))) (Z.to_nat J) dp)
s1 (lp + 1) (dp + 1) (mp + 1) (Cn + 1) R) end.
split; [unfold atail_pc; cbn [la_s]; replace (s1 <? z_nP cx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity|].
split; [exact HJ2|].
lazymatch type of HFr with frame_of ?Ef _ ?m2r _ =>
hout HFr Ef m2r [(z_tm cx + 2 * J, z_tm cx + 2 * J + 2); (z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56);
(z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (z_lm cx + 2 * q, z_lm cx + 2 * q + 2); (0, 0); (0, 0)] end.
rename Hout into Hout2.
lazymatch type of Hout1 with forall a, _ -> _ -> mbyte _ ?m1r a = mbyte _ _ a =>
lazymatch type of Hout2 with forall a, _ -> _ -> mbyte _ _ a = mbyte _ ?m2r a =>
assert (Hms : forall a, 0 <= a < 2 ^ 64 -> ~ (z_tm cx + 2 * P <= a < z_tm cx + 2 * P + 2 * z_idl cx) ->
~ (z_sp cx - 320 - ESTACK <= a < z_sp cx - 320) -> mbyte SEGS m2r a = mbyte SEGS m1r a)
by (intros a Ha Hn1 Hn2; apply (mbyte_of_aview SEGS); apply Hfr; [exact Ha | exact Hn1 | replace (z_sp cx + -320) with (z_sp cx - 320) by lia; exact Hn2]);
assert (Hz2 : forall a, z_tm cx + 2 * P <= a < z_tm cx + 2 * P + 2 * z_idl cx -> mbyte SEGS m2r a = Some (Z_to_bv 8 0))
by (intros a Ha; replace a with (z_tm cx + 2 * P + (a - (z_tm cx + 2 * P))) by lia; apply mbyte_zero_of_aview;
rewrite (Heff (a - (z_tm cx + 2 * P))) by lia; reflexivity)
end end.
unfold ESTACK in Hms. clear Hfr Heff.
assert (Hall : forall a, 0 <= a < 2 ^ 64 ->
outsideA [(z_ctx cx + 60, z_ctx cx + 68); (z_sp cx - 320 + 8, z_sp cx - 320 + 56); (z_ld cx + 2 * lp, z_ld cx + 2 * lp + 4); (0, 0); (z_lm cx + 2 * q, z_lm cx + 2 * q + 2); (0, 0); (0, 0)] a ->
~ (z_tm cx + 2 * P <= a < z_tm cx + 2 * P + 2 * z_idl cx) -> ~ (z_sp cx - 320 - 4096 <= a < z_sp cx - 320) ->
~ (z_tm cx + 2 * J <= a < z_tm cx + 2 * J + 2) ->
mbyte SEGS ltac:(lazymatch type of Hout2 with forall a, _ -> _ -> mbyte _ ?m3r a = _ => exact m3r end) a = mbyte SEGS m a).
{ intros a Ha Hw1 Hr Hsc Hcl. rewrite Hout2; [| exact Ha | cbn; cbn in Hw1; tauto]. rewrite Hms by assumption. apply Hout1; [exact Ha | exact Hw1]. }
split; [intros a Ha; apply Hall; [lia | cbn; repeat split; lia | lia | lia | lia]|].
cellv HS 0%nat 68%nat (z_tm cx + 2 * J) HE68 (SOff 34 0) dp HE34 Vtm.
cellv HS 5%nat 65%nat (z_lm cx + 2 * q) HE65 (SOff 35 0) mp HE35 Vlm.
destruct (inv_switch (z_idl cx) (z_nP cx) Hidl _ q c (s1 - 1) HI ltac:(cbn [la_dp]; lia) ltac:(cbn [la_s]; lia) Hq Hc
ltac:(cbn [la_LI]; exact HLI) ltac:(cbn [la_LM]; exact HLM)) as (HI' & _ & _).
cbn [st_switch la_mp] in HI'. rewrite <- HPdef in HI'. rewrite <- HJdef in HI'. replace (s1 - 1 + 1) with s1 in HI' by lia.
unfold atail_post. cbn [la_lp la_dp la_mp la_s la_TI la_LM la_LI la_TM]. split; [|reflexivity].
split.
{ split; [|split; [aregv HS (30%bv : bv 5) | aregv HS (16%bv : bv 5)]].
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_after E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia] | st_ok _ ?E1 ?ss1 ?ms1 =>
eapply (alzw_regs_fix_afterI E E1 ss1 ms1 _ _ _ HS);
[vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; apply AG; lia | exact HE0 | exact HFC | lia | lia]  end. }
split; [genM 1%nat HS HEv8 HG ltac:(fun a Ha => apply Hall; [lia | cbn; septac HSEP 0%nat 6%nat; septac HSEP 2%nat 6%nat; repeat split; lia | septac HSEP 5%nat 6%nat; lia | lia | septac HSEP 5%nat 6%nat; lia])
(z_ctx cx) (SOff 33 1) (lp + 1) HE33 (SOff 34 1) (dp + 1) HE34 (SOff 35 1) (mp + 1) HE35|].
split.
{ split; [|split; [|split]]; cbn [la_TI la_LM la_LI la_TM].
- eapply arr16_frame; [exact ATI|]. intros a Ha. rewrite LenTI, Z2Nat.id in Ha by lia.
apply Hall; [lia | cbn | septac HSEP 1%nat 5%nat; lia | lia | septac HSEP 1%nat 5%nat; lia]. septac HSEP 0%nat 1%nat. septac HSEP 1%nat 6%nat. septac HSEP 1%nat 2%nat. repeat split; lia.
- eapply arr16_upd; [exact ALM | lia | exact HqLM | lia | exact Vlm |].
intros a Ha Hna. rewrite LenLM in Ha. cbn in Ha.
apply Hall; [lia | cbn | septac HSEP 2%nat 5%nat; lia | lia | septac HSEP 2%nat 5%nat; lia]. septac HSEP 0%nat 2%nat. septac HSEP 2%nat 6%nat. repeat split; first [exact Hna | lia].
- eapply arr16_frame; [exact ALI|]. intros a Ha. rewrite LenLI in Ha. cbn in Ha.
apply Hall; [lia | cbn | septac HSEP 4%nat 5%nat; lia | lia | septac HSEP 4%nat 5%nat; lia]. septac HSEP 0%nat 4%nat. septac HSEP 4%nat 6%nat. septac HSEP 2%nat 4%nat. repeat split; lia.
- assert (ATM2 : arr16 SEGS ltac:(lazymatch type of Hms with forall a, _ -> _ -> _ -> mbyte _ ?m2r a = _ => exact m2r end) (z_tm cx)
(zero_range TM (Z.to_nat P) (Z.to_nat (z_idl cx)))).
{ eapply arr16_zero_range; [exact ATM | lia | lia | rewrite LenTM, <- Z2Nat.inj_add by lia; apply (proj1 (Z2Nat.inj_le (P + z_idl cx) (2049 * z_idl cx) ltac:(lia) ltac:(lia))); lia | |].
- intros a Ha. apply Hz2. lia.
- intros a Ha Hna. rewrite LenTM, Z2Nat.id in Ha by lia.
rewrite Hms; [| lia | first [exact Hna | lia] | lia]. apply Hout1; [lia | cbn]. septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. septac HSEP 2%nat 5%nat. repeat split; lia. }
eapply arr16_upd; [exact ATM2 | lia | rewrite zero_range_length, LenTM; apply (proj1 (Z2Nat.inj_lt J (2049 * z_idl cx) ltac:(lia) ltac:(lia))); lia | lia | exact Vtm |].
intros a Ha Hna. rewrite zero_range_length, LenTM, Z2Nat.id in Ha by lia.
apply Hout2; [lia | cbn]. septac HSEP 0%nat 5%nat. septac HSEP 5%nat 6%nat. septac HSEP 2%nat 5%nat. repeat split; first [exact Hna | lia]. }
split; [exact HI'|]. split; [aregv HS (23%bv : bv 5) | lia].
Qed.
End S.
End e.
End d.
