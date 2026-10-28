(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00 YI16 YK0p YP0h YI19.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0l YP0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0p.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2l AE2h AE2g AE2j AE2d AE2a AE27 AE24 AE25.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbq YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YK0r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition UNLINK : Z := 0x9c9cc.
Definition UN_ECALL : Z := 0x9c9e4.
Definition UN_RET : Z := 0x9c9f8.
Definition UN_SYSRET : Z := 0x8d95c.
Definition UN_ERRLOC : Z := 0x8d2f8.
Definition UN_WIN : Z := 32.
Definition tbl_un : ctable := Eval vm_compute in build_ranges [(UNLINK, 12%nat); (UN_SYSRET, 14%nat); (UN_ERRLOC, 3%nat)] tbl_ff.
Lemma tbl_un_eq : tbl_un = build_ranges [(UNLINK, 12%nat); (UN_SYSRET, 14%nat); (UN_ERRLOC, 3%nat)] tbl_ff.
Proof. vm_cast_no_check (eq_refl tbl_un). Qed.
Lemma tbl_un_ok : table_ok tfibsegs tbl_un.
Proof. rewrite tbl_un_eq. apply build_ranges_ok; [| apply tbl_ff_ok]. repeat constructor; cbn; discriminate. Qed.
Definition RUNU (s : sstate) := sym_runN tfibsegs tbl_un FUEL s.
Definition stkU : YP09.region := YP09.mkRegion (Some 2%nat) (- UN_WIN) 0 (- UN_WIN) 0 [].
Definition errU : YP09.region := YP09.mkRegion (Some 4%nat) (-164) (-160) (-164) (-160) [].
Definition factsU : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (4%nat, mkAF 4096 (2^47) 3)].
Definition ssU1 : sstate := mkSS UNLINK (sr_set sr_atoms 10%bv (SLit A_PATH)) [stkU; errU] None (mkFacts factsU [] []).
Definition eU1 : sstate := Eval vm_compute in fst (RUNU ssU1).
Lemma r_U1 : RUNU ssU1 = (eU1, RS_ecall). Proof. vm_compute. reflexivity. Qed.
Definition resumeU2 (e : sstate) : sstate := resume e (SLit 0) (ss_mem e) (ss_facts e).
Definition eU2 : sstate := Eval vm_compute in fst (RUNU (resumeU2 eU1)).
Lemma r_U2 : RUNU (resumeU2 eU1) = (eU2, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition resumeU2r (e : sstate) : sstate :=
resume e (SOff 40 0) (ss_mem e) (mkFacts ((40%nat, mkAF (2^64 - 4095) (2^64 - 1) 0) :: f_atoms (ss_facts e)) (f_conds (ss_facts e)) (f_alias (ss_facts e))).
Definition eU2r : sstate := Eval vm_compute in fst (RUNU (resumeU2r eU1)).
Lemma r_U2r : RUNU (resumeU2r eU1) = (eU2r, RS_stopped (SR_jalr (SOff 1 0))). Proof. vm_compute. reflexivity. Qed.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition has_chunk (ss : sstate) (i : nat) (off : Z) (n : N) (v : sv) : bool :=
match nth_error (ss_mem ss) i with Some r => existsb (chunk_is off n v) (r_chunks r) | None => false end.
Definition skelsU (e : sstate) : bool :=
match ss_mem e with
| [r0; r1] => skel_is r0 (Some 2%nat) (- UN_WIN) 0 (- UN_WIN) 0 && skel_is r1 (Some 4%nat) (-164) (-160) (-164) (-160)
| _ => false end.
Definition KEPTU : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeU1 (e : sstate) : bool :=
(ss_pc e =? UN_ECALL) && match ss_resv e with None => true | _ => false end
&& reg_is e 17 (SLit 35) && reg_is e 10 (SLit (2^64 - 100)) && reg_is e 11 (SLit A_PATH) && reg_is e 12 (SLit 0)
&& skelsU e && ss_atoms_lt 40 e.
Lemma shapeU1_ok : shapeU1 eU1 = true. Proof. vm_compute. reflexivity. Qed.
Definition shapeU2 (e : sstate) : bool :=
(ss_pc e =? UN_RET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SLit 0) && reg_is e 1 (SOff 1 0) && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTU && skelsU e.
Lemma shapeU2_ok : shapeU2 eU2 = true. Proof. vm_compute. reflexivity. Qed.
Definition shapeU2r (e : sstate) : bool :=
(ss_pc e =? UN_RET) && match ss_resv e with None => true | _ => false end
&& reg_is e 10 (SLit (2^64 - 1)) && reg_is e 1 (SOff 1 0) && forallb (fun r => reg_is e r (SOff (Z.to_nat r) 0)) KEPTU
&& has_chunk e 1 (-164) 4 (SAluw ALU_SUB (SLit 0) (SOff 40 0)) && skelsU e.
Lemma shapeU2r_ok : shapeU2r eU2r = true. Proof. vm_compute. reflexivity. Qed.
Definition WINU : list (option nat * Z * Z) := Eval vm_compute in windows (ss_mem ssU1).
Lemma wins_U : windows (ss_mem ssU1) = WINU /\ windows (ss_mem (resumeU2 eU1)) = WINU /\ windows (ss_mem (resumeU2r eU1)) = WINU.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma un_phase_g : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_un FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1)) /\
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
destruct (msteps_run_gen tfibsegs tbl_un tbl_un_ok FUEL E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
apply (SRr_msteps tfibsegs AF0x.Hwx_tfa W ms msr' md _ Hms). intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb md model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
assert (Hmm : mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) = ms_mem msr') by (pose proof (f_equal ms_mem Hrr) as EE; exact EE).
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply SRr_ret. split; [reflexivity|]. exists (unrestrict (w_H W) (ms_mem ms) msr'), (m_vm_materialized model'). split; [reflexivity|].
split; [rewrite Hrr; exact HS'|]. split; [cbn [unrestrict ms_mem]; apply frame_of_unrestrict; exact Hfr|].
split; [rewrite Hmm; exact Hfr | rewrite Hmm; exact Hgr].
Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis AIL : asink_img_laws tfibsegs B tfib_K.
Theorem tfib_aunlink_spec : aunlink_spec tfibsegs B tfib_K UNLINK.
Proof.
intros W ly S regs mem md ch HPRE G10 HNONE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HNONE as (Henv & Hhead & Hnames).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (FS : AUNLINK_STK = 32) by reflexivity. assert (HT : TFIB_TP = 0x5d8f90) by reflexivity.
rewrite FS in Hslo, Hpres, Hstk0, Hbot.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
pose proof AF0x.Hwx_tfa as Hwx.
pose proof Henv as (Ethr & Enl & Elock & Epath & _).
assert (Etp : getr regs 4 = w64 TFIB_TP) by (rewrite Htp, (ts_tp B TB); reflexivity).
assert (ERRimg : forall a, 0x5d8f90 - 164 <= a < 0x5d8f90 - 160 -> in_img tfibsegs a).
{ intros a Ha. apply (ail_errno_img _ _ _ AIL). rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia. }
assert (HERRown : forall a, TFIB_TP - 164 <= a < TFIB_TP - 160 -> ~ aowned B ly S a).
{ intros a Ha Hown. rewrite HT in Ha. pose proof (proj1 (al_owned_image _ _ LAWS ly S W mem md a HAR (ERRimg a Ha)) Hown) as HX2. rewrite (ts_owned B TB) in HX2.
apply Exists_exists in HX2 as (r & Hr & Hin). unfold Tfib_owned_static in Hr. cbn [In] in Hr. unfold in_zr in Hin.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hin; lia|]). destruct Hr. }
assert (WERR : forall (m : word -> option byte) o, 0 <= o < 4 -> writable_at tfibsegs m (TFIB_TP - 164 + o)).
{ intros m o Ho.
assert (C : forall j, In j [0; 1; 2; 3] -> img_writable_ok tfibsegs (TFIB_TP - 164 + j) = true)
by (intros j Hj; cbn [In] in Hj; repeat (destruct Hj as [<- | Hj]; [vm_compute; reflexivity|]); destruct Hj).
pose proof (C o ltac:(cbn [In]; lia)) as Hw. unfold img_writable_ok in Hw.
apply (writable_at_grows tfibsegs (fun _ => None)); [intros x Hx; exfalso; exact (Hx eq_refl)|].
unfold writable_at. destruct (wview tfibsegs (fun _ => None) (Z_to_bv 64 (TFIB_TP - 164 + o))); [discriminate | discriminate Hw]. }
set (E1 := AE2y.Env regs []).
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (E1_2 : bv_unsigned (ew E1 2) = sp0) by (rewrite (E1reg 2%nat 2%bv eq_refl); reflexivity).
assert (E1_4 : bv_unsigned (ew E1 4) = TFIB_TP) by (rewrite (E1reg 4%nat 4%bv eq_refl), Etp; apply unsigned_lit_small; unfold TFIB_TP; lia).
assert (HS1 : st_ok tfibsegs E1 ssU1 (restrict H (mkst regs (Z_to_bv 64 UNLINK) mem (seg_rom tfibsegs)))).
{ unfold ssU1.
apply (st_ok_pin_reg E1 (mkSS UNLINK sr_atoms [stkU; errU] None (mkFacts factsU [] [])) _ 10%bv (SLit A_PATH));
[| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G10; reflexivity].
rewrite restrict_mkst_fx. unfold E1, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with E1.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons.
{ unfold stkU. apply (region_ok_stack tfibsegs E1 _ 2 sp0 (- 32)); [exact E1_2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply Hpres. lia. }
apply Forall_cons; [|apply Forall_nil].
unfold errU, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E1_4.
split; [lia|]. split; [lia|]. split; [intros o Ho; replace (TFIB_TP + o) with (TFIB_TP - 164 + (o + 164)) by lia; apply WERR; lia | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold stkU, errU, extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E1_2, E1_4, HT.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold UN_WIN. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsU]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E1_2, E1_4, HT.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; lia. }
assert (WIN : forall E rs a, windows rs = WINU -> bv_unsigned (ew E 2) = sp0 -> bv_unsigned (ew E 4) = TFIB_TP -> in_wrange E rs a ->
(sp0 - 32 <= a < sp0) \/ (TFIB_TP - 164 <= a < TFIB_TP - 160)).
{ intros E rs a HWl X2 X4 Hin. destruct (in_wrange_windows E rs a Hin) as (bw & lo & hi & Ht & Hr). rewrite HWl in Ht. unfold WINU in Ht. cbn [In] in Ht.
repeat (destruct Ht as [Et | Ht]; [injection Et as <- <- <-; cbn [base_val] in Hr; rewrite ?X2, ?X4 in Hr; unfold UN_WIN in Hr; lia|]). destruct Ht. }
pose proof wins_U as (WL1 & WL2 & WL2r).
unfold cfg_at. change (w64 UNLINK) with (Z_to_bv 64 UNLINK).
eapply SRr_bind; [exact (un_phase_g W E1 ssU1 eU1 _ (mkst regs (Z_to_bv 64 UNLINK) mem (seg_rom tfibsegs)) md HS1 r_U1)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2 & GR2). cbn [ms_mem mkst] in HF2, GR2. clear HFr2.
set (md2 := with_vm_backing (m_vm_lazy md) mat2 md) in *.
assert (MF2 : same_but_materialized md md2) by (subst md2; apply with_vm_backing_same).
pose proof shapeU1_ok as Hsh. unfold shapeU1 in Hsh.
apply andb_prop in Hsh as [Hsh Hat]. apply andb_prop in Hsh as [Hsh Hsk]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R17]. apply andb_prop in Hsh as [Hpc Hrv]. apply Z.eqb_eq in Hpc.
assert (Hresv2 : ss_resv eU1 = None) by (destruct (ss_resv eU1); [discriminate | reflexivity]).
destruct (st_ok_ecall_shape_r tfibsegs H E1 eU1 ms2 HS2 Hresv2) as (regs2 & mem2 & Hms2 & Hregs2 & Hmemok2 & HG2).
assert (Hmm2 : ms_mem ms2 = mem2) by (rewrite Hms2; reflexivity). rewrite Hmm2 in HF2, GR2.
assert (MEQ2 : forall z : word, ~ ((sp0 - 32 <= bv_unsigned z < sp0) \/ (TFIB_TP - 164 <= bv_unsigned z < TFIB_TP - 160)) -> mem2 z = mem z).
{ intros z Hz. apply (HF2 z). intros Hin. exact (Hz (WIN E1 _ _ WL1 E1_2 E1_4 Hin)). }
clear HF2.
assert (RD2 : forall (r : bv 5) v, reg_is eU1 (bv_unsigned r) v = true -> getr regs2 r = sv_denot E1 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply Hregs2. }
assert (Q2_17 : bv_unsigned (getr regs2 17) = 35) by (rewrite (RD2 17%bv (SLit 35) R17); reflexivity).
assert (Q2_10 : getr regs2 10 = w64 (2 ^ 64 - 100)) by (rewrite (RD2 10%bv _ R10); reflexivity).
assert (Q2_11 : getr regs2 11 = w64 A_PATH) by (rewrite (RD2 11%bv _ R11); reflexivity).
assert (Q2_12 : getr regs2 12 = w64 0) by (rewrite (RD2 12%bv _ R12); reflexivity).
unfold skelsU in Hsk. destruct (ss_mem eU1) as [|r0 [|r1 [|]]] eqn:Hmem; try discriminate Hsk. apply andb_prop in Hsk as [K0 K1].
apply skel_is_sound in K0 as (K0a & K0lo & K0hi & K0b & K0c). apply skel_is_sound in K1 as (K1a & K1lo & K1hi & K1b & K1c).
assert (PRS2s : forall a, sp0 - 32 <= a < sp0 -> apresent H mem2 a).
{ intros a Ha. apply (mem_ok_window_apresent H E1 mem2 _ 0 r0 a Hmemok2 ltac:(rewrite ?Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite K0a, K0b, K0c. cbn [base_val]. rewrite E1_2. unfold UN_WIN. lia. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 32 <= a < sp0) \/ (TFIB_TP - 164 <= a < TFIB_TP - 160)) -> aview tfibsegs H mem2 a = aview tfibsegs H mem a).
{ intros a Hr Hw. apply aview_same. apply MEQ2. rewrite unsigned_lit_small by lia. exact Hw. }
assert (PM2 : forall a, apresent H mem a -> apresent H mem2 a) by (intros a Hp; eapply fo_apresent_grows; [exact GR2 | exact Hp]).
destruct sink_path_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). rewrite <- sink_path_eq in F1, F2, F3, F4, F5, F6, F7.
assert (PIMG : forall j, 0 <= j < 13 -> in_img tfibsegs (A_PATH + j)).
{ intros j Hj. exists Asan.Asan_segment_000. split; [left; reflexivity | unfold A_PATH; cbn; lia]. }
assert (Hpath2 : garr8 tfibsegs (mrestrict H mem2) A_PATH (sink_path_Z ++ [0])).
{ eapply garr8_frame; [exact Epath|]. intros x Hx. unfold sink_path_Z in Hx. cbn [length app] in Hx. unfold A_PATH in Hx.
apply AE2y.mbyte_of_aview. apply AV2; [lia | rewrite HT; clear - Hx Hslo Lbeg; lia]. }
assert (Hraw : garr8 tfibsegs mem2 A_PATH (sink_path_Z ++ [0])).
{ intros j Hj. destruct (Hpath2 j Hj) as [Hv Hb]. split; [|exact Hb]. intros k Hk. pose proof (Hv k Hk) as X.
unfold sink_path_Z in Hj. cbn [length app] in Hj.
replace (A_PATH + Z.of_nat j + Z.of_nat k) with (A_PATH + (Z.of_nat j + Z.of_nat k)) in X |- * by lia.
destruct (ffo_mbyte_unhidden W mem2 (A_PATH + (Z.of_nat j + Z.of_nat k)) (PIMG (Z.of_nat j + Z.of_nat k) ltac:(lia)) ltac:(unfold A_PATH; lia)) as [EE _].
fold H in EE. rewrite EE in X. unfold mbyte, mrb in *. exact X. }
assert (Hcstr : read_cstr (ms_read_byte (pend_at regs2 (Z_to_bv 64 UN_ECALL) mem2 (seg_rom tfibsegs))) (getr regs2 11) = CstrOk sink_path).
{ rewrite pend_read_byte_mrb, Q2_11. change (w64 A_PATH) with (Z_to_bv 64 A_PATH). rewrite sink_path_eq.
apply (read_cstr_of_garr8 tfibsegs mem2 A_PATH sink_path_Z Hraw); [|cbn; lia]. unfold sink_path_Z. repeat (constructor; [lia|]). constructor. }
assert (Hav : ranges_avoid (w_H W) (open_copyins (pend_at regs2 (Z_to_bv 64 UN_ECALL) mem2 (seg_rom tfibsegs)))).
{ intros a n Hin. unfold open_copyins in Hin. rewrite pend_gpr1, pend_read_byte_mrb, Q2_11 in Hin. change (w64 A_PATH) with (Z_to_bv 64 A_PATH) in Hin.
assert (Hlen : (cstr_access_len_aux (mrb tfibsegs mem2) (Z_to_bv 64 A_PATH) path_max <= 13)%nat).
{ apply ffo_cstr_len_le. destruct (Hraw 12%nat ltac:(unfold sink_path_Z; cbn; lia)) as [Hv _]. pose proof (Hv 0%nat ltac:(lia)) as X.
unfold sink_path_Z in X. cbn [nth app Z.of_nat Nat.add] in X. unfold mbyte in X. unfold woff, mrb. rewrite unsigned_lit_small by (unfold A_PATH; lia).
replace (A_PATH + Z.of_nat 12) with (A_PATH + 12 + 0) by lia. rewrite Z.add_0_r in X |- *. replace (A_PATH + 12 + 0) with (A_PATH + 12) in X by lia.
exact X. }
revert Hin Hlen. generalize (cstr_access_len_aux (mrb tfibsegs mem2) (Z_to_bv 64 A_PATH) path_max). intros L Hin Hlen.
destruct Hin as [Heq|[]]. injection Heq as <- <-.
intros k Hk. unfold woff. rewrite unsigned_lit_small by (unfold A_PATH; lia).
exact (proj2 (ffo_mbyte_unhidden W mem2 (A_PATH + Z.of_nat k) (PIMG (Z.of_nat k) ltac:(lia)) ltac:(unfold A_PATH; lia))). }
assert (Hdir : getr regs2 10 = AT_FDCWD) by (rewrite Q2_10; unfold AT_FDCWD; apply bv_eq; reflexivity).
assert (Hfl : bv_unsigned (flag32 (getr regs2 12)) = 0) by (rewrite Q2_12; vm_compute; reflexivity).
pose proof (same_but_materialized_frame md md2 MF2) as (_ & V02 & Z02 & _ & _ & _ & _ & _ & FD02 & _ & _ & FS02 & _).
assert (Hfdn2 : fd_names_path (m_fds md2) sink_path = false) by (rewrite FD02; exact Hnames).
lazymatch goal with |- SRr _ _ _ ?Q => set (POST := Q) end.
assert (TAIL : forall E2 ss3 e3 (RET : word) md3 (res : Z),
(forall i, (i < 40)%nat -> ew E2 i = ew E1 i) ->
st_ok tfibsegs E2 ss3 (restrict H (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 UN_ECALL) 4) mem2 (seg_rom tfibsegs))) ->
RUNU ss3 = (e3, RS_stopped (SR_jalr (SOff 1 0))) -> windows (ss_mem ss3) = WINU ->
(ss_pc e3 =? UN_RET) && match ss_resv e3 with None => true | _ => false end && reg_is e3 10 (SLit res) && reg_is e3 1 (SOff 1 0)
&& forallb (fun r => reg_is e3 r (SOff (Z.to_nat r) 0)) KEPTU && skelsU e3 = true ->
0 <= res < 2 ^ 64 ->
m_vmmaps md3 = m_vmmaps md -> m_vm_lazy md3 = m_vm_lazy md -> os_kept md md3 -> m_fds md3 = m_fds md ->
((res = 0 /\ m_fs md3 = fs_remove (m_fs md) sink_path) \/
(exists e, 1 <= e <= 4095 /\ res = 2 ^ 64 - 1 /\ m_fs md3 = m_fs md /\ has_chunk e3 1 (-164) 4 (SAluw ALU_SUB (SLit 0) (SOff 40 0)) = true /\ bv_unsigned (ew E2 40) = 2 ^ 64 - e)) ->
SRr tfibsegs W (mkCfg (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 UN_ECALL) 4) mem2 (seg_rom tfibsegs)) md3) POST).
{ intros E2 ss3 e3 RET md3 res E2old HS3 Hrun HWl Hsh Hres V3 L3 OK3 FD3 Hout.
assert (E2_2 : bv_unsigned (ew E2 2) = sp0) by (rewrite (E2old 2%nat ltac:(lia)); exact E1_2).
assert (E2_4 : bv_unsigned (ew E2 4) = TFIB_TP) by (rewrite (E2old 4%nat ltac:(lia)); exact E1_4).
eapply SRr_bind; [exact (un_phase_g W E2 ss3 e3 _ (mkst (regupd regs2 10 RET) (v_addi (Z_to_bv 64 UN_ECALL) 4) mem2 (seg_rom tfibsegs)) md3 HS3 Hrun)|].
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4 & GR4). cbn [ms_mem mkst] in HF4, GR4. clear HFr4.
set (md4 := with_vm_backing (m_vm_lazy md3) mat4 md3) in *.
assert (MF34 : same_but_materialized md3 md4) by (subst md4; apply with_vm_backing_same).
apply andb_prop in Hsh as [Hsh Hsk4]. apply andb_prop in Hsh as [Hsh HK4]. apply andb_prop in Hsh as [Hsh Z1]. apply andb_prop in Hsh as [Hsh Z10].
apply andb_prop in Hsh as [Hpc4 Hrv4]. apply Z.eqb_eq in Hpc4.
assert (Hresv4 : ss_resv e3 = None) by (destruct (ss_resv e3); [discriminate | reflexivity]).
unfold skelsU in Hsk4. destruct (ss_mem e3) as [|q0 [|q1 [|]]] eqn:Hmem4; try discriminate Hsk4. apply andb_prop in Hsk4 as [J0 J1].
apply skel_is_sound in J0 as (J0a & J0lo & J0hi & J0b & J0c). apply skel_is_sound in J1 as (J1a & J1lo & J1hi & J1b & J1c).
assert (MEQ4 : forall z : word, ~ ((sp0 - 32 <= bv_unsigned z < sp0) \/ (TFIB_TP - 164 <= bv_unsigned z < TFIB_TP - 160)) -> ms_mem ms4 z = mem2 z).
{ intros z Hz. apply (HF4 z). intros Hin. exact (Hz (WIN E2 _ _ HWl E2_2 E2_4 Hin)). }
clear HF4.
assert (RD4 : forall (r : bv 5) v, reg_is e3 (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot E2 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E2 e3 ms4 r HS4). }
set (regs4 := ms_regs ms4) in *.
assert (PK4 : forall r, In r KEPTU -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (unfold KEPTU in Hin; cbn in Hin; lia).
rewrite forallb_forall in HK4. specialize (HK4 _ Hin). cbn beta in HK4.
rewrite (RD4 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
- cbn [sv_denot]. rewrite (E2old (Z.to_nat r) ltac:(lia)), (E1reg (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK4. }
assert (P4_1 : getr regs4 1 = getr regs 1).
{ rewrite (RD4 1%bv (SOff 1 0) Z1). cbn [sv_denot]. rewrite (E2old 1%nat ltac:(lia)), (E1reg 1%nat 1%bv eq_refl), Z.add_0_r. apply Z_to_bv_bv_unsigned. }
assert (P4_10 : getr regs4 10 = w64 res) by (rewrite (RD4 10%bv (SLit res) Z10); reflexivity).
assert (PRS4s : forall a, sp0 - 32 <= a < sp0 -> apresent H (ms_mem ms4) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent_off H E2 e3 ms4 0 q0 a HS4 ltac:(rewrite ?Hmem4; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite J0a, J0b, J0c. cbn [base_val]. rewrite E2_2. unfold UN_WIN. lia. }
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 32 <= a < sp0) \/ (TFIB_TP - 164 <= a < TFIB_TP - 160)) -> aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem2 a).
{ intros a Hr Hw. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. exact Hw. }
assert (TAV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> ~ (TFIB_TP - 164 <= a < TFIB_TP - 160) -> aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem a).
{ intros a Hr Hs He. rewrite AV4 by (try lia; tauto). apply AV2; [lia | tauto]. }
assert (GR : mem_grows (mrestrict H mem) (mrestrict H (ms_mem ms4))) by (exact (mem_grows_trans _ _ _ GR2 GR4)).
assert (TPM : forall a, apresent H mem a -> apresent H (ms_mem ms4) a) by (intros a Hp; eapply fo_apresent_grows; [exact GR | exact Hp]).
pose proof (st_ok_restrict_mkst tfibsegs H E2 _ _ HS4 Hresv4) as Hshape4. rewrite Hpc4 in Hshape4. fold regs4 in Hshape4.
eapply SRr_bind.
{ eapply (SRr_ret_at tfibsegs tbl_un tbl_un_ok Hwx W E2 e3 ms4 md4
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms4) (v_jalr (getr (ms_regs ms4) 1) 0) (ms_mem ms4) (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md4) mat' md4)));
[exact HS4 | exact Hresv4 | rewrite Hpc4; vm_compute; reflexivity | intros mat'; split; [reflexivity | exists mat'; reflexivity]]. }
intros W5 c5 _ (-> & mat5 & ->).
set (md5 := with_vm_backing (m_vm_lazy md4) mat5 md4). fold regs4.
assert (MF35 : same_but_materialized md3 md5) by (eapply same_but_materialized_trans; [exact MF34 | subst md5; apply with_vm_backing_same]).
pose proof (same_but_materialized_frame md3 md5 MF35) as (_ & V35 & L35 & _ & _ & _ & _ & _ & FD35 & _ & _ & FS35 & _).
rewrite P4_1, Hra.
assert (HARF : AR tfibsegs B ly S W (ms_mem ms4) md5).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms4) md5 HAR).
- intros a Hr Hown. apply TAV; [exact Hr | intros Hs; exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown) | intros He; exact (HERRown a He Hown)].
- intros a Hv. exact (aview_keeps_vis tfibsegs H mem (ms_mem ms4) a GR Hv).
- rewrite V35. exact V3.
- rewrite L35. exact L3.
- apply eager_used_vmmaps; [rewrite V35; exact V3 | rewrite L35; exact L3].
- intros a Hband Hh. pose proof (AE2y.in_band_rw_u64 a Hband) as Hr. change (w64 a) with (Z_to_bv 64 a) in *.
rewrite MEQ4; [apply MEQ2|]; rewrite unsigned_lit_small by lia; intros [Hw|Hw].
+ pose proof (Hpres a Hw) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
+ rewrite HT in Hw. pose proof (proj2 (ffo_mbyte_unhidden W mem a (ERRimg a Hw) Hr)) as Hn0. unfold H in Hh. rewrite Hh in Hn0. discriminate.
+ pose proof (Hpres a Hw) as [Hn0 _]. unfold H in Hn0. rewrite Hh in Hn0. discriminate.
+ rewrite HT in Hw. pose proof (proj2 (ffo_mbyte_unhidden W mem a (ERRimg a Hw) Hr)) as Hn0. unfold H in Hh. rewrite Hh in Hn0. discriminate. }
pose proof OK3 as (Oio & Opipes & Oproc).
pose proof (os_kept_sbm _ _ MF35) as (Oio5 & Opipes5 & Oproc5).
assert (J : ajournal tfibsegs B AUNLINK_STK sp0 [sink_token] ly S W mem md [] ly S W (ms_mem ms4) md5 0).
{ split; [exact HARF|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split.
{ split; [rewrite Oio5; exact Oio|]. split; [rewrite Opipes5; exact Opipes|].
split; [intros fd0; left; unfold m_fds; rewrite (proj1 (same_but_materialized_frame _ _ MF35)); fold (m_fds md3); rewrite FD3; reflexivity|].
split.
{ intros q Hq. rewrite FS35. destruct Hout as [[_ ->] | (e & _ & _ & -> & _)]; [apply fs_lookup_remove_other; exact Hq | reflexivity]. }
split; [intros Hso; rewrite FS35; destruct Hout as [[_ ->] | (e & _ & _ & -> & _)]; [apply fs_remove_sorted; exact Hso | exact Hso]|].
split; [| intros Hc; exfalso; apply Hc; apply sink_open_token; left; reflexivity].
unfold proc_but_pins. rewrite Oproc5, Oproc. reflexivity. }
split; [reflexivity|]. split; [lia|]. split; [lia|].
split.
{   intros a Ha Hs. rewrite FS in Hs. apply TAV; [clear - Ha C1; lia | exact Hs | rewrite HT; clear - Ha C1; lia]. }
split.
{   intros p0 n0 i Hin _ Hi Hnf.
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin) as (_ & Hq0 & Hq0c & _).
apply TAV; [clear - Hq0 Hq0c Hi C1; lia | clear - Hq0c Hi Hceil Hslo; lia |].
intros Hr. rewrite HT in Hr. exact (blk_img tfibsegs B LAWS ly S W mem md p0 n0 (p0 + i) HAR Hin ltac:(lia) (ERRimg _ Hr)). }
split.
{   intros a Hi Hns Hne Hsp. pose proof (ffa_img_range a Hi) as Ra.
apply TAV; [lia | clear - Ra Hslo Hceil C1; lia |]. rewrite (ts_errno B TB) in Hne. unfold TFIB_ERRNO in Hne. rewrite HT. clear - Hne. lia. }
split.
{   intros cid pos a Hin Hr Hnf.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md cid pos HAR Hin) as (Hf0' & Hfc & Hfapp').
pose proof (fs_frame_bytes_nonneg cid) as Hnn. unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
destruct Hr as [Hr | Hr].
- apply TAV; [clear - Hr Hf0' Hfc C1; lia | clear - Hr Hfc Hceil Hslo; lia |].
intros Ho. rewrite HT in Ho. exact (frm_img tfibsegs B LAWS ly S W mem md cid pos a HAR Hin ltac:(lia) (ERRimg _ Ho)).
- pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr ly cid pos + fs_frame_bytes cid) ltac:(clear - Hf0' Hfc C1 C4 Hnn; unfold kHighMemEnd; lia)) as [U1 U2].
apply TAV; [clear - Hr B1 U2 Hse; unfold kLowMemEnd, kHighShadowEnd in *; lia | clear - Hr B1 U2 Hse Lbeg Hslo; unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg in *; lia |].
clear - Hr B1 U2 Hse HT. unfold kLowMemEnd, kHighShadowEnd in *. rewrite HT. lia. }
split; [intros p0 n0 i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; rewrite FS in Ha; apply PRS4s; exact Ha|].
split; [exact Hstk|].
split.
{   intros a HXa Hne. destruct (AR_extra_law_ok tfibsegs B ly S W mem md a HAR HXa) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
apply TAV; [clear - Xapp C1; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; lia | |].
- intros Hs. apply Xs. clear - Hs Hslo Hshi. lia.
- intros Hr. rewrite HT in Hr. exact (Xi (ERRimg _ Hr)). }
exact HQT. }
apply SRr_ret. exists regs4, (ms_mem ms4), md5, res.
split; [reflexivity|]. split; [exact J|].
split.
{ intros rr Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec rr 2) as [->|Hne2]; [apply PK4; unfold KEPTU; INL|].
apply PK4. unfold KEPTU. cbn [In]. lia. }
split; [exact P4_10|].
split.
{
split; [| split; [| rewrite FD35, FD3; exact Hnames]].
- apply (astdio_env_frame tfibsegs tfib_K (mrestrict H mem)); [|exact Henv]. intros a Ha.
destruct (ail_env _ _ _ AIL a Ha) as (Hi & Hns & Hne). pose proof (ffa_img_range a Hi) as Ra. rewrite (ts_errno B TB) in Hne. unfold TFIB_ERRNO in Hne.
apply AE2y.mbyte_of_aview. apply TAV; [lia | clear - Ra Hslo Lbeg; lia | rewrite HT; clear - Hne; lia].
- eapply AE2y.val_mem_kept; [| exact Hhead]. intros k Hk. unfold ak_ofl_head in *. cbn [ak_ofl_lock tfib_K] in *. unfold A_ofl_lock.
apply TAV; [lia | clear - Hk Hslo Lbeg; lia | rewrite HT; clear - Hk; lia]. }
split; [rewrite FD35; exact FD3|].
destruct Hout as [[-> Efs] | (e & He & -> & Efs & Hck & HE40)]; [left; split; [reflexivity | rewrite FS35; exact Efs]|].
right. exists e. split; [exact He|]. split; [reflexivity|]. split; [rewrite FS35; exact Efs|].
unfold has_chunk in Hck. rewrite Hmem4 in Hck. cbn [nth_error] in Hck. apply existsb_exists in Hck as (c & Hc & Hcc). apply chunk_is_sound in Hcc. subst c.
pose proof (st_ok_mem_ok tfibsegs E2 e3 _ HS4) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem4 in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs q1 ltac:(right; left; reflexivity)) as (_ & _ & _ & Hcs). rewrite J1a in Hcs. cbn [base_val] in Hcs. rewrite E2_4 in Hcs.
rewrite (ts_errno B TB). unfold TFIB_ERRNO. replace 6131436 with (TFIB_TP + -164) by (rewrite HT; reflexivity).
apply (val_of_chunk_ok tfibsegs E2 _ _ (-164) 4 _ e (proj1 (Forall_forall _ _) Hcs _ Hc)); [| cbn; lia | cbn; lia].
cbn [sv_denot]. apply bv_eq. rewrite !low32_lit.
replace (alu32 ALU_SUB (Z_to_bv 32 0) (Z_to_bv 32 (bv_unsigned (ew E2 40) + 0))) with (low32 (Z_to_bv 64 e)).
2:{ rewrite low32_lit. apply bv_eq. rewrite alu32_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw]. unfold bv_wrap.
change (bv_modulus 32) with (2 ^ 32). rewrite HE40, Z.add_0_r, (Z.mod_small e) by lia. change (0 mod 2 ^ 32) with 0.
replace (2 ^ 64 - e) with ((2 ^ 32 - e) + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 32 - e)) by lia.
replace (0 - (2 ^ 32 - e)) with (e + (-1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
unfold low32. rewrite sext32_small by lia. reflexivity. }
assert (SHr : (ss_pc eU2r =? UN_RET) && match ss_resv eU2r with None => true | _ => false end && reg_is eU2r 10 (SLit (2 ^ 64 - 1)) && reg_is eU2r 1 (SOff 1 0)
&& forallb (fun r => reg_is eU2r r (SOff (Z.to_nat r) 0)) KEPTU && skelsU eU2r = true) by (vm_compute; reflexivity).
assert (SHs : (ss_pc eU2 =? UN_RET) && match ss_resv eU2 with None => true | _ => false end && reg_is eU2 10 (SLit 0) && reg_is eU2 1 (SOff 1 0)
&& forallb (fun r => reg_is eU2 r (SOff (Z.to_nat r) 0)) KEPTU && skelsU eU2 = true) by (vm_compute; reflexivity).
assert (SHc : has_chunk eU2r 1 (-164) 4 (SAluw ALU_SUB (SLit 0) (SOff 40 0)) = true) by (vm_compute; reflexivity).
assert (KREF : forall md3 e, 1 <= e <= 4095 -> same_but_materialized md2 md3 ->
SRr tfibsegs W (mkCfg (mkst (regupd regs2 10 (errno_ret e)) (v_addi (Z_to_bv 64 UN_ECALL) 4) mem2 (seg_rom tfibsegs)) md3) POST).
{ intros md3 e He MF3. set (RET := errno_ret e).
assert (HRETu : bv_unsigned RET = 2 ^ 64 - e).
{ subst RET. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (- e) with ((2 ^ 64 - e) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
assert (MF03 : same_but_materialized md md3) by (eapply same_but_materialized_trans; [exact MF2 | exact MF3]).
pose proof (same_but_materialized_frame md md3 MF03) as (_ & V3 & L3 & _ & _ & _ & _ & _ & FD3 & _ & _ & FS3 & _).
apply (TAIL (ewset E1 40 RET) (resumeU2r eU1) eU2r RET md3 (2 ^ 64 - 1));
[intros i Hi; apply ew_ewset_other; lia | | exact r_U2r | exact WL2r | exact SHr | lia | exact V3 | exact L3 | exact (os_kept_sbm _ _ MF03) | exact FD3 |].
- unfold resumeU2r. rewrite restrict_mkst_fx, <- Hpc.
apply (st_ok_resume_atom tfibsegs 40 (mkAF (2 ^ 64 - 4095) (2 ^ 64 - 1) 0) E1 eU1 regs2 (mrestrict H mem2) RET Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2 Hat); cbn [af_lo af_hi af_al2]; rewrite ?HRETu; [lia | lia |].
change (2 ^ 0) with 1. apply Z.mod_1_r.
- right. exists e. split; [exact He|]. split; [reflexivity|]. split; [exact FS3|]. split; [exact SHc|]. rewrite ew_ewset_same. exact HRETu. }
assert (KSUC : forall md3, same_but_materialized (with_fs (fs_remove (m_fs md2) sink_path) md2) md3 ->
SRr tfibsegs W (mkCfg (mkst (regupd regs2 10 (Z_to_bv 64 0)) (v_addi (Z_to_bv 64 UN_ECALL) 4) mem2 (seg_rom tfibsegs)) md3) POST).
{ intros md3 MF3.
pose proof (same_but_materialized_frame _ md3 MF3) as (_ & V3 & L3 & _ & _ & _ & _ & _ & FD3 & _ & _ & FS3 & _).
apply (TAIL E1 (resumeU2 eU1) eU2 (Z_to_bv 64 0) md3 0);
[intros i Hi; reflexivity | | exact r_U2 | exact WL2 | exact SHs | lia | rewrite V3; exact V02 | rewrite L3; exact Z02 | | rewrite FD3; cbn [m_fds with_fs]; exact FD02 |].
- unfold resumeU2. rewrite restrict_mkst_fx, <- Hpc. apply (st_ok_resume_sv tfibsegs E1 eU1 regs2 (mrestrict H mem2) (SLit 0) (Z_to_bv 64 0) Hregs2 ltac:(rewrite Hmem; exact Hmemok2) HG2). reflexivity.
- eapply os_kept_trans; [exact (os_kept_sbm _ _ MF2)|]. eapply os_kept_trans; [apply os_kept_with_fs | exact (os_kept_sbm _ _ MF3)].
- left. split; [reflexivity|]. rewrite FS3, m_fs_with_fs, FS02. reflexivity. }
rewrite Hms2. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI. rewrite Hpc.
destruct (fs_under (m_fs md2) sink_path) eqn:Hun.
{ destruct (node_unlink_tmp_isdir_lazy tfibsegs (w_H W) (w_A W) regs2 (Z_to_bv 64 UN_ECALL) mem2 (seg_rom tfibsegs) md2 sink_path sink_name_bytes
HAI Q2_17 Hdir Hcstr Hfl F1 F2 F3 F7 F8 Hfdn2 Hun Hav) as (Hnode & HAI' & Hsbm).
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; exact HAI'|]. intros [].
apply (KREF _ EISDIR); [unfold EISDIR; lia | exact Hsbm]. }
destruct (fs_lookup (m_fs md2) sink_path) as [d|] eqn:Hlk.
- destruct (node_unlink_tmp_present_lazy tfibsegs (w_H W) (w_A W) regs2 (Z_to_bv 64 UN_ECALL) mem2 (seg_rom tfibsegs) md2 sink_path sink_name_bytes d
HAI Q2_17 Hdir Hcstr Hfl F1 F2 F3 F7 F8 Hfdn2 Hun Hlk Hav) as [Hnode Hall].
apply (SRr_node tfibsegs W _ unlink_ix _ (inr tt) _ Hnode); [intros i _; exact (proj1 (Hall i))|]. intros [[e He] | []].
+ cbn [unlink_ret unlink_md proj1_sig]. apply (KREF _ e); [| exact (proj2 (Hall (inl (exist _ e He))))].
apply unlink_errnos_range. unfold unlink_tmp_errnos. do 2 right. exact He.
+ cbn [unlink_ret unlink_md]. apply KSUC. exact (proj2 (Hall (inr tt))).
- destruct (node_unlink_tmp_absent_lazy tfibsegs (w_H W) (w_A W) regs2 (Z_to_bv 64 UN_ECALL) mem2 (seg_rom tfibsegs) md2 sink_path sink_name_bytes
HAI Q2_17 Hdir Hcstr Hfl F1 F2 F3 F7 F8 Hfdn2 Hun Hlk Hav) as (Hnode & HAI' & Hsbm).
apply (SRr_node tfibsegs W _ unit _ tt _ Hnode); [intros [] _; exact HAI'|]. intros [].
apply (KREF _ ENOENT); [unfold ENOENT; lia | exact Hsbm].
Qed.
End f.
End b.
