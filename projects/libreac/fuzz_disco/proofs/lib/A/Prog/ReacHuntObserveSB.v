(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 443 of its 473 lines of code are new or changed and 39 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YA0q YCbm YK06 YI0m YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoFrame DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC1i YC45 YC4b YC7k YC81 YC85 YC88 YCbw YCkd ACbf ACj1 DiscoACja DiscoACjr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
ClassifyCore ReacDiscoClassifyOnSegment ReacDiscoTableObserve DiscoRo ReacFrameCleanLen ReacHuntObserve.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacHuntObserveSeg.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Mem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
disco_classify_c disco_table_c hunt_c reac_disco_table_observe_c reac_frame_clean_len_c reac_hunt_observe_c
HuntObsFacts HuntObsLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis DRO : disco_ro_unowned B.

Lemma ho_out_disj : forall a fa bytes Fr,
  fa <= a -> a < fa + bytes ->
  (Fr + 128 <= fa \/ fa + bytes <= Fr) ->
  (fa + bytes <= 2147446784 \/ 17594333495296 <= fa) ->
  0 <= Fr -> 2147450880 + Fr / 8 + 16 <= 17594333495296 ->
  ~ (Fr <= a < Fr + 24) /\
  ~ (2147450880 + Fr / 8 <= a < 2147450880 + Fr / 8 + 12).
Proof. intros a fa bytes Fr H1 H2 H5 H6 H7 H8. split; lia. Qed.
Lemma ho_pres_hi2 : forall (Wx : world SEGS) ma mb a,
  YM05.alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) mb a = aview SEGS (w_H Wx) ma a -> apresent (w_H Wx) ma a -> apresent (w_H Wx) mb a.
Proof.
intros Wx ma mb a Ha HE Hp.
pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
assert (Hb : 0 <= a < 2 ^ 64) by (clear - Ha D1; lia).
assert (Hni : ~ in_img SEGS a)
by (intros Him; pose proof (pa_segs_low a Him) as Hl; clear - Hl Ha D1 D5; unfold kLowMemEnd in *; lia).
exact (apresent_transfer SEGS (w_H Wx) (w_H Wx) ma mb a Hb Hni HE Hp).
Qed.

Lemma ho_chunk_byte : forall E (m : word -> option byte) (b : Z) cs lo hi wlo whi (off v : Z),
  region_ok SEGS E m (YP09.mkRegion (Some 529%nat) lo hi wlo whi cs) ->
  base_val E (Some 529%nat) = b ->
  In (YP09.mkChunk off (CVal 1 (SLit v))) cs ->
  mbyte SEGS m (b + off) = Some (byte_of_word (Z_to_bv 64 v) 0).
Proof.
intros E m b cs lo hi wlo whi off v (_ & _ & _ & Hcs) Hb Hin.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
cbn [YP09.r_base] in Hck. rewrite Hb in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hcb & Hmb).
cbn [cbyte YP09.c_off YP09.c_val sv_denot] in Hcb. injection Hcb as <-.
rewrite Z.add_0_r in Hmb. exact Hmb.
Qed.

Lemma ho_aview_of_mbyte : forall (Wx : world SEGS) m a (bb : byte),
  mbyte SEGS (mrestrict (w_H Wx) m) a = Some bb -> aview SEGS (w_H Wx) m a = Some (bv_unsigned bb).
Proof. intros Wx m a bb H. unfold aview. rewrite H. reflexivity. Qed.
Lemma ho_val_kept2 : forall (Wa Wb : world SEGS) ma mb a (n : nat) v,
  (forall i, a <= i < a + Z.of_nat n -> aview SEGS (w_H Wb) mb i = aview SEGS (w_H Wa) ma i) ->
  val_mem SEGS (mrestrict (w_H Wa) ma) a n v -> val_mem SEGS (mrestrict (w_H Wb) mb) a n v.
Proof.
intros Wa Wb ma mb a n v HE Hv k Hk. rewrite <- (Hv k Hk).
apply (mbyte_of_aview SEGS). apply HE. lia.
Qed.


Lemma ho_seg_B : ho_seg_C_stmt B -> ho_seg_B_stmt B.
Proof.
unfold ho_seg_B_stmt, ho_seg_C_stmt.
intros HC c fpos ly2 S2 W2 mem2 md2 k2 regs2 sp1 F Hbase H19 H20 H21 H24 Hfsh HchB HoutB.
pose proof (SRr_run_to_pi_AJ (fx := c_fq c) B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ (fx := c_fq c) B LAWS) as RUNP.
unfold ho_base in Hbase.
destruct Hbase as (HPRE & HMID & HSP1 & HFeq & HREGS & HSAVED).
destruct HMID as (HJ & Hfrs2 & Hfa2 & Hperm & HKEPT & HGh & Hflag120 & HlenH & Hk2le).
destruct HSP1 as (Hsp1eq & Hsp1win & Hsp1mod).
destruct HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R22 & R26 & R27).
pose proof HJ as (HAR2 & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk &
  HcA & HcB & HcC & HcD & HcE & Hpres2 & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfin2 : In (1%Z, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
pose proof HPRE as (HPJ & HROD & Hra & Hra4 & Hgp & Htp & Hal16 & Hwin1 & Hwin2 & Hdepth & Hlen & Hnow & Hout & Hh0 & Hh8 & Hin & Hhb & Hhe & Hwr & HOK & LFB & HGH & Hfr50 & Houtp & HKM & HKT & Hchain).
assert (HFaddr : frame_addr ly2 1 fpos = F) by (rewrite Hfa2; symmetry; exact HFeq).
rewrite HFaddr in HFal, HFpres, HFSpres, HF4096, HFceil, HFhigh.
assert (HFR : REAC_HUNT_OBSERVE_STK = 8688) by reflexivity.
rewrite HFR in Hwin1.
assert (HfsF : fs_frame_bytes 1 = 128) by reflexivity.
rewrite HfsF in HFceil, HFpres, HFhigh.
pose proof HFhigh as HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HspZhi : spZ (c_regs c) <= 2 ^ 47) by (clear - Hwin2 Hshi H47; lia).
assert (Hsp1lo : 0 <= sp1) by (clear - Hsp1win Hwin1 Hslo Hceil C1; lia).
assert (Hsp1hi : sp1 < 2 ^ 63) by (clear - Hsp1win HspZhi; lia).
assert (HdisjF : F + 128 <= sp1) by (clear - Hsp1win Hwin1 Hslo Hceil HFceil; lia).
assert (HF0 : 0 <= F) by (clear - HF4096; lia).
assert (HFlt : F + 24 <= 2 ^ 64) by (clear - HFceil C1; lia).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (E9 : ew E 9 = w64 sp1) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl); exact R9).
assert (E26 : ew E 26 = w64 F) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 26 26%bv eq_refl); exact R26).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; clear - Hsp1lo Hsp1hi; lia).
assert (U26 : bv_unsigned (ew E 26) = F) by (rewrite E26; apply unsigned_lit_small; clear - HF0 HFlt C1; lia).
unfold ho_cfg.
assert (HS : st_ok_pi (fx := c_fq c) SEGS VAL E
  (mkSS 28940 sr_atoms [YP09.mkRegion (Some 9%nat) 0 56 0 56 []; YP09.mkRegion (Some 26%nat) 0 24 0 24 []] None (mkFacts [] [] []))
  (restrict (w_H W2) (mkst (fx := c_fq c) regs2 (Z_to_bv 64 (BASE + 28940)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hsp1lo; lia|]. split; [clear - Hsp1hi; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres2. clear - Ho Hsp1win Hwin1 Hslo Hceil Hwin2 C1. lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U26. split; [clear - HF0; lia|]. split; [clear - HFlt; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + o) ltac:(clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint].
    unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U26.
    repeat split; try exact I.
    right. clear - HdisjF. lia.
  - split; [exact I|]. split; exact I. }
paj_run_to_sh RUNTOP HS HJ 0x7148.
{ eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - c_sp0 c);
  [ reflexivity
  | cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite U9; clear; lia
  | cbn [YP09.r_wlo]; clear - Hsp1win Hwin1; lia
  | cbn [YP09.r_whi]; clear - Hsp1win Hwin2; lia
  | ].
  eapply awr_ok_cons_gen with (n := 26%nat) (b := F);
  [ reflexivity
  | rewrite U26; reflexivity
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1%Z, fpos;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
    change (fs_frame_bytes 1) with 128; clear - Ha; lia
  | apply awr_ok_nil ]. }
pose proof (proj1 HJ) as HAR'.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR' Hfin2) as (_ & _ & HFpres' & HFSpres').
rewrite HFaddr in HFpres', HFSpres'. rewrite HfsF in HFpres', HFSpres'.
assert (E27 : ew E 27 = w64 SB) by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs2 _ 27 27%bv eq_refl); exact R27).
assert (HFr8 : 0 <= SB + F / 8 < 2 ^ 64) by (clear - HF0 HFceil C1; unfold SB; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 529 Ev ssv msv [Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
pose proof (img_env_havoc_hi E 529 [Z_to_bv 64 (SB + F / 8)] HEI ltac:(cbv; lia)) as HEI2.
clear HS. rename HS3 into HS.
assert (Eh529 : ew (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) 529 = Z_to_bv 64 (SB + F / 8))
  by (exact (ew_havoc_new E 529 [Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (Eh26 : ew (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) 26 = Z_to_bv 64 F)
  by (rewrite ew_havoc_old by (cbv; lia); exact E26).
assert (Eh27 : ew (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) 27 = Z_to_bv 64 SB)
  by (rewrite ew_havoc_old by (cbv; lia); exact E27).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + F / 8))
    (eq_trans (shadow_decl_ok Ev 26 27 529 F SB Eh26 ltac:(clear - HF0 HFlt; lia) Eh27 Eh529)
              ltac:(cbn [sv_denot]; rewrite Eh529, Z.add_0_r; rewrite unsigned_lit_small by exact HFr8; reflexivity))
    R25 end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (25%bv : bv 5) (SOff 529 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite Eh529, Z.add_0_r, R25; rewrite unsigned_lit_small by exact HFr8; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
assert (Eh9 : ew (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) 9 = Z_to_bv 64 sp1)
  by (rewrite ew_havoc_old by (cbv; lia); exact E9).
assert (B529 : base_val (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) (Some 529%nat) = SB + F / 8)
  by (cbn [base_val]; rewrite Eh529; apply unsigned_lit_small; exact HFr8).
assert (B9 : base_val (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) (Some 9%nat) = sp1)
  by (cbn [base_val]; rewrite Eh9; apply unsigned_lit_small; clear - Hsp1lo Hsp1hi; lia).
assert (B26 : base_val (havoc E 529 [Z_to_bv 64 (SB + F / 8)]) (Some 26%nat) = F)
  by (cbn [base_val]; rewrite Eh26; apply unsigned_lit_small; clear - HF0 HFlt; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv (fshadow_region 529 1 0 12 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
        rewrite B529; change (fs_frame_bytes 1 / 8) with 16;
        split; [clear - HFr8; lia|]; split; [clear - HF0 HFceil C1; unfold SB; lia|]; split; [|constructor];
        intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres';
        apply (proj1 (HFSpres' o ltac:(clear - Ho; lia))))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
        cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
        rewrite B529, B9, B26; change (fs_frame_bytes 1 / 8) with 16;
        split; [left; clear - HF0 HFceil C1 Hsp1win Hwin1 Hslo Hceil; unfold SB; lia|];
        split; [|exact I];
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh; destruct HFhigh as (_ & [HFlo | (HFbig & _)]);
        [right; clear - HFlo HF0; unfold SB; lia | left; clear - HFbig HF0; unfold SB; lia])) as HS3 end.
clear HS. rename HS3 into HS.
paj_run_to_shc RUNTOP HS HJ 0x7178.
{ eapply awr_ok_cons_gen with (n := 529%nat) (b := SB + F / 8);
  [ reflexivity
  | rewrite Eh529; apply unsigned_lit_small; exact HFr8
  | unfold fshadow_region; cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1%Z, fpos;
    split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
    unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 1 / 8) with 16; clear - Ha; lia
  | ].
  eapply awr_ok_cons_stack_off with (n := 9%nat) (d := sp1 - c_sp0 c);
  [ reflexivity
  | rewrite Eh9, unsigned_lit_small by (clear - Hsp1lo Hsp1hi; lia); clear; lia
  | cbn [YP09.r_wlo]; clear - Hsp1win Hwin1; lia
  | cbn [YP09.r_whi]; clear - Hsp1win Hwin2; lia
  | ].
  eapply awr_ok_cons_gen with (n := 26%nat) (b := F);
  [ reflexivity
  | rewrite Eh26; apply unsigned_lit_small; clear - HF0 HFlt; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right; exists 1%Z, fpos;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite HFaddr;
    change (fs_frame_bytes 1) with 128; clear - Ha; lia
  | apply awr_ok_nil ]. }
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (24%bv : bv 5) Q24. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25.
assert (BE9 : base_val E (Some 9%nat) = sp1) by (cbn [base_val]; exact U9).
assert (BE26 : base_val E (Some 26%nat) = F) by (cbn [base_val]; exact U26).
assert (UNCH : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 56) -> ~ (F <= a < F + 24) ->
  ~ (SB + F / 8 <= a < SB + F / 8 + 12) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2 Hn3.
  rewrite (ho_aview_frame _ _ W2 (ms_mem ms) (ms_mem ms0) a HFr0 Ha).
  - apply (ho_aview_frame _ _ W2 mem2 (ms_mem ms) a HFr Ha).
    intros (rr & Hinw & Hr).
    lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end.
    cbn [In] in Hinw.
    destruct Hinw as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    [rewrite BE9 in Hr | rewrite BE26 in Hr]; clear - Hr Hn1 Hn2; lia.
  - intros (rr & Hinw & Hr).
    lazymatch type of Hinw with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rr rs1) in Hinw end.
    cbn [In] in Hinw.
    destruct Hinw as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    [rewrite B529 in Hr | rewrite B9 in Hr | rewrite B26 in Hr]; clear - Hr Hn1 Hn2 Hn3; lia. }
assert (HFSH : SB + F / 8 + 16 < YM05.alloc_ceiling) by (clear - HF0 HFceil C1; unfold SB; lia).
assert (HshHi : SB + F / 8 + 16 <= 17594333495296) by (clear - HF0 HFceil C1; unfold SB; lia).
assert (HstkF : F + 128 <= sp1) by (clear - HFceil Hsp1win Hwin1 Hslo Hceil; lia).
assert (HstkS : SB + F / 8 + 16 <= sp1) by (clear - HFSH Hsp1win Hwin1 Hslo Hceil; lia).
assert (HKEPT2 : treac_hunt_observe_kept B (c_lyc c) (c_Sc c) (c_W c) (c_memc c) W2 (ms_mem ms0)
  (spZ (c_regs c)) (c_h c) (c_out c)).
{ pose proof HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Jpres & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hnw Hw. rewrite HFR in Hnw.
    rewrite (UNCH a ltac:(clear - Ha C1; lia)
      ltac:(clear - Hnw Hsp1win Hwin1 Hwin2; lia)
      ltac:(clear - Ha HFceil C1; lia)
      ltac:(clear - Ha HFSH C1; lia)).
    exact (K1 a Ha ltac:(rewrite HFR; exact Hnw) Hw).
  - intros b m i Hbl Hi Hw.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m (proj1 HJ)
      (Permutation_in _ (Permutation_sym Hperm) Hbl)) as (_ & Gb4096 & Gbceil & Gbapp & _ & _).
    assert (Hd : zdisjoint (b, req_size m) (frame_addr ly2 1 fpos, fs_frame_bytes 1))
      by (apply (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms0) _ b m 1 fpos (proj1 HJ)
                  (Permutation_in _ (Permutation_sym Hperm) Hbl) Hfin2)).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFaddr, HfsF in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gbapp.
    rewrite (UNCH (b + i) ltac:(clear - Hi Gb4096 Gbceil C1; lia)
      ltac:(clear - Hi Gbceil Hsp1win Hwin1 Hslo Hceil; lia)
      ltac:(clear - Hi Hd; lia)
      ltac:(clear - Hi Gbapp HF0 HFceil C1; unfold SB; lia)).
    exact (K2 b m i Hbl Hi Hw).
  - intros a Hia Ho He.
    pose proof (pa_segs_low a Hia) as Hl. unfold kLowMemEnd in Hl.
    pose proof (frm_off_imgP _ _ _ _ _ _ 1 fpos (proj1 HJ) Hfin2) as Hfimg.
    rewrite HFaddr, HfsF in Hfimg. unfold off_img, IMG_LO, IMG_TOP in Hfimg.
    pose proof (pa_img_range a Hia) as Hilo. unfold IMG_LO, IMG_TOP in Hilo.
    rewrite (UNCH a ltac:(clear - Hl; lia)
      ltac:(clear - Hl Hsp1win Hwin1 Hslo Hceil C1; lia)
      ltac:(clear - Hl Hilo Hfimg; unfold IMG_LO, IMG_TOP in *; lia)
      ltac:(clear - Hl HF0; unfold SB; lia)).
    exact (K3 a Hia Ho He).
  - intros cid pos a Hf Hr Hw.
    destruct (in_split _ _ Hf) as (l2 & l3 & Hsplit).
    assert (Hd : zdisjoint (frame_rng ly2 (1%Z, fpos)) (frame_rng ly2 (cid, pos)))
      by (apply (sep_frames_pos SEGS B LAWS ly2 S2 W2 (ms_mem ms0) _ (1%Z, fpos) (cid, pos) [] l2 l3 (proj1 HJ));
          rewrite Hfrs2, Hsplit; reflexivity).
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite HFaddr, HfsF in Hd.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos (proj1 HJ)
      ltac:(rewrite Hfrs2; right; exact Hf)) as (G1 & G2 & G3).
    pose proof (fs_frame_bytes_nonneg cid) as Gn.
    rewrite (Hfa2 cid pos) in Hd, G1, G2, G3.
    unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hr. cbn [fst snd] in Hr.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G3.
    rewrite (UNCH a ltac:(clear - Hr G1 G2 Gn C1 G3; lia)
      ltac:(clear - Hr G1 G2 Gn C1 G3 Hsp1win Hwin1 Hslo Hceil; lia)
      ltac:(clear - Hr Hd Gn G1 G2 G3 HFapp HF0 HFceil C1; lia)
      ltac:(clear - Hr Hd Gn G1 G2 G3 HFapp HF0 HFceil C1; unfold SB; lia)).
    exact (K4 cid pos a Hf Hr Hw).
  - intros a Ha Hnw Hp. rewrite HFR in Hnw.
    apply (ho_pres_hi2 W2 mem2 (ms_mem ms0) a Ha).
    + rewrite (UNCH a ltac:(clear - Ha C1; lia)
        ltac:(clear - Hnw Hsp1win Hwin1 Hwin2; lia)
        ltac:(clear - Ha HFceil C1; lia)
        ltac:(clear - Ha HFSH C1; lia)). reflexivity.
    + exact (K5 a Ha ltac:(rewrite HFR; exact Hnw) Hp).
  - intros a Ha. rewrite HFR in Ha. apply Jpres. clear - Ha Hwin1 Hwin2; lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (c_hb c) (c_hn c) (proj1 HJ)
  (Permutation_in _ (Permutation_sym Hperm) Hin)) as (_ & Hb4096 & Hbceil & Hbapp & _ & _).
assert (Hdh : zdisjoint (c_hb c, req_size (c_hn c)) (frame_addr ly2 1 fpos, fs_frame_bytes 1))
  by (apply (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem ms0) _ (c_hb c) (c_hn c) 1 fpos (proj1 HJ)
              (Permutation_in _ (Permutation_sym Hperm) Hin) Hfin2)).
unfold zdisjoint in Hdh. cbn [fst snd] in Hdh. rewrite HFaddr, HfsF in Hdh.
pose proof Hbapp as Hbapp2. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp2.
assert (HUNCHh : forall i, c_h c <= i < c_h c + 480 ->
  aview SEGS (w_H W2) (ms_mem ms0) i = aview SEGS (w_H W2) mem2 i).
{ intros i Hi. apply UNCH.
  - clear - Hi Hhb Hhe Hb4096 Hbceil C1; lia.
  - clear - Hi Hhb Hhe Hbceil Hsp1win Hwin1 Hslo Hceil; lia.
  - clear - Hi Hhb Hhe Hdh; lia.
  - clear - Hi Hhb Hhe Hbapp2 HF0 HFceil C1; unfold SB; lia. }
assert (HGH2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) (c_h c)
  (map (fun b : byte => bv_unsigned b) (c_H c))).
{ apply (ho_garr_kept W2 W2 mem2 (ms_mem ms0) (c_h c) _); [|exact HGh].
  intros i Hi. rewrite length_map in Hi. apply HUNCHh.
  pose proof HOK as (HL & _ & _ & _). clear - Hi HL; lia. }
assert (HFLG2 : rdword (aview SEGS (w_H W2) (ms_mem ms0)) (frame_addr (c_lyc c) 1 fpos + 120) =
  Some (flag_addr (c_lyc c) 1 fpos)).
{ rewrite <- Hflag120. apply rdword_ext. intros kk Hkk. rewrite <- HFeq. apply UNCH.
  - clear - Hkk HF0 HFceil C1; lia.
  - clear - Hkk HFceil Hsp1win Hwin1 Hslo Hceil; lia.
  - clear - Hkk; lia.
  - clear - Hkk HF0 HFceil C1 HFapp; unfold SB in *; lia. }
assert (HSAVED2 : ho_saved c W2 (ms_mem ms0)).
{ intros j Hj. apply (ho_val_kept2 W2 W2 mem2 (ms_mem ms0)).
  - intros i Hi. cbn [Z.of_nat] in Hi. apply UNCH.
    + clear - Hi Hj Hwin1 Hslo Hceil C1 HspZhi; lia.
    + clear - Hi Hj Hsp1win; lia.
    + clear - Hi Hj HFceil Hwin1 Hslo Hceil; lia.
    + clear - Hi Hj HFSH Hwin1 Hslo Hceil; lia.
  - exact (HSAVED j Hj). }
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as Hreg0.
cbn [ms_mem restrict] in Hreg0.
assert (HFSH2 : ho_fsh W2 (ms_mem ms0) F ho_shC).
{ intros i Hi.
  assert (HUP : forall k, 12 <= k < 16 -> aview SEGS (w_H W2) (ms_mem ms0) (SB + F / 8 + k) =
                 aview SEGS (w_H W2) mem2 (SB + F / 8 + k)).
  { intros kz Hkz. apply UNCH.
    - clear - Hkz HF0 HFceil C1; unfold SB; lia.
    - clear - Hkz HFSH Hsp1win Hwin1 Hslo Hceil; lia.
    - clear - Hkz HF0 HFceil C1 HFapp; unfold SB in *; lia.
    - clear - Hkz; lia. }
  assert (Hcase : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/
                  i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15)
    by (clear - Hi; lia).
  destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
  [ rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 0 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 1 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 2 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 3 18446744073709551601 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 4 0 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 5 0 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 6 0 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 7 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 8 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 9 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 10 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (ho_aview_of_mbyte W2 (ms_mem ms0) _ _
      (ho_chunk_byte _ _ (SB + F / 8) _ _ _ _ _ 11 18446744073709551603 Hreg0 B529 ltac:(cbn [In]; tauto)))
  | rewrite (HUP 12 ltac:(lia)), (Hfsh 12 ltac:(lia))
  | rewrite (HUP 13 ltac:(lia)), (Hfsh 13 ltac:(lia))
  | rewrite (HUP 14 ltac:(lia)), (Hfsh 14 ltac:(lia))
  | rewrite (HUP 15 ltac:(lia)), (Hfsh 15 ltac:(lia)) ];
  vm_compute; reflexivity. }
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
prreg HS (22%bv : bv 5) P22. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
pmkst HS.
eapply (HC c fpos ly2 S2 W2 _ _ _ _ sp1 F).
2: rewrite Q19, (EE 19%nat 19%bv eq_refl); exact H19.
2: rewrite Q20, (EE 20%nat 20%bv eq_refl); exact H20.
2: rewrite Q21, (EE 21%nat 21%bv eq_refl); exact H21.
2: rewrite Q24, (EE 24%nat 24%bv eq_refl); exact H24.
2: rewrite Q23, U26; reflexivity.
2: rewrite Q25; reflexivity.
unfold ho_base, ho_mid, ho_sp1, ho_regs_mid.
split; [exact HPRE|].
split; [split; [exact HJ|]; split; [exact Hfrs2|]; split; [exact Hfa2|];
        split; [exact Hperm|]; split; [exact HKEPT2|]; split; [exact HGH2|];
        split; [exact HFLG2 | split; [exact HlenH | exact Hk2le]]|].
split; [split; [exact Hsp1eq|]; split; [exact Hsp1win | exact Hsp1mod]|].
split; [exact HFeq|].
split.
{ split; [rewrite P2, (EE 2%nat 2%bv eq_refl); exact R2|].
  split; [rewrite P3, (EE 3%nat 3%bv eq_refl); exact R3|].
  split; [rewrite P4, (EE 4%nat 4%bv eq_refl); exact R4|].
  split; [rewrite P8, (EE 8%nat 8%bv eq_refl); exact R8|].
  split; [rewrite P9, (EE 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite P18, (EE 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite P22, (EE 22%nat 22%bv eq_refl); exact R22|].
  split; [rewrite P26, (EE 26%nat 26%bv eq_refl); exact R26
         | rewrite P27, (EE 27%nat 27%bv eq_refl); exact R27]. }
{ exact HSAVED2. }
exact HFSH2.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Hlytop & _).
destruct HchB as (ch0 & HCH0). exists ch0.
apply (achain_kept ly2 (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) (ms_mem ms0))
  (spZ (c_regs c) - 16) (spZ (c_regs c)) ch0 (spZ (c_regs c) - 16) HCH0
  ltac:(clear; lia) ltac:(rewrite Hlytop; clear - Htop H47; lia)).
intros a Ha. apply UNCH;
[ clear - Ha Hwin1 Hslo Hceil C1; lia
| clear - Ha Hsp1win; lia
| clear - Ha HFceil Hwin1 Hslo Hceil; lia
| clear - Ha HFSH Hwin1 Hslo Hceil; lia ].
intros Ho0. apply (ho_garr_kept W2 W2 mem2 (ms_mem ms0) (c_out c) _); [|exact (HoutB Ho0)].
intros i Hi. rewrite length_map in Hi.
destruct (Houtp Ho0) as (Htout & Houth & _).
pose proof Htout as (Hom & Hob & Homr & Hows & Hosep & _ & _ & _ & HOl & _ & Hofr).
rewrite HOl in Hi.
assert (Hdo : ~ (F <= i < F + 24) /\ ~ (SB + F / 8 <= i < SB + F / 8 + 12)).
{ destruct Hofr as [(cid & pos & Hfo & Ho1 & Ho2) | (b & m & Hbo & Ho1 & Ho2)].
  - assert (Hfo2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; right; exact Hfo).
    destruct (in_split _ _ Hfo) as (l2 & l3 & Hsp).
    assert (Hd : zdisjoint (frame_rng ly2 (1%Z, fpos)) (frame_rng ly2 (cid, pos)))
      by (apply (sep_frames_pos SEGS B LAWS ly2 S2 W2 mem2 _ (1%Z, fpos) (cid, pos) [] l2 l3 HAR2);
          rewrite Hfrs2, Hsp; reflexivity).
    unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
    rewrite HFaddr, HfsF, (Hfa2 cid pos) in Hd.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR2 Hfo2) as (G1 & G2 & G3).
    rewrite (Hfa2 cid pos) in G1, G2, G3.
    pose proof G3 as G3u. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G3u.
    pose proof (fs_frame_bytes_nonneg cid) as Gn.
    unfold SB in *.
    exact (ho_out_disj i (frame_addr (c_lyc c) cid pos) (fs_frame_bytes cid) F
             ltac:(clear - Hi Ho1; lia) ltac:(clear - Hi Ho2; lia) Hd ltac:(destruct (proj2 G3u) as [X|[X _]]; [left; exact X | right; exact X]) HF0 HshHi).
  - assert (Hbo2 : In (b, m) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hbo).
    assert (Hd : zdisjoint (b, req_size m) (frame_addr ly2 1 fpos, fs_frame_bytes 1))
      by (apply (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 _ b m 1 fpos HAR2 Hbo2 Hfin2)).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFaddr, HfsF in Hd.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hbo2) as (_ & Gb1 & Gb2 & Gb3 & _ & _).
    pose proof Gb3 as Gb3u. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Gb3u.
    unfold SB in *.
    exact (ho_out_disj i b (req_size m) F
             ltac:(clear - Hi Ho1; lia) ltac:(clear - Hi Ho2; lia)
             ltac:(destruct Hd as [X|X]; [right; exact X | left; exact X])
             ltac:(destruct (proj2 Gb3u) as [X|[X _]]; [left; exact X | right; exact X]) HF0 HshHi). }
apply UNCH;
[ clear - Hi Hout Hob; lia
| rewrite HFR in Hows; clear - Hi Hows Hsp1win; lia
| clear - Hdo; lia
| clear - Hdo; lia ].
Qed.

End h.
End f.
End d.
