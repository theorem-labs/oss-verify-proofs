(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08 YI59.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACey ACev Nrfc6 Nrfc45.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section R1.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Variable MT : ameter_ops.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rfc_C1_ok : RFC_C3_stmt B MT -> RFC_C1_stmt B MT.
Proof.
intros RC3s.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 regs1 mem1 md1 r1 cur1 fattr T P
RC HPL HJ1 HH1 HRC HFR HM RAdst1 KEPT1 HIO1.
pose proof RC as ((HMOK & HCOST & HlenP) & HPerm & Hpd & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hown & HfinC & Hcid & Hfal & Hst1 & Hst2 & Hdst1 & Hdst2 & Hsd
& Hst8 & Hdst8 & HN & Hcur & Hnb & HSEP & HlyF & Hev & Hlive & (HFhi1 & HFimg & HFhi2) & HFceil & (Hph & Hpimg & Hpapp) & Hpceil & HnbM).
rbox HFimg. rbox HFhi2. rbox Hpimg. rbox Hpapp.
pose proof HH1 as (Hr1 & Hhd & Hfattr).
pose proof HM as (Wp & Wn & Wc & _).
pose proof HRC as ((R2 & R3 & R4 & R8 & R18 & R19 & R25 & R22 & R9 & R20 & R23 & R24 & R27) & RC10 & RC14 & RC15 & RC13).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ1 as (HAR1 & Hly1 & _ & _ & _ & _ & Hnev1 & _ & _ & _ & _ & _ & _ & Hpres1 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EFA1 : forall c p, frame_addr lyc c p = frame_addr lyc c p) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity. assert (HEV : EV_RFC = 6) by reflexivity.
assert (HBb1 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc Sc)) by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
assert (Hpdc : In (pdata, nb) (ablocks B lyc Sc)) by (apply HBb1; exact Hpd).
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2].
pose proof (fs_frame_bytes_nonneg cid) as HFB.
assert (HSPB : alloc_ceiling <= spZ regs - TRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia).
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia).
assert (HDST0 : 4096 <= dst) by (clear - Hdst1 HFhi1; lia). assert (HDSTC : dst + 32 <= alloc_ceiling) by (clear - Hdst2 HFceil; lia).
assert (HDSTH : rboxed (dst + 32 <= 2147446784 \/ 17594333495296 <= dst)) by (unfold rboxed in *; clear - Hdst1 Hdst2 HFhi2; lia).
assert (Hpdst : rboxed (pdata + req_size nb <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= pdata)).
{ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ pdata nb cid pos HAR1 Hpdc HfinC) as D. unfold zdisjoint in D. cbn [fst snd] in D. exact D. }
assert (HV : rfc_vals (bv_unsigned (getr regs1 25)) cur 0 0 fattr 0 0 0 cur nb) by (unfold rfc_vals; pose proof (bv_unsigned_in_range 64 (getr regs1 25)) as HRg; change (bv_modulus 64) with (2 ^ 64) in HRg; repeat split; lia).
remember (Ereg regs1 (I_extra regs pdata nb cur 0 fattr 0 0 0 0)) as E eqn:HE.
pose proof (rfc_C1_entry B TL LAWS W1 regs regs1 mem1 lyc Sc md1 ly STK sp0 st dst N pdata nb cur 0 fattr 0 0 0 0 cid pos cur r1 cur1
HAR1 Hpdc HfinC Hst1 Hst2 Hdst1 Hdst2 Hsd Hst8 Hdst8 HN Hnb HV ltac:(clear - Hcur; lia) Hstk Hal16 Hwlo Hwhi Hpres1 HRC HFR HM) as HS. rewrite <- HE in HS.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; clear - HSPB C1 HTS Has; lia).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 dst) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = Z_to_bv 64 N) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 st) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E10 : ew E 10 = Z_to_bv 64 (dst + 16)) by (rewrite (EE 10%nat 10%bv eq_refl); exact RC10).
assert (E13 : ew E 13 = Z_to_bv 64 cur1) by (rewrite (EE 13%nat 13%bv eq_refl); exact RC13).
assert (E15 : ew E 15 = Z_to_bv 64 r1) by (rewrite (EE 15%nat 15%bv eq_refl); exact RC15).
assert (EX : forall j, ew E (32 + j) = nth j (I_extra regs pdata nb cur 0 fattr 0 0 0 0) (Z_to_bv 64 0)) by (intros j; rewrite HE; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 pdata) by exact (EX 0%nat). assert (E33 : ew E 33 = Z_to_bv 64 nb) by exact (EX 1%nat).
assert (E34 : ew E 34 = Z_to_bv 64 cur) by exact (EX 2%nat). assert (E35 : ew E 35 = Z_to_bv 64 0) by exact (EX 3%nat).
assert (E36 : ew E 36 = getr regs 1) by exact (EX 4%nat). assert (E37 : ew E 37 = getr regs 8) by exact (EX 5%nat).
assert (E38 : ew E 38 = getr regs 9) by exact (EX 6%nat). assert (E39 : ew E 39 = getr regs 18) by exact (EX 7%nat).
assert (E40 : ew E 40 = getr regs 19) by exact (EX 8%nat). assert (E41 : ew E 41 = getr regs 20) by exact (EX 9%nat).
assert (E42 : ew E 42 = getr regs 21) by exact (EX 10%nat). assert (E43 : ew E 43 = getr regs 22) by exact (EX 11%nat).
assert (E44 : ew E 44 = getr regs 23) by exact (EX 12%nat). assert (E45 : ew E 45 = getr regs 24) by exact (EX 13%nat).
assert (E46 : ew E 46 = getr regs 25) by exact (EX 14%nat). assert (E47 : ew E 47 = getr regs 26) by exact (EX 15%nat).
assert (E48 : ew E 48 = Z_to_bv 64 fattr) by exact (EX 16%nat). assert (E49 : ew E 49 = Z_to_bv 64 0) by exact (EX 17%nat).
assert (E50 : ew E 50 = Z_to_bv 64 0) by exact (EX 18%nat). assert (E51 : ew E 51 = Z_to_bv 64 0) by exact (EX 19%nat).
assert (E52 : ew E 52 = Z_to_bv 64 0) by exact (EX 20%nat).
clear EX.
assert (B19 : bv_unsigned (ew E 19) = st) by (rewrite E19; apply unsigned_lit_small; lia).
assert (B8 : bv_unsigned (ew E 8) = dst) by (rewrite E8; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
set (Zs := fun a : Z => spZ regs - TRFC_STK <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
assert (ZBsm : forall a, SB <= a < kHighShadowEnd -> ~ Zsm a).
{ intros a Ha. subst Zsm. cbn beta. clear - Ha HSPB HSTB HDST0 HDSTH HTS Has C1 C2 C3 C4 C5. unfold rboxed in HDSTH. unfold SB in Ha. lia. }
reshok_bx HS 22%nat.
pose proof HM as (_ & _ & _ & Wl & Wz & Wfa & Wfg & Wde & Wnl & Wti).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR1 HfinC) as (_ & _ & HFpres & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
assert (HRX : region_ok tfibsegs Ex (ms_mem msx) (YP09.mkRegion (Some 8%nat) 0 32 0 32 [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CZero 8); YP09.mkChunk 16 (CVal 4 (SOff 48 0));
  YP09.mkChunk 20 (CZero 2); YP09.mkChunk 22 (CZero 2); YP09.mkChunk 24 (CVal 2 (SOff 50 0)); YP09.mkChunk 26 (CVal 2 (SOff 51 0)); YP09.mkChunk 28 (CVal 1 (SOff 52 0))])) end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst]. rewrite B8.
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable tfibsegs). apply (proj1 (HFpres (dst + o) ltac:(lia))). }
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val tfibsegs _ _ dst 0 8 _ 0); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Wl].
  + apply (chunk_ok_zero tfibsegs). intros i Hi. cbn [YP09.c_len YP09.cv_len] in Hi. specialize (Wz (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Wz by lia. rewrite Wz. f_equal. f_equal.
    unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
  + apply (chunk_ok_val tfibsegs _ _ dst 16 4 _ fattr); [cbn [sv_denot]; rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wfa].
  + apply (chunk_ok_zero tfibsegs). intros i Hi. cbn [YP09.c_len YP09.cv_len] in Hi.
    pose proof (Wfg (Z.to_nat (0 + i)) ltac:(lia)) as Wq. rewrite Z2Nat.id in Wq by lia.
    replace (dst + 20 + i) with (dst + 20 + (0 + i)) by lia. rewrite Wq. f_equal. f_equal.
    unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
  + apply (chunk_ok_zero tfibsegs). intros i Hi. cbn [YP09.c_len YP09.cv_len] in Hi.
    pose proof (Wfg (Z.to_nat (2 + i)) ltac:(lia)) as Wq. rewrite Z2Nat.id in Wq by lia.
    replace (dst + 22 + i) with (dst + 20 + (2 + i)) by lia. rewrite Wq. f_equal. f_equal.
    unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity.
  + apply (chunk_ok_val tfibsegs _ _ dst 24 2 _ 0); [cbn [sv_denot]; rewrite E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wde].
  + apply (chunk_ok_val tfibsegs _ _ dst 26 2 _ 0); [cbn [sv_denot]; rewrite E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wnl].
  + apply (chunk_ok_val tfibsegs _ _ dst 28 1 _ 0); [cbn [sv_denot]; rewrite E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Wti]. }
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
lazymatch type of HRX with region_ok _ _ _ ?rx => pose proof (ast_ok_set_region tfibsegs Ex ssx msx 3%nat _ rx HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HRX) as HS3; clear HS; rename HS3 into HS end end.
clear HRX. norm_ss HS.
change mem1 with (ms_mem (mkst regs1 (Z_to_bv 64 RFC_RD1) mem1 (seg_rom tfibsegs))) in HJ1.
destruct (Z_le_gt_dec (cur1 + 4) nb) as [CA|CA].
{ assert (HC2 : cur1 = cur + 2) by (destruct Hhd as [(_ & _ & X & _)|(_ & X & ->)]; [exact X | lia]).
assert (GB : forall j, 0 <= j < 4 -> aview tfibsegs (w_H W1) mem1 (pdata + (cur1 + j)) = Some (hb P cur (2 + j))).
{ intros j Hj. rewrite (proj1 (proj2 KEPT1) pdata nb (cur1 + j) Hpd) by (unfold req_size; destruct (Z.eqb_spec nb 0); lia).
  unfold hb. replace (pdata + (cur1 + j)) with (pdata + Z.of_nat (Z.to_nat (cur + (2 + j)))) by lia.
  apply (garr8_aview _ _ _ _ HPL). lia. }
assert (HBR : forall j, 0 <= j < 4 -> 0 <= hb P cur (2 + j) < 256)
  by (intros j Hj; destruct (aview_byte tfibsegs _ _ _ _ (GB j Hj)) as (bb & _ & _ & Hr); exact Hr).
assert (VB : forall i, (i < 4)%nat -> val_mem tfibsegs (mrestrict (w_H W1) mem1) (pdata + cur1 + Z.of_nat i) 1 (hb P cur (2 + Z.of_nat i))).
{ intros i Hi. replace (pdata + cur1 + Z.of_nat i) with (pdata + (cur1 + Z.of_nat i)) by (clear; lia).
  exact (val_mem1_of_aview _ _ _ _ (GB (Z.of_nat i) ltac:(clear - Hi; lia))). }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let WS := constr:(map (Z_to_bv 64) ((pdata + cur1) :: map (fun i => hb P cur (2 + Z.of_nat i)) (seq 0 4))) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS;
assert (EQ : ew (havoc Ev K WS) K = Z_to_bv 64 (pdata + cur1)) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; clear; lia)));
assert (EBy : forall i, (i < 4)%nat -> ew (havoc Ev K WS) (K + (1 + i)) = Z_to_bv 64 (hb P cur (2 + Z.of_nat i)))
  by (intros i Hi; rewrite (ew_havoc_new Ev K WS (1 + i) (Z_to_bv 64 0)) by (cbn [length map seq]; clear - Hi; lia);
      do 4 (destruct i as [|i]; [reflexivity|]); clear - Hi; lia)
end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_alias tfibsegs Ev ssv msv (SAlu ALU_ADD (SOff 32 0) (SOff 13 0)) (SOff K 0) HS
  ltac:(transitivity (Z_to_bv 64 (pdata + cur1));
        [ apply denot_add_atoms; [enorm; exact E32 | enorm; exact E13 | clear - Hph; lia | clear - Hcur HC2; lia | clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB C1; lia]
        | cbn [sv_denot]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB C1; lia); rewrite Z.add_0_r; reflexivity ])) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (src_region K 4) HS eq_refl
  (src_region_ok Ev _ K 4 (pdata + cur1) (fun i => hb P cur (2 + Z.of_nat i))
     ltac:(rewrite EQ; apply unsigned_lit_small; clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(clear - Hcur Hph HC2; lia) ltac:(cbn; clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(intros i Hi; split; [exact (EBy i Hi) | split; [exact (HBR (Z.of_nat i) ltac:(clear - Hi; lia)) | exact (VB i Hi)]]))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold src_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB C1; lia);
    enorm; agnorm; rewrite B8, B19, Usp;
    unfold A_GOT_shadow, A_shadow_glob, off_img in *; unfold rboxed in *;
    clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB HSTB Hpdst Hdst1 Hdst2 Hst1 Hpimg Hpapp HTS Has C1; cbn; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ K (mkAF 4096 140737479966720 0) HS
  ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 HSPB C1; lia);
         rewrite Z.pow_0_r, Z.mod_1_r; clear - Hcur Hnb HC2 CA Hph Hpceil Hrq2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end end.
pose proof (EBy 0%nat ltac:(lia)) as EB0. pose proof (EBy 1%nat ltac:(lia)) as EB1. pose proof (EBy 2%nat ltac:(lia)) as EB2. pose proof (EBy 3%nat ltac:(lia)) as EB3. cbn [Nat.add Z.of_nat] in EB0, EB1, EB2, EB3. clear EBy GB VB.
rebaseH HS AG.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
assert (HB2 : 0 <= hb P cur 2 < 256) by exact (HBR 0 ltac:(lia)). assert (HB3 : 0 <= hb P cur 3 < 256) by exact (HBR 1 ltac:(lia)).
assert (HB4 : 0 <= hb P cur 4 < 256) by exact (HBR 2 ltac:(lia)). assert (HB5 : 0 <= hb P cur 5 < 256) by exact (HBR 3 ltac:(lia)).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (RAst1 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAst1 E19 E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
2: { exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur1 2) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur1 + 2)); [lia | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur1) 4)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CA HC2 Hcur Hrq2; lia);
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN2. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT2 HSEP UN2 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT3. clear KEPT2.
vkeepUN2 UN2 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
2: { exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur1 4) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur1 + 4)); [lia | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur1) 4)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CA HC2 Hcur Hrq2; lia);
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN2; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_RD3.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN3. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT3 HSEP UN3 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT3.
vkeepUN2 UN3 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKJ : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) _ a)
  by (intros a Ha; apply UN3; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHKJ ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as RAdstJ. clear SHKJ.
rename Wp into Vp. rename Wn into Vn. clear Wc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 4%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 5%nat _ HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict] in HRt;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
pose proof (field_of_region _ _ 19%nat st _ _ _ _ _ 16 8 (SOff 13 2) (cur1 + 2) HRt B18n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite E13, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 0 8 (SOff 35 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 16 4 (SOff 48 0) fattr HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 26 2 (SOff 51 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 28 1 (SOff 52 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 22 2 (dst + 22) 2 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as V22.
pose proof (field1_of_region _ _ 8%nat dst _ _ _ _ _ 20 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 55 0)) (SLit 8)) (SExt false 8 (SOff 54 0))) ((hb P cur 2) + 256 * (hb P cur 3)) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8 _ 55 54 (hb P cur 3) (hb P cur 2)); [enorm; exact EB1 | enorm; exact EB0 | lia | lia])
  ltac:(lia)) as Vq0.
replace (((hb P cur 2) + 256 * (hb P cur 3)) mod 256) with (hb P cur 2) in Vq0 by (rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia; reflexivity).
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 21 1 (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 55 0)) (SLit 8)) (SExt false 8 (SOff 54 0))) (SLit 8)) (hb P cur 3) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8_hi _ 55 54 (hb P cur 3) (hb P cur 2)); [enorm; exact EB1 | enorm; exact EB0 | lia | lia])
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vq1.
replace (dst + 21) with (dst + 20 + 1) in Vq1 by lia.
pose proof (val_mem_bytes2 _ _ _ _ Vq0 Vq1 ltac:(lia) ltac:(lia)) as V20. clear Vq0 Vq1.
replace (dst + 22) with (dst + 20 + 2) in V22 by lia.
pose proof (val_mem_half2 _ _ _ _ V20 V22 ltac:(lia) ltac:(lia)) as Vfg. rewrite Z.mul_0_r, Z.add_0_r in Vfg. clear V20 V22.
pose proof (field1_of_region _ _ 8%nat dst _ _ _ _ _ 24 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 57 0)) (SLit 8)) (SExt false 8 (SOff 56 0))) ((hb P cur 4) + 256 * (hb P cur 5)) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8 _ 57 56 (hb P cur 5) (hb P cur 4)); [enorm; exact EB3 | enorm; exact EB2 | lia | lia])
  ltac:(lia)) as Vq0.
replace (((hb P cur 4) + 256 * (hb P cur 5)) mod 256) with (hb P cur 4) in Vq0 by (rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia; reflexivity).
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 25 1 (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 57 0)) (SLit 8)) (SExt false 8 (SOff 56 0))) (SLit 8)) (hb P cur 5) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8_hi _ 57 56 (hb P cur 5) (hb P cur 4)); [enorm; exact EB3 | enorm; exact EB2 | lia | lia])
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vq1.
replace (dst + 25) with (dst + 24 + 1) in Vq1 by lia.
pose proof (val_mem_bytes2 _ _ _ _ Vq0 Vq1 ltac:(lia) ltac:(lia)) as Vde. clear Vq0 Vq1.
pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Uspn
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
clear HRd HRs HRt.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vc, Vl, Vfa, Vnl, Vti. rewrite Z.add_0_r in Vl.
destruct Hhd as [(Hz & H2 & Hc1 & Efa) | (_ & X & ->)]; [| exfalso; clear - X CA HC2; lia]. subst r1.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
rreg HS (13%bv : bv 5) Q13. rreg HS (15%bv : bv 5) Q15. rreg HS (16%bv : bv 5) Q16. rreg HS (17%bv : bv 5) Q17.
rreg HS (10%bv : bv 5) Q10. rregS HS (14%bv : bv 5) Q14s.
pose proof (denot_shx _ 19 22 16 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
pose proof (denot_shx _ 19 22 8 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_RD3 end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
eapply (RC3s STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 (ms_regs msX) (ms_mem msX) mdX 0 0 0 (cur1 + 2) (cur1 + 4) fattr (hb P cur 2 + 256 * hb P cur 3) (hb P cur 4 + 256 * hb P cur 5) T P);
[ exact RC | exact HPL | exact HJc
| unfold hdr3; split; [left; reflexivity|]; split; [left; reflexivity|]; split; [left; reflexivity|]; split; [left; repeat split; try reflexivity; lia|]; repeat split; lia
| unfold C3_regs_at, I_regs_at, w64;
  rewrite Q14s, (denot_srl3 _ 8 16 dst) by first [enorm; agnorm; exact E8 | lia];
  rewrite Q23, Q24, D16, D8;
  rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27, Q10, Q13, Q15, Q16, Q17; enorm; agnorm; rewrite ?B19, ?B8;
  rewrite E3, E4, E8, E18, E19, E22, E27, ?E13, ?E15, ?E33, <- Usp, Z_to_bv_bv_unsigned;
  repeat split; try reflexivity; first [ symmetry; apply Z_to_bv_bv_unsigned | rewrite unsigned_lit_small by lia; reflexivity ]
| exact HFR2
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstJ
| exact KEPT4
| io_now ] end end.
}
destruct (Z_le_gt_dec (cur1 + 2) nb) as [CB|CC].
{ assert (HC2 : cur1 = cur + 2) by (destruct Hhd as [(_ & _ & X & _)|(_ & X & ->)]; [exact X | lia]).
assert (GB : forall j, 0 <= j < 2 -> aview tfibsegs (w_H W1) mem1 (pdata + (cur1 + j)) = Some (hb P cur (2 + j))).
{ intros j Hj. rewrite (proj1 (proj2 KEPT1) pdata nb (cur1 + j) Hpd) by (unfold req_size; destruct (Z.eqb_spec nb 0); lia).
  unfold hb. replace (pdata + (cur1 + j)) with (pdata + Z.of_nat (Z.to_nat (cur + (2 + j)))) by lia.
  apply (garr8_aview _ _ _ _ HPL). lia. }
assert (HBR : forall j, 0 <= j < 2 -> 0 <= hb P cur (2 + j) < 256)
  by (intros j Hj; destruct (aview_byte tfibsegs _ _ _ _ (GB j Hj)) as (bb & _ & _ & Hr); exact Hr).
assert (VB : forall i, (i < 2)%nat -> val_mem tfibsegs (mrestrict (w_H W1) mem1) (pdata + cur1 + Z.of_nat i) 1 (hb P cur (2 + Z.of_nat i))).
{ intros i Hi. replace (pdata + cur1 + Z.of_nat i) with (pdata + (cur1 + Z.of_nat i)) by (clear; lia).
  exact (val_mem1_of_aview _ _ _ _ (GB (Z.of_nat i) ltac:(clear - Hi; lia))). }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let WS := constr:(map (Z_to_bv 64) ((pdata + cur1) :: map (fun i => hb P cur (2 + Z.of_nat i)) (seq 0 2))) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS;
assert (EQ : ew (havoc Ev K WS) K = Z_to_bv 64 (pdata + cur1)) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; clear; lia)));
assert (EBy : forall i, (i < 2)%nat -> ew (havoc Ev K WS) (K + (1 + i)) = Z_to_bv 64 (hb P cur (2 + Z.of_nat i)))
  by (intros i Hi; rewrite (ew_havoc_new Ev K WS (1 + i) (Z_to_bv 64 0)) by (cbn [length map seq]; clear - Hi; lia);
      do 2 (destruct i as [|i]; [reflexivity|]); clear - Hi; lia)
end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_alias tfibsegs Ev ssv msv (SAlu ALU_ADD (SOff 32 0) (SOff 13 0)) (SOff K 0) HS
  ltac:(transitivity (Z_to_bv 64 (pdata + cur1));
        [ apply denot_add_atoms; [enorm; exact E32 | enorm; exact E13 | clear - Hph; lia | clear - Hcur HC2; lia | clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB C1; lia]
        | cbn [sv_denot]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB C1; lia); rewrite Z.add_0_r; reflexivity ])) as HS3;
clear HS; rename HS3 into HS end;
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (src_region K 2) HS eq_refl
  (src_region_ok Ev _ K 2 (pdata + cur1) (fun i => hb P cur (2 + Z.of_nat i))
     ltac:(rewrite EQ; apply unsigned_lit_small; clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(clear - Hcur Hph HC2; lia) ltac:(cbn; clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB C1; lia)
     ltac:(intros i Hi; split; [exact (EBy i Hi) | split; [exact (HBR (Z.of_nat i) ltac:(clear - Hi; lia)) | exact (VB i Hi)]]))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold src_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB C1; lia);
    enorm; agnorm; rewrite B8, B19, Usp;
    unfold A_GOT_shadow, A_shadow_glob, off_img in *; unfold rboxed in *;
    clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB HSTB Hpdst Hdst1 Hdst2 Hst1 Hpimg Hpapp HTS Has C1; cbn; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end end.
lazymatch type of EQ with ew ?Eh ?K = _ =>
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (st_ok_add_fact tfibsegs Ev _ _ K (mkAF 4096 140737479966720 0) HS
  ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EQ, unsigned_lit_small by (clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 HSPB C1; lia);
         rewrite Z.pow_0_r, Z.mod_1_r; clear - Hcur Hnb HC2 CB Hph Hpceil Hrq2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end end.
pose proof (EBy 0%nat ltac:(lia)) as EB0. pose proof (EBy 1%nat ltac:(lia)) as EB1. cbn [Nat.add Z.of_nat] in EB0, EB1. clear EBy GB VB.
rebaseH HS AG.
renvI HS AG E8 E19 E22 Usp st dst E8n E18n E25n Uspn B8n B18n.
assert (HB2 : 0 <= hb P cur 2 < 256) by exact (HBR 0 ltac:(lia)). assert (HB3 : 0 <= hb P cur 3 < 256) by exact (HBR 1 ltac:(lia)).
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (RAst1 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAst1 E19 E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
2: { exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur1 2) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur1 + 2)); [lia | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur1) 2)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CB HC2 Hcur Hrq2; lia);
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN2. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT2 HSEP UN2 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT3. clear KEPT2.
vkeepUN2 UN2 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
{ exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur1 4) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur1 + 4)); [discriminate Hc | lia]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
assert (RApC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF (pdata + cur1) 2)
by (apply (range_addressable_of_block tfibsegs B LAWS lyc Sc W1 _ _ pdata nb _ _ (proj1 HJc) Hpdc); clear - CB HC2 Hcur Hrq2; lia);
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN2; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_RD3.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
all: try (oblH RApC EQ E22).
{ awrI Uspn E18n E8n Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN3. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT3 HSEP UN3 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT3.
vkeepUN2 UN3 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKJ : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) _ a)
  by (intros a Ha; apply UN3; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHKJ ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as RAdstJ. clear SHKJ.
rename Wp into Vp. rename Wn into Vn. clear Wc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 4%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 5%nat _ HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict] in HRt;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
pose proof (field_of_region _ _ 19%nat st _ _ _ _ _ 16 8 (SOff 13 2) (cur1 + 2) HRt B18n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite E13, unsigned_lit_small by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 0 8 (SOff 35 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 16 4 (SOff 48 0) fattr HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 26 2 (SOff 51 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 28 1 (SOff 52 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 22 2 (dst + 22) 2 HRd B8n ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as V22.
pose proof (field1_of_region _ _ 8%nat dst _ _ _ _ _ 20 (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 55 0)) (SLit 8)) (SExt false 8 (SOff 54 0))) ((hb P cur 2) + 256 * (hb P cur 3)) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8 _ 55 54 (hb P cur 3) (hb P cur 2)); [enorm; exact EB1 | enorm; exact EB0 | lia | lia])
  ltac:(lia)) as Vq0.
replace (((hb P cur 2) + 256 * (hb P cur 3)) mod 256) with (hb P cur 2) in Vq0 by (rewrite Z.mul_comm, Z.mod_add, Z.mod_small by lia; reflexivity).
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 21 1 (SAlu ALU_SRL (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 55 0)) (SLit 8)) (SExt false 8 (SOff 54 0))) (SLit 8)) (hb P cur 3) HRd B8n ltac:(cbn; tauto)
  ltac:(rewrite denot_lit_U; f_equal; apply (U_hl8_hi _ 55 54 (hb P cur 3) (hb P cur 2)); [enorm; exact EB1 | enorm; exact EB0 | lia | lia])
  ltac:(cbn; lia) ltac:(cbn; lia)) as Vq1.
replace (dst + 21) with (dst + 20 + 1) in Vq1 by lia.
pose proof (val_mem_bytes2 _ _ _ _ Vq0 Vq1 ltac:(lia) ltac:(lia)) as V20. clear Vq0 Vq1.
replace (dst + 22) with (dst + 20 + 2) in V22 by lia.
pose proof (val_mem_half2 _ _ _ _ V20 V22 ltac:(lia) ltac:(lia)) as Vfg. rewrite Z.mul_0_r, Z.add_0_r in Vfg. clear V20 V22.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 24 2 (SOff 50 0) 0 HRd B8n ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Uspn
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
clear HRd HRs HRt.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vc, Vl, Vfa, Vnl, Vti. rewrite Z.add_0_r in Vl.
destruct Hhd as [(Hz & H2 & Hc1 & Efa) | (_ & X & ->)]; [| exfalso; clear - X CB HC2; lia]. subst r1.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
rreg HS (13%bv : bv 5) Q13. rreg HS (15%bv : bv 5) Q15. rreg HS (16%bv : bv 5) Q16. rreg HS (17%bv : bv 5) Q17.
rreg HS (10%bv : bv 5) Q10. rregS HS (14%bv : bv 5) Q14s.
pose proof (denot_shx _ 19 22 16 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
pose proof (denot_shx _ 19 22 8 st SB E18n E25n ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_RD3 end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
eapply (RC3s STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 (ms_regs msX) (ms_mem msX) mdX 0 0 (2 ^ 64 - 1) (cur1 + 2) nb fattr (hb P cur 2 + 256 * hb P cur 3) 0 T P);
[ exact RC | exact HPL | exact HJc
| unfold hdr3; split; [left; reflexivity|]; split; [left; reflexivity|]; split; [right; reflexivity|]; split; [right; split; [change (Z.lor 0 0) with 0; rewrite (lor_m1 0) by lia; lia|]; split; lia|]; repeat split; lia
| unfold C3_regs_at, I_regs_at, w64;
  rewrite Q14s, (denot_srl3 _ 8 16 dst) by first [enorm; agnorm; exact E8 | lia];
  rewrite Q23, Q24, D16, D8;
  rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27, Q10, Q13, Q15, Q16, Q17; enorm; agnorm; rewrite ?B19, ?B8;
  rewrite E3, E4, E8, E18, E19, E22, E27, ?E13, ?E15, ?E33, <- Usp, Z_to_bv_bv_unsigned;
  repeat split; try reflexivity; first [ symmetry; apply Z_to_bv_bv_unsigned | rewrite unsigned_lit_small by lia; reflexivity ]
| exact HFR2
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstJ
| exact KEPT4
| io_now ] end end.
}
{
pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo1 & Ehi1 & _).
assert (RAst1 : range_addressable (aview tfibsegs (w_H W1) mem1) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 mem1 _ st 24 HAR1); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]).
norm_ss HS. reshok_bx HS 22%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblS RAst1 E19 E22).
{ awrI Usp E19 E8 Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN1. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT1 HSEP UN1 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT2. clear KEPT1.
vkeepUN2 UN1 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
{ exfalso. rewrite branch_geu_U, (U_atom _ 33 nb), (U_atom_off _ 13 cur1 2) in Hc by first [unfold M64; lia | enorm; agnorm; first [exact E33 | exact E13] | lia]. destruct (Z.ltb_spec nb (cur1 + 2)); [discriminate Hc | lia]. }
clear Hc. norm_ss HS. reshok_bx HS 22%nat.
try clear RAstC. try clear RApC.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W1) (ms_mem msX)) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS lyc Sc W1 (ms_mem msX) _ st 24 (proj1 HJc)); [rewrite Elo1; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi1; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
lazymatch type of UN1 with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mprev a =>
assert (SHKc : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) mprev a)
by (intros a Ha; apply UN1; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end;
let R2 := fresh "RAd2" in pose proof (RA_kept_band _ _ dst 32 SHKc ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst1) as R2; clear SHKc; try clear RAdstC; rename R2 into RAdstC end end.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan RFC_RD3.
all: try (oblS RAstC E19 E22).
all: try (oblD RAdstC E8 E22).
{ awrI Usp E19 E8 Hown EFA1. }
unrunRD HFr Zsm Usp B8 Usp UN3. clear HF HFr HG.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT2 HSEP UN3 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT4. clear KEPT2.
vkeepUN2 UN3 Wp Wn ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKJ : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W1) (ms_mem msX) a = aview tfibsegs (w_H W1) _ a)
  by (intros a Ha; apply UN3; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]) end.
pose proof (RA_kept_band _ _ dst 32 SHKJ ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdstC) as RAdstJ. clear SHKJ.
rename Wp into Vp. rename Wn into Vn. clear Wc.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 3%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 4%nat _ HS ltac:(vm_compute; reflexivity)) as HRt; cbn [ms_mem restrict] in HRt;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
pose proof (field_of_region _ _ 19%nat st _ _ _ _ _ 16 8 (SOff 33 0) nb HRt B19 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 0 8 (SOff 35 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd B8 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 16 4 (SOff 48 0) fattr HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E48, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 26 2 (SOff 51 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E51, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 28 1 (SOff 52 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E52, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 22 2 (dst + 22) 2 HRd B8 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as V22.
pose proof (zero_of_region _ _ 8%nat dst _ _ _ _ _ 20 2 (dst + 20) 2 HRd B8 ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as V20.
replace (dst + 22) with (dst + 20 + 2) in V22 by lia.
pose proof (val_mem_half2 _ _ _ _ V20 V22 ltac:(lia) ltac:(lia)) as Vfg. rewrite Z.mul_0_r, Z.add_0_r in Vfg. clear V20 V22.
pose proof (field_of_region _ _ 8%nat dst _ _ _ _ _ 24 2 (SOff 50 0) 0 HRd B8 ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?E50, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (rfc_frame_of_stackI _ _ regs _ _ _ _ _ HRs Usp
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Nat.add]; first [exact E36 | exact E37 | exact E38 | exact E39 | exact E40 | exact E41 | exact E42 | exact E43 | exact E44 | exact E45 | exact E46 | exact E47]|]); exfalso; clear - Hj; lia)) as HFR2.
clear HRd HRs HRt.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vc, Vl, Vfa, Vnl, Vti. rewrite Z.add_0_r in Vl.
assert (Hr1r : 0 <= r1 < 2 ^ 64) by (destruct Hr1 as [-> | ->]; lia).
assert (HnbC : nb < cur + 6) by (destruct Hhd as [(_ & _ & X & _)|(_ & X & _)]; lia).
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23.
rreg HS (24%bv : bv 5) Q24. rreg HS (25%bv : bv 5) Q25. rreg HS (27%bv : bv 5) Q27.
rreg HS (13%bv : bv 5) Q13. rreg HS (15%bv : bv 5) Q15. rreg HS (16%bv : bv 5) Q16. rreg HS (17%bv : bv 5) Q17.
rreg HS (10%bv : bv 5) Q10. rregS HS (14%bv : bv 5) Q14s.
pose proof (denot_shx _ 19 22 16 st SB E19 E22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D16. cbn [sv_denot] in D16. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D16.
pose proof (denot_shx _ 19 22 8 st SB E19 E22 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SB; lia)) as D8. cbn [sv_denot] in D8. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in D8.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_RD3 end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W1 (ms_mem msX) _ _ |- _ =>
eapply (RC3s STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W1 (ms_regs msX) (ms_mem msX) mdX r1 (2 ^ 64 - 1) (2 ^ 64 - 1) nb nb fattr 0 0 T P);
[ exact RC | exact HPL | exact HJc
| unfold hdr3; split; [exact Hr1|]; split; [right; reflexivity|]; split; [right; reflexivity|]; split; [right; split; [rewrite (lor_m1 r1) by lia; rewrite (lor_m1 (2 ^ 64 - 1)) by lia; lia|]; split; lia|]; repeat split; lia
| unfold C3_regs_at, I_regs_at, w64;
  rewrite Q14s, (denot_srl3 _ 8 16 dst) by first [enorm; agnorm; exact E8 | lia];
  rewrite Q23, Q24, D16, D8;
  rewrite Q2, Q3, Q4, Q8, Q18, Q19, Q22, Q9, Q20, Q27, Q10, Q13, Q15, Q16, Q17; enorm; agnorm; rewrite ?B19, ?B8;
  rewrite E3, E4, E8, E18, E19, E22, E27, ?E13, ?E15, ?E33, <- Usp, Z_to_bv_bv_unsigned;
  repeat split; try reflexivity; first [ symmetry; apply Z_to_bv_bv_unsigned | rewrite unsigned_lit_small by lia; reflexivity ]
| exact HFR2
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstJ
| exact KEPT4
| io_now ] end end.
}
Qed.
End R1.
End d.
