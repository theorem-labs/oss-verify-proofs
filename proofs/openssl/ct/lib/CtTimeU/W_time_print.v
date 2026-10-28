(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApFmt CtSizes CtWire CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_apfmt Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_printfx8 PrnTimeIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeDefs TimeKit TimeKit2 TimeFmtPure TimeToTmDefs W_time_leaves W_time_to_tm_A W_time_to_tm TimePrnFmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Definition GENTIME_PRINT_STACK : Z := 16 + 160 + BIO_PRINTF_STACK.

(* [comment removed for export] *)
Ltac isdig_call cv :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evt_cut;
    [ eapply ossl_ascii_isdigit_spec with (c := cv);
      [ rewrite ?unsigned_lit by lia; eassumption | eassumption | unfold GLOBALS_TOP; lia | rewrite ?unsigned_lit by lia; lia | lia | reflexivity ]
    | intros ms' PO; unfold leaf16_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO; post_call ctusegs mx ]
  end.

Local Ltac brc :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace (if c then a else b) with a by (vm_compute; reflexivity)
    | false => replace (if c then a else b) with b by (vm_compute; reflexivity)
    end
  end.
Local Ltac nchk := let C := fresh "C" in if_cases C; [exfalso; zify_cond C; rewrite ?land64, ?Z.mod_small in C by lia; lia | clear C].
Local Ltac achk H := let C := fresh "C" in if_cases C;
  [exfalso; zify_cond C; change 7 with (Z.ones 3) in C; rewrite Z.land_ones in C by lia; change (2^3) with 8 in C; apply C;
   rewrite ?unsigned_lit by lia; first [exact H | clear - H; Z.div_mod_to_equations; lia] | clear C].
Local Ltac uchk1 := let C := fresh "C" in if_cases C; zify_cond C;
  [exfalso; repeat (rewrite Z.shiftl_mul_pow2 in C by lia); rewrite ?land64 in C; rewrite ?unsigned_lit in C by lia;
   rewrite ?ZBridge.zb_lxor_ones in C by lia; rewrite ?unsigned_lit in C by lia; lia | ]; try clear C.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ro_of_rw' : forall m A cs, rw_cells ctusegs m A cs -> ro_cells ctusegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Lemma gentime_print : gentime_print_stmt GENTIME_PRINT_STACK.
Proof.
  unfold gentime_print_stmt. intros until canary.
  intros ST MI GLO LO SP16 SP63 SSP TP FRM HB OB NW NM HG SEPG SEPGO HD PR TSR D4K DLO SEPDO G0 GA8 OA8 -> ->. subst tp.
  unfold GENTIME_PRINT_STACK, BIO_PRINTF_STACK, VSN_DEPTH, GENTIME_PRINT, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold GLOBALS_TOP in GLO. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof OB as (OB0 & OB1 & OB2). unfold BIO_SIZE, GLOBALS_TOP in OB0, OB1, OB2.
  destruct NM as [NM1 NM2].
  destruct (gentime_adj ts) as [t|] eqn:GA; [| unfold printable in PR; rewrite GA in PR; discriminate].
  pose proof (gentime_adj_valid ts t GA) as TV. pose proof (ts_ms_range ts) as MSR. pose proof TV as (VY & VMO & VMD & VHH & VMI & VSS).
  pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  unfold asn1_string_cells, MallocRep.wz, V_ASN1_GENERALIZEDTIME in HG. pose proof (rw_cells_bound _ _ _ _ HG) as GB0. cbn in GB0.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  unfold NULL_METHOD, BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz in NM1, NM2. change (2978032 + 16) with 2978048 in NM1. change (2978032 + 48) with 2978080 in NM2.
  pose proof (munch_refl [(lo, bv_unsigned sp); (out, out + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 step. zstep. nchk. zstep. zstep. achk GA8. step. rewrite (sx32_small 24) by lia. step.
  step. if_cases K0; zify_cond K0; [exfalso; apply K0; reflexivity|]. try clear K0.
  do 3 step. release_frame FR ST (bv_unsigned sp). step.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 5 step. step.
  (* [comment removed for export] *)
  carve_frame 160%nat ST. do 12 step. do 4 step. step.
  name_mem m1. match goal with H : rw_cells _ m1 (bv_unsigned sp + -176) _ |- _ => rename H into FR1 end.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB ctusegs m1 _ [] 80 _ _ [16; 8; 56]%nat) in FR1; [| reflexivity]. cbn [mk_CB_cells app] in FR1.
  lazymatch type of FR1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?rest) =>
    pose proof (proj1 (rw_cells_app m1 _ [c0] (c1 :: c2 :: rest)) FR1) as [FRa FRx];
    pose proof (proj1 (rw_cells_app m1 _ [c1] (c2 :: rest)) FRx) as [FRp FRy];
    pose proof (proj1 (rw_cells_app m1 _ [c2] rest) FRy) as [FRt FRs]; clear FR1 FRx FRy end.
  cbn [cells_size csize Nat.add] in FRp, FRt, FRs.
  replace (bv_unsigned sp + -176 + Z.of_nat 16) with (bv_unsigned sp + -160) in FRp by lia.
  replace (bv_unsigned sp + -176 + Z.of_nat 16 + Z.of_nat 8) with (bv_unsigned sp + -152) in FRt by lia.
  replace (bv_unsigned sp + -176 + Z.of_nat 16 + Z.of_nat 8 + Z.of_nat 56) with (bv_unsigned sp + -96) in FRs by lia.
  (* [comment removed for export] *)
  lazymatch type of HG with rw_cells _ ?mx _ _ =>
    pose proof (proj1 (rw_cells_app mx G [C4 (Z_to_bv 64 19); C4 (Z_to_bv 64 24); C8 (Z_to_bv 64 D)] [C8 (Z_to_bv 64 0)]) HG) as [HG3 _] end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (HGC : rw_cells ctusegs mx D (gcells t (ts_ms ts))) end.
  { eapply rw_cells_recast; [exact HD| unfold gcells, zb8; cbn; tauto|].
    rewrite <- (genstr_gcells ts t GA). unfold zb. cbn [cells_bytes cbytes app map]. rewrite app_nil_r. reflexivity. }
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -176)) = bv_unsigned sp + -176) by (apply unsigned_lit; lia).
  unfold gcells, zb8, CH_DOT, CH_Z in HGC.
  eapply evt_cut.
  { lazymatch type of FRt with rw_cells _ _ _ [CB _ ?j] =>
    eapply (time_to_tm_copy_spec _ (Z_to_bv 64 (bv_unsigned sp + -176))) with (lo := lo) (DA := G) (GS := D) (t := t) (ms := ts_ms ts)
             (TMA := bv_unsigned sp + -152) (junk := j) end; rewrite ?ESP;
      [ exact ST | exact MI | unfold GLOBALS_TOP; lia | unfold TIME_TO_TM_STACK; lia | lia
      | apply ro_of_rw'; exact HG3 | lia | pose proof (rw_cells_bound _ _ _ _ HG) as GB; cbn in GB; lia | exact G0 | exact GA8 | apply ro_of_rw'; exact HGC | lia | lia | lia | exact TV | lia
      | exact FRt | lia | lia | lia | lia | reflexivity | reflexivity ]. }
  clear HG3 HD FRt. intros ms' PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end.
  match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -152) [CB _ (cells_bytes _)] |- _ => rename H into HT end.
  name_mem m2.
  (* [comment removed for export] *)
  lazymatch type of HT with rw_cells _ _ _ [CB _ (cells_bytes ?tc)] =>
    assert (HTC : rw_cells ctusegs m2 (bv_unsigned sp + -152) tc) by (eapply rw_cells_recast; [exact HT| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity]) end.
  clear HT. unfold TM_CELLS in HTC.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. try clear K1.
  zstep. nchk. zstep. zstep. achk GA8.
  step. rewrite (sx32_small 24) by lia. step. step. if_cases K2; zify_cond K2; [exfalso; apply K2; reflexivity|]. try clear K2.
  step. rewrite (sx32_small 19) by lia. step. step. brF ltsz.
  step. zstep. nchk. zstep. step. uchk1. step. rewrite (zxb_lit 46) by lia. step. step. if_cases K3; zify_cond K3; [exfalso; apply K3; reflexivity|]. try clear K3.
  zstep. step. uchk1.
  (* [comment removed for export] *)
  do 7 zstep.
  pose proof (digit_range (ts_ms ts / 100) ltac:(split; [apply Z.div_pos; lia| enough (ts_ms ts / 100 < 10) by lia; apply Z.div_lt_upper_bound; lia])) as DG1.
  pose proof (digit_range ((ts_ms ts / 10) mod 10) ltac:(pose proof (Z.mod_pos_bound (ts_ms ts / 10) 10 ltac:(lia)); lia)) as DG2.
  pose proof (digit_range (ts_ms ts mod 10) ltac:(pose proof (Z.mod_pos_bound (ts_ms ts) 10 ltac:(lia)); lia)) as DG3.
  (* [comment removed for export] *)
  step. brc. step. uchk1. zstep. step. rewrite (zxb_lit (digit (ts_ms ts / 100))) by lia. step. isdig_call (digit (ts_ms ts / 100)). rewrite (isdigit_range (digit (ts_ms ts / 100))) by lia.
  step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  zstep. zstep. zstep. zstep. step. brc.
  step. brc. step. uchk1. zstep. step. rewrite (zxb_lit (digit ((ts_ms ts / 10) mod 10))) by lia. step. isdig_call (digit ((ts_ms ts / 10) mod 10)). rewrite (isdigit_range (digit ((ts_ms ts / 10) mod 10))) by lia.
  step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  zstep. zstep. zstep. zstep. step. brc.
  step. brc. step. uchk1. zstep. step. rewrite (zxb_lit (digit (ts_ms ts mod 10))) by lia. step. isdig_call (digit (ts_ms ts mod 10)). rewrite (isdigit_range (digit (ts_ms ts mod 10))) by lia.
  step. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|]. try clear K4.
  zstep. zstep. zstep. zstep. step. brc.
  step. brc. step. uchk1. zstep. step. rewrite (zxb_lit 90) by lia. step. isdig_call 90. rewrite (isdigit_false 90) by lia.
  step. if_cases K4; zify_cond K4; [| exfalso; first [apply K4; reflexivity| lia]]. try clear K4.
  (* [comment removed for export] *)
  step. if_cases K6; zify_cond K6; [exfalso; rewrite ?unsigned_lit in K6 by lia; lia|]. try clear K6.
  zstep. step. step. if_cases K7; zify_cond K7; [| exfalso; first [apply K7; reflexivity| lia]]. try clear K7.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST3 end. name_mem m3.
  (* [comment removed for export] *)
  step. rewrite (sx32_small (t_mon t - 1)) by lia. zstep. step. if_cases K8; zify_cond K8; [exfalso; rewrite ?unsigned_lit in K8 by lia; lia|]. try clear K8.
  zstep. zstep. zstep. zstep. step. uchk1.
  step. rewrite (sx32_signed (t_year t - 1900)) by lia.
  step. setreg 10%Z (Z_to_bv 64 (t_year t)) ltac:(f_equal; rewrite addiw_small by lia; lia).
  step. brF ltsz.
  step. rewrite (sx32_small (t_sec t)) by lia. step. rewrite (sx32_small (t_min t)) by lia.
  step. rewrite (sx32_small (t_hour t)) by lia. step. rewrite (sx32_small (t_mday t)) by lia.
  zstep. setreg 12%Z (Z_to_bv 64 (4 * (t_mon t - 1) + A_MON)) ltac:(unfold A_MON; f_equal; rewrite ?land64, ?Z.shiftl_mul_pow2 by lia; clear - VMO; Z.to_euclidean_division_equations; lia).
  zstep. zstep. step. step. step. step. step. step.
  name_mem m4.
  (* [comment removed for export] *)
  match goal with H : munch _ m m4 |- _ => rename H into MU4 end. match goal with H : wmono ctusegs m m4 |- _ => rename H into WM4 end.
  assert (SSP4 : ssp_cells m4 canary).
  { eapply ssp_cells_agree; [apply (agree_on_of_munch _ _ _ MU4 WM4)| | exact SSP]. intros a Ha. unfold ssp_addr, got_ssp, ssp_guard in Ha. cbn. split; [lia|]. split; [lia| exact I]. }
  lazymatch type of HGC with rw_cells _ ?mx _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?rest) =>
    pose proof (proj2 (proj1 (rw_cells_app mx D [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14] rest) HGC)) as HF3 end.
  cbn [cells_size csize Nat.add] in HF3.
  pose proof (proj1 (proj1 (rw_cells_app m4 (D + Z.of_nat 15) [C1 (Z_to_bv 8 (digit (ts_ms ts / 100))); C1 (Z_to_bv 8 (digit ((ts_ms ts / 10) mod 10))); C1 (Z_to_bv 8 (digit (ts_ms ts mod 10)))] _) HF3)) as HF.
  pose proof (proj2 (proj1 HF)) as HFB. cbn [cells_bytes cbytes app] in HFB. replace (D + Z.of_nat 15) with (D + 15) in HFB by lia. clear HF3 HF.
  match goal with H : rw_cells ctusegs m4 (bv_unsigned sp + -176) _ |- _ => rename H into FRa4 end.
  destruct (pcokx_C16 m4 lo (bv_unsigned sp + -176) t (ts_ms ts) (D + 15)
              (Z_to_bv 64 (4 * (t_mon t - 1) + A_MON)) (Z_to_bv 64 (t_mday t)) (Z_to_bv 64 (t_hour t)) (Z_to_bv 64 (t_min t)) (Z_to_bv 64 (t_sec t))
              (Z_to_bv 64 3) (Z_to_bv 64 (D + 15)) (Z_to_bv 64 (t_year t))
              ltac:(assumption) ltac:(unfold STATIC_SPLIT; lia) TV ltac:(lia) eq_refl
              ltac:(rewrite unsigned_lit by lia; apply Z.mod_small; lia) ltac:(rewrite unsigned_lit by lia; apply Z.mod_small; lia)
              ltac:(rewrite unsigned_lit by lia; apply Z.mod_small; lia) ltac:(rewrite unsigned_lit by lia; apply Z.mod_small; lia)
              ltac:(rewrite unsigned_lit by lia; reflexivity) eq_refl ltac:(rewrite unsigned_lit by lia; apply Z.mod_small; lia)
              HFB ltac:(lia) ltac:(lia) ltac:(lia)) as (o & OL & PC).
  pose proof (zdigits_le4 (t_year t) ltac:(lia)) as ZD. pose proof (zdigits_range (t_year t) ltac:(lia)) as ZR.
  eapply evt_cut.
  { eapply (BIO_printf_null_spec_x8 _ (Z_to_bv 64 (bv_unsigned sp + -176))) with (lo := lo) (out := out) (pv := pv) (nw := nw) (canary := canary) (o := o);
      rewrite ?ESP;
      [ exact ST3 | assumption | unfold GLOBALS_TOP; lia | unfold BIO_PRINTF_STACK, VSN_DEPTH; lia | lia | clear - SP16; Z.div_mod_to_equations; lia
      | exact SSP4 | exact FRM
      | unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB | exact OB | exact OA8 | lia
      | split; [unfold NULL_METHOD, BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz; change (2978032 + 16) with 2978048; exact NM1
               | unfold NULL_METHOD, NULL_PUTS, MallocRep.wz; change (2978032 + 48) with 2978080; exact NM2]
      | exact FRa4 | lia | exact PC | reflexivity | reflexivity ]. }
  clear HFB PC. intros ms' PO; unfold bio_printf_post in PO; rewrite ?ESP in PO; revert ms' PO. post_call ctusegs m4. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST5 end.
  match goal with H : frm0 _ |- _ => rename H into FRM5 end.
  match goal with H : forall k : reg, _ -> reg_get _ k = reg_get F k |- _ => rename H into FREG end.
  match goal with H : ssp_cells _ canary |- _ => rename H into SSP5 end.
  match goal with H : rw_cells ctusegs _ out _ |- _ => rename H into HB5 end.
  name_mem m5.
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 1) ltac:(rewrite sgt0_lit by lia; rewrite (proj2 (Z.ltb_lt 0 (zlength o))) by lia; reflexivity).
  (* [comment removed for export] *)
  match goal with H : rw_cells ctusegs m5 (bv_unsigned sp + -176) _ |- _ => rename H into FA5 end.
  match goal with H : rw_cells ctusegs m5 (bv_unsigned sp + -160) _ |- _ => rename H into FP5 end.
  match goal with H : rw_cells ctusegs m5 (bv_unsigned sp + -152) _ |- _ => rename H into FT5 end.
  match goal with H : rw_cells ctusegs m5 (bv_unsigned sp + -96) _ |- _ => rename H into FS5 end.
  lazymatch type of FA5 with rw_cells _ _ _ ?ca =>
    replace (bv_unsigned sp + -160) with (bv_unsigned sp + -176 + Z.of_nat (cells_size ca)) in FP5 by (cbn; lia);
    pose proof (proj2 (rw_cells_app m5 _ _ _) (conj FA5 FP5)) as FAP end.
  lazymatch type of FAP with rw_cells _ _ _ ?ca =>
    replace (bv_unsigned sp + -152) with (bv_unsigned sp + -176 + Z.of_nat (cells_size ca)) in FT5 by (cbn; lia);
    pose proof (proj2 (rw_cells_app m5 _ _ _) (conj FAP FT5)) as FAT end.
  lazymatch type of FAT with rw_cells _ _ _ ?ca =>
    replace (bv_unsigned sp + -96) with (bv_unsigned sp + -176 + Z.of_nat (cells_size ca)) in FS5 by (cbn; lia);
    pose proof (proj2 (rw_cells_app m5 _ _ _) (conj FAT FS5)) as FR5 end.
  clear FA5 FP5 FT5 FS5 FAP FAT. cbn [app] in FR5.
  do 10 step. step. release_frame FR5 ST5 (bv_unsigned sp + -16). step.
  (* [comment removed for export] *)
  zstep. setreg 10%Z (Z_to_bv 64 1) ltac:(reflexivity).
  step. step. step.
  match goal with H : rw_cells ctusegs _ (bv_unsigned sp + -16) _ |- _ => release_frame H ST5 (bv_unsigned sp) end. step.
  name_mem m6. apply evt_done. exists (zlength o). split; [lia|]. unfold bio_printf_post.
  do 14 eexists. eexists. eexists. exists m6. split; [reflexivity|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact FRM5|]. split; [exact FREG|].
  split; [exact ST5|]. split; [exact SSP5|]. exact HB5.
Qed.

End WithCeiling0.
