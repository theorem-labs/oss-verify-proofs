(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac U.Bz.BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac U.Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_sd4P.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDE.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation SLMA := (e_selectorMtf e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1200 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variable m0 : word -> option byte.
  Variable nG : Z.
  Hypothesis VW : sd_vw cx e P m0.
  Notation MD H i16 b m := (MA3 cx g e nG P m0 H i16 b m).
  Notation cP := (Z_to_bv 64 P). Notation cE := (Z_to_bv 64 E).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  Notation FLX L := (L cx g e Q gp tp F fc P CX SEP Gmtf Gbs Gzb Hnb CEP PHI LIM HLIM m0 nG).
  Variable nSel : Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Variables (ra s5 s6 s7 s8 s9 s10 s11 : word).
  Notation RD a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4 :=
    (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  Lemma U0_bsw3_tail : forall (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (a1 a2 a4 a5 a6 a7 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4 : word),
    let bf := bsW b 3 nG in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall m' (a2' : word) (b1 : bw),
        b1 = bs_needw BS_FUEL b -> MD H bs bf m' -> (bv_unsigned a2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ bf)) a1 a2' (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 5) a5 a6 a7 (Z_to_bv 64 nG) t1 t2 t3 t4
                              (Z_to_bv 64 (bw_live bf)) t6 s1 s2 s3 s4)
                          F (Z_to_bv 64 0x1bb58) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ b1)) a1 a2 (Z_to_bv 64 (bw_live b1)) a4 a5 a6 a7 (Z_to_bv 64 nG) t1 t2 t3 t4 t5 t6 s1 s2 s3 s4)
                      F (Z_to_bv 64 0x1bb0c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b b1 m a1 a2 a4 a5 a6 a7 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4. cbv zeta. intros OK Eb1 NL L1 MEM K.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 3 nG = BW (Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296)) (bw_live b1 + 3) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    urun_to 0x1bb58%Z.
    lazymatch type of EH2 with context [Z.shiftl _ (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 3)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rewrite EBW in K. cbn [bw_numZ bw_live bw_buff] in K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ b1); [st_eq| exact Eb1| closeMD|] end.
    rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
    try (lazymatch goal with |- context [Z.shiftl _ (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 3)%Z by (rewrite Z.mod_small; lia) end).
    rewrite low32_small; [reflexivity| exact XR].
  Qed.

  Lemma U0_bsw3 : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (a0 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4 : word),
    let bf := bsW b 3 nG in
    h928 H = Z_to_bv 64 nG -> h944 H = Z_to_bv 64 nSel ->
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (a2' a5' a6' a7' : word) (b1 : bw),
        b1 = bs_needw BS_FUEL b -> MD H bs bf m' -> (bv_unsigned a2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ bf)) (Z_to_bv 64 (bw_numZ b)) a2' (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 5) a5' a6' a7' (Z_to_bv 64 nG)
                              t1 t2 t3 t4 (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 nSel) s1 s2 s3 s4)
                          F (Z_to_bv 64 0x1bb58) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD a0 (Z_to_bv 64 (bw_numZ b)) a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4)
                      F (Z_to_bv 64 0x1ba60) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b m a0 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s1 s2 s3 s4. cbv zeta. intros HGW HSW OK NL MEM K.
    pose proof (bsW_NZM b 3 nG) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    urun_to 0x1ba84%Z.
    rewrite HGW, HSW.
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (U0_bsw3_tail H bs b b m _ _ a4 a5 a6 a7 t1 t2 t3 t4 t5 _ s1 s2 s3 s4); [st_eq| exact OK| | exact NL| lia| closeMD|].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' a2' b1 Eb1 MEM' X'. eapply (K m' a2' a5 a6 a7 b1); [exact Eb1| exact MEM'| exact X'].
    - wstep. wstep. wstep.
      enter_with (FLX ufl_1ba94 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
      { pose proof (bsW_bytes b 3 nG) as [BB _]. rewrite <- BB. lia. }
      { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
      intros b1 m' a4' a5' a6' a7' Eb1 MEM' X4' L1.
      enter_with (U0_bsw3_tail H bs b b1 m' _ _ _ _ _ _ t1 t2 t3 t4 _ _ s1 s2 s3 s4); [st_eq| exact OK| exact Eb1| exact NL| exact L1| exact MEM'|].
      intros m'' a2'' b1' Eb1' MEM'' X''. eapply (K m'' a2'' a5' a6' a7' b1'); [exact Eb1'| exact MEM''| exact X''].
  Qed.

  Lemma U0_bsw15_tail : forall (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t6 s1 s2 s3 s4 : word),
    let bf := bsW b 15 nSel in
    h976 H = Z_to_bv 64 nSel ->
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned a2 mod 4294967296 = bw_buff b1)%Z -> MD H bs b1 m ->
    (forall m' (a3' a4' t2' : word),
        MD H bs bf m' -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ bf)) a1 a2 a3' a4' a5 a6 a7 t0 t1 t2' t3 t4 (Z_to_bv 64 (bw_live bf)) t6 s1 s2 s3 s4)
                          F (Z_to_bv 64 0x1bc20) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ b1)) a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 (Z_to_bv 64 (bw_live b1)) t6 s1 s2 s3 s4)
                      F (Z_to_bv 64 0x1bbd8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b b1 m a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t6 s1 s2 s3 s4. cbv zeta. intros HS OK Eb1 NL L1 X MEM K.
    openCX. openMD MEM. rewrite HS in HI.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 15 nSel = BW (Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296)) (bw_live b1 + 15) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    urun_to 0x1bc20%Z.
    lazymatch type of EH2 with context [Z.shiftl _ (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 15)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296))%Z.
    { rewrite (low32_or_shifted2 _ _ a2 (bw_buff b1)) by first [exact X| lia].
      rewrite low32_small; [reflexivity| exact XR]. }
    rewrite EBW in K. cbn [bw_numZ bw_live bw_buff] in K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _); [st_eq| rewrite <- HS in HI; closeMD|] end.
    rewrite (low32_or_shifted2 _ _ a2 (bw_buff b1)) by first [exact X| lia].
    try (lazymatch goal with |- context [Z.shiftl _ (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 15)%Z by (rewrite Z.mod_small; lia) end).
    rewrite low32_small; [reflexivity| exact XR].
  Qed.

  Lemma U0_bsw15 : forall (H : sdw) (bs : list byte) (b : bw) (l0 : Z) (m : word -> option byte)
      (a1 a2 a5 a6 a7 t0 t1 t2 t3 t4 t6 s1 s2 s3 s4 : word),
    let bf := bsW b 15 nSel in
    h976 H = Z_to_bv 64 nSel ->
    bw_ok b -> (bw_live b = l0 + 3)%Z -> (0 <= l0)%Z -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned a2 mod 4294967296 = bw_buff b)%Z -> MD H bs b m ->
    (forall m' (a2' a3' a4' a5' a6' a7' t2' : word),
        MD H bs bf m' -> bw_ok bf -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ bf)) a1 a2' a3' a4' a5' a6' a7' t0 t1 t2' t3 t4 (Z_to_bv 64 (bw_live bf)) t6 s1 s2 s3 s4)
                          F (Z_to_bv 64 0x1bc20) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ b)) a1 a2 (Z_to_bv 64 l0) (Z_to_bv 64 5) a5 a6 a7 t0 t1 t2 t3 t4 (Z_to_bv 64 (bw_live b)) t6 s1 s2 s3 s4)
                      F (Z_to_bv 64 0x1bb58) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b l0 m a1 a2 a5 a6 a7 t0 t1 t2 t3 t4 t6 s1 s2 s3 s4. cbv zeta. intros HS OK El0 Hl0 NL X MEM K.
    pose proof (bsW_NZM b 15 nSel) as NZ0. unfold NZM in NZ0.
    cps_pose (bsW_facts b 15 nSel OK ltac:(lia) ltac:(lia)) as (_ & OKf & LVf & _).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (U0_bsw15_tail H bs b b m a1 a2 _ _ a5 a6 a7 t0 t1 t2 t3 t4 t6 s1 s2 s3 s4); [st_eq| exact HS| exact OK| | exact NL| lia| exact X| closeMD|].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' a3' a4' t2' MEM' X'. eapply (K m' a2 a3' a4' a5 a6 a7 t2'); [exact MEM'| exact OKf| exact X'].
    - wstep.
      enter_with (FLX ufl_1bb60 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X| closeMD|].
      { pose proof (bsW_bytes b 15 nSel) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a2' a4' a5' a6' a7' Eb1 MEM' X' L1.
      enter_with (U0_bsw15_tail H bs b b1 m' a1 a2' _ _ _ _ _ t0 t1 t2 t3 t4 t6 s1 s2 s3 s4); [st_eq| exact HS| exact OK| exact Eb1| exact NL| exact L1| exact X'| exact MEM'|].
      intros m'' a3'' a4'' t2'' MEM'' X''. eapply (K m'' a2' a3'' a4'' a5' a6' a7' t2''); [exact MEM''| exact OKf| exact X''].
  Qed.

  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef SLMA i = true /\ (0 <= zget SLMA i < nG)%Z.
  Notation RS a0 a1 i t2 t5 t6 s1 s2 s3 s4 :=
    (RD a0 a1 (Z_to_bv 64 i) (Z_to_bv 64 8) (Z_to_bv 64 7) (Z_to_bv 64 32) (Z_to_bv 64 31) (Z_to_bv 64 18001) (Z_to_bv 64 (E + 19706))
        (Z_to_bv 64 nSel) t2 (NOT (E + 19706)) (Z_to_bv 64 1) t5 t6 s1 s2 s3 s4).

  Notation ONES_IH n :=
    (forall (i j s : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a1 t2 s2 s3 s4 : word),
      (j + Z.of_nat n = s)%Z -> (0 <= j)%Z -> (0 <= i < nSel)%Z -> (s = zget SLMA i) ->
      let bf := sm_put_ones n b in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned t2 mod 4294967296 = bw_buff b)%Z -> MD H bs b m ->
      (forall m' (t2' s2' s3' s4' : word),
          MD H bs bf m' -> bw_ok bf -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
          evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ bf)) a1 i t2' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 s) (Z_to_bv 64 (E + 19706 + i)) s2' s3' s4')
                           F (Z_to_bv 64 0x1bd44) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ b)) a1 i t2 (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 j) (Z_to_bv 64 (E + 19706 + i)) s2 s3 s4)
                       F (Z_to_bv 64 0x1bc78) fc None m (seg_rom s0segs))).

  Lemma U0_ones_tail : forall (i j s : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (a1 t2 s2 s3 s4 : word),
    (j + Z.of_nat (S n) = s)%Z -> (0 <= j)%Z -> (0 <= i < nSel)%Z -> (s = zget SLMA i) ->
    let bf := sm_put_ones n (bsW b 1 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned t2 mod 4294967296 = bw_buff b1)%Z -> MD H bs b1 m ->
    ONES_IH n ->
    (forall m' (t2' s2' s3' s4' : word),
        MD H bs bf m' -> bw_ok bf -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ bf)) a1 i t2' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 s) (Z_to_bv 64 (E + 19706 + i)) s2' s3' s4')
                         F (Z_to_bv 64 0x1bd44) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ b1)) a1 i t2 (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 j) (Z_to_bv 64 (E + 19706 + i)) s2 s3 s4)
                     F (Z_to_bv 64 0x1bcfc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i j s n H bs b b1 m a1 t2 s2 s3 s4 Hj Hj0 Hi Hs. cbv zeta. intros OK Eb1 NL L1 X MEM IHn K.
    destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 1 1 = BW (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 1)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (LV2 : bw_live (bsW b 1 1) = (bw_live b1 + 1)%Z) by (rewrite EBW; reflexivity).
    assert (NZ2 : bw_numZ (bsW b 1 1) = bw_numZ b1) by (rewrite EBW; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    urun_to 0x1bc78%Z.
    lazymatch type of EH2 with context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_shifted2 _ _ t2 (bw_buff b1)) by first [exact X| lia].
      rewrite low32_small; [reflexivity| exact XR]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn i (j + 1)%Z s H bs (bsW b 1 1) mm a1 _ _ _ _);
        [st_eq| lia| lia| exact Hi| exact Hs| exact OK2| exact NL| | rewrite EBW; closeMD| exact K] end.
    rewrite EBW. cbn [bw_buff].
    rewrite (low32_or_shifted2 _ _ t2 (bw_buff b1)) by first [exact X| lia].
    try (lazymatch goal with |- context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z by (rewrite Z.mod_small; lia) end).
    rewrite low32_small; [reflexivity| exact XR].
  Qed.

  Lemma U0_ones_loop : forall (n : nat), ONES_IH n.
  Proof using All.
    induction n as [|n IH].
    - intros i j s H bs b m a1 t2 s2 s3 s4 Hj Hj0 Hi Hs. cbv zeta. intros OK NL X MEM K.
      destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR. cbn [sm_put_ones] in K.
      openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
      openVW VW.
      pose proof (ovb_read1 s0segs m (E + 19706) SLMA (jseg J 19706 18002) 18002 i _ SLM ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RDs.
      closeVW.
      wstep. clear RDs. cbv beta. rewrite <- Hs. rewrite (unsigned_lit8 s) by lia.
      wstep; if_cases Kc; zify_cond_z Kc; [|exfalso; lia].
      enter_with (K m _ _ _ _); [st_eq| closeMD| exact OK| exact X].
    - intros i j s H bs b m a1 t2 s2 s3 s4 Hj Hj0 Hi Hs. cbv zeta. intros OK NL X MEM K.
      destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR.
      rewrite put_ones_S in NL, K.
      pose proof (put_ones_NZM n (bsW b 1 1)) as NZ1. unfold NZM in NZ1.
      pose proof (bsW_NZM b 1 1) as NZ0. unfold NZM in NZ0.
      openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
      pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
      openVW VW.
      pose proof (ovb_read1 s0segs m (E + 19706) SLMA (jseg J 19706 18002) 18002 i _ SLM ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RDs.
      closeVW.
      wstep. clear RDs. cbv beta. rewrite <- Hs. rewrite (unsigned_lit8 s) by lia.
      wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (U0_ones_tail i j s n H bs b b m a1 t2 _ _ s4); [st_eq| lia| lia| exact Hi| exact Hs| exact OK| | exact NL| lia| exact X| closeMD| exact IH| exact K].
        unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + enter_with (FLX ufl_1bc84 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X| closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' t2' s2' s3' s4' Eb1 MEM' X' L1.
        enter_with (U0_ones_tail i j s n H bs b b1 m' a1 t2' s2' s3' s4');
          [st_eq| lia| lia| exact Hi| exact Hs| exact OK| exact Eb1| exact NL| exact L1| exact X'| exact MEM'| exact IH| exact K].
  Qed.

  Notation SELS_IH n :=
    (forall (i : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a1 t2 t6 s1 s2 s3 s4 : word),
      (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
      let bf := sm_put_sels n b SLMA i in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned t2 mod 4294967296 = bw_buff b)%Z -> MD H bs b m ->
      (forall m' (t2' t6' s1' s2' s3' s4' : word),
          MD H bs bf m' -> bw_ok bf -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
          evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ bf)) a1 nSel t2' (Z_to_bv 64 (bw_live bf)) t6' s1' s2' s3' s4')
                           F (Z_to_bv 64 0x1bdf8) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ b)) a1 i t2 (Z_to_bv 64 (bw_live b)) t6 s1 s2 s3 s4)
                       F (Z_to_bv 64 0x1bc60) fc None m (seg_rom s0segs))).

  Lemma U0_sels_fin : forall (i : Z) (n : nat) (H : sdw) (bs : list byte) (bo b1 : bw) (m : word -> option byte)
      (a1 t2 t6 s1 s2 s3 s4 : word),
    (i + Z.of_nat (S n) = nSel)%Z -> (0 <= i)%Z ->
    let bf := sm_put_sels n (bsW bo 1 0) SLMA (i + 1) in
    bw_ok bo -> b1 = bs_needw BS_FUEL bo -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned t2 mod 4294967296 = bw_buff b1)%Z -> MD H bs b1 m ->
    SELS_IH n ->
    (forall m' (t2' t6' s1' s2' s3' s4' : word),
        MD H bs bf m' -> bw_ok bf -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ bf)) a1 nSel t2' (Z_to_bv 64 (bw_live bf)) t6' s1' s2' s3' s4')
                         F (Z_to_bv 64 0x1bdf8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ b1)) a1 i t2 (Z_to_bv 64 (bw_live b1)) t6 s1 s2 s3 s4)
                     F (Z_to_bv 64 0x1bdc0) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i n H bs bo b1 m a1 t2 t6 s1 s2 s3 s4 Hi Hi0. cbv zeta. intros OK Eb1 NL L1 X MEM IHn K.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW bo 1 0 = BW (bw_buff b1) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1)).
    { unfold bsW. rewrite <- Eb1. f_equal. rewrite lor_shl0. reflexivity. }
    assert (OK2 : bw_ok (bsW bo 1 0)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (LV2 : bw_live (bsW bo 1 0) = (bw_live b1 + 1)%Z) by (rewrite EBW; reflexivity).
    assert (NZ2 : bw_numZ (bsW bo 1 0) = bw_numZ b1) by (rewrite EBW; reflexivity).
    urun_to 0x1bdf4%Z.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z H bs (bsW bo 1 0) mm a1 t2 _ _ _ s3 s4);
        [st_eq| lia| lia| lia| exact OK2| exact NL| rewrite EBW; exact X| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_sels] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2| rewrite EBW; exact X] end.
  Qed.

  Lemma U0_sels_outer : forall (n : nat), SELS_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros i H bs b m a1 t2 t6 s1 s2 s3 s4 Hi Hi0 _. cbv zeta. intros OK NL X MEM K.
    destruct (SLMF i ltac:(lia)) as [ZD ZR].
    rewrite put_sels_S in NL, K.
    set (s := zget SLMA i) in *.
    set (bo := sm_put_ones (Z.to_nat s) b) in NL, K.
    pose proof (put_sels_NZM n (bsW bo 1 0) SLMA (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM bo 1 0) as NZ0. unfold NZM in NZ0.
    pose proof (put_ones_NZM (Z.to_nat s) b) as NZo. unfold NZM in NZo. fold bo in NZo.
    destruct (put_ones_ok (Z.to_nat s) b OK) as [OKo LVo]. fold bo in OKo, LVo.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    urun_to 0x1bc78%Z.
    enter_with (U0_ones_loop (Z.to_nat s) i 0 s H bs b m a1 t2 s2 s3 s4);
      [st_eq| lia| lia| lia| reflexivity| exact OK| fold bo; lia| exact X| closeMD|].
    fold bo. clear EH1 EH2 AR2 HI I16 MI MU WM.
    intros m' t2' s2' s3' s4' MEM' OK' X'.
    cps_pose OK' as (OKb' & OKl' & OKn').
    cps_pose (bs_needw_post BS_FUEL bo OK' ltac:(unfold BS_FUEL; cbn; lia)) as (OK1' & M1' & N1').
    pose proof (Z.mod_pos_bound (bw_live bo) 8 ltac:(lia)) as MB'.
    openMD MEM'.
    wstep; if_cases Kc2; zify_cond_z Kc2.
    - enter_with (U0_sels_fin i n H bs bo bo m' a1 t2' _ _ s2' s3' s4');
        [st_eq| lia| lia| exact OKo| | exact NL| lia| exact X'| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live bo)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX ufl_1bd48 BS_FUEL H bs bo m'); [st_eq| exact OK'| lia| unfold BS_FUEL; cbn; lia| | exact X'| closeMD|].
      { pose proof (bsW_bytes bo 1 0) as [BB _]. rewrite <- BB. lia. }
      intros b1 m'' t2'' s1'' s2'' t6'' Eb1 MEM'' X'' L1.
      enter_with (U0_sels_fin i n H bs bo b1 m'' a1 t2'' t6'' s1'' s2'' s3' s4');
        [st_eq| lia| lia| exact OKo| exact Eb1| exact NL| exact L1| exact X''| exact MEM''| exact IH| exact K].
  Qed.

  Lemma U0_sels : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 s1 s2 s3 s4 : word),
    let bf := sm_put_sels (Z.to_nat nSel) b SLMA 0 in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned t2 mod 4294967296 = bw_buff b)%Z -> MD H bs b m ->
    (forall m' (t2' t6' s1' s2' s3' s4' : word),
        MD H bs bf m' -> bw_ok bf -> (bv_unsigned t2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS (Z_to_bv 64 (bw_numZ bf)) a1 nSel t2' (Z_to_bv 64 (bw_live bf)) t6' s1' s2' s3' s4')
                         F (Z_to_bv 64 0x1bdf8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RD (Z_to_bv 64 (bw_numZ b)) a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 nSel) s1 s2 s3 s4)
                     F (Z_to_bv 64 0x1bc20) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b m a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 s1 s2 s3 s4. cbv zeta. intros OK NL X MEM K.
    openCX. openMD MEM.
    wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    urun_to 0x1bc60%Z.
    replace (Z.land 18446744073709551615 nSel) with nSel by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small; lia).
    enter_with (U0_sels_outer (Z.to_nat nSel) 0%Z H bs b m a1 t2 _ _ s2 s3 s4); [st_eq| lia| lia| lia| exact OK| exact NL| exact X| closeMD| exact K].
  Qed.
End SDE.
End ACeilS1.
