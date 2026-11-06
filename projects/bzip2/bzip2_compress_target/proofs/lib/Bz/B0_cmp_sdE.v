(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdFL1 B0_cmp_sdFL2.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac openCX_d CX SEP CEP :=
  let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in
  let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let ME := ident:(ME) in let MA1 := ident:(MA1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in
  let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  let U := fresh "CEPL" in pose proof CEP as U; unfold CEIL in U;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  clear XF0 XF1 Xb0 Xb1 Xf0 Xf1 MF Mb Mf LJb;
  let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
  cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _); hide_disj.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDE.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z) (w64 w72 w104 : word).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Notation INUA := (e_inUse e). Notation SLMA := (e_selectorMtf e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG : Z) (m0 : word -> option byte).
  Notation WD := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1384, P + 1568); (P + 1576, P + 1592)]%Z.
  Hypothesis VW : sd_vw cx e P FB SHF SHE w64 w72 w104 m0.
  Hypothesis SHe : shzW b0segs WD m0 E (E + ESTATE_SIZE).
  Hypothesis SH1 : shzW b0segs WD m0 A1 (A1 + ARR1_SIZE).
  Hypothesis SH2 : shzW b0segs WD m0 A2 (A2 + ARR2_SIZE).
  Notation MD H i16 b m := (MA3 cx g e nG P m0 H i16 b m).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 644))
         (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 80)) s10 (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation SX L := (L cx g e Q gp tp s0 F fc P SHE FB SHF w64 w72 w104 CX SEP Gmtf Gbs Gzb Hnb CEP PHI AE LIM HLIM nG m0 VW SHe SH1 SH2).
  (* [comment removed for export] *)
  Notation FLX L f H bs b m := (SX L f H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  Variable nSel : Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  (* [comment removed for export] *)
  Ltac curH k := let HI := ident:(HI) in
    lazymatch type of HI with rw_cells _ _ _ (_ :: _ :: C8 ?v00 :: C8 ?v08 :: C8 ?v16 :: C8 ?v24 :: C8 ?v32 :: _ :: C8 ?v48 :: C8 ?v56 :: _ :: C8 ?v72 :: _ ::
                                              C8 ?v88 :: C8 ?v96 :: C8 ?v04 :: C8 ?v12 :: C8 ?v20 :: C8 ?v28 :: _) =>
      k (SDW v00 v08 v16 v24 v32 v48 v56 v72 v88 v96 v04 v12 v20 v28) end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_bsw3_tail : forall (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    let bf := bsW b 3 nG in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall m' (a2' : word) (b1 : bw),
        b1 = bs_needw BS_FUEL b -> MD H bs bf m' ->
        evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 5) a2' (Z_to_bv 64 (bw_live bf)) a4 a5 a6 a7 s10 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x94808) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 (bw_live b1)) a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x947a0) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b b1 m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6. cbv zeta. intros OK Eb1 NL L1 MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 3 nG = BW (Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296)) (bw_live b1 + 3) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    brun_to 0x94808%Z.
    lazymatch type of EH2 with context [Z.shiftl _ (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 3)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rewrite EBW in K. cbn [bw_numZ bw_live bw_buff] in K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ b1); [st_eq| exact Eb1| closeMD] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_bsw3 : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    let bf := bsW b 3 nG in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (H' : sdw) (a2' a4' a5' a6' : word) (b1 : bw),
        w1448 H' = w1448 H -> w1496 H' = w1496 H -> w1504 H' = w1504 H -> w1512 H' = w1512 H -> w1520 H' = w1520 H ->
        b1 = bs_needw BS_FUEL b -> MD H' bs bf m' ->
        evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 5) a2' (Z_to_bv 64 (bw_live bf)) a4' a5' a6' a7 s10 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x94808) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x94614) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6. cbv zeta. intros OK NL MEM K.
    pose proof (bsW_NZM b 3 nG) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    openVW VW. brun_to 0x94660%Z. closeVW.
    curH ltac:(fun HH => pose (H1 := HH)).
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (B0_bsw3_tail H1 bs b b mm ra t0 t1 t2 _ _ _ a4 a5 a6 a7 s10 t3 t4 t5 t6); [exact OK| | exact NL| lia| closeMD|] end.
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' a2' b1 Eb1 MEM'. eapply (K m' H1 _ _ _ _ b1); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Eb1| exact MEM'].
    - (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (FLX fl_943a4 BS_FUEL H1 bs b mm); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|] end.
      { pose proof (bsW_bytes b 3 nG) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a3' a4' a2' a5' a6' Eb1 MEM' L1.
      eapply (B0_bsw3_tail H1 bs b b1 m' ra t0 t1 t2 _ _ _ _ _ _ a7 s10 t3 t4 t5 t6); [exact OK| exact Eb1| exact NL| exact L1| exact MEM'|].
      intros m'' a2'' b1' Eb1' MEM''. eapply (K m'' H1 _ _ _ _ b1'); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Eb1'| exact MEM''].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_bsw15_tail : forall (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    let bf := bsW b 15 nSel in
    w1520 H = Z_to_bv 64 nSel ->
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall m' (a0' a1' a2' a3' : word),
        MD H bs bf m' ->
        evt b0segs Q (MS (RD ra t0 t1 (Z_to_bv 64 E) a0' a1' a2' a3' a4 a5 a6 a7 s10 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x949b0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 a1 a2 (Z_to_bv 64 (bw_live b1)) a4 a5 a6 a7 s10 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x94948) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b b1 m ra t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s10 t3 t4 t5 t6. cbv zeta. intros HS OK Eb1 NL L1 MEM K.
    openCX. openMD MEM. rewrite HS in HI. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 15 nSel = BW (Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296)) (bw_live b1 + 15) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    brun_to 0x949a8%Z. openVW VW. wstep. closeVW. wstep.
    lazymatch type of EH2 with context [Z.shiftl _ (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 15)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rewrite EBW in K.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _); [st_eq| rewrite <- HS in HI; closeMD] end.
  Qed.

  Lemma B0_bsw15 : forall (H : sdw) (bs : list byte) (b : bw) (l0 : Z) (m : word -> option byte)
      (ra t0 t1 t2 a2 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    let bf := bsW b 15 nSel in
    w1520 H = Z_to_bv 64 nSel ->
    bw_ok b -> (bw_live b = l0 + 3)%Z -> (0 <= l0)%Z -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (a0' a1' a2' a3' a4' a5' a6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RD ra t0 t1 (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7 s10 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x949b0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 l0) (Z_to_bv 64 5) a2 (Z_to_bv 64 (bw_live b)) a4 a5 a6 a7 s10 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x94808) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b l0 m ra t0 t1 t2 a2 a4 a5 a6 a7 s10 t3 t4 t5 t6. cbv zeta. intros HS OK El0 Hl0 NL MEM K.
    pose proof (bsW_NZM b 15 nSel) as NZ0. unfold NZM in NZ0.
    cps_pose (bsW_facts b 15 nSel OK ltac:(lia) ltac:(lia)) as (_ & OKf & LVf & _).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      eapply (B0_bsw15_tail H bs b b m ra t0 t1 t2 _ _ a2 a4 a5 a6 a7 s10 t3 t4 t5 t6); [exact HS| exact OK| | exact NL| lia| closeMD|].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' a0' a1' a2' a3' MEM'. eapply K; [exact MEM'| exact OKf].
    - (* [comment removed for export] *)
      wstep.
      enter_with (FLX fl_9454c BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b 15 nSel) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a0' a4' a2' a5' a6' Eb1 MEM' L1.
      eapply (B0_bsw15_tail H bs b b1 m' ra t0 t1 t2 _ _ _ _ _ _ a7 s10 t3 t4 t5 t6); [exact HS| exact OK| exact Eb1| exact NL| exact L1| exact MEM'|].
      intros m'' a0'' a1'' a2'' a3'' MEM''. eapply K; [exact MEM''| exact OKf].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef SLMA i = true /\ (0 <= zget SLMA i < nG)%Z.
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation RS ra i t1 t2 a0 a1 a2 a3 s10 t5 t6 :=
    (RD ra (Z_to_bv 64 i) t1 t2 a0 a1 a2 a3 (Z_to_bv 64 8) (Z_to_bv 64 7) (Z_to_bv 64 32) (Z_to_bv 64 31) s10 (NOT (E + 19706)) (Z_to_bv 64 1) t5 t6).
  (* [comment removed for export] *)
  Definition selH (H : sdw) : sdw :=
    SDW (w1400 H) (w1408 H) (w1416 H) (w1424 H) (w1432 H) (w1448 H) (w1456 H) (w1472 H) (Z_to_bv 64 nSel) (w1496 H) (w1504 H) (w1512 H) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 18001).
  Definition sel_ok (H : sdw) : Prop := w1488 H = Z_to_bv 64 nSel /\ w1520 H = Z_to_bv 64 (E + 19706) /\ w1528 H = Z_to_bv 64 18001.
  Lemma selH_ok : forall H, sel_ok (selH H).
  Proof. intros H. repeat split. Qed.
  (* [comment removed for export] *)
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac sin HK := let HI := ident:(HI) in
    let a := fresh "HK88" in let b := fresh "HK20" in let c := fresh "HK28" in
    pose proof HK as (a & b & c); rewrite a, b, c in HI; clear a b c.
  Ltac sout HK := let HI := ident:(HI) in
    let a := fresh "HK88" in let b := fresh "HK20" in let c := fresh "HK28" in
    pose proof HK as (a & b & c); rewrite <- a, <- b, <- c in HI; clear a b c.

  (* [comment removed for export] *)
  Notation ONES_IH n :=
    (forall (i j s SHi : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra t1 t2 a0 a1 a2 s10 : word),
      (j + Z.of_nat n = s)%Z -> (0 <= j)%Z -> (0 <= i < nSel)%Z -> (s = zget SLMA i) -> saddr (E + 19706 + i) SHi ->
      let bf := sm_put_ones n b in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
      (forall m' (ra' t1' t2' a0' a2' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt b0segs Q (MS (RS ra' i t1' t2' a0' (Z_to_bv 64 (bw_live bf)) a2' (Z_to_bv 64 (E + 19706 + i)) s10 (Z_to_bv 64 s) (Z_to_bv 64 SHi)) F (Z_to_bv 64 0x94c0c) fc None m' (seg_rom b0segs))) ->
      evt b0segs Q (MS (RS ra i t1 t2 a0 a1 a2 (Z_to_bv 64 (E + 19706 + i)) s10 (Z_to_bv 64 j) (Z_to_bv 64 SHi)) F (Z_to_bv 64 0x94a30) fc None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Lemma B0_ones_tail : forall (i j s : Z) (n : nat) (SHi : Z) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (ra t1 t2 a0 a2 s10 : word),
    (j + Z.of_nat (S n) = s)%Z -> (0 <= j)%Z -> (0 <= i < nSel)%Z -> (s = zget SLMA i) -> saddr (E + 19706 + i) SHi ->
    let bf := sm_put_ones n (bsW b 1 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    ONES_IH n ->
    (forall m' (ra' t1' t2' a0' a2' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RS ra' i t1' t2' a0' (Z_to_bv 64 (bw_live bf)) a2' (Z_to_bv 64 (E + 19706 + i)) s10 (Z_to_bv 64 s) (Z_to_bv 64 SHi)) F (Z_to_bv 64 0x94c0c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RS ra i t1 t2 a0 (Z_to_bv 64 (bw_live b1)) a2 (Z_to_bv 64 (E + 19706 + i)) s10 (Z_to_bv 64 j) (Z_to_bv 64 SHi)) F (Z_to_bv 64 0x94b84) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i j s n SHi H bs b b1 m ra t1 t2 a0 a2 s10 Hj Hj0 Hi Hs AS. cbv zeta. intros OK Eb1 NL L1 MEM IHn K.
    destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 1 1 = BW (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 1)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    brun_to 0x94a30%Z.
    lazymatch type of EH2 with context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn i (j + 1)%Z s SHi H bs (bsW b 1 1) mm _ _ _ _ _ _ s10);
        [st_eq| lia| lia| exact Hi| exact Hs| exact AS| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_ones_loop : forall (n : nat), ONES_IH n.
  Proof using All.
    induction n as [|n IH].
    - intros i j s SHi H bs b m ra t1 t2 a0 a1 a2 s10 Hj Hj0 Hi Hs AS. cbv zeta. intros OK NL MEM K.
      destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR. cbn [sm_put_ones] in K.
      openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
      brun.
      openVW VW.
      pose proof (ovb_read1 b0segs m (E + 19706) SLMA (jseg J 19706 18002) 18002 i _ SLM ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
      closeVW.
      wstep. clear RD. cbv beta. rewrite <- Hs. rewrite (unsigned_lit8 s) by lia.
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc; [|exfalso; lia].
      enter_with (K m _ _ _ _ _); [st_eq| closeMD| exact OK].
    - intros i j s SHi H bs b m ra t1 t2 a0 a1 a2 s10 Hj Hj0 Hi Hs AS. cbv zeta. intros OK NL MEM K.
      destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR.
      rewrite put_ones_S in NL, K.
      pose proof (put_ones_NZM n (bsW b 1 1)) as NZ1. unfold NZM in NZ1.
      pose proof (bsW_NZM b 1 1) as NZ0. unfold NZM in NZ0.
      openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
      pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
      brun.
      openVW VW.
      pose proof (ovb_read1 b0segs m (E + 19706) SLMA (jseg J 19706 18002) 18002 i _ SLM ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
      closeVW.
      wstep. clear RD. cbv beta. rewrite <- Hs. rewrite (unsigned_lit8 s) by lia.
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
      (* [comment removed for export] *)
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (B0_ones_tail i j s n SHi H bs b b m _ _ _ _ _ s10); [st_eq| lia| lia| exact Hi| exact Hs| exact AS| exact OK| | exact NL| lia| closeMD| exact IH| exact K].
        unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + enter_with (FLX fl_9478c BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' a0' ra' a2' t2' t1' Eb1 MEM' L1.
        enter_with (B0_ones_tail i j s n SHi H bs b b1 m' _ _ _ _ _ s10); [st_eq| lia| lia| exact Hi| exact Hs| exact AS| exact OK| exact Eb1| exact NL| exact L1| exact MEM'| exact IH| exact K].
  Qed.

  (* [comment removed for export] *)
  Notation SELS_IH n :=
    (forall (i : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra t1 t2 a0 a1 a2 a3 s10 t5 t6 : word),
      (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> sel_ok H ->
      let bf := sm_put_sels n b SLMA i in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
      (forall m' (ra' t1' t2' a0' a1' a2' a3' s10' t5' t6' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt b0segs Q (MS (RS ra' nSel t1' t2' a0' a1' a2' a3' s10' t5' t6') F (Z_to_bv 64 0x94d9c) fc None m' (seg_rom b0segs))) ->
      evt b0segs Q (MS (RS ra i t1 t2 a0 a1 a2 a3 s10 t5 t6) F (Z_to_bv 64 0x94a04) fc None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Lemma B0_sels_fin : forall (i : Z) (n : nat) (H : sdw) (bs : list byte) (bo b1 : bw) (m : word -> option byte)
      (ra t1 t2 a0 a2 a3 s10 t5 t6 : word),
    (i + Z.of_nat (S n) = nSel)%Z -> (0 <= i)%Z -> sel_ok H ->
    let bf := sm_put_sels n (bsW bo 1 0) SLMA (i + 1) in
    bw_ok bo -> b1 = bs_needw BS_FUEL bo -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    SELS_IH n ->
    (forall m' (ra' t1' t2' a0' a1' a2' a3' s10' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RS ra' nSel t1' t2' a0' a1' a2' a3' s10' t5' t6') F (Z_to_bv 64 0x94d9c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RS ra i t1 t2 a0 (Z_to_bv 64 (bw_live b1)) a2 a3 s10 t5 t6) F (Z_to_bv 64 0x94d44) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i n H bs bo b1 m ra t1 t2 a0 a2 a3 s10 t5 t6 Hi Hi0 HK. cbv zeta. intros OK Eb1 NL L1 MEM IHn K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. sin HK.
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW bo 1 0 = BW (bw_buff b1) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1)).
    { unfold bsW. rewrite <- Eb1. f_equal. change 4294967296%Z with M32. rewrite lor_shl0. reflexivity. }
    assert (OK2 : bw_ok (bsW bo 1 0)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    brun. sout HK. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z H bs (bsW bo 1 0) mm _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| exact HK| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_sels] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_sels_outer : forall (n : nat), SELS_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros i H bs b m ra t1 t2 a0 a1 a2 a3 s10 t5 t6 Hi Hi0 _ HK. cbv zeta. intros OK NL MEM K.
    destruct (SLMF i ltac:(lia)) as [ZD ZR].
    rewrite put_sels_S in NL, K.
    set (s := zget SLMA i) in *.
    set (bo := sm_put_ones (Z.to_nat s) b) in NL, K.
    pose proof (put_sels_NZM n (bsW bo 1 0) SLMA (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM bo 1 0) as NZ0. unfold NZM in NZ0.
    pose proof (put_ones_NZM (Z.to_nat s) b) as NZo. unfold NZM in NZo. fold bo in NZo.
    destruct (put_ones_ok (Z.to_nat s) b OK) as [OKo LVo]. fold bo in OKo, LVo.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn). sin HK.
    (* [comment removed for export] *)
    brun_to 0x94a30%Z. sout HK.
    (* [comment removed for export] *)
    pose proof (saddr_intro (E + 19706 + i)) as AS. set (SHi := ((E + 19706 + i) / 8 + 2147450880)%Z) in *. clearbody SHi.
    enter_with (B0_ones_loop (Z.to_nat s) i 0 s SHi H bs b m _ _ _ _ _ _ _); [st_eq| lia| lia| lia| reflexivity| exact AS| exact OK| fold bo; lia| closeMD|].
    fold bo. clear EH1 EH2 AR2 HI I16 MI MU WM.
    intros m' ra' t1' t2' a0' a2' MEM' OK'.
    cps_pose OK' as (OKb' & OKl' & OKn').
    cps_pose (bs_needw_post BS_FUEL bo OK' ltac:(unfold BS_FUEL; cbn; lia)) as (OK1' & M1' & N1').
    pose proof (Z.mod_pos_bound (bw_live bo) 8 ltac:(lia)) as MB'.
    openMD MEM'.
    (* [comment removed for export] *)
    wstep; if_cases Kc2; zify_cond_z Kc2.
    - enter_with (B0_sels_fin i n H bs bo bo m' _ _ _ _ _ _ _ _ _); [st_eq| lia| lia| exact HK| exact OKo| | exact NL| lia| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live bo)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX fl_9494c BS_FUEL H bs bo m'); [st_eq| exact OK'| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes bo 1 0) as [BB _]. rewrite <- BB. lia. }
      intros b1 m'' a0'' a2'' t5'' a3'' t1'' Eb1 MEM'' L1.
      enter_with (B0_sels_fin i n H bs bo b1 m'' _ _ _ _ _ _ _ _ _); [st_eq| lia| lia| exact HK| exact OK'| exact Eb1| exact NL| exact L1| exact MEM''| exact IH| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_sels : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    w1448 H = Z_to_bv 64 nSel ->
    let bf := sm_put_sels (Z.to_nat nSel) b SLMA 0 in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (ra' t1' t2' a0' a1' a2' a3' s10' t5' t6' : word),
        MD (selH H) bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RS ra' nSel t1' t2' a0' a1' a2' a3' s10' t5' t6') F (Z_to_bv 64 0x94d9c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6) F (Z_to_bv 64 0x949b0) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b m ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 HS. cbv zeta. intros OK NL MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. rewrite HS in HI.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    brun_to 0x949c4%Z. rewrite <- HS in HI.
    brun_to 0x949e8%Z. wstep. lit_store. brun_to 0x94a04%Z.
    replace (Z.land 18446744073709551615 nSel) with nSel in HI by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_sels_outer (Z.to_nat nSel) 0%Z (selH H) bs b mm _ _ _ _ _ _ _ _ _ _); [st_eq| lia| lia| lia| apply selH_ok| exact OK| exact NL| closeMD| exact K] end.
  Qed.
End SDE.
End ACeilS1.
