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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_cmp_sdBV.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
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

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require U0_cmp_sdB1 U0_cmp_sdB2.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDB.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp ra s1 s3 s4 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1200 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variable m0 : word -> option byte.
  Notation MD b m := (MUd cx g e usp m0 b m).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMUd Gmtf Gbs Gzb H.
  Ltac closeMD := closeMUd Gmtf Gbs Gzb.
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Variable nG : Z. Hypothesis HG : (2 <= nG <= 6)%Z.
  Variable nSel : Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  Notation RU a4 a5 a6 a7 t0 t1 t2 t3 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 LR) (Z_to_bv 64 CR)
         (Z_to_bv 64 (18446744073709551615 - LR)) (Z_to_bv 64 (18446744073709551615 - CR)) a4 a5 a6 a7
         (Z_to_bv 64 gs) s3 s4 (Z_to_bv 64 7) (Z_to_bv 64 32) s7 s8 s9 s10 s11 t3 t4 t5 t6).
  Notation SX L := (L cx g e Q sp gp tp ra s1 s3 s4 s7 s8 s9 s10 s11 t4 t5 t6 F fc CX SEP Gmtf Gbs Gzb Hnb USP1 USP2 LIM HLIM m0
                      A HA nG HG nSel HNS LENF CODF SELF ZB1 sc gs Hsc Hgs HgsE MTFV).

  Lemma Hsel : (0 <= sel < 6)%Z. Proof using SELF Hsc HG. pose proof (SELF sc Hsc). lia. Qed.

  Lemma fl_17 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d9dc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d964) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_17_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 18)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1da34) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d9dc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1da34%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_17 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 18)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1da34) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 17)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d8e8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 17) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 17)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 17)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 17))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_17_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_17 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_17_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_18 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1db28) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1dab0) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_18_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 19)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1db80) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1db28) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1db80%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_18 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 19)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1db80) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 18)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1da34) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 18) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 18)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 18)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 18))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_18_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_18 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_18_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_19 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1dc74) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1dbfc) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_19_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 20)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1dccc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1dc74) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1dccc%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_19 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 20)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1dccc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 19)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1db80) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 19) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 19)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 19)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 19))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_19_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_19 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_19_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_20 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1ddc0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1dd48) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_20_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 21)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1de18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1ddc0) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1de18%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_20 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 21)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1de18) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 20)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1dccc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 20) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 20)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 20)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 20))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_20_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_20 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_20_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_21 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1df0c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1de94) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_21_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 22)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1df64) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1df0c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1df64%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_21 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 22)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1df64) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 21)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1de18) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 21) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 21)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 21)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 21))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_21_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_21 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_21_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_22 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e058) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1dfe0) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_22_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 23)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e0b0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e058) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e0b0%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_22 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 23)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e0b0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 22)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1df64) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 22) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 22)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 22)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 22))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_22_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_22 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_22_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_23 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e1a4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e12c) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_23_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 24)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e1fc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e1a4) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e1fc%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_23 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 24)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e1fc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 23)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e0b0) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 23) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 23)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 23)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 23))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_23_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_23 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_23_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_24 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e2f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e278) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros b m a4 a5 a6 t0 t1 t2 t3 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    urun.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    match type of AR2 with u8arr _ _ _ (zb8 ?l _) => replace l with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X4. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) _ _ a5 a6 _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma blk_24_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 25)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e348) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e2f0) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e348%Z.
    rewrite (Z.mod_small (32 - bw_live b1 - n) 32) in EH2 by lia.
    rewrite Z.lor_comm in EH2.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    enter_with (K _ _ _ _ _); [st_eq| closeMD|].
    cbn [bw_buff]. rewrite (Z.mod_small (32 - bw_live b1 - n) 32) by lia. rewrite Z.lor_comm.
    rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
    rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
    apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma blk_24 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 25)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e348) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 24)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e1fc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 24) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 24)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 24)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 24))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_24_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_24 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_24_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma blocks_17_24 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 17)) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 17)) m' -> (bv_unsigned a4' mod 4294967296 = bw_buff (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 17)))%Z -> bw_ok (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 17)) ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 25)) (Z_to_bv 64 (bw_live (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 17)))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e348) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 17)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d8e8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    remember (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 17)) as bf eqn:RES. symmetry in RES.
    revert a4 a5 t0 t1 t2 t3 m OK X4 MEM RES. generalize b. intros B a4 a5 t0 t1 t2 t3 m OKB XB MEM RES.
    rewrite put_syms_S in RES. replace (gs + 17 + 1)%Z with (gs + 18)%Z in RES by lia.
    pose proof (put_syms_NZM 7 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))) LENA CODA ARR1 sel (gs + 18)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 17) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_17 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 18 + 1)%Z with (gs + 19)%Z in RES by lia.
    pose proof (put_syms_NZM 6 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))) LENA CODA ARR1 sel (gs + 19)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 18) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_18 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 19 + 1)%Z with (gs + 20)%Z in RES by lia.
    pose proof (put_syms_NZM 5 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))) LENA CODA ARR1 sel (gs + 20)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 19) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_19 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 20 + 1)%Z with (gs + 21)%Z in RES by lia.
    pose proof (put_syms_NZM 4 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))) LENA CODA ARR1 sel (gs + 21)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 20) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_20 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 21 + 1)%Z with (gs + 22)%Z in RES by lia.
    pose proof (put_syms_NZM 3 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))) LENA CODA ARR1 sel (gs + 22)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 21) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_21 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 22 + 1)%Z with (gs + 23)%Z in RES by lia.
    pose proof (put_syms_NZM 2 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))) LENA CODA ARR1 sel (gs + 23)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 22) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_22 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 23 + 1)%Z with (gs + 24)%Z in RES by lia.
    pose proof (put_syms_NZM 1 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))) LENA CODA ARR1 sel (gs + 24)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 23) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_23 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 24 + 1)%Z with (gs + 25)%Z in RES by lia.
    pose proof (put_syms_NZM 0 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))) LENA CODA ARR1 sel (gs + 25)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 24) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_24 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_0 in RES. subst B. eapply K; [exact MEM| exact XB| exact OKB].
  Qed.

  Lemma blocks_1_24 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1)) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1)) m' -> (bv_unsigned a4' mod 4294967296 = bw_buff (sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1)))%Z -> bw_ok (sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1)) ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 25)) (Z_to_bv 64 (bw_live (sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1)))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e348) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 1)) t0 (Z_to_bv 64 (bw_live b)) t1 t2 t3) F (Z_to_bv 64 0x1c428) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    change (24)%nat with (8 + 16)%nat in K, NL. rewrite put_syms_split in K, NL.
    replace (gs + 1 + Z.of_nat 8)%Z with (gs + 9)%Z in K, NL by lia.
    pose proof (put_syms_NZM 16 (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 1)) LENA CODA ARR1 sel (gs + 9)) as NZ. unfold NZM in NZ.
    eapply ((SX U0_cmp_sdB1.blocks_1_8) b m _ _ _ _ _ _); [exact OK| lia| exact X4| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 X4 OK. intros m a4 a5 t0 t1 t2 t3 MEM X4 OK.
    clear NZ. revert a4 a5 t0 t1 t2 t3 m OK MEM X4 K NL. generalize (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 1)). clear b. intros b a4 a5 t0 t1 t2 t3 m OK MEM X4 K NL.
    change (16)%nat with (8 + 8)%nat in K, NL. rewrite put_syms_split in K, NL.
    replace (gs + 9 + Z.of_nat 8)%Z with (gs + 17)%Z in K, NL by lia.
    pose proof (put_syms_NZM 8 (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)) LENA CODA ARR1 sel (gs + 17)) as NZ. unfold NZM in NZ.
    eapply ((SX U0_cmp_sdB2.blocks_9_16) b m _ _ _ _ _ _); [exact OK| lia| exact X4| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 X4 OK. intros m a4 a5 t0 t1 t2 t3 MEM X4 OK.
    clear NZ. revert a4 a5 t0 t1 t2 t3 m OK MEM X4 K NL. generalize (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)). clear b. intros b a4 a5 t0 t1 t2 t3 m OK MEM X4 K NL.
    eapply (blocks_17_24 b m _ _ _ _ _ _); [exact OK| exact NL| exact X4| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 X4 OK. intros m a4 a5 t0 t1 t2 t3 MEM X4 OK.
    eapply K; [exact MEM| exact X4| exact OK].
  Qed.

End SDB.
End ACeilS1.
