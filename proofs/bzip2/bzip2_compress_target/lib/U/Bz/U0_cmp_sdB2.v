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

  Lemma fl_9 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1cf7c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1cf04) fc None m (seg_rom s0segs)).
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

  Lemma blk_9_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 10)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1cfd4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1cf7c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1cfd4%Z.
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

  Lemma blk_9 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 10)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1cfd4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 9)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1ce88) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 9) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 9)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 9)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 9))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_9_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_9 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_9_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_10 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d0c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d050) fc None m (seg_rom s0segs)).
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

  Lemma blk_10_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 11)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d120) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d0c8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d120%Z.
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

  Lemma blk_10 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 11)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d120) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 10)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1cfd4) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 10) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 10)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 10)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 10))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_10_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_10 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_10_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_11 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d214) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d19c) fc None m (seg_rom s0segs)).
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

  Lemma blk_11_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 12)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d26c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d214) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d26c%Z.
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

  Lemma blk_11 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 12)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d26c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 11)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d120) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 11) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 11)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 11)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 11))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_11_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_11 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_11_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_12 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d360) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d2e8) fc None m (seg_rom s0segs)).
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

  Lemma blk_12_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 13)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d3b8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d360) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d3b8%Z.
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

  Lemma blk_12 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 13)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d3b8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 12)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d26c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 12) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 12)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 12)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 12))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_12_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_12 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_12_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_13 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d4ac) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d434) fc None m (seg_rom s0segs)).
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

  Lemma blk_13_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 14)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d504) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d4ac) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d504%Z.
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

  Lemma blk_13 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 14)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d504) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 13)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d3b8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 13) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 13)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 13)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 13))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_13_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_13 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_13_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_14 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d5f8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d580) fc None m (seg_rom s0segs)).
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

  Lemma blk_14_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 15)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d650) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d5f8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d650%Z.
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

  Lemma blk_14 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 15)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d650) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 14)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d504) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 14) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 14)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 14)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 14))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_14_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_14 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_14_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_15 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d744) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d6cc) fc None m (seg_rom s0segs)).
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

  Lemma blk_15_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 16)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d79c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d744) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d79c%Z.
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

  Lemma blk_15 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 16)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d79c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 15)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d650) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 15) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 15)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 15)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 15))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_15_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_15 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_15_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_16 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1d890) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d818) fc None m (seg_rom s0segs)).
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

  Lemma blk_16_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 17)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1d8e8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1d890) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1d8e8%Z.
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

  Lemma blk_16 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 17)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d8e8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 16)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1d79c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 16) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 16)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 16)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 16))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_16_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_16 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_16_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma blocks_9_16 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)) m' -> (bv_unsigned a4' mod 4294967296 = bw_buff (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)))%Z -> bw_ok (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)) ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 17)) (Z_to_bv 64 (bw_live (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1d8e8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 9)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1ce88) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    remember (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 9)) as bf eqn:RES. symmetry in RES.
    revert a4 a5 t0 t1 t2 t3 m OK X4 MEM RES. generalize b. intros B a4 a5 t0 t1 t2 t3 m OKB XB MEM RES.
    rewrite put_syms_S in RES. replace (gs + 9 + 1)%Z with (gs + 10)%Z in RES by lia.
    pose proof (put_syms_NZM 7 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))) LENA CODA ARR1 sel (gs + 10)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 9) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_9 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 10 + 1)%Z with (gs + 11)%Z in RES by lia.
    pose proof (put_syms_NZM 6 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))) LENA CODA ARR1 sel (gs + 11)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 10) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_10 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 11 + 1)%Z with (gs + 12)%Z in RES by lia.
    pose proof (put_syms_NZM 5 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))) LENA CODA ARR1 sel (gs + 12)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 11) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_11 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 12 + 1)%Z with (gs + 13)%Z in RES by lia.
    pose proof (put_syms_NZM 4 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))) LENA CODA ARR1 sel (gs + 13)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 12) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_12 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 13 + 1)%Z with (gs + 14)%Z in RES by lia.
    pose proof (put_syms_NZM 3 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))) LENA CODA ARR1 sel (gs + 14)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 13) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_13 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 14 + 1)%Z with (gs + 15)%Z in RES by lia.
    pose proof (put_syms_NZM 2 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))) LENA CODA ARR1 sel (gs + 15)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 14) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_14 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 15 + 1)%Z with (gs + 16)%Z in RES by lia.
    pose proof (put_syms_NZM 1 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))) LENA CODA ARR1 sel (gs + 16)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 15) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_15 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 16 + 1)%Z with (gs + 17)%Z in RES by lia.
    pose proof (put_syms_NZM 0 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))) LENA CODA ARR1 sel (gs + 17)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 16) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_16 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_0 in RES. subst B. eapply K; [exact MEM| exact XB| exact OKB].
  Qed.

End SDB.
End ACeilS1.
