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

  Lemma fl_25 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e43c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e3c4) fc None m (seg_rom s0segs)).
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

  Lemma blk_25_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 26)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e494) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e43c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e494%Z.
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

  Lemma blk_25 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 26)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e494) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 25)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e348) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 25) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 25)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 25)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 25))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_25_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_25 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_25_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_26 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e588) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e510) fc None m (seg_rom s0segs)).
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

  Lemma blk_26_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 27)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e5e0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e588) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e5e0%Z.
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

  Lemma blk_26 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 27)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e5e0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 26)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e494) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 26) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 26)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 26)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 26))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_26_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_26 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_26_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_27 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e6d4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e65c) fc None m (seg_rom s0segs)).
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

  Lemma blk_27_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 28)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e72c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e6d4) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e72c%Z.
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

  Lemma blk_27 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 28)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e72c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 27)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e5e0) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 27) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 27)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 27)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 27))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_27_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_27 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_27_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_28 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e820) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e7a8) fc None m (seg_rom s0segs)).
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

  Lemma blk_28_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 29)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e878) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e820) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e878%Z.
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

  Lemma blk_28 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 29)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e878) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 28)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e72c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 28) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 28)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 28)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 28))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_28_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_28 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_28_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_29 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1e96c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e8f4) fc None m (seg_rom s0segs)).
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

  Lemma blk_29_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 30)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1e9c4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1e96c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1e9c4%Z.
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

  Lemma blk_29 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 30)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1e9c4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 29)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e878) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 29) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 29)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 29)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 29))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_29_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_29 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_29_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_30 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1eab8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1ea40) fc None m (seg_rom s0segs)).
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

  Lemma blk_30_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 31)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1eb10) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1eab8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1eb10%Z.
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

  Lemma blk_30 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 31)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1eb10) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 30)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e9c4) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 30) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 30)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 30)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 30))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_30_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_30 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_30_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_31 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1ec04) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1eb8c) fc None m (seg_rom s0segs)).
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

  Lemma blk_31_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 32)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1ec5c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1ec04) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1ec5c%Z.
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

  Lemma blk_31 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 32)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1ec5c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 31)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1eb10) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 31) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 31)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 31)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 31))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_31_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_31 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_31_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma fl_32 : forall (f : nat) (b : bw) (m : word -> option byte) (a4 a5 a6 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a7' t1' t2' t3' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RU a4' a5 a6 a7' (Z_to_bv 64 (bw_live b1)) t1' t2' t3') F (Z_to_bv 64 0x1ed50) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 a6 (Z_to_bv 64 (bw_numZ b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1ecd8) fc None m (seg_rom s0segs)).
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

  Lemma blk_32_tail : forall (b1 : bw) (n cv : Z) (m : word -> option byte) (a4 a7 t1 t2 t3 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (a4' a5' t1' t2' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD b' m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b')%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 33)) (Z_to_bv 64 (bw_live b1 + n)) (Z_to_bv 64 (bw_live b1)) t1' t2' t3) F (Z_to_bv 64 0x1eda8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 (Z_to_bv 64 n) (sx32 (Z_to_bv 64 cv)) a7 (Z_to_bv 64 (bw_live b1)) t1 t2 t3) F (Z_to_bv 64 0x1ed50) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b1 n cv m a4 a7 t1 t2 t3 OK L1 Hn Hcv X4 MEM K.
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    urun_to 0x1eda8%Z.
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

  Lemma blk_32 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))) m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))))%Z ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 33)) (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1eda8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 32)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1ec5c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 32) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 32)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 32)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 32))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_32_tail b n cv m a4 _ _ _ _); [st_eq| exact OK| lia| lia| lia| exact X4| closeMD|].
      intros m' a4' a5' t1' t2' b' MEM' X4'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM'| exact X4'].
    - wstep.
      enter_with (fl_32 BS_FUEL b _ a4 _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a4' a7' t1' t2' t3' Eb1 MEM' X4' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_32_tail b1 n cv m' a4' _ _ _ _); [st_eq| exact OK1| lia| lia| lia| exact X4'| exact MEM'|].
      intros m'' a4'' a5'' t1'' t2'' b' MEM'' X4''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact MEM''| exact X4''].
  Qed.

  Lemma blocks_25_32 : forall (b : bw) (m : word -> option byte) (a4 a5 t0 t1 t2 t3 : word),
    bw_ok b -> (bw_numZ (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 25)) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a4' a5' t0' t1' t2' t3' : word),
        MD (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 25)) m' -> (bv_unsigned a4' mod 4294967296 = bw_buff (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 25)))%Z -> bw_ok (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 25)) ->
        evt s0segs Q (MS (RU a4' a5' (Z_to_bv 64 (gs + 33)) (Z_to_bv 64 (bw_live (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 25)))) t0' t1' t2' t3')
                         F (Z_to_bv 64 0x1eda8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU a4 a5 (Z_to_bv 64 (gs + 25)) (Z_to_bv 64 (bw_live b)) t0 t1 t2 t3) F (Z_to_bv 64 0x1e348) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m a4 a5 t0 t1 t2 t3 OK NL X4 MEM K.
    remember (sm_put_syms 8 b LENA CODA ARR1 sel (gs + 25)) as bf eqn:RES. symmetry in RES.
    revert a4 a5 t0 t1 t2 t3 m OK X4 MEM RES. generalize b. intros B a4 a5 t0 t1 t2 t3 m OKB XB MEM RES.
    rewrite put_syms_S in RES. replace (gs + 25 + 1)%Z with (gs + 26)%Z in RES by lia.
    pose proof (put_syms_NZM 7 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))) LENA CODA ARR1 sel (gs + 26)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 25) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_25 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 26 + 1)%Z with (gs + 27)%Z in RES by lia.
    pose proof (put_syms_NZM 6 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))) LENA CODA ARR1 sel (gs + 27)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 26) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_26 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 27 + 1)%Z with (gs + 28)%Z in RES by lia.
    pose proof (put_syms_NZM 5 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))) LENA CODA ARR1 sel (gs + 28)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 27) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_27 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 28 + 1)%Z with (gs + 29)%Z in RES by lia.
    pose proof (put_syms_NZM 4 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))) LENA CODA ARR1 sel (gs + 29)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 28) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_28 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 29 + 1)%Z with (gs + 30)%Z in RES by lia.
    pose proof (put_syms_NZM 3 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))) LENA CODA ARR1 sel (gs + 30)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 29) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_29 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 30 + 1)%Z with (gs + 31)%Z in RES by lia.
    pose proof (put_syms_NZM 2 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))) LENA CODA ARR1 sel (gs + 31)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 30) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_30 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 31 + 1)%Z with (gs + 32)%Z in RES by lia.
    pose proof (put_syms_NZM 1 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))) LENA CODA ARR1 sel (gs + 32)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 31) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_31 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_S in RES. replace (gs + 32 + 1)%Z with (gs + 33)%Z in RES by lia.
    pose proof (put_syms_NZM 0 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))) LENA CODA ARR1 sel (gs + 33)) as NZ; rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 32) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    eapply (blk_32 B m _ _ _ _ _ _); [exact OKB| lia| exact XB| exact MEM|].
    clear MEM m a4 a5 t0 t1 t2 t3 XB. intros m a4 a5 t0 t1 t2 t3 MEM XB.
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32))) OKB
                  ltac:(pose proof (LENF sel _ ltac:(lia) MV); lia) ltac:(pose proof (CODF sel _ ltac:(lia) MV); lia)) as OKB'.
    clear OKB NZ MV SD SR. revert a4 a5 t0 t1 t2 t3 m OKB' MEM XB RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))). clear B. intros B a4 a5 t0 t1 t2 t3 m OKB MEM XB RES.
    rewrite put_syms_0 in RES. subst B. eapply K; [exact MEM| exact XB| exact OKB].
  Qed.

End SDB.
End ACeilS1.
