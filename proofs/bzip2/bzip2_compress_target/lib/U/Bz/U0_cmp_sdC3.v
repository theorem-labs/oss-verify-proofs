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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_smV U0_cmp_sdY.
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

Section SLOW.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp ra s3 s7 s9 : word) (F : bvmap 5 word) (fc : bv 32).
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
  Variables (sc gs ge : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs <= ge)%Z. Hypothesis Hge : (ge <= gs + 49)%Z.
  Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i <= ge)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Hypothesis SEL0 : u8arr s0segs m0 (E + 1704) (ovb SELA (jseg J 1704 18002) 18002).
  Hypothesis F960 : rw_cells s0segs m0 (usp + 960) [C8 (Z_to_bv 64 (E + 37708))].
  Hypothesis F1008 : rw_cells s0segs m0 (usp + 1008) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 2147483647)].
  Hypothesis HRA : ra = Z_to_bv 64 (18446744073709551615 - (E + 39256)).
  Hypothesis HS9 : s9 = Z_to_bv 64 (18446744073709551615 - (E + 37708)).
  Notation sel := (zget SELA sc).
  Notation NVi i := (zget LENA (258 * sel + mtfv_at ARR1 i)).
  Notation CVi i := (zget CODA (258 * sel + mtfv_at ARR1 i)).
  Notation NRA := (Z_to_bv 64 (18446744073709551615 - (E + 39256))).
  Notation NS9 := (Z_to_bv 64 (18446744073709551615 - (E + 37708))).
  Notation RS t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 i :=
    (mkR NRA sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 (ge + 1)) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 i) s3 (Z_to_bv 64 sc) (Z_to_bv 64 7) (Z_to_bv 64 32) s7 (Z_to_bv 64 (ge + 1)) NS9 (Z_to_bv 64 50) (Z_to_bv 64 5)
         t3 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032)).
  Notation RX t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 :=
    (mkR NRA sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 (Z_to_bv 64 sc) (Z_to_bv 64 7) (Z_to_bv 64 32) s7 (Z_to_bv 64 (ge + 1)) NS9 (Z_to_bv 64 50) (Z_to_bv 64 5)
         t3 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032)).

  Lemma ro_now : forall (b : bw) (m : word -> option byte), MD b m ->
    u8arr s0segs m (E + 1704) (ovb SELA (jseg J 1704 18002) 18002) /\
    rw_cells s0segs m (usp + 960) [C8 (Z_to_bv 64 (E + 37708))] /\
    rw_cells s0segs m (usp + 1008) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 2147483647)].
  Proof using All.
    intros b m (_ & _ & _ & _ & _ & _ & _ & _ & MU & WM).
    openCX. unfold id in *. unfold sdWd in MU.
    refine (conj _ (conj _ _)).
    - eapply u8arr_transport; [exact SEL0| exact MU| exact WM|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
    - eapply rw_cells_transport; [exact F960| exact MU| exact WM|]. cbn [disjoint_from cells_size csize]. repeat split; lia.
    - eapply rw_cells_transport; [exact F1008| exact MU| exact WM|]. cbn [disjoint_from cells_size csize]. repeat split; lia.
  Qed.

  Lemma fl_s : forall (f : nat) (i : Z) (b : bw) (m : word -> option byte) (a1 a2 a3 a5 a6 a7 t0 t1 t2 t3 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a5 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' a5' a6' a7' t0' : word), b1 = bs_needw f b -> MD b1 m' ->
        (bv_unsigned a5' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RS t0' t1 t2 a1 a2 (Z_to_bv 64 (bw_live b1)) a4' a5' a6' a7' t3 i) F (Z_to_bv 64 0x201e0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS t0 t1 t2 a1 a2 a3 (Z_to_bv 64 (bw_numZ b)) a5 a6 a7 t3 i) F (Z_to_bv 64 0x2017c) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros i b m a1 a2 a3 a5 a6 a7 t0 t1 t2 t3 OK L8 Lf NL X5 MEM K; [lia|].
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
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite X5. rewrite unsigned_lit by lia. rewrite shiftr_div24. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IH i (bw_emit b) _ a1 a2 _ _ _ _ _ t1 t2 t3); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a5' a6' a7' t0' Eb1 MEM' X5' L1. eapply K; [|exact MEM'| exact X5'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) _ _ _ _ _ _); [st_eq| | closeMD| | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Definition SIH (n : nat) : Prop :=
    forall (i : Z) (b : bw) (m : word -> option byte) (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 : word),
    (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z -> bw_ok b ->
    (bw_numZ (sm_put_syms n b LENA CODA ARR1 sel i) <= LIM)%Z -> MD b m ->
    (forall m' (s1' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word),
       MD (sm_put_syms n b LENA CODA ARR1 sel i) m' -> bw_ok (sm_put_syms n b LENA CODA ARR1 sel i) ->
       evt s0segs Q (MS (RX t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3') F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 i) F (Z_to_bv 64 0x200dc) fc None m (seg_rom s0segs)).

  Lemma slow_tail : forall (i : Z) (b b1 : bw) (m : word -> option byte) (n : nat) (a4 a5 a6 a7 t0 t1 t2 t3 : word),
    (i + Z.of_nat (S n) = ge + 1)%Z -> (gs <= i)%Z ->
    bw_ok b -> b1 = bs_needw BS_FUEL b ->
    (bw_numZ (sm_put_syms n (bsW b (NVi i) (CVi i)) LENA CODA ARR1 sel (i + 1)) <= LIM)%Z -> MD b1 m ->
    SIH n ->
    (forall m' (s1' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word),
       MD (sm_put_syms n (bsW b (NVi i) (CVi i)) LENA CODA ARR1 sel (i + 1)) m' ->
       bw_ok (sm_put_syms n (bsW b (NVi i) (CVi i)) LENA CODA ARR1 sel (i + 1)) ->
       evt s0segs Q (MS (RX t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3') F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS t0 t1 t2 (Z_to_bv 64 (NVi i)) (sx32 (Z_to_bv 64 (CVi i))) (Z_to_bv 64 (bw_live b1)) a4 a5 a6 a7 t3 i)
                      F (Z_to_bv 64 0x201e0) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i b b1 m n a4 a5 a6 a7 t0 t1 t2 t3 Hn Hi OK Eb1 NL MEM IHn K. unfold SIH in IHn.
    set (v := mtfv_at ARR1 i) in *. set (nv := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (put_syms_NZM n (bsW b nv cv) LENA CODA ARR1 sel (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (ro_now _ _ MEM) as (_ & _ & F1008m).
    openCX. openMD MEM.
    pose proof (MTFV i ltac:(lia)) as MV. fold v in MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG]. fold nv in LD, LRG. fold cv in CD, CRG.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    urun.
    rewrite (Z.mod_small (32 - bw_live b1 - nv) 32) in EH2 by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - nv)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    assert (EBW : bsW b nv cv = BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - nv)) mod 4294967296)) (bw_live b1 + nv) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b nv cv)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    if_cases Kc; zify_cond_z Kc.
    - enter_with (IHn (i + 1)%Z (bsW b nv cv) _ _ _ _ _ _ _ _ _ t1 t2 t3); [st_eq| lia| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. rewrite put_syms_0 in K.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2].
  Qed.

  Lemma loop_lit : forall n, SIH n.
  Proof using All.
    intro n. induction n as [|n IH]; unfold SIH in *; [intros; lia|].
    intros i b m a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 _ Hin Hi OK NL MEM K.
    rewrite put_syms_S in NL, K.
    set (v := mtfv_at ARR1 i) in *. set (nv := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (put_syms_NZM n (bsW b nv cv) LENA CODA ARR1 sel (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b nv cv) as NZ0. unfold NZM in NZ0.
    pose proof (ro_now _ _ MEM) as (SELm & F960m & F1008m).
    openCX. openMD MEM.
    cps_pose OK as (OKb & OKl & OKn).
    pose proof (MTFV i ltac:(lia)) as MV. fold v in MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG]. fold nv in LD, LRG. fold cv in CD, CRG.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    urun.
    pose proof (ovb_read1 s0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SELm ltac:(lia) SD ltac:(unfold wa; f_equal; lia)) as RDS.
    wstep. clear RDS. cbv beta. rewrite (unsigned_lit8 sel) by lia.
    urun.
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * i)) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    urun.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold nv. rewrite (unsigned_lit8 nv) by lia.
    urun.
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    urun.
    if_cases Kc; zify_cond_z Kc.
    - enter_with (slow_tail i b b m n _ _ _ _ _ t1 t2 t3); [st_eq| lia| lia| exact OK| | exact NL| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - wstep. wstep.
      enter_with (fl_s BS_FUEL i b _ _ _ _ _ _ _ _ t1 t2 t3); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
      { pose proof (bsW_bytes b nv cv) as [BB _]. rewrite <- BB. lia. }
      { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
      intros b1 m' a4' a5' a6' a7' t0' Eb1 MEM' X5' L1.
      enter_with (slow_tail i b b1 m' n _ _ _ _ _ t1 t2 t3); [st_eq| lia| lia| exact OK| exact Eb1| exact NL| exact MEM'| exact IH| exact K].
  Qed.

  Lemma slow_loop : forall (n : nat) (i : Z) (b : bw) (m : word -> option byte) (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 : word),
    (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z -> bw_ok b ->
    (bw_numZ (sm_put_syms n b LENA CODA ARR1 sel i) <= LIM)%Z -> MD b m ->
    (forall m' (s1' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word),
       MD (sm_put_syms n b LENA CODA ARR1 sel i) m' -> bw_ok (sm_put_syms n b LENA CODA ARR1 sel i) ->
       evt s0segs Q (MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 (Z_to_bv 64 sc)
                             (Z_to_bv 64 7) (Z_to_bv 64 32) s7 (Z_to_bv 64 (ge + 1)) s9 (Z_to_bv 64 50) (Z_to_bv 64 5) t3'
                             (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032))
                        F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 (ge + 1)) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 i) s3 (Z_to_bv 64 sc) (Z_to_bv 64 7) (Z_to_bv 64 32) s7 (Z_to_bv 64 (ge + 1)) s9
                          (Z_to_bv 64 50) (Z_to_bv 64 5) t3 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032))
                     F (Z_to_bv 64 0x200dc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros n i b m a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 Hn Hin Hi OK NL MEM K.
    rewrite HRA, HS9 in K |- *.
    exact (loop_lit n i b m a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 Hn Hin Hi OK NL MEM K).
  Qed.
End SLOW.

Lemma SLOW_proof : SLOW_spec.
Proof. exact slow_loop. Qed.

Lemma U0_sd_emit_closed : U0_sd_emit_spec.
Proof. exact (U0_sd_emit SLOW_proof). Qed.
End ACeilS1.
