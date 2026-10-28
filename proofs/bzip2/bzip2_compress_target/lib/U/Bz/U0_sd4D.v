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

Section SDD.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation INUA := (e_inUse e).
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
  Notation c128 := (Z_to_bv 64 (E + 128)). Notation cI16 := (Z_to_bv 64 (P + 1044)).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  Notation FLX L := (L cx g e Q gp tp F fc P CX SEP Gmtf Gbs Gzb Hnb CEP PHI LIM HLIM m0 nG).
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef INUA k = true /\ (0 <= zget INUA k < 256)%Z.

  Section PH1.
  Variables (ra s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word).
  Notation RI i t0 t1 t2 t3 t4 :=
    (mkR ra cP gp tp t0 t1 t2 cE s1 c128 (Z_to_bv 64 (16 * i)) (NOT (E + 128)) (Z_to_bv 64 i) cI16 (Z_to_bv 64 16) (Z_to_bv 64 1)
         (Z_to_bv 64 (E + 128 + 16 * i)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).

  Lemma U0_in16_inner : forall (n : nat) (i j acc : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t4 : word),
    (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z -> (acc = 0 \/ acc = 1)%Z ->
    Z.of_nat (length bs) = 16%Z -> nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 acc) ->
    MD H bs b m ->
    (forall m' bs' (t4' : word),
        MD H bs' b m' -> Z.of_nat (length bs') = 16%Z ->
        nth_error bs' (Z.to_nat i) = Some (Z_to_bv 8 (sm_in16_row n INUA i j acc)) ->
        (forall k, k <> Z.to_nat i -> nth_error bs' k = nth_error bs k) ->
        evt s0segs Q (MS (RI i (Z_to_bv 64 (P + 1044 + i)) (Z_to_bv 64 0) (Z_to_bv 64 (16 * i + 16)) (Z_to_bv 64 (E + 128 + 16 * i + 16)) t4')
                          F (Z_to_bv 64 0x1b6c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI i (Z_to_bv 64 (P + 1044 + i)) (Z_to_bv 64 (16 - j)) (Z_to_bv 64 (16 * i + j)) (Z_to_bv 64 (E + 128 + 16 * i + j)) t4)
                      F (Z_to_bv 64 0x1b6a4) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i j acc H bs b m t4 Hj Hj0 _ Hi Hacc Lbs Nbs MEM K.
    openCX. openMD MEM.
    destruct (INUF (16 * i + j) ltac:(lia)) as [ZD ZR].
    ustep.
    openVW VW.
    pose proof (ovb_read1 s0segs m (E + 128) INUA (jseg J 128 256) 256 (16 * i + j) _ INU ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta.
    rewrite in16_row_S in K. replace (i * 16 + j)%Z with (16 * i + j)%Z in K by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - rewrite (unsigned_lit8 (zget INUA (16 * i + j))) in Kc by lia.
      replace (negb (zget INUA (16 * i + j) =? 0))%Z with false in K by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
      wstep. wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH i (j + 1)%Z acc H bs b m _); [st_eq| lia| lia| lia| lia| exact Hacc| exact Lbs| exact Nbs| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_in16_row] in K.
        enter_with (K m bs _); [st_eq| closeMD| exact Lbs| exact Nbs| intros; reflexivity].
    - rewrite (unsigned_lit8 (zget INUA (16 * i + j))) in Kc by lia.
      replace (negb (zget INUA (16 * i + j) =? 0))%Z with true in K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      pose proof (u8arr_store_ok s0segs m (P + 1044) bs i _ I16 ltac:(lia) eq_refl) as SO.
      wstep. u8_store_done I16 i. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1) mod 256)) with (Z_to_bv 8 1) in I16.
      wstep. wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH i (j + 1)%Z 1%Z H (upd bs (Z.to_nat i) (Z_to_bv 8 1)) b mm _);
          [st_eq| lia| lia| lia| lia| right; reflexivity| rewrite upd_length; exact Lbs| |closeMD|] end.
        { rewrite nth_error_upd_same by lia. reflexivity. }
        intros m' bs' t4' MEM' L' N' O'. eapply K; [exact MEM'| exact L'| exact N'|].
        intros k Hk. rewrite O' by exact Hk. apply nth_error_upd_other. lia.
      + assert (n = 0%nat) by lia. subst n. cbn [sm_in16_row] in K.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm (upd bs (Z.to_nat i) (Z_to_bv 8 1)) _); [st_eq| closeMD| rewrite upd_length; exact Lbs| |] end.
        { rewrite nth_error_upd_same by lia. reflexivity. }
        intros k Hk. apply nth_error_upd_other. lia.
  Qed.

  Lemma U0_in16_outer : forall (n : nat) (i : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 t1 t2 t3 t4 : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < i)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    MD H bs b m ->
    (forall m' bs' (t0' t1' t2' t3' t4' : word),
        MD H bs' b m' -> Z.of_nat (length bs') = 16%Z ->
        (forall k, (0 <= k < 16)%Z -> nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
        evt s0segs Q (MS (RI 16 t0' t1' t2' t3' t4') F (Z_to_bv 64 0x1b6d8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI i t0 t1 t2 t3 t4) F (Z_to_bv 64 0x1b690) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i H bs b m t0 t1 t2 t3 t4 Hi Hi0 _ Lbs ROWS MEM K.
    openCX. openMD MEM.
    wstep.
    pose proof (u8arr_store_ok s0segs m (P + 1044) bs i _ I16 ltac:(lia) eq_refl) as SO.
    wstep. u8_store_done I16 i. change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (Z_to_bv 8 0) in I16.
    wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (U0_in16_inner 16 i 0 0 H (upd bs (Z.to_nat i) (Z_to_bv 8 0)) b mm _);
      [st_eq| lia| lia| lia| lia| left; reflexivity| rewrite upd_length; exact Lbs| | closeMD|] end.
    { rewrite nth_error_upd_same by lia. reflexivity. }
    intros m' bs' t4' MEM' L' N' O'. fold (ROW16 INUA i) in N'.
    assert (ROWS' : forall k, (0 <= k < i + 1)%Z -> nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))).
    { intros k Hk. destruct (Z.eq_dec k i) as [->|NE]; [exact N'|].
      rewrite O' by lia. rewrite nth_error_upd_other by lia. apply ROWS. lia. }
    clear EH1 EH2 AR2 HI I16 MI MU WM. openMD MEM'.
    wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z H bs' b m' _ _ _ _ _); [st_eq| lia| lia| lia| exact L'| exact ROWS'| closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n.
      enter_with (K m' bs' _ _ _ _ _); [st_eq| closeMD| exact L'|]. intros k Hk. apply ROWS'. lia.
  Qed.

  Lemma U0_in16_pre : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 : word),
    MD H bs b m ->
    evt s0segs Q (MS (RI 0 t0 t1 t2 t3 t4) F (Z_to_bv 64 0x1b690) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1b670) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 MEM K.
    openCX. openMD MEM.
    urun_to 0x1b690%Z.
    enter_with K; st_eq.
  Qed.

  End PH1.

  Section PH2.
  Variables (ra s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
  Notation RP a1 a3 i t4 t5 t6 s1 s2 :=
    (mkR ra cP gp tp (Z_to_bv 64 32) (Z_to_bv 64 31) (Z_to_bv 64 16) cE s1 c128 a1 (NOT (E + 128)) a3 (Z_to_bv 64 i) cI16 (Z_to_bv 64 8) (Z_to_bv 64 7)
         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) t4 t5 t6).
  Notation BWmid b1 n v := (BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - n) mod 4294967296)) (bw_live b1) (bw_numZ b1) (bw_zb b1)).
  Notation PIN16_IH n :=
    (forall (i : Z) (in16 : zarr) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a3 t4 t5 t6 s1 s2 : word),
      (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
      Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
      (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
      let bf := sm_put_in16 n b in16 i in
      bw_ok b -> (bw_numZ bf <= LIM)%Z ->
      MD H bs b m ->
      (forall m' (t4' t5' t6' s1' s2' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ bf)) a3 16 t4' t5' t6' s1' s2') F (Z_to_bv 64 0x1b884) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ b)) a3 i t4 t5 t6 s1 s2) F (Z_to_bv 64 0x1b700) fc None m (seg_rom s0segs))).

  Lemma U0_pin16_join : forall (i : Z) (n : nat) (in16 : zarr) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (a3 t5 t6 s1 s2 : word) (v : Z),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    (0 <= v <= 1)%Z ->
    let bf := sm_put_in16 n (bsW b 1 v) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    MD H bs (BWmid b1 1 v) m ->
    PIN16_IH n ->
    (forall m' (t4' t5' t6' s1' s2' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ bf)) a3 16 t4' t5' t6' s1' s2') F (Z_to_bv 64 0x1b884) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ b1)) a3 i (Z_to_bv 64 (bw_live b1)) t5 t6 s1 s2) F (Z_to_bv 64 0x1b874) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i n in16 H bs b b1 m a3 t5 t6 s1 s2 v Hi Hi0 Lbs ROWS IN16 Hv. cbv zeta. intros OK Eb1 NL MEM IHn K.
    pose proof (put_in16_NZM n (bsW b 1 v) in16 (i + 1)) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. cbn [bw_buff bw_live bw_numZ bw_zb] in EH1, EH2.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 v = BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NZe : bw_numZ (bsW b 1 v) = bw_numZ b1) by (rewrite EBW; reflexivity).
    urun_to 0x1b880%Z.
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z in16 H bs (bsW b 1 v) mm a3 _ t5 t6 s1 s2);
        [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_in16] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  Lemma U0_pin16_tail1 : forall (i : Z) (n : nat) (in16 : zarr) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (a3 t5 t6 s1 s2 : word),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_in16 n (bsW b 1 1) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PIN16_IH n ->
    (forall m' (t4' t5' t6' s1' s2' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ bf)) a3 16 t4' t5' t6' s1' s2') F (Z_to_bv 64 0x1b884) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ b1)) a3 i (Z_to_bv 64 (bw_live b1)) t5 t6 s1 s2) F (Z_to_bv 64 0x1b790) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i n in16 H bs b b1 m a3 t5 t6 s1 s2 Hi Hi0 Lbs ROWS IN16. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n).
    urun_to 0x1b874%Z.
    lazymatch type of EH2 with context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U0_pin16_join i n in16 H bs b b1 mm a3 _ _ s1 s2 1%Z);
        [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| exact Eb1| exact NL| closeMD| exact IHn| exact K] end.
  Qed.

  Lemma U0_pin16_tail0 : forall (i : Z) (n : nat) (in16 : zarr) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (a3 t5 t6 s1 s2 : word),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_in16 n (bsW b 1 0) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PIN16_IH n ->
    (forall m' (t4' t5' t6' s1' s2' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ bf)) a3 16 t4' t5' t6' s1' s2') F (Z_to_bv 64 0x1b884) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ b1)) a3 i (Z_to_bv 64 (bw_live b1)) t5 t6 s1 s2) F (Z_to_bv 64 0x1b84c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i n in16 H bs b b1 m a3 t5 t6 s1 s2 Hi Hi0 Lbs ROWS IN16. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX.
    urun_to 0x1b874%Z.
    enter_with (U0_pin16_join i n in16 H bs b b1 m a3 _ _ s1 s2 0%Z);
      [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| exact Eb1| exact NL| | exact IHn| exact K].
    rewrite lor_shl0. openMD MEM. closeMD.
  Qed.

  Lemma U0_pin16_loop : forall (n : nat), PIN16_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros i in16 H bs b m a3 t4 t5 t6 s1 s2 Hi Hi0 _ Lbs ROWS IN16. cbv zeta. intros OK NL MEM K.
    rewrite put_in16_S in NL, K. rewrite (IN16 i) in NL, K by lia.
    set (v := (if negb (ROW16 INUA i =? 0) then 1 else 0)%Z) in NL, K.
    pose proof (put_in16_NZM n (bsW b 1 v) in16 (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 v) as NZ0. unfold NZM in NZ0.
    assert (R01 : (0 <= ROW16 INUA i <= 1)%Z) by (destruct (ROW16_01 INUA i); lia).
    assert (Hv : (0 <= v <= 1)%Z) by (subst v; destruct (negb _); lia).
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NF : b = bs_needw BS_FUEL b \/ (8 <= bw_live b)%Z).
    { destruct (Z.leb_spec 8 (bw_live b)); [right; assumption|left]. unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    wstep.
    pose proof (u8arr_read s0segs m (P + 1044) bs i _ _ I16 (ROWS i ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (ROW16 INUA i)) by lia.
    wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - assert (Ev : v = 0%Z) by (subst v; replace (ROW16 INUA i =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (U0_pin16_tail0 i n in16 H bs b b m a3 _ _ _ _);
          [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + wstep.
        enter_with (FLX ufl_1b7d4 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
        intros b1 m' s1' s2' t5' t6' Eb1 MEM' X4' L1.
        enter_with (U0_pin16_tail0 i n in16 H bs b b1 m' a3 _ _ _ _);
          [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
    - assert (Ev : v = 1%Z) by (subst v; replace (ROW16 INUA i =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (U0_pin16_tail1 i n in16 H bs b b m a3 _ _ _ _);
          [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + wstep.
        enter_with (FLX ufl_1b718 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
        intros b1 m' s1' s2' t5' t6' Eb1 MEM' X4' L1.
        enter_with (U0_pin16_tail1 i n in16 H bs b b1 m' a3 _ _ _ _);
          [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
  Qed.

  Lemma U0_pin16_pre : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (a1 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s1 s2 : word),
    bw_ok b -> (bw_numZ b <= LIM)%Z ->
    MD H bs b m ->
    evt s0segs Q (MS (RP (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 (bw_numZ b)) 0 t4 t5 t6 s1 s2) F (Z_to_bv 64 0x1b700) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 c128 a1 (NOT (E + 128)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1b6d8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b m a1 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 s1 s2 OK NL MEM K.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    urun_to 0x1b700%Z.
    enter_with K; st_eq.
  Qed.

  End PH2.

  Section PH3.
  Variables (ra s6 s7 s8 s9 s10 s11 : word).
  Notation RUo a1 a3 i t5 t6 s1 s2 s3 s4 s5 :=
    (mkR ra cP gp tp (Z_to_bv 64 8) (Z_to_bv 64 7) (Z_to_bv 64 32) cE s1 c128 a1 (NOT (E + 128)) a3 (Z_to_bv 64 i) (Z_to_bv 64 (256 - 16 * i)) cI16 (Z_to_bv 64 16)
         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 31) (Z_to_bv 64 1) t5 t6).
  Notation RU a1 a3 i j s1 s2 s3 s4 s5 := (RUo a1 a3 i (Z_to_bv 64 j) (Z_to_bv 64 (16 * i)) s1 s2 s3 s4 s5).
  Notation BWmid b1 n v := (BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - n) mod 4294967296)) (bw_live b1) (bw_numZ b1) (bw_zb b1)).
  Notation PINUSE_IH n :=
    (forall (i j : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a3 s1 s2 s3 s4 s5 : word),
      (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z ->
      let bf := sm_put_inuse_row n b INUA i j in
      bw_ok b -> (bw_numZ bf <= LIM)%Z ->
      MD H bs b m ->
      (forall m' (s1' s2' s3' s4' s5' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ bf)) a3 i 16 s1' s2' s3' s4' s5') F (Z_to_bv 64 0x1ba54) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ b)) a3 i j s1 s2 s3 s4 s5) F (Z_to_bv 64 0x1b8bc) fc None m (seg_rom s0segs))).

  Lemma U0_pinuse_join : forall (i j : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (a3 s2 s3 s4 s5 : word) (v : Z),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z -> (0 <= v <= 1)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 v) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    MD H bs (BWmid b1 1 v) m ->
    PINUSE_IH n ->
    (forall m' (s1' s2' s3' s4' s5' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ bf)) a3 i 16 s1' s2' s3' s4' s5') F (Z_to_bv 64 0x1ba54) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ b1)) a3 i j (Z_to_bv 64 (bw_live b1)) s2 s3 s4 s5) F (Z_to_bv 64 0x1ba44) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i j n H bs b b1 m a3 s2 s3 s4 s5 v Hj Hj0 Hi Hv. cbv zeta. intros OK Eb1 NL MEM IHn K.
    pose proof (put_inuse_row_NZM n (bsW b 1 v) INUA i (j + 1)) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. cbn [bw_buff bw_live bw_numZ bw_zb] in EH1, EH2.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 v = BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NZe : bw_numZ (bsW b 1 v) = bw_numZ b1) by (rewrite EBW; reflexivity).
    urun_to 0x1ba50%Z.
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn i (j + 1)%Z H bs (bsW b 1 v) mm a3 _ s2 s3 s4 s5);
        [st_eq| lia| lia| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse_row] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  Lemma U0_pinuse_tail1 : forall (i j : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (a3 s2 s3 s4 s5 : word),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 1) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PINUSE_IH n ->
    (forall m' (s1' s2' s3' s4' s5' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ bf)) a3 i 16 s1' s2' s3' s4' s5') F (Z_to_bv 64 0x1ba54) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ b1)) a3 i j (Z_to_bv 64 (bw_live b1)) s2 s3 s4 s5) F (Z_to_bv 64 0x1b960) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i j n H bs b b1 m a3 s2 s3 s4 s5 Hj Hj0 Hi. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n).
    urun_to 0x1ba44%Z.
    lazymatch type of EH2 with context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U0_pinuse_join i j n H bs b b1 mm a3 _ _ s4 s5 1%Z);
        [st_eq| lia| lia| lia| lia| exact OK| exact Eb1| exact NL| closeMD| exact IHn| exact K] end.
  Qed.

  Lemma U0_pinuse_tail0 : forall (i j : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (a3 s2 s3 s4 s5 : word),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 0) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PINUSE_IH n ->
    (forall m' (s1' s2' s3' s4' s5' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ bf)) a3 i 16 s1' s2' s3' s4' s5') F (Z_to_bv 64 0x1ba54) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RU (Z_to_bv 64 (bw_numZ b1)) a3 i j (Z_to_bv 64 (bw_live b1)) s2 s3 s4 s5) F (Z_to_bv 64 0x1ba1c) fc None m (seg_rom s0segs)).
  Proof using All.
    intros i j n H bs b b1 m a3 s2 s3 s4 s5 Hj Hj0 Hi. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX.
    urun_to 0x1ba44%Z.
    enter_with (U0_pinuse_join i j n H bs b b1 m a3 _ _ s4 s5 0%Z);
      [st_eq| lia| lia| lia| lia| exact OK| exact Eb1| exact NL| | exact IHn| exact K].
    rewrite lor_shl0. openMD MEM. closeMD.
  Qed.

  Lemma U0_pinuse_inner : forall (n : nat), PINUSE_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros i j H bs b m a3 s1 s2 s3 s4 s5 Hj Hj0 _ Hi. cbv zeta. intros OK NL MEM K.
    rewrite put_inuse_row_S in NL, K.
    destruct (INUF (i * 16 + j) ltac:(lia)) as [ZD ZR].
    set (v := (if negb (zget INUA (i * 16 + j) =? 0) then 1 else 0)%Z) in NL, K.
    pose proof (put_inuse_row_NZM n (bsW b 1 v) INUA i (j + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 v) as NZ0. unfold NZM in NZ0.
    assert (Hv : (0 <= v <= 1)%Z) by (subst v; destruct (negb _); lia).
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (NF : b = bs_needw BS_FUEL b \/ (8 <= bw_live b)%Z).
    { destruct (Z.leb_spec 8 (bw_live b)); [right; assumption|left]. unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    urun_to 0x1b8d4%Z.
    openVW VW.
    pose proof (ovb_read1 s0segs m (E + 128) INUA (jseg J 128 256) 256 (i * 16 + j) _ INU ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget INUA (i * 16 + j))) by lia.
    wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - assert (Ev : v = 0%Z) by (subst v; replace (zget INUA (i * 16 + j) =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (U0_pinuse_tail0 i j n H bs b b m a3 _ _ _ _); [st_eq| lia| lia| lia| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + wstep.
        enter_with (FLX ufl_1b9a4 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
        intros b1 m' s2' s3' s4' s5' Eb1 MEM' X4' L1.
        enter_with (U0_pinuse_tail0 i j n H bs b b1 m' a3 _ _ _ _); [st_eq| lia| lia| lia| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
    - assert (Ev : v = 1%Z) by (subst v; replace (zget INUA (i * 16 + j) =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (U0_pinuse_tail1 i j n H bs b b m a3 _ _ _ _); [st_eq| lia| lia| lia| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + wstep.
        enter_with (FLX ufl_1b8e8 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
        intros b1 m' s2' s3' s4' s5' Eb1 MEM' X4' L1.
        enter_with (U0_pinuse_tail1 i j n H bs b b1 m' a3 _ _ _ _); [st_eq| lia| lia| lia| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
  Qed.

  Lemma U0_pinuse_outer : forall (n : nat) (i : Z) (in16 : zarr) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (a3 t5 t6 s1 s2 s3 s4 s5 : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_inuse n b in16 INUA i in
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b m ->
    (forall m' (t5' t6' s1' s2' s3' s4' s5' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RUo (Z_to_bv 64 (bw_numZ bf)) a3 16 t5' t6' s1' s2' s3' s4' s5') F (Z_to_bv 64 0x1ba60) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RUo (Z_to_bv 64 (bw_numZ b)) a3 i t5 t6 s1 s2 s3 s4 s5) F (Z_to_bv 64 0x1b8a8) fc None m (seg_rom s0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i in16 H bs b m a3 t5 t6 s1 s2 s3 s4 s5 Hi Hi0 _ Lbs ROWS IN16. cbv zeta. intros OK NL MEM K.
    rewrite put_inuse_S in NL, K. rewrite (IN16 i) in NL, K by lia.
    assert (R01 : (0 <= ROW16 INUA i <= 1)%Z) by (destruct (ROW16_01 INUA i); lia).
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    wstep.
    pose proof (u8arr_read s0segs m (P + 1044) bs i _ _ I16 (ROWS i ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (ROW16 INUA i)) by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - replace (negb (ROW16 INUA i =? 0))%Z with false in NL, K by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
      pose proof (put_inuse_NZM n b in16 INUA (i + 1)) as NZ1. unfold NZM in NZ1.
      wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH (i + 1)%Z in16 H bs b m a3 _ _ s1 s2 s3 s4 s5); [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact NL| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse] in K.
        enter_with (K m _ _ _ _ _ _ _); [st_eq| closeMD| exact OK].
    - replace (negb (ROW16 INUA i =? 0))%Z with true in NL, K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      set (b16 := sm_put_inuse_row 16 b INUA i 0) in NL, K.
      pose proof (put_inuse_NZM n b16 in16 INUA (i + 1)) as NZ1. unfold NZM in NZ1.
      wstep. wstep.
      enter_with (U0_pinuse_inner 16 i 0 H bs b m a3 s1 s2 s3 s4 s5); [st_eq| lia| lia| lia| lia| exact OK| fold b16; lia| closeMD|].
      fold b16. clear EH1 EH2 AR2 HI I16 MI MU WM.
      intros m' s1' s2' s3' s4' s5' MEM' OK'.
      openMD MEM'. cps_pose OK' as (OKb' & OKl' & OKn').
      wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH (i + 1)%Z in16 H bs b16 m' a3 _ _ _ _ _ _ _); [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK'| exact NL| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse] in K.
        enter_with (K m' _ _ _ _ _ _ _); [st_eq| closeMD| exact OK'].
  Qed.

  Lemma U0_pinuse_pre : forall (m : word -> option byte) (a1 a3 t4 t5 t6 s1 s2 s3 s4 s5 : word),
    evt s0segs Q (MS (RUo a1 a3 0 t5 t6 s1 s2 s3 s4 s5) F (Z_to_bv 64 0x1b8a8) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (mkR ra cP gp tp (Z_to_bv 64 32) (Z_to_bv 64 31) (Z_to_bv 64 16) cE s1 c128 a1 (NOT (E + 128)) a3 (Z_to_bv 64 16) cI16 (Z_to_bv 64 8) (Z_to_bv 64 7)
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) t4 t5 t6) F (Z_to_bv 64 0x1b884) fc None m (seg_rom s0segs)).
  Proof using All.
    intros m a1 a3 t4 t5 t6 s1 s2 s3 s4 s5 K.
    urun_to 0x1b8a8%Z.
    enter_with K; st_eq.
  Qed.

  End PH3.
End SDD.
End ACeilS1.
