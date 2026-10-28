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

Lemma low32_or_reg : forall (x : word) (v sh buff : Z), (bv_unsigned x mod 4294967296 = buff)%Z ->
  (bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned x) (bv_swrap 32 (Z.shiftl v sh) mod 18446744073709551616))) mod 4294967296
   = Z.lor buff (Z.shiftl v sh mod 4294967296))%Z.
Proof. intros x v sh buff X. rewrite low32_lit, low32_lor, X, low32_swrap_mod64. reflexivity. Qed.

Section SDF.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e).
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
  Variable A : Z.
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Notation LR t := (E + 37708 + 258 * t)%Z.
  Variables (ra s7 s11 : word).
  Notation RX a0 t s2 s3 s4 s5 s6 s8 s10 t3 t4 t5 t6 :=
    (mkR ra cP gp tp (Z_to_bv 64 257) (Z_to_bv 64 A) (Z_to_bv 64 2) cE (Z_to_bv 64 3) a0 (Z_to_bv 64 t) (Z_to_bv 64 6) (Z_to_bv 64 258)
         (Z_to_bv 64 8) (Z_to_bv 64 7) (Z_to_bv 64 32) (Z_to_bv 64 31) s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  Notation RW a0 t s2 s3 s4 s5 s6 s8 s10 t4 t5 := (RX a0 t s2 s3 s4 s5 s6 s8 s10 (Z_to_bv 64 (LR t)) t4 t5 (NOT (LR t))).
  Ltac rdlen t i tgt Htgt ZD ZR :=
    let LEN := ident:(LEN) in let RD := ident:(RD) in
    openVW VW;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovb_read1 s0segs mm (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    closeVW;
    wstep; clear RD; cbv beta; rewrite <- ?Htgt; rewrite (unsigned_lit8 tgt) by lia.

  Notation UP_IH f :=
    (forall (t i curr tgt : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 s2 s6 s8 s10 : word),
      (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
      (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat f)%Z ->
      let r := sm_put_up f b curr tgt in
      bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m -> (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
      (forall m' (s2' s8' s10' : word),
          MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt -> (bv_unsigned s2' mod 4294967296 = bw_buff (fst r))%Z ->
          evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 tgt) s8' s10' (Z_to_bv 64 tgt) (Z_to_bv 64 i))
                            F (Z_to_bv 64 0x1c0d4) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (LR t + i)) s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 i))
                        F (Z_to_bv 64 0x1bf50) fc None m (seg_rom s0segs))).

  Lemma U0_up_tail : forall (t i curr tgt : Z) (f : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (a0 s2 s6 s8 s10 : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
    (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat (S f))%Z ->
    let r := sm_put_up f (bsW b 2 2) (curr + 1) tgt in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b1)%Z ->
    UP_IH f ->
    (forall m' (s2' s8' s10' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt -> (bv_unsigned s2' mod 4294967296 = bw_buff (fst r))%Z ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 tgt) s8' s10' (Z_to_bv 64 tgt) (Z_to_bv 64 i))
                          F (Z_to_bv 64 0x1c0d4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (LR t + i)) s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 i))
                      F (Z_to_bv 64 0x1bfcc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t i curr tgt f H bs b b1 m a0 s2 s6 s8 s10 Ht Hi Htgt Hc Hf. cbv zeta. intros OK Eb1 NL L1 MEM X4 IHn K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    pose proof (put_up_NZM f (bsW b 2 2) (curr + 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 2 2 = BW (Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296)) (bw_live b1 + 2) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 2 2)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NZe : bw_numZ (bsW b 2 2) = bw_numZ b1) by (rewrite EBW; reflexivity).
    assert (LVe : bw_live (bsW b 2 2) = (bw_live b1 + 2)%Z) by (rewrite EBW; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    urun_to 0x1bf48%Z.
    lazymatch type of EH2 with context [Z.shiftl 2 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 2)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    lazymatch goal with |- context [Z.shiftl 2 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 2)%Z by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296))%Z.
    { rewrite (low32_or_reg _ _ _ (bw_buff b1) X4). symmetry. apply Z.mod_small. exact XR. }
    rdlen t i tgt Htgt ZD ZR.
    wstep; if_cases Kc; zify_cond_z Kc.
    - assert (ER : sm_put_up f (bsW b 2 2) (curr + 1) tgt = (bsW b 2 2, (curr + 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_up_S. replace (curr + 1 <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ER in K. cbn [fst snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2| lia| rewrite EBW; cbn [bw_buff]; apply low32_or_reg; exact X4] end.
    - destruct f as [|f']; [exfalso; lia|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn t i (curr + 1)%Z tgt H bs (bsW b 2 2) mm a0 _ _ _ _);
        [st_eq| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| rewrite EBW; cbn [bw_buff]; apply low32_or_reg; exact X4| exact K] end.
  Qed.

  Lemma U0_up_loop : forall (f : nat), UP_IH f.
  Proof using All.
    induction f as [|f IH]; [intros; lia|].
    intros t i curr tgt H bs b m a0 s2 s6 s8 s10 Ht Hi Htgt Hc Hf. cbv zeta. intros OK NL MEM X4 K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    rewrite put_up_S in NL, K. replace (curr <? tgt)%Z with true in NL, K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (put_up_NZM f (bsW b 2 2) (curr + 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 2 2) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (U0_up_tail t i curr tgt f H bs b b m a0 s2 s6 s8 s10);
        [st_eq| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| | exact NL| lia| closeMD| exact X4| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX ufl_1bf54 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b 2 2) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' s2' s6' s8' s10' Eb1 MEM' X4' L1.
      enter_with (U0_up_tail t i curr tgt f H bs b b1 m' a0 _ _ _ _);
        [st_eq| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| exact Eb1| exact NL| exact L1| exact MEM'| exact X4'| exact IH| exact K].
  Qed.

  Notation DOWN_IH f :=
    (forall (t i curr tgt : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 s2 s6 s8 s10 : word),
      (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
      (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat f)%Z ->
      let r := sm_put_down f b curr tgt in
      bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m -> (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
      (forall m' (s2' s8' s10' : word),
          MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt -> (bv_unsigned s2' mod 4294967296 = bw_buff (fst r))%Z ->
          evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 tgt) s8' s10' (Z_to_bv 64 tgt) (Z_to_bv 64 i))
                            F (Z_to_bv 64 0x1c0d8) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (LR t + i)) s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 i))
                        F (Z_to_bv 64 0x1c014) fc None m (seg_rom s0segs))).

  Lemma U0_down_tail : forall (t i curr tgt : Z) (f : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (a0 s2 s6 s8 s10 : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
    (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat (S f))%Z ->
    let r := sm_put_down f (bsW b 2 3) (curr - 1) tgt in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b1)%Z ->
    DOWN_IH f ->
    (forall m' (s2' s8' s10' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt -> (bv_unsigned s2' mod 4294967296 = bw_buff (fst r))%Z ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 tgt) s8' s10' (Z_to_bv 64 tgt) (Z_to_bv 64 i))
                          F (Z_to_bv 64 0x1c0d8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (LR t + i)) s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 i))
                      F (Z_to_bv 64 0x1c090) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t i curr tgt f H bs b b1 m a0 s2 s6 s8 s10 Ht Hi Htgt Hc Hf. cbv zeta. intros OK Eb1 NL L1 MEM X4 IHn K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    pose proof (put_down_NZM f (bsW b 2 3) (curr - 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 2 3 = BW (Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296)) (bw_live b1 + 2) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 2 3)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NZe : bw_numZ (bsW b 2 3) = bw_numZ b1) by (rewrite EBW; reflexivity).
    assert (LVe : bw_live (bsW b 2 3) = (bw_live b1 + 2)%Z) by (rewrite EBW; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    urun_to 0x1c0cc%Z.
    lazymatch type of EH2 with context [Z.shiftl 3 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 2)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    lazymatch goal with |- context [Z.shiftl 3 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 2)%Z by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296))%Z.
    { rewrite (low32_or_reg _ _ _ (bw_buff b1) X4). symmetry. apply Z.mod_small. exact XR. }
    rdlen t i tgt Htgt ZD ZR.
    ustep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - destruct f as [|f']; [exfalso; lia|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn t i (curr - 1)%Z tgt H bs (bsW b 2 3) mm a0 _ _ _ _);
        [st_eq| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| rewrite EBW; cbn [bw_buff]; apply low32_or_reg; exact X4| exact K] end.
    - assert (ER : sm_put_down f (bsW b 2 3) (curr - 1) tgt = (bsW b 2 3, (curr - 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_down_S. replace (tgt <? curr - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ER in K. cbn [fst snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2| lia| rewrite EBW; cbn [bw_buff]; apply low32_or_reg; exact X4] end.
  Qed.

  Lemma U0_down_loop : forall (f : nat), DOWN_IH f.
  Proof using All.
    induction f as [|f IH]; [intros; lia|].
    intros t i curr tgt H bs b m a0 s2 s6 s8 s10 Ht Hi Htgt Hc Hf. cbv zeta. intros OK NL MEM X4 K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    rewrite put_down_S in NL, K. replace (tgt <? curr)%Z with true in NL, K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (put_down_NZM f (bsW b 2 3) (curr - 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 2 3) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (U0_down_tail t i curr tgt f H bs b b m a0 s2 s6 s8 s10);
        [st_eq| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| | exact NL| lia| closeMD| exact X4| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX ufl_1c018 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b 2 3) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' s2' s6' s8' s10' Eb1 MEM' X4' L1.
      enter_with (U0_down_tail t i curr tgt f H bs b b1 m' a0 _ _ _ _);
        [st_eq| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| exact Eb1| exact NL| exact L1| exact MEM'| exact X4'| exact IH| exact K].
  Qed.

  Definition LROW (n : nat) (t : Z) : Prop :=
    forall (i curr : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 s2 s5 s6 s8 s10 : word),
      (0 <= t < nG)%Z -> (i + Z.of_nat n = A)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (1 <= curr <= 17)%Z ->
      let r := sm_put_lens_row n b LENA t i curr in
      bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m -> (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
      (forall m' (s2' s4' s5' s6' s8' s10' t4' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) s4' s5' s6' s8' s10' t4' (Z_to_bv 64 A)) F (Z_to_bv 64 0x1c18c) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 (bw_live b)) s5 s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x1bf34) fc None m (seg_rom s0segs)).

  Lemma U0_lens_fin : forall (t i tgt : Z) (n : nat) (H : sdw) (bs : list byte) (bo b1 : bw) (m : word -> option byte) (a0 s2 s5 s6 s8 s10 : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (1 <= tgt <= 17)%Z ->
    let r := sm_put_lens_row n (bsW bo 1 0) LENA t (i + 1) tgt in
    bw_ok bo -> b1 = bs_needw BS_FUEL bo -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b1)%Z ->
    LROW n t ->
    (forall m' (s2' s4' s5' s6' s8' s10' t4' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) s4' s5' s6' s8' s10' t4' (Z_to_bv 64 A)) F (Z_to_bv 64 0x1c18c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) s5 s6 s8 s10 (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x1c154) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t i tgt n H bs bo b1 m a0 s2 s5 s6 s8 s10 Ht Hi Hi0 Htg. cbv zeta. intros OK Eb1 NL L1 MEM X4 IHn K.
    openCX. openMD MEM.
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW bo 1 0 = BW (bw_buff b1) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1)).
    { unfold bsW. rewrite <- Eb1. f_equal. rewrite lor_shl0. reflexivity. }
    assert (OK2 : bw_ok (bsW bo 1 0)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NZe : bw_numZ (bsW bo 1 0) = bw_numZ b1) by (rewrite EBW; reflexivity).
    assert (LVe : bw_live (bsW bo 1 0) = (bw_live b1 + 1)%Z) by (rewrite EBW; reflexivity).
    urun_to 0x1c188%Z.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z tgt H bs (bsW bo 1 0) mm a0 s2 _ _ _ _);
        [st_eq| exact Ht| lia| lia| lia| exact Htg| exact OK2| exact NL| rewrite EBW; closeMD| rewrite EBW; exact X4| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_lens_row fst snd] in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  Lemma U0_lens_pre : forall (t i tgt : Z) (n : nat) (H : sdw) (bs : list byte) (bo : bw) (m : word -> option byte) (a0 s2 s5 s6 s8 s10 : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (1 <= tgt <= 17)%Z ->
    let r := sm_put_lens_row n (bsW bo 1 0) LENA t (i + 1) tgt in
    bw_ok bo -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs bo m -> (bv_unsigned s2 mod 4294967296 = bw_buff bo)%Z ->
    LROW n t ->
    (forall m' (s2' s4' s5' s6' s8' s10' t4' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) s4' s5' s6' s8' s10' t4' (Z_to_bv 64 A)) F (Z_to_bv 64 0x1c18c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ bo)) (Z_to_bv 64 (bw_live bo)) s5 s6 s8 s10 (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x1c0d8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t i tgt n H bs bo m a0 s2 s5 s6 s8 s10 Ht Hi Hi0 Htg. cbv zeta. intros OK NL MEM X4 IHn K.
    pose proof (put_lens_row_NZM n (bsW bo 1 0) LENA t (i + 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM bo 1 0) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live bo) 8 ltac:(lia)) as MB.
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (U0_lens_fin t i tgt n H bs bo bo m a0 s2 s5 s6 s8 s10);
        [st_eq| exact Ht| lia| lia| exact Htg| exact OK| | exact NL| lia| closeMD| exact X4| exact IHn| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live bo)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX ufl_1c0dc BS_FUEL H bs bo m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes bo 1 0) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' s2' s5' s6' s8' Eb1 MEM' X4' L1.
      enter_with (U0_lens_fin t i tgt n H bs bo b1 m' a0 _ _ _ _ _);
        [st_eq| exact Ht| lia| lia| exact Htg| exact OK| exact Eb1| exact NL| exact L1| exact MEM'| exact X4'| exact IHn| exact K].
  Qed.

  Lemma U0_lens_mid : forall (t i curr tgt : Z) (n : nat) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 s2 s8 s10 : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (tgt = zget LENA (258 * t + i)) ->
    (tgt <= curr <= 17)%Z ->
    let rd := sm_put_down 40 b curr tgt in
    let r := sm_put_lens_row n (bsW (fst rd) 1 0) LENA t (i + 1) (snd rd) in
    bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m -> (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
    LROW n t ->
    (forall m' (s2' s4' s5' s6' s8' s10' t4' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ (fst r))) s4' s5' s6' s8' s10' t4' (Z_to_bv 64 A)) F (Z_to_bv 64 0x1c18c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 tgt) s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 i))
                      F (Z_to_bv 64 0x1c0d4) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t i curr tgt n H bs b m a0 s2 s8 s10 Ht Hi Hi0 Htgt Hc. cbv zeta. intros OK NL MEM X4 IHn K.
    destruct (LENF t i Ht ltac:(lia)) as [ZD ZR]. rewrite <- Htgt in ZR.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    wstep; if_cases Kc; zify_cond_z Kc.
    - destruct (sm_put_down 40 b curr tgt) as [b2 c2] eqn:ED. cbn [fst snd] in NL, K.
      pose proof (put_lens_row_NZM n (bsW b2 1 0) LENA t (i + 1) c2) as NZ1. unfold NZM in NZ1.
      pose proof (bsW_NZM b2 1 0) as NZ0. unfold NZM in NZ0.
      enter_with (U0_down_loop 40%nat t i curr tgt H bs b m a0 s2 _ s8 s10);
        [st_eq| exact Ht| lia| exact Htgt| lia| cbn; lia| exact OK| rewrite ED; cbn [fst]; lia| closeMD| exact X4|].
      rewrite ED. cbn [fst snd]. intros m' s2' s8' s10' MEM' OK' -> X4'.
      enter_with (U0_lens_pre t i tgt n H bs b2 m' a0 s2' _ _ _ _);
        [st_eq| exact Ht| lia| lia| lia| exact OK'| exact NL| exact MEM'| exact X4'| exact IHn| exact K].
    - assert (ED : sm_put_down 40 b curr tgt = (b, curr)).
      { change 40%nat with (S 39). rewrite put_down_S. replace (tgt <? curr)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ED in NL, K. cbn [fst snd] in NL, K. assert (Ec : curr = tgt) by lia. subst curr.
      enter_with (U0_lens_pre t i tgt n H bs b m a0 s2 _ _ s8 s10);
        [st_eq| exact Ht| lia| lia| lia| exact OK| exact NL| closeMD| exact X4| exact IHn| exact K].
  Qed.

  Lemma U0_lens_inner : forall (n : nat) (t : Z), LROW n t.
  Proof using All.
    induction n as [|n IH]; intros t; unfold LROW; [intros; lia|].
    intros i curr H bs b m a0 s2 s5 s6 s8 s10 Ht Hi Hi0 _ Hc. cbv zeta. intros OK NL MEM X4 K.
    destruct (LENF t i Ht ltac:(lia)) as [ZD ZR].
    rewrite put_lens_row_S in NL, K. cbv zeta in NL, K.
    set (tgt := zget LENA (258 * t + i)) in *.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    urun_to 0x1bf48%Z.
    openVW VW.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta. fold tgt. rewrite (unsigned_lit8 tgt) by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - assert (EU : sm_put_up 40 b curr tgt = (b, curr)).
      { change 40%nat with (S 39). rewrite put_up_S. replace (curr <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite EU in NL, K.
      enter_with (U0_lens_mid t i curr tgt n H bs b m a0 s2 s8 s10);
        [st_eq| exact Ht| lia| lia| reflexivity| lia| exact OK| | closeMD| exact X4| exact (IH t)| ].
      + destruct (sm_put_down 40 b curr tgt) as [b2 c2]. cbn [fst snd]. exact NL.
      + destruct (sm_put_down 40 b curr tgt) as [b2 c2]. cbn [fst snd]. exact K.
    - destruct (sm_put_up 40 b curr tgt) as [b1 c1] eqn:EU.
      pose proof (put_down_NZM 40 b1 c1 tgt) as NZd. unfold NZM in NZd.
      destruct (sm_put_down 40 b1 c1 tgt) as [b2 c2] eqn:ED.
      pose proof (put_lens_row_NZM n (bsW b2 1 0) LENA t (i + 1) c2) as NZ1. unfold NZM in NZ1. cbn [fst] in NZd, NZ1.
      pose proof (bsW_NZM b2 1 0) as NZ0. unfold NZM in NZ0.
      enter_with (U0_up_loop 40%nat t i curr tgt H bs b m a0 s2 _ s8 s10);
        [st_eq| exact Ht| lia| reflexivity| lia| cbn; lia| exact OK| rewrite EU; cbn [fst]; lia| closeMD| exact X4|].
      rewrite EU. cbn [fst snd]. intros m' s2' s8' s10' MEM' OK' Ec1 X4'. subst c1.
      enter_with (U0_lens_mid t i tgt tgt n H bs b1 m' a0 s2' s8' s10');
        [st_eq| exact Ht| lia| lia| reflexivity| lia| exact OK'| | exact MEM'| exact X4'| exact (IH t)| ].
      + rewrite ED. cbn [fst snd]. exact NL.
      + rewrite ED. cbn [fst snd]. exact K.
  Qed.

  Lemma U0_lens5_tail : forall (t curr : Z) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (a0 s2 s5 s6 s8 s10 t5 t6 : word),
    (0 <= t < nG)%Z -> (curr = zget LENA (258 * t + 0)) -> h968 H = Z_to_bv 64 A ->
    let bf := bsW b 5 curr in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall m' (s2' : word),
        MD H bs bf m' -> bw_ok bf -> (bv_unsigned s2' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RW a0 t s2' (Z_to_bv 64 (bw_numZ bf)) (Z_to_bv 64 (bw_live bf)) s5 s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 0)) F (Z_to_bv 64 0x1bf34) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RX a0 t s2 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) s5 s6 s8 s10 (Z_to_bv 64 (LR t)) (Z_to_bv 64 curr) t5 t6) F (Z_to_bv 64 0x1bee4) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t curr H bs b b1 m a0 s2 s5 s6 s8 s10 t5 t6 Ht Hc HS68. cbv zeta. intros OK Eb1 NL L1 MEM K.
    destruct (LENF t 0 Ht ltac:(lia)) as [ZD ZR]. rewrite <- Hc in ZR.
    openCX. openMD MEM. rewrite HS68 in HI.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 5 curr = BW (Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296)) (bw_live b1 + 5) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 5 curr)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NZe : bw_numZ (bsW b 5 curr) = bw_numZ b1) by (rewrite EBW; reflexivity).
    assert (LVe : bw_live (bsW b 5 curr) = (bw_live b1 + 5)%Z) by (rewrite EBW; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    urun_to 0x1bf28%Z.
    lazymatch type of EH2 with context [Z.shiftl curr (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 5)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    lazymatch goal with |- context [Z.shiftl curr (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 5)%Z by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia. reflexivity. }
    wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|].
    rewrite <- HS68 in HI.
    urun_to 0x1bf34%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (K mm _); [st_eq| rewrite EBW; closeMD| exact OK2| ] end.
    rewrite EBW. cbn [bw_buff]. rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia. apply Z.mod_small. exact XR.
  Qed.

  Notation LENS_IH n :=
    (forall (t : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 s2 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word),
      (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
      h928 H = Z_to_bv 64 nG -> h960 H = Z_to_bv 64 (E + 37708) -> h968 H = Z_to_bv 64 A ->
      let bf := sm_put_lens n b LENA A t in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
      (forall m' (s2' s4' s5' s6' s8' s10' t4' t5' t6' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt s0segs Q (MS (RX a0 nG s2' (Z_to_bv 64 (bw_numZ bf)) s4' s5' s6' s8' s10' (Z_to_bv 64 nG) t4' t5' t6') F (Z_to_bv 64 0x1c198) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RX a0 t s2 (Z_to_bv 64 (bw_numZ b)) s4 s5 s6 s8 s10 t3 t4 t5 t6) F (Z_to_bv 64 0x1be40) fc None m (seg_rom s0segs))).

  Lemma U0_lens_body : forall (t curr : Z) (b1 : bw) (c1 : Z) (n : nat) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 s2 s5 s6 s8 s10 : word),
    (t + Z.of_nat (S n) = nG)%Z -> (0 <= t)%Z -> (curr = zget LENA (258 * t + 0)) ->
    h928 H = Z_to_bv 64 nG -> h960 H = Z_to_bv 64 (E + 37708) -> h968 H = Z_to_bv 64 A ->
    sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr = (b1, c1) ->
    let bf := sm_put_lens n b1 LENA A (t + 1) in
    bw_ok (bsW b 5 curr) -> (bw_numZ bf <= LIM)%Z -> MD H bs (bsW b 5 curr) m ->
    (bv_unsigned s2 mod 4294967296 = bw_buff (bsW b 5 curr))%Z ->
    LENS_IH n ->
    (forall m' (s2' s4' s5' s6' s8' s10' t4' t5' t6' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt s0segs Q (MS (RX a0 nG s2' (Z_to_bv 64 (bw_numZ bf)) s4' s5' s6' s8' s10' (Z_to_bv 64 nG) t4' t5' t6') F (Z_to_bv 64 0x1c198) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RW a0 t s2 (Z_to_bv 64 (bw_numZ (bsW b 5 curr))) (Z_to_bv 64 (bw_live (bsW b 5 curr))) s5 s6 s8 s10 (Z_to_bv 64 curr) (Z_to_bv 64 0)) F (Z_to_bv 64 0x1bf34) fc None m (seg_rom s0segs)).
  Proof using All.
    intros t curr b1 c1 n H bs b m a0 s2 s5 s6 s8 s10 Ht Ht0 Hc HS28 HS60 HS68 ER. cbv zeta. intros OK NL MEM X4 IHn K.
    destruct (LENF t 0 ltac:(lia) ltac:(lia)) as [ZD ZR]. rewrite <- Hc in ZR.
    pose proof (put_lens_NZM n b1 LENA A (t + 1)) as NZ2. unfold NZM in NZ2.
    eapply (U0_lens_inner (Z.to_nat A) t 0%Z curr H bs (bsW b 5 curr) m a0 s2 s5 s6 s8 s10);
      [lia| lia| lia| lia| lia| exact OK| rewrite ER; cbn [fst]; lia| exact MEM| exact X4|].
    rewrite ER. cbn [fst]. clear MEM. intros m' s2' s4' s5' s6' s8' s10' t4' MEM OK1.
    openCX. openMD MEM. rewrite HS28 in HI. cps_pose OK1 as (OK1b & OK1l & OK1n).
    urun_to 0x1c194%Z. rewrite <- HS28 in HI.
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IHn (t + 1)%Z H bs b1 m' a0 _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| exact HS28| exact HS60| exact HS68| exact OK1| exact NL| closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_lens] in K.
      enter_with (K m' _ _ _ _ _ _ _ _ _); [st_eq| closeMD| exact OK1].
  Qed.

  Lemma U0_lens_outer : forall (n : nat), LENS_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros t H bs b m a0 s2 s4 s5 s6 s8 s10 t3 t4 t5 t6 Ht Ht0 _ HS28 HS60 HS68. cbv zeta. intros OK NL MEM K.
    destruct (LENF t 0 ltac:(lia) ltac:(lia)) as [ZD ZR].
    rewrite put_lens_S in NL, K. cbv zeta in NL, K.
    set (curr := zget LENA (258 * t + 0)) in *.
    destruct (sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr) as [b1 c1] eqn:ER.
    pose proof (put_lens_NZM n b1 LENA A (t + 1)) as NZ2. unfold NZM in NZ2.
    pose proof (put_lens_row_NZM (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr) as NZ1. rewrite ER in NZ1. unfold NZM in NZ1. cbn [fst] in NZ1.
    pose proof (bsW_NZM b 5 curr) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    rewrite HS60 in HI. urun_to 0x1be60%Z. rewrite <- HS60 in HI.
    openVW VW.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (ovb_read1 s0segs mm (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + 0) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD end.
    closeVW.
    wstep. clear RD. cbv beta. fold curr. rewrite (unsigned_lit8 curr) by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (U0_lens5_tail t curr H bs b b mm a0 _ _ _ _ _ _ _); [st_eq| lia| reflexivity| exact HS68| exact OK| | lia| lia| closeMD|] end.
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' s2' MEM' OK' X4'.
      eapply (U0_lens_body t curr b1 c1 n H bs b m' a0 s2' _ _ _ _);
        [lia| lia| reflexivity| exact HS28| exact HS60| exact HS68| exact ER| exact OK'| exact NL| exact MEM'| exact X4'| exact IH| exact K].
    - wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (FLX ufl_1be6c BS_FUEL H bs b mm); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | | closeMD|] end.
      { pose proof (bsW_bytes b 5 curr) as [BB _]. rewrite <- BB. lia. }
      { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
      intros b0 m' s2' s5' t5' t6' Eb0 MEM' X4' L1.
      enter_with (U0_lens5_tail t curr H bs b b0 m' a0 _ _ _ _ _ _ _); [st_eq| lia| reflexivity| exact HS68| exact OK| exact Eb0| lia| exact L1| exact MEM'|].
      intros m'' s2'' MEM'' OK'' X4''.
      eapply (U0_lens_body t curr b1 c1 n H bs b m'' a0 s2'' _ _ _ _);
        [lia| lia| reflexivity| exact HS28| exact HS60| exact HS68| exact ER| exact OK''| exact NL| exact MEM''| exact X4''| exact IH| exact K].
  Qed.

  Lemma U0_lens : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 t3 t4 t5 t6 : word),
    h928 H = Z_to_bv 64 nG -> h960 H = Z_to_bv 64 (E + 37708) -> h968 H = Z_to_bv 64 A ->
    let bf := sm_put_lens (Z.to_nat nG) b LENA A 0 in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (s2' s4' s5' s6' s8' s10' t4' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RX (Z_to_bv 64 (bw_numZ b)) nG s2' (Z_to_bv 64 (bw_numZ bf)) s4' s5' s6' s8' s10' (Z_to_bv 64 nG) t4' t5' t6')
                          F (Z_to_bv 64 0x1c198) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1bdf8) fc None m (seg_rom s0segs)).
  Proof using All.
    intros H bs b m t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s10 t3 t4 t5 t6 HS28 HS60 HS68. cbv zeta. intros OK NL MEM K.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    rewrite HS68 in HI. urun_to 0x1be40%Z. rewrite <- HS68 in HI.
    replace (Z.land 18446744073709551615 A) with A by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia; rewrite Z.mod_small; lia).
    enter_with (U0_lens_outer (Z.to_nat nG) 0%Z H bs b m (Z_to_bv 64 (bw_numZ b)) _ _ _ _ _ _ _ _ _ _);
      [st_eq| lia| lia| lia| exact HS28| exact HS60| exact HS68| exact OK| exact NL| closeMD| exact K].
  Qed.

End SDF.
End ACeilS1.
