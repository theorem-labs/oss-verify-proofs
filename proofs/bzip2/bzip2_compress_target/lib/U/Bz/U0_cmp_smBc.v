(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpSmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutSmB BzCFactsSmB BzCFactsSmB2 CmpSmKit2.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section U0SMBC.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac lit_store4 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v))
    | _ => idtac
    end.

  Notation RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.
  Notation ROWF t := (E + 45448 + 1032 * t)%Z.
  Lemma zfill0_S : forall n a i, zfill0 (S n) a i = zfill0 n (zset a i 0) (i + 1)%Z. Proof. reflexivity. Qed.

  Notation Wfv := [(SP + 1060, SP + 1084)]%Z.
  Lemma U0_sm_ihead : forall (f : zarr) (jf : list byte) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    length jf = 24%nat -> u8arr s0segs m (SP + 1060) jf ->
    mem_inv s0segs m -> munch Wfv mf m -> wmono s0segs mf m ->
    frdW s0segs Wfv mf (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    (forall m',
      u32arr s0segs m' (SP + 1060) (zw32 (zero6 f) 6) ->
      mem_inv s0segs m' -> munch Wfv mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 0) (Z_to_bv 64 (E + 45448)) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17474) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1745c) fc None m (seg_rom s0segs)).
  Proof.
    intros f jf m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6 LJf FAV MI MU WM V952 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    cps_destruct (fave_cells_of_junk6 s0segs m (SP + 1060) jf FAV LJf) as (f1 & f2 & f3 & f4 & f5 & f6 & FC). clear FAV.
    wstep.
    do 5 ((wstep; lit_store4; try mem_after_store); wstep; wstep; if_cases Kl; zify_cond_z Kl; [clear Kl| exfalso; lia]).
    (wstep; lit_store4; try mem_after_store). wstep. wstep; if_cases Kl; zify_cond_z Kl; [exfalso; lia| clear Kl].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (fave_zero_cells6 s0segs mm (SP + 1060) f FC) as FAVE end. clear FC.
    poseV V952 RO. wstep. wstep. clear RO.
    enter_with (K _); [st_eq| exact FAVE| assumption| assumption| assumption].
  Qed.

  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  Lemma U0_sm_rfzi : forall (n : nat) (t v : Z) (rf : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < nG)%Z ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    mem_inv s0segs m -> munch Wrf mf m -> wmono s0segs mf m ->
    (forall m' (a2 a3 a4 : word),
      u32arr s0segs m' (E + 45448) (ovw (zfill0 n rf (258 * t + v)) (jseg J 45448 6192) 1548) ->
      mem_inv s0segs m' -> munch Wrf mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (ROWF t)) a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x174d0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (ROWF t)) (Z_to_bv 64 (4 * v)) (NOT (ROWF t)) a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x174ac) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t v rf m mf ra t0 t1 t2 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 Hv Hv0 Hn Ht RFQ MI MU WM K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rf (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    rewrite zfill0_S in K. replace (258 * t + v + 1)%Z with (258 * t + (v + 1))%Z in K by lia.
    urun_to 0x174c8%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (E + 45448) _ (258 * t + v) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    wstep. lit_store4. store_addr (E + 45448 + 4 * (258 * t + v))%Z. ovw_store RFQ (258 * t + v)%Z 0%Z (rewrite unsigned_lit by lia; reflexivity).
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH t (v + 1)%Z _ _ mf); [st_eq| lia| lia| lia| lia| exact RFQ| assumption| assumption| assumption| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [zfill0] in K.
      enter_with (K _ _ _ _); [st_eq| exact RFQ| assumption| assumption| assumption].
  Qed.

  Lemma U0_sm_rfzo : forall (n : nat) (t : Z) (rf : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    mem_inv s0segs m -> munch Wrf mf m -> wmono s0segs mf m ->
    frdW s0segs Wrf mf (SP + 928) [C8 (Z_to_bv 64 nG)] -> frdW s0segs Wrf mf (SP + 944) [C8 (NOT (E + 45448))] ->
    frdW s0segs Wrf mf (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] -> frdW s0segs Wrf mf (SP + 968) [C8 (Z_to_bv 64 A)] ->
    (forall m' (a0 a1 a2 a3 a4 : word),
      u32arr s0segs m' (E + 45448) (ovw (sm_rfreq_zero n rf A t) (jseg J 45448 6192) 1548) ->
      mem_inv s0segs m' -> munch Wrf mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x174e0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 (ROWF t)) a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17474) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t rf m mf ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 Ht Ht0 Hn RFQ MI MU WM V928 V944 V952 V968 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    rewrite sm_rfreq_zero_S in K.
    poseV V968 RO. wstep. clear RO. wstep; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    poseV V944 RO. poseV V952 RO2. urun_to 0x174ac%Z. clear RO RO2.
    enter_with (U0_sm_rfzi (Z.to_nat A) t 0 rf m m);
      [st_eq| lia| lia| lia| lia| exact RFQ| exact MI| apply munch_refl| apply wmono_refl|].
    clear RFQ MI. intros m1 ya2 ya3 ya4 RFQ MI MU1 WM1.
    transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    replace (258 * t + 0)%Z with (258 * t)%Z in RFQ by lia.
    poseV V928 RO. wstep. wstep. wstep. clear RO. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z _ m1 mf);
        [st_eq| lia| lia| lia| exact RFQ| exact MI| assumption| assumption| exact V928| exact V944| exact V952| exact V968| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_zero] in K.
      enter_with (K m1 _ _ _ _ _); [st_eq| exact RFQ| exact MI| assumption| assumption].
  Qed.

  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  Ltac lread LEN i D :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovb_read1 s0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 i _ LEN ltac:(lia) D ltac:(unfold wa; f_equal; lia)) as RD end;
    lstep; clear RD; cbv beta; rewrite ?unsigned_lit8 by lia.
  Ltac lwrite LPK len v ih il j :=
    let SO := fresh "SO" in
    pose proof (lenpack_word_range (zget len il) (zget len ih) ltac:(lia) ltac:(lia));
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (E + 51640) _ (4 * v + j) _ LPK ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
      lstep; store_addr (E + 51640 + 4 * (4 * v + j))%Z;
      ovw_store LPK (4 * v + j)%Z (Z.lor (zget len ih * 65536) (zget len il)) (rewrite unsigned_lit by lia; reflexivity) end.
  Notation Wlp := [(E + 51640, E + 55768)]%Z.
  Lemma U0_sm_lpk : forall (n : nat) (v : Z) (lp len : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    mem_inv s0segs m -> munch Wlp mf m -> wmono s0segs mf m ->
    frdW s0segs Wlp mf (SP + 528) [C8 (NOT (E + 38740))] -> frdW s0segs Wlp mf (SP + 536) [C8 (NOT (E + 38998))] ->
    frdW s0segs Wlp mf (SP + 544) [C8 (NOT (E + 38224))] -> frdW s0segs Wlp mf (SP + 552) [C8 (NOT (E + 38482))] ->
    frdW s0segs Wlp mf (SP + 560) [C8 (Z_to_bv 64 (E + 38998))] -> frdW s0segs Wlp mf (SP + 568) [C8 (NOT (E + 51640))] ->
    frdW s0segs Wlp mf (SP + 576) [C8 (NOT (E + 37966))] -> frdW s0segs Wlp mf (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW s0segs Wlp mf (SP + 968) [C8 (Z_to_bv 64 A)] -> frdW s0segs Wlp mf (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    (forall m' (a0 a1 a2 a3 a4 a5 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (sm_lenpack n lp len v) (jseg J 51640 4128) 1032) ->
      mem_inv s0segs m' -> munch Wlp mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x175e4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 (16 * v)) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17500) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v lp len m mf ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 Hv Hv0 Hn LF LEN LPK MI MU WM
      V528 V536 V544 V552 V560 V568 V576 V960 V968 V1000 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length_nat lp (jseg J 51640 4128) 1032) as LLP.
    rewrite sm_lenpack_S in K. rewrite !lenpack_word_eq in K by (lazymatch goal with |- (0 <= zget _ (258 * ?t + _))%Z => exact (proj1 (proj2 (LF t v ltac:(lia) ltac:(lia)))) end).
    replace (258 * 1 + v)%Z with (258 + v)%Z in K by lia. replace (258 * 0 + v)%Z with v in K by lia.
    replace (258 * 3 + v)%Z with (774 + v)%Z in K by lia. replace (258 * 2 + v)%Z with (516 + v)%Z in K by lia.
    replace (258 * 5 + v)%Z with (1290 + v)%Z in K by lia. replace (258 * 4 + v)%Z with (1032 + v)%Z in K by lia.
    destruct (LF 1 v ltac:(lia) ltac:(lia)) as [D1 R1]; replace (258 * 1 + v)%Z with (258 + v)%Z in D1, R1 by lia.
    destruct (LF 0 v ltac:(lia) ltac:(lia)) as [D0 R0]; replace (258 * 0 + v)%Z with v in D0, R0 by lia.
    destruct (LF 3 v ltac:(lia) ltac:(lia)) as [D3 R3]; replace (258 * 3 + v)%Z with (774 + v)%Z in D3, R3 by lia.
    destruct (LF 2 v ltac:(lia) ltac:(lia)) as [D2 R2]; replace (258 * 2 + v)%Z with (516 + v)%Z in D2, R2 by lia.
    destruct (LF 5 v ltac:(lia) ltac:(lia)) as [D5 R5]; replace (258 * 5 + v)%Z with (1290 + v)%Z in D5, R5 by lia.
    destruct (LF 4 v ltac:(lia) ltac:(lia)) as [D4 R4]; replace (258 * 4 + v)%Z with (1032 + v)%Z in D4, R4 by lia.
    poseV V576 RO1. poseV V568 RO2. poseV V560 RO3. poseV V1000 RO4.
    urun. lread LEN (258 + v)%Z D1. urun. lread LEN v D0. urun. clear RO1 RO2 RO3 RO4.
    lwrite LPK len v (258 + v)%Z v 0%Z. replace (4 * v + 0)%Z with (4 * v)%Z in LPK by lia.
    poseV V960 RO1. poseV V552 RO2. poseV V544 RO3.
    urun. lread LEN (774 + v)%Z D3. urun. lread LEN (516 + v)%Z D2. urun. clear RO1 RO2 RO3.
    lwrite LPK len v (774 + v)%Z (516 + v)%Z 1%Z.
    poseV V960 RO1. poseV V536 RO2. poseV V528 RO3.
    urun. lread LEN (1290 + v)%Z D5. urun. lread LEN (1032 + v)%Z D4. urun. clear RO1 RO2 RO3.
    lwrite LPK len v (1290 + v)%Z (1032 + v)%Z 2%Z.
    poseV V968 RO. wstep. wstep. clear RO. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (v + 1)%Z _ len _ mf);
        [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| assumption| assumption| assumption|
         exact V528| exact V536| exact V544| exact V552| exact V560| exact V568| exact V576| exact V960| exact V968| exact V1000| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_lenpack] in K.
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| assumption| assumption| assumption].
  Qed.

  Ltac fsub V := lazymatch goal with MU' : munch _ ?mf0 ?mm |- frdW _ _ ?mm _ _ => eapply (frdW_sub s0segs Wlp Wlp mf0 mm); [exact V| exact MU'| u_sub_fp] end.
  Lemma U0_sm_pre1 : forall (lp len : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    mem_inv s0segs m -> munch Wlp mf m -> wmono s0segs mf m ->
    frdW s0segs Wlp mf (SP + 24) [C8 (Z_to_bv 64 (flag6 nG))] ->
    frdW s0segs Wlp mf (SP + 528) [C8 (NOT (E + 38740))] -> frdW s0segs Wlp mf (SP + 536) [C8 (NOT (E + 38998))] ->
    frdW s0segs Wlp mf (SP + 544) [C8 (NOT (E + 38224))] -> frdW s0segs Wlp mf (SP + 552) [C8 (NOT (E + 38482))] ->
    frdW s0segs Wlp mf (SP + 560) [C8 (Z_to_bv 64 (E + 38998))] -> frdW s0segs Wlp mf (SP + 568) [C8 (NOT (E + 51640))] ->
    frdW s0segs Wlp mf (SP + 576) [C8 (NOT (E + 37966))] -> frdW s0segs Wlp mf (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW s0segs Wlp mf (SP + 968) [C8 (Z_to_bv 64 A)] -> frdW s0segs Wlp mf (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    (forall m' (a0 a1 a2 a3 a4 a5 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) lp len 0 else lp) (jseg J 51640 4128) 1032) ->
      mem_inv s0segs m' -> munch Wlp mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x175e4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x174e0) fc None m (seg_rom s0segs)).
  Proof.
    intros lp len m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 LF LEN LPK MI MU WM V24
      V528 V536 V544 V552 V560 V568 V576 V960 V968 V1000 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    poseV V24 RO. wstep. clear RO. wstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
      enter_with (K m _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| exact MI| exact MU| exact WM].
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
      poseV V960 RO. urun_to 0x17500%Z. clear RO.
      enter_with (U0_sm_lpk (Z.to_nat A) 0 lp len m m);
        [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| exact MI| apply munch_refl| apply wmono_refl|
         fsub V528| fsub V536| fsub V544| fsub V552| fsub V560| fsub V568| fsub V576| fsub V960| fsub V968| fsub V1000|].
      clear LEN LPK MI. intros m' ya0 ya1 ya2 ya3 ya4 ya5 LEN LPK MI MU' WM'.
      transport_after_call s0segs m m' MU' WM'. clear MU' WM'.
      enter_with (K m' _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| exact MI| assumption| assumption].
  Qed.

  Notation Wp2 := [(SP + 912, SP + 928); (SP + 976, SP + 984); (SP + 1024, SP + 1032)]%Z.
  Lemma U0_sm_pre2 : forall (w912 w920 w976 w1024 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells s0segs m (SP + 912) [C8 w912] -> rw_cells s0segs m (SP + 920) [C8 w920] ->
    rw_cells s0segs m (SP + 976) [C8 w976] -> rw_cells s0segs m (SP + 1024) [C8 w1024] ->
    mem_inv s0segs m -> munch Wp2 mf m -> wmono s0segs mf m ->
    (forall m' (a0 : word),
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells s0segs m' (SP + 912) [C8 (Z_to_bv 64 0)] -> rw_cells s0segs m' (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
      rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 0)] -> rw_cells s0segs m' (SP + 1024) [C8 (Z_to_bv 64 0)] ->
      mem_inv s0segs m' -> munch Wp2 mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17600) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x175e4) fc None m (seg_rom s0segs)).
  Proof.
    intros w912 w920 w976 w1024 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 EH2 C912 C920 C976 C1024 MI MU WM K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold EHEAD2 in EH2. rewrite GM in EH2.
    wstep. try rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
    wstep; lit_store. wstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    wstep; lit_store. wstep; lit_store. wstep; lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _); [st_eq| unfold EHEAD2; rewrite GM; assumption| assumption| assumption| assumption| assumption| assumption| assumption| assumption] end.
  Qed.
End U0SMBC.
End ACeilS1.
