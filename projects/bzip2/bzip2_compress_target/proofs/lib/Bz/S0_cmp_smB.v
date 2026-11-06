(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 BzCFactsSmA CmpFsKit0 CmpHmKit.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 BzCFactsSmA CmpFsKit0 CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require S0_memset.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Module S0_cmp_smA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl.S0_memset.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0SMA.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv : word).
  (* [comment removed for export] *)
  Variables (xs9 xs10 xs11 : word).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx. Hypothesis SF : smA_facts e.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  (* [comment removed for export] *)
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    cps_destruct S as (?AEA1 & ?AEA2 & ?AEF & _ & _ & ?AA12 & ?A1F & _).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).

  (* [comment removed for export] *)
  Notation OFS := (258 * nG + 37450 + A)%Z.
  Notation RI ra t0 a0 a1 a2 a3 a4 s1 s2 s4 s6 s7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (E + 676)) (Z_to_bv 64 (-258)) (Z_to_bv 64 1)
         s2 (Z_to_bv 64 OFS) s4 (Z_to_bv 64 (E + 672)) s6 s7 s8 s9 (Z_to_bv 64 (-2147483647)) (Z_to_bv 64 4294967296) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smA_grow : forall (f : nat) (ge aF gs tF remF : Z) (m : word -> option byte)
      (ra t0 a4 s1 s2 s4 s7 t3 t4 t5 t6 : word) (w576 w584 w592 w600 : word),
    (1 <= f)%nat -> (A - 1 - ge <= Z.of_nat f)%Z ->
    (0 <= gs)%Z -> (gs - 1 <= ge <= A - 2)%Z -> (aF < tF)%Z -> (0 < tF <= nMTF)%Z ->
    aF = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 1 - gs)) ->
    remF = sumF (fun v => zget mf v) gs (Z.to_nat (A - gs)) -> (remF <= nMTF)%Z ->
    u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 (Z_to_bv 64 nInUse)] ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall ge' aF' (a2 a3 a4 : word),
      sm_grow f mf tF A ge aF = (ge', aF') -> (ge < ge' <= A - 1)%Z -> aF' = sumF (fun v => zget mf v) gs (Z.to_nat (ge' + 1 - gs)) -> (0 <= aF' <= remF)%Z ->
      evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 (ge' * 4294967296)) (Z_to_bv 64 tF) a2 a3 a4 s1 s2 s4 (Z_to_bv 64 gs) s7 (Z_to_bv 64 aF') (Z_to_bv 64 ge') t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15f10) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 (ge * 4294967296)) (Z_to_bv 64 tF) (Z_to_bv 64 (E + 676 + 4 * ge)) (Z_to_bv 64 ge) a4 s1 s2 s4 (Z_to_bv 64 gs) s7 (Z_to_bv 64 aF) (Z_to_bv 64 ge) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15eec) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros; lia. }
    intros ge aF gs tF remF m ra t0 a4 s1 s2 s4 s7 t3 t4 t5 t6 w576 w584 w592 w600 Hf1 Hf Hgs Hge HaF HtF EaF EremF HremF MTF SC CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear AEA1 AEA2 AEF AA12 A1F. openSF. bz_ceil; bz_params; unfold CEIL in CE. unfold sm_alpha, sm_nmtf in *.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    pose proof (MFD (ge + 1)%Z ltac:(lia)) as [Dq Rq].
    (* [comment removed for export] *)
    assert (EaF' : (aF + zget mf (ge + 1))%Z = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 2 - gs))).
    { rewrite EaF. replace (Z.to_nat (ge + 2 - gs)) with (S (Z.to_nat (ge + 1 - gs))) by lia. rewrite sumF_S_last. f_equal. f_equal. lia. }
    assert (BaF' : (0 <= aF + zget mf (ge + 1) <= remF)%Z).
    { rewrite EaF', EremF. apply sumF_prefix_le; [lia|]. intros b Hb. apply (proj1 (proj2 (MFD b ltac:(lia)))). }
    rewrite sm_grow_S in K. replace ((aF <? tF) && (ge <? nInUse + 2 - 1))%Z%bool with true in K
      by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 672) mf (jseg J 672 1032) 258 (ge + 1) _ MTF ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget mf (ge + 1))) by lia.
    (* [comment removed for export] *)
    wstep. wstep. try rewrite (sx32_of_Z (zget mf (ge + 1) + aF)) by lia. wstep. try rewrite (sx32_of_Z_signed (ge + 1)) by lia. try rewrite (sx32_of_Z (ge + 1)) by lia.
    (* [comment removed for export] *)
    wstep.
    wstep; if_cases Kx; zify_cond_z Kx.
    - (* [comment removed for export] *)
      enter_with (K (ge + 1)%Z (aF + zget mf (ge + 1))%Z _ _ _); [st_eq| | lia| | lia].
      + apply sm_grow_stop. lia.
      + rewrite EaF'. f_equal. lia.
    - (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
      + enter_with (IH (ge + 1)%Z (aF + zget mf (ge + 1))%Z gs tF remF m); [st_eq| lia| lia| lia| lia| lia| lia| | exact EremF| lia| exact MTF| exact SC| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
        * rewrite EaF'. f_equal. lia.
        * intros ge' aF' y1 y2 y3 E' Hge' EaF2 B2. eapply K; [exact E'| lia| exact EaF2| exact B2].
      + enter_with (K (ge + 1)%Z (aF + zget mf (ge + 1))%Z _ _ _); [st_eq| | lia| | lia].
        * apply sm_grow_stop. lia.
        * rewrite EaF'. f_equal. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma lxor_sign_mod : forall z, (- 9223372036854775808 <= z < 9223372036854775808)%Z ->
    Z.lxor (z mod 18446744073709551616) 9223372036854775808 = (z + 9223372036854775808)%Z.
  Proof.
    intros z Hz.
    assert (R : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 9223372036854775808 = ((x + 9223372036854775808) mod 18446744073709551616)%Z).
    { intros x Hx. change 9223372036854775808%Z with (2^63)%Z. change 18446744073709551616%Z with (2^64)%Z. apply zb_lxor_sign.
      change (2^64)%Z with 18446744073709551616%Z. lia. }
    destruct (Z.lt_ge_cases z 0).
    - replace (z mod 18446744073709551616)%Z with (z + 18446744073709551616)%Z.
      2:{ symmetry. rewrite <- (Z.mod_add z 1 18446744073709551616) by lia. apply Z.mod_small. lia. }
      rewrite R by lia. rewrite <- (Z.mod_add _ (-1)) by lia.
      replace (z + 18446744073709551616 + 9223372036854775808 + -1 * 18446744073709551616)%Z with (z + 9223372036854775808)%Z by lia.
      apply Z.mod_small. lia.
    - rewrite (Z.mod_small z) by lia. rewrite R by lia. apply Z.mod_small. lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smA_setrow : forall (n : nat) (v t gs ge : Z) (len : zarr) (me m : word -> option byte)
      (ra t0 a3 a4 s1 s2 s4 s7 s8 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < 6)%Z ->
    (0 <= gs <= 258)%Z -> (gs - 1 <= ge <= 258)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) -> mem_inv s0segs m ->
    munch [(E + 37708, E + 39256)]%Z me m -> wmono s0segs me m ->
    (forall m' (a0 a3 a4 : word),
      u8arr s0segs m' (E + 37708) (ovb (sm_setrow n len t gs ge v) (jseg J 37708 1548) 1548) -> mem_inv s0segs m' ->
      munch [(E + 37708, E + 39256)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RI ra t0 a0 (Z_to_bv 64 (E + 37708 + 258 * t + A)) (Z_to_bv 64 (E + 37708 + 258 * t + A)) a3 a4 s1 s2 s4 (Z_to_bv 64 gs) s7 s8 (Z_to_bv 64 ge) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15f8c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 v) (Z_to_bv 64 (E + 37708 + 258 * t + A)) (Z_to_bv 64 (E + 37708 + 258 * t + v)) a3 a4 s1 s2 s4 (Z_to_bv 64 gs) s7 s8 (Z_to_bv 64 ge) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15f68) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t gs ge len me m ra t0 a3 a4 s1 s2 s4 s7 s8 t3 t4 t5 t6 Hv Hv0 Hn Ht Hgs Hge LEN MI MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear AEA1 AEA2 AEF AA12 A1F. openSF. unfold sm_alpha in *.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_setrow_S in K.
    (* [comment removed for export] *)
    destruct (Z.ltb_spec v gs) as [Hl|Hl]; [| destruct (Z.ltb_spec ge v) as [Hr|Hr]];
      (wstep; rewrite ?lxor_sign_mod by lia; flags); (wstep; rewrite ?lxor_sign_mod by lia; flags); wstep; wstep; wstep.
    all: pose proof (u8arr_store_ok s0segs m (E + 37708) _ (258 * t + v) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    all: wstep; store_addr (E + 37708 + (258 * t + v))%Z; ovb_store1 LEN (258 * t + v)%Z.
    all: lazymatch type of LEN with context [wr8 ?l0 ?i0 ?w] =>
           replace (wr8 l0 i0 w) with (zset l0 i0 (setrow_val gs ge v)) in LEN
             by (unfold wr8, setrow_val, BZ_LESSER_ICOST, BZ_GREATER_ICOST; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia;
                 destruct (Z.leb_spec gs v), (Z.leb_spec v ge); cbn [andb]; first [reflexivity| exfalso; lia]) end.
    (* [comment removed for export] *)
    all: wstep; wstep; wstep; if_cases Ke; zify_cond_z Ke;
      [ enter_with (IH (v + 1)%Z t gs ge (zset len (258 * t + v) (setrow_val gs ge v)) me); [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| exact MI| exact MU| exact WM| exact K]
      | assert (n = 0)%nat by lia; subst n; cbn [sm_setrow] in K;
        enter_with (K _ _ _ _); [st_eq| exact LEN| exact MI| exact MU| exact WM] ].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma row_before_memset : forall segs m P l Jl N a k,
    u8arr segs m P (ovb l Jl N) -> (0 <= a)%Z -> (0 <= k)%Z -> (a + k <= N)%Z ->
    u8arr segs m P (firstn (Z.to_nat a) (ovb l Jl N)) /\
    rw_cells segs m (P + a)%Z [CB (Z.to_nat k) (firstn (Z.to_nat k) (skipn (Z.to_nat a) (ovb l Jl N)))] /\
    u8arr segs m (P + a + k)%Z (skipn (Z.to_nat (a + k)) (ovb l Jl N)).
  Proof.
    intros segs m P l Jl N a k H Ha Hk HN. pose proof (ovb_length_nat l Jl N) as L.
    rewrite <- (firstn_skipn (Z.to_nat a) (ovb l Jl N)) in H. apply (proj1 (u8arr_app segs m P _ _)) in H. destruct H as [H0 H].
    rewrite length_firstn, L in H. replace (P + Z.of_nat (Nat.min (Z.to_nat a) (Z.to_nat N)))%Z with (P + a)%Z in H by lia.
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat a) (ovb l Jl N))) in H. apply (proj1 (u8arr_app segs m (P + a) _ _)) in H. destruct H as [H1 H2].
    rewrite length_firstn, length_skipn, L, skipn_skipn in H2.
    replace (P + a + Z.of_nat (Nat.min (Z.to_nat k) (Z.to_nat N - Z.to_nat a)))%Z with (P + a + k)%Z in H2 by lia.
    replace (Z.to_nat k + Z.to_nat a)%nat with (Z.to_nat (a + k)) in H2 by lia.
    split; [exact H0|]. split; [|exact H2].
    apply (rw_cells_of_u8arr segs) in H1. rewrite length_firstn, length_skipn, L in H1.
    replace (Nat.min (Z.to_nat k) (Z.to_nat N - Z.to_nat a)) with (Z.to_nat k) in H1 by lia. exact H1.
  Qed.
  Lemma ovb_row_split : forall l Jl N t k, (0 <= t)%Z -> (0 <= k)%Z -> (258 * t + k <= N)%Z ->
    ovb (sm_len_init_row (Z.to_nat k) l t 0) Jl N = firstn (Z.to_nat (258 * t)) (ovb l Jl N) ++ repeat (Z_to_bv 8 15) (Z.to_nat k) ++ skipn (Z.to_nat (258 * t + k)) (ovb l Jl N).
  Proof.
    intros l Jl N t k Ht Hk HN. apply nth_error_ext. intros i.
    pose proof (ovb_length_nat l Jl N) as L. pose proof (ovb_length_nat (sm_len_init_row (Z.to_nat k) l t 0) Jl N) as L'.
    destruct (Nat.lt_ge_cases i (Z.to_nat N)) as [Hi|Hi].
    2:{ rewrite (proj2 (nth_error_None _ _)) by lia. symmetry. apply (proj2 (nth_error_None _ _)).
        rewrite !length_app, length_firstn, repeat_length, length_skipn. lia. }
    replace i with (Z.to_nat (Z.of_nat i)) by lia.
    rewrite ovb_nth_raw by lia. rewrite sm_len_init_row_def, sm_len_init_row_get.
    destruct (Nat.lt_ge_cases i (Z.to_nat (258 * t))) as [H1|H1].
    - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn' by lia. rewrite ovb_nth_raw by lia.
      replace ((258 * t + 0 <=? Z.of_nat i) && (Z.of_nat i <? 258 * t + 0 + Z.of_nat (Z.to_nat k)))%Z%bool with false
        by (symmetry; apply Bool.andb_false_iff; left; apply Z.leb_gt; lia).
      reflexivity.
    - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
      destruct (Nat.lt_ge_cases i (Z.to_nat (258 * t) + Z.to_nat k)) as [H2|H2].
      + rewrite nth_error_app1 by (rewrite repeat_length; lia). rewrite nth_error_repeat by lia.
        replace ((258 * t + 0 <=? Z.of_nat i) && (Z.of_nat i <? 258 * t + 0 + Z.of_nat (Z.to_nat k)))%Z%bool with true
          by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        reflexivity.
      + rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_error_skipn.
        replace (Z.to_nat (258 * t + k) + (Z.to_nat (Z.of_nat i) - Nat.min (Z.to_nat (258 * t)) (length (ovb l Jl N)) - Z.to_nat k))%nat with (Z.to_nat (Z.of_nat i)) by lia.
        rewrite ovb_nth_raw by lia.
        replace ((258 * t + 0 <=? Z.of_nat i) && (Z.of_nat i <? 258 * t + 0 + Z.of_nat (Z.to_nat k)))%Z%bool with false
          by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia).
        reflexivity.
  Qed.
  Lemma row_after_memset : forall segs m P l Jl N t k,
    u8arr segs m P (firstn (Z.to_nat (258 * t)) (ovb l Jl N)) ->
    rw_cells segs m (P + 258 * t)%Z [CB (Z.to_nat k) (repeat (Z_to_bv 8 15) (Z.to_nat k))] ->
    u8arr segs m (P + 258 * t + k)%Z (skipn (Z.to_nat (258 * t + k)) (ovb l Jl N)) ->
    (0 <= t)%Z -> (0 <= k)%Z -> (258 * t + k <= N)%Z ->
    u8arr segs m P (ovb (sm_len_init_row (Z.to_nat k) l t 0) Jl N).
  Proof.
    intros segs m P l Jl N t k H0 H1 H2 Ht Hk HN. pose proof (ovb_length_nat l Jl N) as L.
    rewrite (ovb_row_split l Jl N t k) by lia.
    apply (proj2 (u8arr_app segs m P _ _)). split; [exact H0|].
    rewrite length_firstn, L. replace (P + Z.of_nat (Nat.min (Z.to_nat (258 * t)) (Z.to_nat N)))%Z with (P + 258 * t)%Z by lia.
    apply (proj2 (u8arr_app segs m _ _ _)). split.
    - pose proof (u8arr_of_rw_cells segs m _ _ _ H1) as U. exact U.
    - rewrite repeat_length. replace (P + 258 * t + Z.of_nat (Z.to_nat k))%Z with (P + 258 * t + k)%Z by lia. exact H2.
  Qed.

  (* [comment removed for export] *)
  Notation RMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1 s2 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (-1)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 A1) (Z_to_bv 64 (E + 128))
         (Z_to_bv 64 A) xs9 xs10 xs11 t3 t4 t5 t6).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smA_lenrows : forall (n : nat) (t : Z) (len : zarr) (me m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (w576 w584 w592 w600 : word),
    (t + Z.of_nat n = 6)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 (Z_to_bv 64 nInUse)] -> mem_inv s0segs m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    munch [(E + 37708, E + 39256)]%Z me m -> wmono s0segs me m ->
    (forall m' (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u8arr s0segs m' (E + 37708) (ovb (sm_len_init n len A t) (jseg J 37708 1548) 1548) ->
      rw_cells s0segs m' (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 (Z_to_bv 64 nInUse)] -> mem_inv s0segs m' ->
      munch [(E + 37708, E + 39256)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RMS (Z_to_bv 64 0x15dcc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (E + 37708 + 258 * 6)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15dd8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RMS ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 (E + 37708 + 258 * t)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15db4) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t len me m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 w576 w584 w592 w600 Ht Ht0 Hn LEN SC MI CE SPB MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear AEA1 AEA2 AEF AA12 A1F. openSF. bz_ceil; bz_params; unfold CEIL in CE. unfold sm_alpha in *.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LLn.
    rewrite sm_len_init_S in K.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kn; zify_cond_z Kn; [exfalso; lia|]. wstep. wstep. wstep.
    cps_destruct (row_before_memset s0segs m (E + 37708) len (jseg J 37708 1548) 1548 (258 * t) (nInUse + 2) LEN ltac:(lia) ltac:(lia) ltac:(lia)) as (L0 & L1 & L2). clear LEN.
    (* [comment removed for export] *)
    wstep.
    eapply evt_cut.
    { eapply (S0_memset_specZ (E + 37708 + 258 * t) (nInUse + 2) 15); [exact L1 | exact MI | f_equal; lia | reflexivity | reflexivity | lia | lia | lia]. }
    clear L1. post_call s0segs m.
    match goal with H : rw_cells _ _ (E + 37708 + 258 * t)%Z _ |- _ => rename H into L1 end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
    pose proof (row_after_memset s0segs m2 (E + 37708) len (jseg J 37708 1548) 1548 t (nInUse + 2) L0 L1 L2 ltac:(lia) ltac:(lia) ltac:(lia)) as LEN. clear L0 L1 L2.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z (sm_len_init_row (Z.to_nat (nInUse + 2)) len t 0) me m2); [st_eq| lia| lia| lia| exact LEN| exact SC| exact MI2| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| assumption| assumption| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_len_init] in K.
      enter_with (K m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact LEN| exact SC| exact MI2| assumption| assumption].
  Qed.
  (* [comment removed for export] *)
  Lemma zbv_mod_mul : forall x c, Z_to_bv 64 ((x mod 18446744073709551616) * c) = Z_to_bv 64 (x * c).
  Proof.
    intros x c. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z.
    rewrite (Z.mod_eq x 18446744073709551616) by lia.
    replace ((x - 18446744073709551616 * (x / 18446744073709551616)) * c)%Z with (x * c + (- (x / 18446744073709551616) * c) * 18446744073709551616)%Z by nia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.
  Lemma zbv_add_mod_mul : forall a x c, Z_to_bv 64 (a + (x mod 18446744073709551616) * c) = Z_to_bv 64 (a + x * c).
  Proof.
    intros a x c. apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z.
    rewrite (Z.mod_eq x 18446744073709551616) by lia.
    replace (a + (x - 18446744073709551616 * (x / 18446744073709551616)) * c)%Z with (a + x * c + (- (x / 18446744073709551616) * c) * 18446744073709551616)%Z by nia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma v_divw_lit : forall a b, (0 <= a < 2147483648)%Z -> (0 < b < 2147483648)%Z ->
    v_divw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
  Proof.
    intros a b Ha Hb. unfold v_divw. rewrite !unsigned_lit by lia. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. rewrite (Z.mod_small b 4294967296%Z ltac:(lia)).
    replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (swrap32_small a) by lia. rewrite (swrap32_small b) by lia. rewrite Z.quot_div_nonneg by lia.
    pose proof (Z.div_pos a b ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound a b a ltac:(lia) ltac:(nia)).
    rewrite swrap32_small by lia. reflexivity.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
End S0SMA.

End ACeilS1.
End S0_cmp_smA.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smB.S0_cmp_smA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require Import S0_memset.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section S0SMB.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv : word).
  (* [comment removed for export] *)
  Variables (xs9 xs10 xs11 : word).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx. Hypothesis SF : smA_facts e.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  (* [comment removed for export] *)
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    cps_destruct S as (?AEA1 & ?AEA2 & ?AEF & _ & _ & ?AA12 & ?A1F & _).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)
  Notation OFS := (258 * nG + 37450 + A)%Z.
  Notation RI ra t0 a0 a1 a2 a3 a4 s1 s2 s4 s6 s7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 (E + 676)) (Z_to_bv 64 (-258)) (Z_to_bv 64 1)
         s2 (Z_to_bv 64 OFS) s4 (Z_to_bv 64 (E + 672)) s6 s7 s8 s9 (Z_to_bv 64 (-2147483647)) (Z_to_bv 64 4294967296) t3 t4 t5 t6).

  Notation smGROW := (S0_smA_grow cx e Q sp gp tp F fc CX SEP SF).
  Notation smSETROW := (S0_smA_setrow cx e Q sp gp tp F fc CX SEP SF).

  (* [comment removed for export] *)
  Lemma S0_smA_iloop : forall (n k : nat) (me m : word -> option byte)
      (ra t0 a1 a2 a3 a4 s7 s8 s9 t3 t4 t5 t6 : word) (w576 w584 w592 w600 : word),
    let s := sip_k e k in
    ip_nPart s = Z.of_nat n -> (1 <= n)%nat -> (Z.of_nat k + Z.of_nat n = nG)%Z ->
    u8arr s0segs m (E + 37708) (ovb (ip_len s) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells s0segs m (usp + 96) [C8 (Z_to_bv 64 nG)] ->
    rw_cells s0segs m (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 (Z_to_bv 64 nInUse)] -> mem_inv s0segs m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    munch [(E + 37708, E + 39256)]%Z me m -> wmono s0segs me m ->
    (forall m' (a1 a2 a3 a4 s8 s9 : word), let s' := sip_k e (k + n) in
      u8arr s0segs m' (E + 37708) (ovb (ip_len s') (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells s0segs m' (usp + 96) [C8 (Z_to_bv 64 nG)] ->
      rw_cells s0segs m' (usp + 576) [C8 w576; C8 w584; C8 w592; C8 w600; C8 (Z_to_bv 64 nInUse)] -> mem_inv s0segs m' ->
      munch [(E + 37708, E + 39256)]%Z me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 0) a1 a2 a3 a4 (Z_to_bv 64 (ip_remF s')) (Z_to_bv 64 (Z.of_nat (k + n))) (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) (Z_to_bv 64 (ip_gs s')) (Z_to_bv 64 1) s8 s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16010) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 (ip_nPart s)) a1 a2 a3 a4 (Z_to_bv 64 (ip_remF s)) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (E + 37708 + 258 * (ip_nPart s - 1))) (Z_to_bv 64 (ip_gs s)) s7 s8 s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x15ebc) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros k me m ra t0 a1 a2 a3 a4 s7 s8 s9 t3 t4 t5 t6 w576 w584 w592 w600 s HnP Hn Hk LEN MTF EH2 SA96 SC MI CE SPB MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. clear AEA1 AEA2 AEF AA12 A1F. openSF. bz_ceil; bz_params; unfold CEIL in CE. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (IPK k ltac:(lia)) as IK. cbv zeta in IK. fold s in IK. cps_destruct IK as (EnP & Hgs & EremF & HremF).
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length_nat (ip_len s) (jseg J 37708 1548) 1548) as LLn.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    unfold EHEAD2 in EH2.
    set (nP := ip_nPart s) in *. set (gs := ip_gs s) in *. set (remF := ip_remF s) in *.
    (* [comment removed for export] *)
    destruct (ex_intro (fun t => t = (remF / nP)%Z) (remF / nP)%Z eq_refl) as [tF EtF].
    assert (HtF : (0 <= tF <= remF)%Z).
    { rewrite EtF. split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_compat_l remF 1 nP ltac:(lia) ltac:(lia)) as Hd. rewrite Z.div_1_r in Hd. exact Hd. }
    change (id (tF = remF / nP)%Z) in EtF.
    (* [comment removed for export] *)
    wstep. wstep. wstep. rewrite (v_divw_lit remF nP) by lia. replace (remF / nP)%Z with tF by exact EtF. wstep. try rewrite (sx32_of_Z_signed (gs + -1)) by lia.
    assert (ADJ : forall ge1, ip_adj nG s ge1 = ((gs <? ge1) && negb (nP =? nG) && negb (nP =? 1) && ((nG - nP) mod 2 =? 1))%Z%bool) by (intros; reflexivity).
    (* [comment removed for export] *)
    assert (POSTADJ : forall ge1 aF1 ge2 aF2 (ya0 ya1 xa2 xa3 xa4 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
        (ge2 = (if ip_adj nG s ge1 then ge1 - 1 else ge1))%Z -> (aF2 = (if ip_adj nG s ge1 then aF1 - zget mf ge1 else aF1))%Z ->
        (gs - 1 <= ge2 <= A - 1)%Z -> (0 <= aF2 <= remF)%Z ->
      evt s0segs Q (MS (RI ra t0 ya0 ya1 xa2 xa3 xa4 (Z_to_bv 64 remF) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (E + 37708 + 258 * (nP - 1))) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 aF2) (Z_to_bv 64 ge2) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15f44) fc None m (seg_rom s0segs))).
  { intros ge1 aF1 ge2 aF2 ya0 ya1 xa2 xa3 xa4 EG Hge1 EaF1 BaF1 Ege2 EaF2 Hge2 BaF2.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
      wstep. wstep; if_cases Kn2; zify_cond_z Kn2; [exfalso; lia|].
      wstep. wstep. wstep. wstep. wstep.
      (* [comment removed for export] *)
      replace (Z_to_bv 64 (E + (OFS + Z.of_nat k * 18446744073709551358))) with (Z_to_bv 64 (E + 37708 + 258 * (nP - 1) + A)).
      2:{ apply Z_to_bv_eqm. change (2^64)%Z with 18446744073709551616%Z.
          replace (E + (OFS + Z.of_nat k * 18446744073709551358))%Z with ((E + 37708 + 258 * (nP - 1) + A) + Z.of_nat k * 18446744073709551616)%Z by lia.
          rewrite Z.mod_add by lia. reflexivity. }
      enter_with (smSETROW (Z.to_nat A) 0 (nP - 1) gs ge2 (ip_len s) m m);
        [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| exact MI| apply munch_refl| apply wmono_refl|].
      intros m2 za0 za3 za4 LEN2 MI2 MU2 WM2. clear LEN MI. unfold EHEAD2 in EH2. transport_after_call s0segs m m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      wstep. wstep. try rewrite (sx32_of_Z (ge2 + 1)) by lia. wstep. try rewrite (sx32_of_Z (remF - aF2)) by lia. try rewrite (sx32_of_Z_signed (remF - aF2)) by lia. wstep. wstep.
      (* [comment removed for export] *)
      assert (Es' : sip_k e (S k) = SIP (sm_setrow (Z.to_nat A) (ip_len s) (nP - 1) gs ge2 0) (nP - 1) (remF - aF2) (ge2 + 1)).
      { rewrite sip_k_S. fold s. rewrite (sm_init_iter_spec mf nG A s ge1 aF1).
        2:{ unfold id in EtF. subst nP gs remF. rewrite <- EtF. exact EG. }
        cbv zeta. subst nP gs remF. rewrite <- Ege2, <- EaF2. reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        pose proof (IH (S k)) as IH'. cbv zeta in IH'. rewrite Es' in IH'. cbn [ip_nPart ip_remF ip_gs ip_len] in IH'.
        enter_with (IH' me m2 _ _ _ _ _ _ _ _ _ _ _ _ _ w576 w584 w592 w600);
          [st_eq| lia| lia| lia| exact LEN2| assumption| assumption| assumption| assumption| exact MI2| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| assumption| assumption|].
        intros m' y1 y2 y3 y4 y5 y6. replace (S k + n)%nat with (k + S n)%nat by lia. exact (K m' y1 y2 y3 y4 y5 y6).
      - (* [comment removed for export] *)
        assert (n = 0)%nat by lia. subst n. wstep.
        pose proof K as K'. cbv zeta in K'. replace (k + 1)%nat with (S k) in K' by lia. rewrite Es' in K'. cbn [ip_nPart ip_remF ip_gs ip_len] in K'.
        enter_with (K' m2 _ _ _ _ _ _); [st_eq| exact LEN2| assumption| assumption| assumption| assumption| exact MI2| assumption| assumption]. }
    (* [comment removed for export] *)
    assert (POSTGROW : forall ge1 aF1 (xa2 xa3 xa4 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
      evt s0segs Q (MS (RI ra t0 (Z_to_bv 64 (ge1 * 4294967296)) (Z_to_bv 64 tF) xa2 xa3 xa4 (Z_to_bv 64 remF) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 (E + 37708 + 258 * (nP - 1))) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 aF1) (Z_to_bv 64 ge1) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x15f10) fc None m (seg_rom s0segs))).
    { intros ge1 aF1 xa2 xa3 xa4 EG Hge1 EaF1 BaF1.
      (* [comment removed for export] *)
      wstep; if_cases K1; zify_cond_z K1.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (gs <? ge1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
      (* [comment removed for export] *)
      wstep. wstep; if_cases K2; zify_cond_z K2.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? nG)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z; reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases K3; zify_cond_z K3.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z, (nP =? nG)%Z; reflexivity. }
      (* [comment removed for export] *)
      wstep. wstep. try rewrite (sx32_of_Z (nG - nP)) by lia. try rewrite (sx32_of_Z_signed (nG - nP)) by lia. wstep.
      try rewrite (land_mask31 (nG - nP)) by lia.
      destruct (ex_intro (fun p => p = ((nG - nP) mod 2)%Z) ((nG - nP) mod 2)%Z eq_refl) as [par Epar].
      assert (Hpar : (0 <= par <= 1)%Z) by (rewrite Epar; Z.div_mod_to_equations; lia).
      rewrite <- Epar. change (id (par = (nG - nP) mod 2)%Z) in Epar.
      (* [comment removed for export] *)
      wstep; if_cases K4; zify_cond_z K4.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); unfold id in Epar; rewrite <- Epar;
          replace (par =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia);
          destruct (gs <? ge1)%Z, (nP =? nG)%Z, (nP =? 1)%Z; reflexivity. }
      (* [comment removed for export] *)
      assert (AT : ip_adj nG s ge1 = true).
      { rewrite (ADJ ge1). unfold id in Epar. rewrite <- Epar. replace (gs <? ge1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (nP =? nG)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (nP =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        replace (par =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      pose proof (MFD ge1 ltac:(lia)) as [Dg Rg].
      assert (BaF2 : (0 <= aF1 - zget mf ge1)%Z).
      { rewrite EaF1. replace (Z.to_nat (ge1 + 1 - gs)) with (S (Z.to_nat (ge1 - gs))) by lia. rewrite sumF_S_last.
        replace (gs + Z.of_nat (Z.to_nat (ge1 - gs)))%Z with ge1 by lia.
        pose proof (sumF_nonneg (Z.to_nat (ge1 - gs)) (fun v => zget mf v) gs ltac:(intros b Hb; apply (proj1 (proj2 (MFD b ltac:(lia)))))). lia. }
      wstep. replace (ge1 * 4294967296 / 1073741824)%Z with (4 * ge1)%Z
        by (replace (ge1 * 4294967296)%Z with ((4 * ge1) * 1073741824)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
      wstep.
      pose proof (ovw_read s0segs m (E + 672) mf (jseg J 672 1032) 258 ge1 _ MTF ltac:(lia) Dg ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf ge1)) by lia.
      wstep. try rewrite (sx32_of_Z (aF1 - zget mf ge1)) by lia. try rewrite (sx32_of_Z_signed (aF1 - zget mf ge1)) by lia.
      wstep. try rewrite (sx32_of_Z_signed (ge1 + -1)) by lia. try rewrite (sx32_of_Z (ge1 + -1)) by lia.
      enter_with (POSTADJ ge1 aF1 (ge1 - 1)%Z (aF1 - zget mf ge1)%Z _ _ _ _ _); [st_eq| exact EG| lia| exact EaF1| lia| rewrite AT; reflexivity| rewrite AT; reflexivity| lia| lia]. }
    (* [comment removed for export] *)
    assert (E0 : 0%Z = sumF (fun v => zget mf v) gs (Z.to_nat (gs - 1 + 1 - gs))) by (replace (Z.to_nat (gs - 1 + 1 - gs)) with 0%nat by lia; reflexivity).
    wstep; if_cases K5; zify_cond_z K5.
    { eapply (POSTADJ (gs - 1)%Z 0%Z (gs - 1)%Z 0%Z); [apply sm_grow_stop; lia| lia| exact E0| lia| | | lia| lia];
        rewrite (ADJ (gs - 1)%Z); replace (gs <? gs - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
    (* [comment removed for export] *)
    wstep. wstep; if_cases K6; zify_cond_z K6.
    { eapply (POSTADJ (gs - 1)%Z 0%Z (gs - 1)%Z 0%Z); [apply sm_grow_stop; lia| lia| exact E0| lia| | | lia| lia];
        rewrite (ADJ (gs - 1)%Z); replace (gs <? gs - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. rewrite ?zbv_mod_mul, ?zbv_add_mod_mul.
    enter_with (smGROW 260%nat (gs - 1)%Z 0%Z gs tF remF m);
      [st_eq| lia| lia| lia| lia| lia| lia| exact E0| exact EremF| lia| exact MTF| exact SC| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    intros ge' aF' y2 y3 y4 EG' Hge' EaF' BaF'. eapply (POSTGROW ge' aF'); [exact EG'| lia| exact EaF'| exact BaF'].
  Qed.
End S0SMB.

End ACeilS1.
