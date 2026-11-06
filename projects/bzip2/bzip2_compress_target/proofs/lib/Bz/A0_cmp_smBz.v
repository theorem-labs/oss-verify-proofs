(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV A0_cmp_smBc.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GZ.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV FB SHF : Z) (w16 w24 : word).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation LOA := (sm_loA cx e FB SHF SHE w16 w24). Notation LOB := (sm_loB cx e SHE).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac RDV V :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RO := fresh "RO" in pose proof (V mm MU') as RO; unfold sm_loA, sm_loB, sm_hi in RO; cbv zeta in RO; lstep; clear RO end.

  (* [comment removed for export] *)
  Notation IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 cSB s5 s6 (Z_to_bv 64 A) (Z_to_bv 64 A1) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 nG) s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_it1 : forall (m : word -> option byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s11 t3 t4 t5 t6 : word),
    frdW a0segs [] m (P + 16) LOA -> frdW a0segs [] m (P + 160) LOB ->
    evt a0segs Q (MS (IZ (Z_to_bv 64 0x8a9fc) t0 t1 t2 (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * A)) a3 a4 a5 a6 a7
                         (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 nG) (Z_to_bv 64 (4 * A)) s6 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs)) ->
    evt a0segs Q (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s3 s5 s6 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a9d8) fc None m (seg_rom a0segs)).
  Proof.
    intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s11 t3 t4 t5 t6 VA VB K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (munch_refl [] m) as MU.
    (* [comment removed for export] *)
    lstep. RDV VB. RDV VA. lstep. lstep; if_cases Kn; zify_cond_z Kn; [exfalso; lia|].
    lstep. lstep. lstep. lstep.
    enter_with K; [st_eq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wit2 := [(E + 51640, E + 55768); (P + 1424, P + 1440)]%Z.
  Lemma A0_sm_it2 : forall (t : Z) (lp len : zarr) (w1360 w1424 w1432 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word),
    (0 <= t < nG)%Z ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr a0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells a0segs m (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 999999999); C8 w1360; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 CO); C8 (Z_to_bv 64 FV);
                                  C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 A); C8 w1424; C8 w1432] ->
    mem_inv a0segs m -> munch Wit2 mf m -> wmono a0segs mf m ->
    frdW a0segs Wit2 mf (P + 16) LOA -> frdW a0segs Wit2 mf (P + 160) LOB -> frdW a0segs Wit2 mf (E + 640) (EHEAD2 cx g e) ->
    shzW a0segs Wit2 mf E (E + ESTATE_SIZE) ->
    (* [comment removed for export] *)
    ((t + 1 < nG)%Z ->
      evt a0segs Q (MS (IZ (Z_to_bv 64 0x8a9fc) t0 t1 t2 (Z_to_bv 64 (E + 45448 + 1032 * (t + 1))) (Z_to_bv 64 0) (Z_to_bv 64 (4 * A)) a3 a4 a5 a6 a7
                           (Z_to_bv 64 (E + 45448 + 1032 * (t + 1))) (Z_to_bv 64 (nG - (t + 1))) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 668)) s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    ((t + 1 = nG)%Z -> forall m' (t0' t1' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr a0segs m' (E + 51640) (ovw (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) lp len 0 else lp) (jseg J 51640 4128) 1032) ->
      rw_cells a0segs m' (P + 1344) (sm_hi cx e CO FV w1360 0 0) ->
      mem_inv a0segs m' -> munch Wit2 mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (IZ (Z_to_bv 64 0x8ac34) t0' t1' (Z_to_bv 64 CO) (Z_to_bv 64 CO) (Z_to_bv 64 0) (Z_to_bv 64 12) a3' a4' a5' a6' a7'
                           (Z_to_bv 64 nMTF) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 0) (Z_to_bv 64 49) (Z_to_bv 64 (E + 668)) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x52ea0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448 + 1032 * t)) (Z_to_bv 64 (nG - t)) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 668)) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8a9fc) fc None m (seg_rom a0segs)).
  Proof.
    intros t lp len w1360 w1424 w1432 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 Ht LF LEN LPK HI MI MU WM VA VB VEH2 SHe KR KG.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'.
    (* [comment removed for export] *)
    RDV VB. lstep. lstep. lstep; if_cases Kr; zify_cond_z Kr.
    - (* [comment removed for export] *)
      lstep. lstep; if_cases Kn; zify_cond_z Kn; [exfalso; lia|].
      lstep. lstep. lstep. lstep.
      enter_with (KR ltac:(lia)); [st_eq].
    - (* [comment removed for export] *)
      assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
      (* [comment removed for export] *)
      assert (POST : forall lp' m1 (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 : word),
        lp' = (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) lp len 0 else lp) ->
        u8arr a0segs m1 (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
        u32arr a0segs m1 (E + 51640) (ovw lp' (jseg J 51640 4128) 1032) ->
        rw_cells a0segs m1 (P + 1344) [C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 999999999); C8 w1360; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 CO); C8 (Z_to_bv 64 FV);
                                       C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (E + 45448)); C8 (Z_to_bv 64 (E + 45448 + 1032 * nG)); C8 (Z_to_bv 64 A); C8 w1424; C8 w1432] ->
        mem_inv a0segs m1 -> munch Wit2 mf m1 -> wmono a0segs mf m1 ->
        evt a0segs Q (MS (IZ xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 (Z_to_bv 64 E) (Z_to_bv 64 (E + 668)) s11 xt3 xt4 xt5 xt6)
                         F (Z_to_bv 64 0x8abe8) fc None m1 (seg_rom a0segs))).
      { intros lp' m1 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xt3 xt4 xt5 xt6 Elp LEN1 LPK1 HI1 MI1 MU1 WM1.
        unfold ESTATE_SIZE in SHe.
        (* [comment removed for export] *)
        pose proof (VEH2 m1 MU1) as EH2. unfold EHEAD2 in EH2. rewrite GM in EH2.
        pose proof (VB m1 MU1) as RO. unfold sm_loB in RO. cbv zeta in RO.
        arun_to 0x8abfc%Z. clear EH2 RO. try rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
        (* [comment removed for export] *)
        lstep. lstep. lstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
        (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. lit_store. lstep. lit_store. wstep. lstep. lstep. lstep. lstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KG ltac:(lia) mm _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact LEN1| rewrite <- Elp; exact LPK1| unfold sm_hi; cbv zeta; lazymatch type of HI1 with rw_cells _ _ _ ?L => lazymatch goal with |- rw_cells _ _ _ ?L2 => replace L2 with L; [exact HI1| CmpFast.rlf] end end| assumption| assumption| assumption]. }
      RDV VA. RDV VA. lstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
        enter_with (POST lp m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| destruct (Z.eqb_spec nG 6); [exfalso; lia| reflexivity]| exact LEN| exact LPK| exact HI| exact MI| exact MU| exact WM].
      + destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
        (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. lstep. lstep. lstep.
        RDV VA. RDV VA. RDV VB. RDV VA. lstep. RDV VA.
        enter_with (A0_sm_lpk cx e Q gp tp s0 F fc P CX HA (Z.to_nat A) 0 lp len m m);
          [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| exact MI| apply munch_refl| apply wmono_refl| |].
        { eapply (shzW_sub a0segs Wit2 _ mf m); [exact SHe| exact MU| a_sub_fp| lia| lia]. }
        clear LEN LPK MI. intros m' ya0 ya1 ys2 yt5 yt6 LEN LPK MI MU' WM'.
        transport_after_call a0segs m m' MU' WM'. clear MU' WM'.
        enter_with (POST _ m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| destruct (Z.eqb_spec nG 6); [reflexivity| exfalso; lia]| exact LEN| exact LPK| exact HI| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wit4 := [(P + 152, P + 160)]%Z.
  Lemma A0_sm_it4 : forall (iter : Z) (w1360 : word) (totc gs : Z) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 : word),
    (0 <= iter < 4)%Z ->
    rw_cells a0segs m (P + 152) [C8 (Z_to_bv 64 iter)] ->
    mem_inv a0segs m -> munch Wit4 mf m -> wmono a0segs mf m ->
    frdW a0segs Wit4 mf (P + 16) LOA -> frdW a0segs Wit4 mf (P + 160) LOB -> frdW a0segs Wit4 mf (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
    frdW a0segs Wit4 mf (E + 640) (EHEAD2 cx g e) -> shzW a0segs Wit4 mf E (E + ESTATE_SIZE) ->
    (forall m',
      rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 (iter + 1))] ->
      mem_inv a0segs m' -> munch Wit4 mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (IZ (Z_to_bv 64 0x8f1bc) t0 t1 t2 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) (Z_to_bv 64 17) a4 a5 a6 a7
                           (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (E + 45448)) s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9d0c8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f16c) fc None m (seg_rom a0segs)).
  Proof.
    intros iter w1360 totc gs m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 Hit ITER MI MU WM VA VB VH VEH2 SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe.
    (* [comment removed for export] *)
    wstep. lstep.
    pose proof (VEH2 m MU) as EH2. unfold EHEAD2 in EH2.
    pose proof (VA m MU) as RO. unfold sm_loA in RO. cbv zeta in RO.
    arun_to 0x8f190%Z. clear EH2 RO.
    wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
    (* [comment removed for export] *)
    lstep. wstep. lstep. RDV VB. RDV VH. lstep. lstep. lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end; [st_eq| assumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_it5 : forall (t iter : Z) (w1360 : word) (totc gs : Z) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s11 t3 t4 t5 t6 : word),
    (0 <= t < nG)%Z -> (1 <= iter <= 4)%Z ->
    frdW a0segs [] m (P + 152) [C8 (Z_to_bv 64 iter)] -> frdW a0segs [] m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
    (* [comment removed for export] *)
    ((t + 1 < nG)%Z ->
      evt a0segs Q (MS (IZ (Z_to_bv 64 0x8f1bc) t0 t1 t2 (Z_to_bv 64 (E + 37708 + 258 * (t + 1))) (Z_to_bv 64 (E + 45448 + 1032 * (t + 1))) (Z_to_bv 64 A) (Z_to_bv 64 17) a4 a5 a6 a7
                           (Z_to_bv 64 (E + 37708 + 258 * (t + 1))) (Z_to_bv 64 (E + 45448 + 1032 * (t + 1))) s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x9d0c8) fc None m (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    ((t + 1 = nG)%Z -> (iter < 4)%Z ->
      evt a0segs Q (MS (IZ (Z_to_bv 64 0x8a9d8) t0 t1 t2 (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                           (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (E + 45448 + 1032 * nG)) s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) ->
    (* [comment removed for export] *)
    ((t + 1 = nG)%Z -> (iter = 4)%Z ->
      evt a0segs Q (MS (IZ ra t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 4) (Z_to_bv 64 (E + 45448 + 1032 * nG)) a3 a4 a5 a6 a7
                           (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (E + 45448 + 1032 * nG)) s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f29c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 (E + 45448 + 1032 * t)) s5 s6 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f1bc) fc None m (seg_rom a0segs)).
  Proof.
    intros t iter w1360 totc gs m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s11 t3 t4 t5 t6 Ht Hit VI VH KM KI KE.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    pose proof (munch_refl [] m) as MU.
    (* [comment removed for export] *)
    RDV VH. lstep. lstep. lstep; if_cases Kt; zify_cond_z Kt.
    - (* [comment removed for export] *)
      lstep. lstep. lstep. lstep. lstep.
      enter_with (KM ltac:(lia)); [st_eq].
    - (* [comment removed for export] *)
      RDV VI. RDV VH. lstep. lstep; if_cases Ki; zify_cond_z Ki.
      + enter_with (KE ltac:(lia) ltac:(lia)); [st_eq].
      + (* [comment removed for export] *)
        lstep. lstep. RDV VH. lstep. lstep.
        enter_with (KI ltac:(lia) ltac:(lia)); [st_eq].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_sm_it4b : forall (iter : Z) (w1360 : word) (totc gs : Z) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 : word),
    (0 <= iter < 4)%Z ->
    rw_cells a0segs m (P + 152) [C8 (Z_to_bv 64 iter)] ->
    mem_inv a0segs m -> munch Wit4 mf m -> wmono a0segs mf m ->
    frdW a0segs Wit4 mf (P + 16) LOA -> frdW a0segs Wit4 mf (P + 160) LOB -> frdW a0segs Wit4 mf (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
    frdW a0segs Wit4 mf (E + 640) (EHEAD2 cx g e) -> shzW a0segs Wit4 mf E (E + ESTATE_SIZE) ->
    (forall m' (a0' a1' a3' : word),
      rw_cells a0segs m' (P + 152) [C8 (Z_to_bv 64 (iter + 1))] ->
      mem_inv a0segs m' -> munch Wit4 mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (IZ ra t0 t1 t2 a0' a1' a2 a3' a4 a5 a6 a7 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (E + 45448)) s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f1a8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f16c) fc None m (seg_rom a0segs)).
  Proof.
    intros iter w1360 totc gs m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 Hit ITER MI MU WM VA VB VH VEH2 SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe.
    wstep. lstep.
    pose proof (VEH2 m MU) as EH2. unfold EHEAD2 in EH2.
    pose proof (VA m MU) as RO. unfold sm_loA in RO. cbv zeta in RO.
    arun_to 0x8f190%Z. clear EH2 RO.
    wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
    lstep. wstep. lstep. RDV VB. RDV VH.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _) end; [st_eq| assumption| assumption| assumption| assumption].
  Qed.

  Lemma A0_sm_it6 : forall (iter : Z) (w1360 : word) (totc gs : Z) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 : word),
    (1 <= iter <= 4)%Z ->
    frdW a0segs [] m (P + 152) [C8 (Z_to_bv 64 iter)] -> frdW a0segs [] m (P + 1344) (sm_hi cx e CO FV w1360 totc gs) ->
    ((iter < 4)%Z ->
      evt a0segs Q (MS (IZ (Z_to_bv 64 0x8a9d8) t0 t1 t2 (Z_to_bv 64 FV) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
                           (Z_to_bv 64 (E + 45448)) s3 s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x52ea0) fc None m (seg_rom a0segs))) ->
    ((iter = 4)%Z ->
      evt a0segs Q (MS (IZ ra t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s3 s5 s6 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x8f29c) fc None m (seg_rom a0segs))) ->
    evt a0segs Q (MS (IZ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8f1cc) fc None m (seg_rom a0segs)).
  Proof.
    intros iter w1360 totc gs m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s11 t3 t4 t5 t6 Hit VI VH KI KE.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb.
    pose proof (munch_refl [] m) as MU.
    (* [comment removed for export] *)
    RDV VI. RDV VH. lstep. lstep; if_cases Ki; zify_cond_z Ki.
    - enter_with (KE ltac:(lia)); [st_eq].
    - (* [comment removed for export] *)
      lstep. lstep. RDV VH. lstep. lstep.
      enter_with (KI ltac:(lia)); [st_eq].
  Qed.
End GZ.
End ACeilS1.
