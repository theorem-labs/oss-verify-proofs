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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut0.
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

Section U0SMP.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e. Hypothesis GM : g_mtf g = true. Hypothesis CI : cctx_img S0C cx.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation J := (c_J cx). Notation A1 := (c_A1 cx).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation MASK := (Z_to_bv 64 18446744071562067969).
  Notation LR t := (E + 37708 + 258 * t)%Z.
  Notation Wlen := [(E + 37708, E + 39256)]%Z.
  Notation W904 := [(SP + 904, SP + 912)]%Z.
  Notation Whd := [(SP + 16, SP + 24); (SP + 904, SP + 912); (SP + 928, SP + 936); (SP + 960, SP + 976); (SP + 984, SP + 992);
                   (SP + 1000, SP + 1024); (SP + 1032, SP + 1040); (SP + 1096, SP + 1200); (E + 37708, E + 39256)]%Z.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  Notation RIu t0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 :=
    (mkR ra cSP gp tp t0 (Z_to_bv 64 258) (Z_to_bv 64 1) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 6) s3 s4 s5 s6 (Z_to_bv 64 (A - 1)) (Z_to_bv 64 257) (NOT (E + 37708)) (Z_to_bv 64 (E + 672)) (NOT (E + 672))
         MASK (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 15)).

  Section LROWS.
  Variables (t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word).
  Notation RL a0 a4 a5 a6 a7 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 A) a0 (Z_to_bv 64 258) (Z_to_bv 64 15) (Z_to_bv 64 6) a4 a5 a6 a7
         s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).

  Lemma U0_smA_lenrow : forall (n : nat) (v t : Z) (len : zarr) (me m : word -> option byte) (a7 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < 6)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    mem_inv s0segs m -> munch Wlen me m -> wmono s0segs me m ->
    frdW s0segs Wlen me (SP + 984) [C8 (Z_to_bv 64 A)] ->
    (forall m',
      u8arr s0segs m' (E + 37708) (ovb (sm_len_init_row n len t v) (jseg J 37708 1548) 1548) ->
      mem_inv s0segs m' -> munch Wlen me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RL (Z_to_bv 64 t) (Z_to_bv 64 (LR t)) (Z_to_bv 64 A) (NOT (LR t)) (Z_to_bv 64 A))
                       F (Z_to_bv 64 0x1703c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL (Z_to_bv 64 t) (Z_to_bv 64 (LR t)) (Z_to_bv 64 v) (NOT (LR t)) a7)
                     F (Z_to_bv 64 0x17018) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t len me m a7 Hv Hv0 Hn Ht LEN MI MU WM V984 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. unfold sm_alpha in *.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_len_init_row_S in K.
    pose proof (u8arr_store_ok s0segs m (E + 37708) _ (258 * t + v) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    urun_to 0x17030%Z.
    wstep. store_addr (E + 37708 + (258 * t + v))%Z. ovb_store1 LEN (258 * t + v)%Z.
    lazymatch type of LEN with context [wr8 ?l0 ?i0 ?w] =>
      replace (wr8 l0 i0 w) with (zset l0 i0 BZ_GREATER_ICOST) in LEN
        by (unfold wr8, BZ_GREATER_ICOST; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity) end.
    poseV V984 RO. wstep. clear RO.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (v + 1)%Z t (zset len (258 * t + v) BZ_GREATER_ICOST) me _ _);
        [st_eq| lia| lia| lia| lia| exact LEN| assumption| exact MU| exact WM| exact V984| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_len_init_row] in K.
      enter_with (K _); [st_eq| exact LEN| assumption| exact MU| exact WM].
  Qed.

  Lemma U0_smA_lenrows : forall (n : nat) (t : Z) (len : zarr) (me m : word -> option byte) (a5 a6 a7 : word),
    (t + Z.of_nat n = 6)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    mem_inv s0segs m -> munch Wlen me m -> wmono s0segs me m ->
    frdW s0segs Wlen me (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wlen me (SP + 968) [C8 (Z_to_bv 64 A)] ->
    frdW s0segs Wlen me (SP + 984) [C8 (Z_to_bv 64 A)] ->
    (forall m' (a5' a6' a7' : word),
      u8arr s0segs m' (E + 37708) (ovb (sm_len_init n len A t) (jseg J 37708 1548) 1548) ->
      mem_inv s0segs m' -> munch Wlen me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RL (Z_to_bv 64 6) (Z_to_bv 64 (LR 6)) a5' a6' a7')
                       F (Z_to_bv 64 0x1704c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL (Z_to_bv 64 t) (Z_to_bv 64 (LR t)) a5 a6 a7)
                     F (Z_to_bv 64 0x16ff8) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t len me m a5 a6 a7 Ht Ht0 Hn LEN MI MU WM V960 V968 V984 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_len_init_S in K.
    wstep; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    urun_to 0x1700c%Z.
    poseV V960 RO. wstep. clear RO.
    urun_to 0x17018%Z.
    enter_with (U0_smA_lenrow (Z.to_nat A) 0 t len me m _); [st_eq| lia| lia| lia| lia| exact LEN| exact MI| exact MU| exact WM| exact V984|].
    clear LEN MI MU WM. intros m1 LEN MI MU WM.
    urun_to 0x17044%Z.
    poseV V968 RO. wstep. clear RO.
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z (sm_len_init_row (Z.to_nat A) len t 0) me m1 _ _ _);
        [st_eq| lia| lia| lia| exact LEN| exact MI| exact MU| exact WM| exact V960| exact V968| exact V984| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_len_init] in K.
      enter_with (K m1 _ _ _); [st_eq| exact LEN| exact MI| exact MU| exact WM].
  Qed.

  Ltac ng_end K EFL :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _); [st_eq| unfold EHEAD2; rewrite GM; assumption| rewrite EFL; assumption| assumption| assumption| assumption] end.
  Lemma U0_smA_ngsel : forall (w904 : word) (me m : word -> option byte) (a5 a6 a7 : word),
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) -> rw_cells s0segs m (SP + 904) [C8 w904] ->
    mem_inv s0segs m -> munch W904 me m -> wmono s0segs me m ->
    (forall m' (a0 : word),
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) -> rw_cells s0segs m' (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] ->
      mem_inv s0segs m' -> munch W904 me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RL a0 (Z_to_bv 64 (LR 6)) (Z_to_bv 64 nG) a6 (Z_to_bv 64 nMTF))
                       F (Z_to_bv 64 0x170b4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL (Z_to_bv 64 6) (Z_to_bv 64 (LR 6)) a5 a6 a7)
                     F (Z_to_bv 64 0x1704c) fc None m (seg_rom s0segs)).
  Proof.
    intros w904 me m a5 a6 a7 EH2 C904 MI MU WM K.
    openCX. try clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openSF. unfold CEIL in CEP.
    assert (HMd : nMTF = e_nMTF e) by reflexivity.
    assert (HNM : (1 <= nMTF < 2147483648)%Z) by lia.
    unfold EHEAD2 in EH2. rewrite GM in EH2.
    wstep. change (e_nMTF e) with nMTF. try rewrite (sx32_of_Z nMTF) by lia.
    wstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    wstep. wstep; if_cases K2; zify_cond_z K2.
    - wstep. wstep; if_cases K3; zify_cond_z K3.
      + wstep. wstep; if_cases K4; zify_cond_z K4.
        * destruct (Z.ltb_spec nMTF 2400) as [L24|L24].
          { assert (ENG : nG = 5%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
            assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
            wstep. wstep. wstep.
            replace (Z.lxor (Z.b2z (nMTF / 32 <? 75)) 1) with 0%Z by (replace (nMTF / 32 <? 75)%Z with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia); reflexivity).
            wstep; lit_store. wstep. ng_end K EFL. }
          { assert (ENG : nG = 6%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
            assert (EFL : flag6 nG = 1%Z) by (rewrite ENG; reflexivity).
            wstep. wstep. wstep.
            replace (Z.lxor (Z.b2z (nMTF / 32 <? 75)) 1) with 1%Z by (replace (nMTF / 32 <? 75)%Z with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia); reflexivity).
            wstep; lit_store. wstep. ng_end K EFL. }
        * assert (ENG : nG = 4%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
          assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
          wstep; lit_store. wstep. wstep. ng_end K EFL.
      + assert (ENG : nG = 3%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
        assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
        wstep; lit_store. wstep. wstep. ng_end K EFL.
    - assert (ENG : nG = 2%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
      assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
      wstep; lit_store. wstep. wstep. ng_end K EFL.
  Qed.
  End LROWS.

  Lemma U0_smA_head : forall (sv : word) (me m : word -> option byte)
      (t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
      (w16 w904 w928 w960 w968 w984 w1000 w1008 w1016 w1032 : word)
      (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : word),
    rw_cells s0segs m E (EHEAD1 cx g e) -> rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    u8arr s0segs m (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) ->
    cimg_mem S0C m sv ->
    rw_cells s0segs m (SP + 16) [C8 w16] -> rw_cells s0segs m (SP + 904) [C8 w904] -> rw_cells s0segs m (SP + 928) [C8 w928] ->
    rw_cells s0segs m (SP + 960) [C8 w960] -> rw_cells s0segs m (SP + 968) [C8 w968] -> rw_cells s0segs m (SP + 984) [C8 w984] ->
    rw_cells s0segs m (SP + 1000) [C8 w1000] -> rw_cells s0segs m (SP + 1008) [C8 w1008] -> rw_cells s0segs m (SP + 1016) [C8 w1016] ->
    rw_cells s0segs m (SP + 1032) [C8 w1032] ->
    rw_cells s0segs m (SP + 1096) [C8 v0; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 v7; C8 v8; C8 v9; C8 v10; C8 v11; C8 v12] ->
    mem_inv s0segs m -> munch Whd me m -> wmono s0segs me m ->
    (forall m' (x0 xa1 xa2 xa3 xa4 xa5 xa6 xs4 xs5 xs6 : word),
      rw_cells s0segs m' E (EHEAD1 cx g e) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      u32arr s0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      u8arr s0segs m' (E + 37708) (ovb (smA_len e) (jseg J 37708 1548) 1548) ->
      cimg_mem S0C m' sv ->
      rw_cells s0segs m' (SP + 16) [C8 sv] -> rw_cells s0segs m' (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] ->
      rw_cells s0segs m' (SP + 928) [C8 (Z_to_bv 64 nG)] ->
      rw_cells s0segs m' (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] -> rw_cells s0segs m' (SP + 968) [C8 (Z_to_bv 64 A)] ->
      rw_cells s0segs m' (SP + 984) [C8 (Z_to_bv 64 A)] ->
      rw_cells s0segs m' (SP + 1000) [C8 (Z_to_bv 64 (A * 4294967296))] -> rw_cells s0segs m' (SP + 1008) [C8 (Z_to_bv 64 0)] ->
      rw_cells s0segs m' (SP + 1016) [C8 MASK] -> rw_cells s0segs m' (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
      rw_cells s0segs m' (SP + 1096) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      mem_inv s0segs m' -> munch Whd me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIu x0 (Z_to_bv 64 (E + 37708 + 258 * (nG - 1))) (Z_to_bv 64 nG) xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 nMTF) (Z_to_bv 64 0) xs4 xs5 xs6)
                       F (Z_to_bv 64 0x17120) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra (Z_to_bv 64 (SP + 1200)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16f4c) fc None m (seg_rom s0segs)).
  Proof.
    intros sv me m t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
      w16 w904 w928 w960 w968 w984 w1000 w1008 w1016 w1032 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
      EH1 EH2 MTF LEN CM C16 C904 C928 C960 C968 C984 C1000 C1008 C1016 C1032 SAV MI MU WM K.
    openCX. try clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA1 MA2 MF Mb Mf LJb. openSF. unfold CEIL in CEP.
    assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof CI as CIL. unfold cctx_img, img_apart, IMG_LO3, ESTATE_SIZE in CIL. cbn [ci_hi S0C] in CIL. destruct CIL as [CIE _].
    assert (EL7 : Z.land E 7 = 0%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME. Z.div_mod_to_equations. lia. }
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. rewrite GM in EH1, EH2.
    cps_destruct CM as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_crc ci_crcx ci_stderrp S0C] in CM1, CM2, CM3, CM4.
    wstep. do 13 wstep. wstep. wstep. rewrite EL7.
    urun_to 0x16f9c%Z. wstep; lit_store.
    urun_to 0x16fa4%Z. wstep; first [ if_cases Kv; zify_cond_z Kv; [| exfalso; lia] | idtac ].
    wstep. try rewrite (sx32_of_Z nInUse) by lia. wstep. try rewrite (sx32_of_Z (nInUse + 2)) by lia. wstep; lit_store.
    urun_to 0x16fdc%Z. wstep; lit_store.
    wstep. try replace ((nInUse + 2) * 4294967296 / 4294967296)%Z with (nInUse + 2)%Z by (rewrite Z.div_mul; lia). wstep; lit_store.
    urun_to 0x16ff4%Z. wstep; lit_store.
    enter_with (U0_smA_lenrows t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 6%nat 0%Z (e_len e) _ _ a5 a6 a7);
      [st_eq| lia| lia| lia| exact LEN| exact MI| apply munch_refl| apply wmono_refl| | | | ].
    1-3: (apply frdW_intro; [eassumption| cbn [disjoint_from]; simpl_sizes; slia]).
    intros m2 y5 y6 y7 LEN2 MI2 MU2 WM2.
    lazymatch type of MI with mem_inv _ ?mm => clear LEN MI; transport_after_call s0segs mm m2 MU2 WM2 end. clear MU2 WM2.
    enter_with (U0_smA_ngsel t0 t1 t2 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 _ m2 m2 y5 y6 y7);
      [st_eq| unfold EHEAD2; rewrite GM; exact EH2| exact C904| exact MI2| apply munch_refl| apply wmono_refl|].
    intros m3 x0 EH2' C904' MI3 MU3 WM3. clear EH2 C904 MI2. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    unfold EHEAD2 in EH2'. rewrite GM in EH2'.
    wstep. wstep. try rewrite (sx32_of_Z (A + -1)) by lia.
    urun_to 0x170fc%Z. wstep; lit_store.
    urun_to 0x17114%Z. wstep; lit_store. wstep; lit_store. wstep; lit_store.
    assert (EMK : Z_to_bv 64 (-2147483647) = MASK) by (apply Lib.ZBridge.Z_to_bv_eqm; reflexivity). rewrite EMK in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| unfold EHEAD1; rewrite GM; assumption| unfold EHEAD2; rewrite GM; exact EH2'| assumption| exact LEN2
      | unfold cimg_mem; cbn [ci_segs ci_got ci_crc ci_crcx ci_stderrp S0C]; split; [|split; [|split]]; assumption
      | assumption| exact C904'| assumption| assumption| assumption| assumption| assumption| assumption| assumption| assumption| assumption
      | exact MI3| assumption| assumption].
  Qed.
End U0SMP.
End ACeilS1.
