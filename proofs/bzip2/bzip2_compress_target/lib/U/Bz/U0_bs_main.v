(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 DecTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_msV.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
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
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.
Strategy 1000 [ms_ro_init ms_sh_shift ms_sh_pass ms_shell].

Ltac shell_pass SI h h3 roX ftX RKX MONO ROX FTB MIX FVX FAX FFX :=
  enter_with (SI h h3 roX ftX);
    [st_eq| lia| reflexivity| exact RKX| exact MONO| exact ROX| exact FTB| exact MIX| exact FVX| exact FAX| exact FFX| apply munch_refl| apply wmono_refl|].
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs4 BzIncs CmpCut CmpCut0 CmpSmKit2 CmpSmKit20 CmpHmKit U0_bs_mainS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition U_junkw (J : list byte) (k : Z) : zarr :=
  zarr_of_list (map (fun i => bv_unsigned (jw J (Z.of_nat i))) (seq 0 (Z.to_nat k))).
Lemma U_junkw_get : forall J k i, (0 <= i < k)%Z -> zget (U_junkw J k) i = bv_unsigned (jw J i).
Proof.
  intros J k i Hi. unfold U_junkw.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia. rewrite zget_of_list by (rewrite length_map, length_seq; lia).
  erewrite nth_error_nth; [reflexivity|]. rewrite nth_error_map, nth_error_seq by lia. cbn [option_map]. f_equal. f_equal. f_equal. lia.
Qed.
Lemma U_zw32_of_junk : forall segs m A k (J : list byte), rw_cells segs m A [CB (Z.to_nat (4 * k)) J] -> (0 <= k)%Z ->
  u32arr segs m A (zw32 (U_junkw J k) k).
Proof.
  intros segs m A k J H Hk.
  replace (zw32 (U_junkw J k) k) with (ovw znew J k); [apply (ovw_init segs _ _ k _ H Hk)|].
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (Z.to_nat k)) as [L|G].
  - replace i with (Z.to_nat (Z.of_nat i)) by lia. rewrite ovw_nth_raw, zw32_nth by lia. rewrite zdef_znew.
    rewrite U_junkw_get by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite ovw_length_nat; lia). rewrite (proj2 (nth_error_None _ _)) by (rewrite zw32_length_nat; lia). reflexivity.
Qed.

Definition U_bigN (qoff nb : Z) (ro : zarr) (i : Z) (s : mss) : Prop :=
  forall k, (k < 256)%nat -> let s' := ms_step1 k qoff nb (zget ro i) 0 s in s_exit s' = false -> (0 <= s_nqs s' /\ s_nqs s' + nb <= 2147483647)%Z.

Section S0MS.
  Variable X : msenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X.
  Notation usp := (bv_unsigned (me_sp X)). Notation p := (bv_unsigned (me_sp X) - 5008)%Z.
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation E := (me_E X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).

  Definition WBIG : list (Z * Z) := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 262148); (p + 8, p + 2644); (p + 3668, p + 4904)]%Z.

  Definition U_bigs_spec : Prop := forall (cnt : nat) (i b nqs : Z) (a1 a2 ft bd cs ce sl sh sd nl nh nd ro : zarr) (Jlo Jhi Jd : list byte) (nx : list word)
      (w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288 : word)
      (x0 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x18 x20 x26 x27 x28 x29 x30 : word) (me m : word -> option byte),
    let s := MSS a1 a2 ft bd cs ce b nqs (MQL sl sh sd nl nh nd) false in
    Z.of_nat cnt = (256 - i)%Z -> (0 <= i <= 255)%Z -> (0 <= b < 2147483648)%Z ->
    (forall k, i + Z.of_nat k <= 255 -> let s' := ms_bigs k ro qo n i s in s_exit s' = false -> bigF qo n ro (i + Z.of_nat k) s')%Z ->
    (forall k, i + Z.of_nat k <= 255 -> let s' := ms_bigs k ro qo n i s in s_exit s' = false -> U_bigN qo n ro (i + Z.of_nat k) s')%Z ->
    zbok a1 -> zbok a2 -> zbok bd -> pr n a1 0 (n - 1) ->
    Z.of_nat (length Jlo) = 400%Z -> Z.of_nat (length Jhi) = 400%Z -> Z.of_nat (length Jd) = 400%Z -> Z.of_nat (length nx) = 9%Z ->
    u8arr s0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m FT (zw32 ft 65537) ->
    u8arr s0segs m (p + 2388) (zb8 bd 256) -> u32arr s0segs m (p + 1364) (zw32 cs 256) -> u32arr s0segs m (p + 340) (zw32 ce 256) ->
    u32arr s0segs m (p + 4504) (ovw sl Jlo 100) -> u32arr s0segs m (p + 4104) (ovw sh Jhi 100) -> u32arr s0segs m (p + 3704) (ovw sd Jd 100) ->
    u32arr s0segs m (p + 3668) nx -> u32arr s0segs m (p + 2644) (zw32 ro 256) ->
    rw_cells s0segs m (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 w96 w104 w112)) ->
    rw_cells s0segs m (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)) ->
    rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] -> rw_cells s0segs m 210296 [CB 56 incs_bytes] ->
    mem_inv s0segs m -> munch WBIG me m -> wmono s0segs me m ->
    apart FT 262148 210296 56 -> apart A1 ARR1_SIZE 210296 56 -> apart A2 ARR2_SIZE 210296 56 ->
    (forall m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30 : word),
      ms_bigs cnt ro qo n i s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') false -> (0 <= b' <= b)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd' 256) -> u32arr s0segs m' (p + 1364) (zw32 cs' 256) -> u32arr s0segs m' (p + 340) (zw32 ce' 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WBIG me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                            y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22104) fc None m' (seg_rom s0segs))) ->
    (forall m' (a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' : zarr) (nx' : list word) (b' nqs' : Z)
            (v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288 : word)
            (y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      ms_bigs cnt ro qo n i s = MSS a1' a2' ft' bd' cs' ce' b' nqs' (MQL sl' sh' sd' nl' nh' nd') true -> (-2147483648 < b' < 0)%Z ->
      zbok a1' -> zbok a2' -> zbok bd' -> pr n a1' 0 (n - 1) -> Z.of_nat (length nx') = 9%Z ->
      u8arr s0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr s0segs m' A2 (zb8 a2' ARR2_SIZE) -> u32arr s0segs m' FT (zw32 ft' 65537) ->
      u8arr s0segs m' (p + 2388) (zb8 bd' 256) -> u32arr s0segs m' (p + 1364) (zw32 cs' 256) -> u32arr s0segs m' (p + 340) (zw32 ce' 256) ->
      u32arr s0segs m' (p + 4504) (ovw sl' Jlo 100) -> u32arr s0segs m' (p + 4104) (ovw sh' Jhi 100) -> u32arr s0segs m' (p + 3704) (ovw sd' Jd 100) ->
      u32arr s0segs m' (p + 3668) nx' -> u32arr s0segs m' (p + 2644) (zw32 ro 256) ->
      rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA v40 v48 v64 v72 v96 v104 v112)) ->
      rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288)) ->
      rw_cells s0segs m' (p + 336) [C4 (Z_to_bv 64 b')] -> rw_cells s0segs m' 210296 [CB 56 incs_bytes] ->
      mem_inv s0segs m' -> munch WBIG me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 b') y8
                            y9 y10 y11 y12 y13 y14 y15 y16
                            (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22114) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 i) x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 nqs) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32)
                          x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20dfc) fc None m (seg_rom s0segs)).
  Hypothesis S0_bigs : U_bigs_spec.

  Ltac lit_store8 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    end.
  Ltac urun_ls p := urun_to p || (urun; lit_store8; urun_ls p).

  Lemma U_bs_setup : forall (x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word)
      (w24 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
       w232 w240 w248 w256 w264 w272 w280 w288 w296 : word) (me m : word -> option byte),
    rw_cells s0segs m (p + 8) [C8 (Z_to_bv 64 (n * budget_q)); C8 (Z_to_bv 64 E); C8 w24; C8 (Z_to_bv 64 (n - 1));
                               C8 w40; C8 w48; C8 (Z_to_bv 64 0); C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112] ->
    rw_cells s0segs m (p + 120) [C8 w120; C8 w128; C8 w136; C8 w144; C8 w152; C8 w160; C8 w168; C8 w176; C8 w184;
                                 C8 w192; C8 w200; C8 w208; C8 w216; C8 (Z_to_bv 64 (18446744073709551615 - A2)); C8 w232; C8 w240; C8 w248; C8 w256;
                                 C8 w264; C8 w272; C8 w280; C8 w288; C8 w296;
                                 C8 (Z_to_bv 64 FT); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (A2 + qo)); C8 (Z_to_bv 64 (18446744073709551615 - FT))] ->
    rw_cells s0segs m 0x320e8 [C8 (Z_to_bv 64 0x32098)] -> rw_cells s0segs m 0x32098 [C8 (me_sv X)] -> mem_inv s0segs m ->
    munch [(p + 8, p + 336)]%Z me m -> wmono s0segs me m ->
    (forall m', rw_cells s0segs m' (p + 8) (sca_cells X (mkSCA w40 w48 w64 w72 w96 w104 w112)) ->
       rw_cells s0segs m' (p + 120) (scb_cells X (mkSCB w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288)) ->
       rw_cells s0segs m' 0x320e8 [C8 (Z_to_bv 64 0x32098)] -> rw_cells s0segs m' 0x32098 [C8 (me_sv X)] -> mem_inv s0segs m' ->
       munch [(p + 8, p + 336)]%Z me m' -> wmono s0segs me m' ->
       evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp (Z_to_bv 64 (p + 1364)) (Z_to_bv 64 (p + 340)) (Z_to_bv 64 65535) x7 x8
                             (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - (p + 340))) (Z_to_bv 64 2147483647) (Z_to_bv 64 0) x13
                             (Z_to_bv 64 (p + 4504)) (Z_to_bv 64 (p + 4104)) (Z_to_bv 64 (p + 3704))
                             (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 (Z_to_bv 64 0) (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152)
                             (Z_to_bv 64 32) x26 x27 x28 x29 x30)
                        F (Z_to_bv 64 0x20dfc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
                          (Z_to_bv 64 A1) x18 (Z_to_bv 64 A2) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20d24) fc None m (seg_rom s0segs)).
  Proof.
    intros x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
      w24 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
      w232 w240 w248 w256 w264 w272 w280 w288 w296 me m SA SB G1 G2 MI MU WM K.
    msenv_open XOK.
    urun_ls 0x20dfc%Z. lit_store8.
    replace (Z.land A1 3) with 0%Z in SB by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm) end;
      [st_eq| unfold sca_cells; exact SA| unfold scb_cells; exact SB| exact G1| exact G2| assumption| assumption| assumption].
  Qed.


  Lemma U_bs_exitF : forall (x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word)
      (sa : sca) (sb : scb) (b : Z) (m : word -> option byte),
    (0 <= b < 2147483648)%Z ->
    rw_cells s0segs m (p + 8) (sca_cells X sa) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] ->
    mem_inv s0segs m ->
    (forall (y0 y4 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 : word),
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 y7 (Z_to_bv 64 E) y9 y10 y11 y12 y13 y14 y15 y16
                            x17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x22130) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x22104) fc None m (seg_rom s0segs)).
  Proof.
    intros x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 sa sb b m Hb SA SB BU MI K.
    msenv_open XOK. unfold sca_cells, scb_cells in *.
    urun.
    if_cases Kb; zify_cond_z Kb; [exfalso; lia|].
    enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); st_eq.
  Qed.

  Lemma U_bs_exitT : forall (x0 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word)
      (sa : sca) (sb : scb) (b : Z) (m : word -> option byte),
    (-2147483648 <= b < 0)%Z ->
    rw_cells s0segs m (p + 8) (sca_cells X sa) -> rw_cells s0segs m (p + 120) (scb_cells X sb) -> rw_cells s0segs m (p + 336) [C4 (Z_to_bv 64 b)] ->
    rw_cells s0segs m (E + 24) [C8 (Z_to_bv 64 A1); C8 (Z_to_bv 64 A2)] -> mem_inv s0segs m ->
    (forall (y0 y4 y5 y6 y18 y19 y20 y14 y15 y16 : word),
      evt s0segs Q (MS (mkR y0 (Z_to_bv 64 p) gp tp y4 y5 y6 (Z_to_bv 64 b) (Z_to_bv 64 E)
                            (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 FT) (Z_to_bv 64 n) (Z_to_bv 64 0) y14 y15 y16
                            x17 y18 y19 y20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x20410) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 b) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x22114) fc None m (seg_rom s0segs)).
  Proof.
    intros x0 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 sa sb b m Hb SA SB BU EH MI K.
    msenv_open XOK. unfold sca_cells, scb_cells in *.
    urun.
    if_cases Kb; zify_cond_z Kb; [| exfalso; change 18446744073709551615%Z with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by lia;
       rewrite <- (Z.mod_unique b (2^64) (-1) (b + 2^64)) in Kb by lia; lia].
    urun_to 0x20410%Z.
    enter_with (K _ _ _ _ _ _ _ _ _ _); st_eq.
  Qed.


  Ltac u_stk_add ST K :=
    lazymatch type of K with stk _ _ ?b' ?c =>
    lazymatch type of ST with stk ?segs ?m ?lo ?b =>
      let H := fresh in pose proof (stk_merge segs m lo b c ST ltac:(replace b with b' by lia; exact K) ltac:(lia)) as H; clear ST K; rename H into ST end end.
  Ltac u_stk_eat ST H :=
    let K := fresh "Kst" in
    first [ pose proof (stk_of_u8arr s0segs _ _ _ H) as K; rewrite ?zb8_length_nat, ?ovb_length_nat in K
          | pose proof (stk_of_u32arr s0segs _ _ _ H) as K; rewrite ?zw32_length_nat, ?ovw_length_nat in K
          | pose proof (stk_of_rw_cells s0segs _ _ _ H) as K; unfold sca_cells, scb_cells in K;
            cbn [cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in K ];
    u_stk_add ST K; clear H.
  Ltac cb_len H L :=
    let W := fresh in pose proof (proj1 (proj1 H)) as W; cbn in W; destruct W as [L _].

  Lemma U_bs_main_s : U_bs_main_spec X Q.
  Proof using XOK XSEP S0_bigs.
    unfold U_bs_main_spec.
    intros a1 a2 ft bd ro j0 jce jcs jnx jsd jhi jlo
      w24 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
      w232 w240 w248 w256 w264 w272 w280 w288 w296
      x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 me m
      HA1 HA2 HFT A1OK A2OK BDOK PR HB BF BN AR1 AR2 FTB J0 SA SB BU CE CS BD RO NX SD SH SL EH CI MI MU WM KF KB.
    msenv_open XOK. pose proof XSEP as SEPH. unfold msenv_sep, apartm in SEPH. cps_destruct SEPH as (AP12 & AP1F & AP2F & AE1 & AE2 & AEF).
    bz_params.
    pose proof CI as CI0. unfold cimg_mem in CI0. cbn [S0C ci_segs ci_got ci_stderrp ci_crc ci_crcx] in CI0.
    cps_destruct CI0 as (G1 & G24 & G2 & CRC). clear G24.
    lazymatch type of CRC with rw_cells _ _ _ (?c1 :: ?rest) => change (c1 :: rest) with ([c1] ++ rest) in CRC end.
    apply (proj1 (rw_cells_app_iff s0segs m _ _ _)) in CRC. destruct CRC as [_ INC]. cbn [cells_size csize] in INC.
    lazymatch type of INC with rw_cells _ _ ?a _ => replace a with 0x33578%Z in INC by lia end.
    cb_len SD LJd. cb_len SH LJh. cb_len SL LJl.
    eapply (U_bs_setup x0 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x18 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
              w24 w40 w48 w64 w72 w80 w88 w96 w104 w112 w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216
              w232 w240 w248 w256 w264 w272 w280 w288 w296 m m SA SB G1 G2 MI (munch_refl _ _) (wmono_refl _ _)).
    intros m1 SA1 SB1 G1' G2' MI1 MU1 WM1.
    clear SA SB G1 G2 MI.
    unfold WMAIN in MU.
    transport_after_call s0segs m m1 MU1 WM1.
    pose proof (cimg_transportK0 S0C _ _ _ _ eq_refl CI MU1 WM1
      ltac:(unfold w_img_apartK, IMG_LO3; repeat (apply Forall_cons; [cbn [fst snd ci_hi S0C]; lia|]); apply Forall_nil)) as CI1.
    clear CI.
    clear MU1 WM1.
    pose proof (U_zw32_of_junk s0segs m1 (p + 1364) 256 jcs CS ltac:(lia)) as CSw.
    pose proof (U_zw32_of_junk s0segs m1 (p + 340) 256 jce CE ltac:(lia)) as CEw.
    pose proof (ovw_init s0segs m1 (p + 4504) 100 jlo SL ltac:(lia)) as SLw.
    pose proof (ovw_init s0segs m1 (p + 4104) 100 jhi SH ltac:(lia)) as SHw.
    pose proof (ovw_init s0segs m1 (p + 3704) 100 jsd SD ltac:(lia)) as SDw.
    pose proof (ovw_init s0segs m1 (p + 3668) 9 jnx NX ltac:(lia)) as NXw.
    clear CS CE SL SH SD NX.
    set (CSJ := U_junkw jcs 256) in *. set (CEJ := U_junkw jce 256) in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_bigs 256%nat 0%Z (n * budget_q)%Z 0%Z a1 a2 ft bd CSJ CEJ znew znew znew znew znew znew ro jlo jhi jsd (ovw znew jnx 9)
                    w40 w48 w64 w72 w96 w104 w112 w128 w136 w144 w152 w168 w176 w184 w208 w232 w240 w248 w256 w288
                    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mm mm) end;
      [st_eq| reflexivity| lia| lia| intros k Hk; exact (BF CSJ CEJ znew znew znew k Hk)
      | intros k Hk s' Ex j Hj; exact (BN CSJ CEJ znew znew znew k Hk Ex j Hj)
      | exact A1OK| exact A2OK| exact BDOK| exact PR| lia| lia| lia| rewrite ovw_length_nat; lia
      | exact AR1| exact AR2| exact FTB| exact BD| exact CSw| exact CEw| exact SLw| exact SHw| exact SDw| exact NXw| exact RO
      | exact SA1| exact SB1| exact BU| exact INC| exact MI1| apply munch_refl| apply wmono_refl
      | unfold apart; lia| unfold apart; lia| unfold apart; lia| |].
    - intros m2 a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' nx' b' nqs'
        v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
        y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y26 y27 y28 y29 y30.
      intros EB Hb' OK1 OK2 OKbd PR' Lnx' AR1' AR2' FTB' BD' CS' CE' SL' SH' SD' NX' RO' SA' SB' BU' INC' MI2 MU2 WM2.
      clear AR1 AR2 FTB BD CSw CEw SLw SHw SDw RO NXw SA1 SB1 BU INC MI1.
      pose proof (cimg_transportK0 S0C _ _ _ _ eq_refl CI1 MU2 WM2
        ltac:(unfold w_img_apartK, IMG_LO3; repeat (apply Forall_cons; [cbn [fst snd ci_hi S0C]; lia|]); apply Forall_nil)) as CI2.
      unfold WBIG in MU2.
      transport_after_call s0segs m1 m2 MU2 WM2.
      assert (MUm : munch (WMAIN X) me m2) by (unfold WMAIN; exact MU).
      assert (WMm : wmono s0segs me m2) by exact WM.
      assert (ST : stk s0segs m2 p (p + 4904)).
      { pose proof (stk_of_rw_cells s0segs _ _ _ J0) as ST. cbn [cells_size csize Nat.add] in ST.
        u_stk_eat ST SA'. u_stk_eat ST SB'. u_stk_eat ST BU'. u_stk_eat ST CE'. u_stk_eat ST CS'. u_stk_eat ST BD'. u_stk_eat ST RO'.
        u_stk_eat ST NX'. u_stk_eat ST SD'. u_stk_eat ST SH'. u_stk_eat ST SL'.
        lazymatch type of ST with stk _ _ _ ?hi => replace (p + 4904)%Z with hi by lia end. exact ST. }
      enter_with (U_bs_exitF y0 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20
                    (Z_to_bv 64 nqs') (Z_to_bv 64 (p + 2388)) (Z_to_bv 64 256) (Z_to_bv 64 2097152) (Z_to_bv 64 32) y26 y27 y28 y29 y30
                    (mkSCA v40 v48 v64 v72 v96 v104 v112) (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288) b' m2);
        [st_eq| lia| exact SA'| exact SB'| exact BU'| exact MI2|].
      intros z0 z4 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30.
      eapply (KF m2 a1' a2' ft' bd' cs' ce' CSJ CEJ b' nqs' (MQL sl' sh' sd' nl' nh' nd')
                 z0 z4 z5 z6 z7 z9 z10 z11 z12 z13 z14 z15 z16 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30);
        [exact EB| lia| exact OK1| exact OK2| exact AR1'| exact AR2'| exact FTB'| exact ST| exact EH| exact CI2| exact MI2| exact MUm| exact WMm].
    - intros m2 a1' a2' ft' bd' cs' ce' sl' sh' sd' nl' nh' nd' nx' b' nqs'
        v40 v48 v64 v72 v96 v104 v112 v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288
        y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30.
      intros EB Hb' OK1 OK2 OKbd PR' Lnx' AR1' AR2' FTB' BD' CS' CE' SL' SH' SD' NX' RO' SA' SB' BU' INC' MI2 MU2 WM2.
      clear AR1 AR2 FTB BD CSw CEw SLw SHw SDw RO NXw SA1 SB1 BU INC MI1.
      pose proof (cimg_transportK0 S0C _ _ _ _ eq_refl CI1 MU2 WM2
        ltac:(unfold w_img_apartK, IMG_LO3; repeat (apply Forall_cons; [cbn [fst snd ci_hi S0C]; lia|]); apply Forall_nil)) as CI2.
      unfold WBIG in MU2.
      transport_after_call s0segs m1 m2 MU2 WM2.
      assert (MUm : munch (WMAIN X) me m2) by (unfold WMAIN; exact MU).
      assert (WMm : wmono s0segs me m2) by exact WM.
      assert (ST : stk s0segs m2 p (p + 4904)).
      { pose proof (stk_of_rw_cells s0segs _ _ _ J0) as ST. cbn [cells_size csize Nat.add] in ST.
        u_stk_eat ST SA'. u_stk_eat ST SB'. u_stk_eat ST BU'. u_stk_eat ST CE'. u_stk_eat ST CS'. u_stk_eat ST BD'. u_stk_eat ST RO'.
        u_stk_eat ST NX'. u_stk_eat ST SD'. u_stk_eat ST SH'. u_stk_eat ST SL'.
        lazymatch type of ST with stk _ _ _ ?hi => replace (p + 4904)%Z with hi by lia end. exact ST. }
      enter_with (U_bs_exitT y0 y4 y5 y6 y8 y9 y10 y11 y12 y13 y14 y15 y16 (Z_to_bv 64 A1) y18 (Z_to_bv 64 A2) y20
                    y21 y22 y23 y24 y25 y26 y27 y28 y29 y30
                    (mkSCA v40 v48 v64 v72 v96 v104 v112) (mkSCB v128 v136 v144 v152 v168 v176 v184 v208 v232 v240 v248 v256 v288) b' m2);
        [st_eq| lia| exact SA'| exact SB'| exact BU'| exact EH| exact MI2|].
      intros z0 z4 z5 z6 z18 z19 z20 z14 z15 z16.
      eapply (KB m2 a1' a2' ft' bd' cs' ce' CSJ CEJ b' nqs' (MQL sl' sh' sd' nl' nh' nd')
                 z0 z4 z5 z6 (Z_to_bv 64 b') z14 z15 z16 z18 z19 z20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30);
        [exact EB| lia| exact OK1| exact OK2| exact AR1'| exact AR2'| exact FTB'| exact ST| exact EH| exact CI2| exact MI2| exact MUm| exact WMm].
  Qed.


End S0MS.

Lemma U_bs_main : (forall X Q, msenv_ok X -> msenv_sep X -> U_bigs_spec X Q) ->
  forall X Q, msenv_ok X -> msenv_sep X -> U_bs_main_spec X Q.
Proof. intros HB X Q XOK XSEP. exact (U_bs_main_s X Q XOK XSEP (HB X Q XOK XSEP)). Qed.

End ACeilS1.
