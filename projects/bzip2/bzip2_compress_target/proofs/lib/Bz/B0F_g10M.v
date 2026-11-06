(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzDefs BzModel BzTac BzTac2 BzInv BzTables BzContracts DecCut DecTac DecTac2 DecAux.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzLemmasT BzLemmasT2 BzWalkArith BzWalkArith2 BzWalkArith3 BzWalkArith4 BzDU9 DecAux12F BzDU5 BzDUM BzDU11 BzDU12F BzDU12S DecAux12S BzDOKS DecTacF3 DecCutF DecTacF DecTacFR.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU9 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDUM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU11 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12F OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecAux12S OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOKS OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFR.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecCutFB DecTacFB DecTacFRB B0F_decV DecTacSB.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecCutFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacFRB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.B0F_decV OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.DecTacSB.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import LinSplit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import NatLit.
Local Ltac Zify.zify_pre_hook ::= NatLit.natlen_ctx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require NormFast FLiaA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= FLiaA.lia_f.
Local Ltac BzTac.bz32 ::= NormFast.bz32_m.
Local Ltac BzTac2.bz32l ::= NormFast.bz32l_m.
Local Ltac Zify.zify_pre_hook ::= NormFast.nf_pre_natlen.
Local Ltac DecCutF.unset_Z ::= NormFast.unset_Z_subst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require DecTac2.
Local Ltac AsanKit.a_norm ::= DecTac2.lit_store_fix.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import S0_glue10K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_g10A.

Section ACeilS1. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Lemma land_div1_byte : forall bb b, (0 <= bb)%Z -> (0 <= b < 256)%Z -> Z.land ((bb * 256 + b) / 1) 255 = b.
Proof.
  intros bb b Hbb Hb. rewrite Z.div_1_r. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8)%Z with 256%Z.
  rewrite Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
End ACeilS1.

(* [comment removed for export] *)
Definition parked (X : Prop) : Prop := X.
Ltac park H := lazymatch type of H with ?T => change T with (parked T) in H end.
Ltac g_frh FRH MUL WML :=
  unfold parked in FRH; eapply (rw_cells_transport b0segs _ _ _ _ _ FRH MUL WML);
  cbv [disjoint_from fst snd]; cbn [cells_size csize length Nat.add]; lia.

(* [comment removed for export] *)
Ltac g_head Hstrm := hd_proj; rewrite ?Hstrm; lazymatch goal with H : rw_cells b0segs ?mm ?S0 _ |- rw_cells b0segs ?mm ?S0 _ => rw_by H end.
Ltac g_strm Hsrc Hlen := bs_proj; rewrite ?Hsrc, ?Hlen; lazymatch goal with H : rw_cells b0segs ?mm ?S0 _ |- rw_cells b0segs ?mm ?S0 _ => rw_by H end.
Ltac g_mi := lazymatch goal with H : mem_inv b0segs ?mm |- mem_inv b0segs ?mm => exact H end.

Section ACeilS2. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition W10m (A : act14) : list ivl :=
  [(b_s (a_cx A), b_s (a_cx A) + 68)%Z; (b_strm (a_cx A), b_strm (a_cx A) + 20)%Z; (a_P A, a_P A + 128)%Z].
Section M.
  Variable A : act14.
  Variable Q : machine_state -> Prop.
  Variable m0 : word -> option byte.
  Notation S := (b_s (a_cx A)).
  Notation strm := (b_strm (a_cx A)).
  Notation src := (b_src (a_cx A)).
  Notation len := (b_len (a_cx A)).
  Notation P := (a_P A).
  Notation payload := (a_payload A).
  Hypothesis GL : g10_lin A.
  Hypothesis GS : (0 < src /\ src + len <= alloc_ceiling /\ 0 <= len < 2 ^ 27 /\ Z.of_nat (length payload) = len)%Z.
  Hypothesis ANS : sanchor S (a_shs A).
  (* [comment removed for export] *)
  Hypothesis ANT : sanchor strm (a_sht A).
  Hypothesis SEPst : (S + 64144 <= strm \/ strm + 80 <= S)%Z.
  Hypothesis SEPsrc : (S + 64144 <= src \/ src + len <= S)%Z.
  Hypothesis SEPtsrc : (strm + 80 <= src \/ src + len <= strm)%Z.
  Hypothesis SHS : shzW b0segs (W10 A) m0 S (S + 64144).
  Hypothesis SHT : shzW b0segs (W10 A) m0 strm (strm + 80).
  Hypothesis SHP : shpW b0segs (W10 A) m0 src (src + len).

  (* [comment removed for export] *)
  Definition B0F_g10_KX (OUT : Z -> Prop) (m : word -> option byte) (h : dsh) (b : bzs) (lbl : Z) (x2 gp tp x8 : word) (Fr : bvmap 5 word) (fc : bv 32)
      (w0 w8 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 : word)
      (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 : word) : Prop :=
    forall (rc : Z) (m' : word -> option byte) (bsBuff' nn ai' : Z) (til' tih' : word) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
      let h' := DSH (sh_strm h) lbl (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) bsBuff' 0 nn (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
      rw_cells b0segs m' S (HEAD_CELLS h') -> (0 <= bsBuff' < 2 ^ 32)%Z -> (0 <= nn < 2 ^ 32)%Z ->
      rw_cells b0segs m' strm (STRM_CELLS (bupd b ai' til' tih')) -> (0 <= ai' <= bs_ai b)%Z ->
      bytes_at b0segs m' src payload ->
      B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
      B0FH A m' w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
      stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10m A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
      (rc = 0 \/ rc = -5)%Z -> OUT rc ->
      evt b0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 rc) y11 y12 y13 y14 y15 y16 y17 y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31) Fr (Z_to_bv 64 0xafb90) fc None m' (seg_rom b0segs)).

  (* [comment removed for export] *)
  Lemma B0F_g10_M1 : forall (x1 x2 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
      (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h : dsh) (b : bzs)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
      (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 : word),
    munch (W10 A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m S (HEAD_CELLS h) -> sh_strm h = strm -> sh_bsLive h = 0%Z -> (0 <= sh_bsBuff h < 2 ^ 23)%Z -> (0 <= sh_n h < 2 ^ 32)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells b0segs m strm (STRM_CELLS b) -> bs_src b = src -> bs_len b = len -> (0 <= bs_ai b <= len)%Z ->
    bs_til b = Z_to_bv 64 (len - bs_ai b) ->
    bytes_at b0segs m src payload ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    B0F_g10_KX (fun rc => (rc = 0 /\ bs_ai b = 0) \/ (rc = -5 /\ exists b8, nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 /\ bv_unsigned b8 <> 66))%Z
      m h b 10 x2 gp tp x8 Fr fc w0 w8 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 ->
    (forall (m' : word -> option byte) (b8 : byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
        let h' := DSH (sh_strm h) 10 (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) (sh_bsBuff h * 256 + 66)%Z 0 (sh_n h) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        rw_cells b0segs m' S (HEAD_CELLS h') ->
        nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 -> bv_unsigned b8 = 66%Z ->
        rw_cells b0segs m' strm (STRM_CELLS (bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b))) -> (1 <= bs_ai b)%Z ->
        bytes_at b0segs m' src payload ->
        B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
        B0FH A m' w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
        stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10m A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) y11 y12 y13 y14 y15 y16 y17 y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31) Fr (Z_to_bv 64 0xa9da4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xa9d1c) fc None m (seg_rom b0segs)).
  Proof.
    intros until w752. intros MU WM HD Hstrm HBL HBB HN L1 L2 L3 STRM Hsrc Hlen Hai TIL PAY FRL FRH ST MI HX HN'.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    cps_pose GS as (G1 & G2 & G3 & G4).
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANT) as STRM8. pose proof (proj2 ANT : saddr strm (a_sht A)) as ANT0.
    unfold W10 in MU, SHS, SHT, SHP. unfold B0F_g10_KX in HX.
    pose proof (SEPst : id _) as BXst. pose proof (SEPsrc : id _) as BXsrc. pose proof (SEPtsrc : id _) as BXtsrc.
    rewrite Hstrm, HBL in HD. rewrite TIL, Hsrc, Hlen in STRM.
    set (ai := bs_ai b) in *. set (bb := sh_bsBuff h) in *.
    pose proof (munch_refl (W10m A) m) as MUL. pose proof (wmono_refl b0segs m) as WML. unfold W10m in MUL.
    (* [comment removed for export] *)
    bstep. park FRH.
    brun. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX 0%Z _ bb (sh_n h) ai (Z_to_bv 64 (len - ai)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | left; split; [reflexivity| clear - K2 Hai G3; zb_masks; mlia] ]. }
    assert (AI1 : (1 <= ai)%Z) by (clear - K2 Hai G3; zb_masks; mlia). clear K2.
    (* [comment removed for export] *)
    brun_to 0xaa674%Z. forget_reg 23%Z wj23. forget_reg 25%Z wj25.
    ack_rd (src + (len - ai))%Z 1%Z.
    brun_to 0xaa67c%Z. ack_merge.
    brun_to 0xaa680%Z.
    destruct (nth_error_ok payload (len - ai)%Z (length payload) eq_refl ltac:(lia)) as [b8 NTH].
    pose proof (u8ro_read b0segs _ src payload (len - ai)%Z b8 _ PAY NTH ltac:(lia) eq_refl) as RD.
    (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => first [ constr_eq e (src + (len - ai))%Z | replace e with (src + (len - ai))%Z by lia ] end).
    wstepl. clear RD.
    pose proof (bv_unsigned_in_range 8 b8) as Rb8; unfold bv_modulus in Rb8; cbn in Rb8.
    (* [comment removed for export] *)
    brun. if_cases K3; zify_cond_z K3; [| exfalso; clear - K3 Hai G3 AI1; lia]. clear K3.
    lazymatch goal with H : rw_cells _ _ S _ |- _ => rewrite (lor_shl8_byte' bb (bv_unsigned b8)) in H by lia end.
    (* [comment removed for export] *)
    brun. rewrite (land_div1_byte bb (bv_unsigned b8)) by lia.
    if_cases K4; zify_cond_z K4.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX (-5)%Z _ (bb * 256 + bv_unsigned b8)%Z (sh_n h) (ai - 1)%Z (Z_to_bv 64 (len - ai + 1)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | right; split; [reflexivity| exists b8; split; [exact NTH| clear - K4 Rb8; lia]] ]. }
    assert (E8 : bv_unsigned b8 = 66%Z) by (clear - K4 Rb8; lia). clear K4.
    brun_to 0xa9da4%Z.
    eapply evt_eq; [ | eapply (HN' _ b8) ];
      [ st_eq | rewrite <- E8; g_head Hstrm | exact NTH | exact E8 | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_g10_M2 : forall (x1 x2 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
      (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h : dsh) (b : bzs)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
      (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 : word),
    munch (W10 A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m S (HEAD_CELLS h) -> sh_strm h = strm -> sh_bsLive h = 0%Z -> (0 <= sh_bsBuff h < 2 ^ 23)%Z -> (0 <= sh_n h < 2 ^ 32)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells b0segs m strm (STRM_CELLS b) -> bs_src b = src -> bs_len b = len -> (0 <= bs_ai b <= len)%Z ->
    bs_til b = Z_to_bv 64 (len - bs_ai b) ->
    bytes_at b0segs m src payload ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    B0F_g10_KX (fun rc => (rc = 0 /\ bs_ai b = 0) \/ (rc = -5 /\ exists b8, nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 /\ bv_unsigned b8 <> 90))%Z
      m h b 11 x2 gp tp x8 Fr fc w0 w8 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 ->
    (forall (m' : word -> option byte) (b8 : byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
        let h' := DSH (sh_strm h) 11 (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) (sh_bsBuff h * 256 + 90)%Z 0 (sh_n h) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        rw_cells b0segs m' S (HEAD_CELLS h') ->
        nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 -> bv_unsigned b8 = 90%Z ->
        rw_cells b0segs m' strm (STRM_CELLS (bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b))) -> (1 <= bs_ai b)%Z ->
        bytes_at b0segs m' src payload ->
        B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
        B0FH A m' w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
        stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10m A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) y11 y12 y13 y14 y15 y16 y17 y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31) Fr (Z_to_bv 64 0xa9e2c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xa9da4) fc None m (seg_rom b0segs)).
  Proof.
    intros until w752. intros MU WM HD Hstrm HBL HBB HN L1 L2 L3 STRM Hsrc Hlen Hai TIL PAY FRL FRH ST MI HX HN'.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    cps_pose GS as (G1 & G2 & G3 & G4).
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANT) as STRM8. pose proof (proj2 ANT : saddr strm (a_sht A)) as ANT0.
    unfold W10 in MU, SHS, SHT, SHP. unfold B0F_g10_KX in HX.
    pose proof (SEPst : id _) as BXst. pose proof (SEPsrc : id _) as BXsrc. pose proof (SEPtsrc : id _) as BXtsrc.
    rewrite Hstrm, HBL in HD. rewrite TIL, Hsrc, Hlen in STRM.
    set (ai := bs_ai b) in *. set (bb := sh_bsBuff h) in *.
    pose proof (munch_refl (W10m A) m) as MUL. pose proof (wmono_refl b0segs m) as WML. unfold W10m in MUL.
    (* [comment removed for export] *)
    bstep. park FRH.
    brun. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX 0%Z _ bb (sh_n h) ai (Z_to_bv 64 (len - ai)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | left; split; [reflexivity| clear - K2 Hai G3; zb_masks; mlia] ]. }
    assert (AI1 : (1 <= ai)%Z) by (clear - K2 Hai G3; zb_masks; mlia). clear K2.
    (* [comment removed for export] *)
    brun_to 0xaa37c%Z. forget_reg 23%Z wj23. forget_reg 25%Z wj25.
    ack_rd (src + (len - ai))%Z 1%Z.
    brun_to 0xaa384%Z. ack_merge.
    brun_to 0xaa388%Z.
    destruct (nth_error_ok payload (len - ai)%Z (length payload) eq_refl ltac:(lia)) as [b8 NTH].
    pose proof (u8ro_read b0segs _ src payload (len - ai)%Z b8 _ PAY NTH ltac:(lia) eq_refl) as RD.
    (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => first [ constr_eq e (src + (len - ai))%Z | replace e with (src + (len - ai))%Z by lia ] end).
    wstepl. clear RD.
    pose proof (bv_unsigned_in_range 8 b8) as Rb8; unfold bv_modulus in Rb8; cbn in Rb8.
    (* [comment removed for export] *)
    brun. if_cases K3; zify_cond_z K3; [| exfalso; clear - K3 Hai G3 AI1; lia]. clear K3.
    lazymatch goal with H : rw_cells _ _ S _ |- _ => rewrite (lor_shl8_byte' bb (bv_unsigned b8)) in H by lia end.
    (* [comment removed for export] *)
    brun. rewrite (land_div1_byte bb (bv_unsigned b8)) by lia.
    if_cases K4; zify_cond_z K4.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX (-5)%Z _ (bb * 256 + bv_unsigned b8)%Z (sh_n h) (ai - 1)%Z (Z_to_bv 64 (len - ai + 1)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | right; split; [reflexivity| exists b8; split; [exact NTH| clear - K4 Rb8; lia]] ]. }
    assert (E8 : bv_unsigned b8 = 90%Z) by (clear - K4 Rb8; lia). clear K4.
    brun_to 0xa9e2c%Z.
    eapply evt_eq; [ | eapply (HN' _ b8) ];
      [ st_eq | rewrite <- E8; g_head Hstrm | exact NTH | exact E8 | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_g10_M3 : forall (x1 x2 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
      (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h : dsh) (b : bzs)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
      (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 : word),
    munch (W10 A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m S (HEAD_CELLS h) -> sh_strm h = strm -> sh_bsLive h = 0%Z -> (0 <= sh_bsBuff h < 2 ^ 23)%Z -> (0 <= sh_n h < 2 ^ 32)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells b0segs m strm (STRM_CELLS b) -> bs_src b = src -> bs_len b = len -> (0 <= bs_ai b <= len)%Z ->
    bs_til b = Z_to_bv 64 (len - bs_ai b) ->
    bytes_at b0segs m src payload ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    B0F_g10_KX (fun rc => (rc = 0 /\ bs_ai b = 0) \/ (rc = -5 /\ exists b8, nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 /\ bv_unsigned b8 <> 104))%Z
      m h b 12 x2 gp tp x8 Fr fc w0 w8 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 ->
    (forall (m' : word -> option byte) (b8 : byte) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y23 y24 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
        let h' := DSH (sh_strm h) 12 (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) (sh_bsBuff h * 256 + 104)%Z 0 (sh_n h) (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        rw_cells b0segs m' S (HEAD_CELLS h') ->
        nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 -> bv_unsigned b8 = 104%Z ->
        rw_cells b0segs m' strm (STRM_CELLS (bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b))) -> (1 <= bs_ai b)%Z ->
        bytes_at b0segs m' src payload ->
        B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
        B0FH A m' w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
        stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10m A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) y11 y12 y13 y14 y15 y16 y17 y18 y19 (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 y24 y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31) Fr (Z_to_bv 64 0xa9eb4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xa9e2c) fc None m (seg_rom b0segs)).
  Proof.
    intros until w752. intros MU WM HD Hstrm HBL HBB HN L1 L2 L3 STRM Hsrc Hlen Hai TIL PAY FRL FRH ST MI HX HN'.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    cps_pose GS as (G1 & G2 & G3 & G4).
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANT) as STRM8. pose proof (proj2 ANT : saddr strm (a_sht A)) as ANT0.
    unfold W10 in MU, SHS, SHT, SHP. unfold B0F_g10_KX in HX.
    pose proof (SEPst : id _) as BXst. pose proof (SEPsrc : id _) as BXsrc. pose proof (SEPtsrc : id _) as BXtsrc.
    rewrite Hstrm, HBL in HD. rewrite TIL, Hsrc, Hlen in STRM.
    set (ai := bs_ai b) in *. set (bb := sh_bsBuff h) in *.
    pose proof (munch_refl (W10m A) m) as MUL. pose proof (wmono_refl b0segs m) as WML. unfold W10m in MUL.
    (* [comment removed for export] *)
    bstep. park FRH.
    brun. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX 0%Z _ bb (sh_n h) ai (Z_to_bv 64 (len - ai)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | left; split; [reflexivity| clear - K2 Hai G3; zb_masks; mlia] ]. }
    assert (AI1 : (1 <= ai)%Z) by (clear - K2 Hai G3; zb_masks; mlia). clear K2.
    (* [comment removed for export] *)
    brun_to 0xaa1e0%Z. forget_reg 23%Z wj23. forget_reg 25%Z wj25.
    ack_rd (src + (len - ai))%Z 1%Z.
    brun_to 0xaa1e8%Z. ack_merge.
    brun_to 0xaa1ec%Z.
    destruct (nth_error_ok payload (len - ai)%Z (length payload) eq_refl ltac:(lia)) as [b8 NTH].
    pose proof (u8ro_read b0segs _ src payload (len - ai)%Z b8 _ PAY NTH ltac:(lia) eq_refl) as RD.
    (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => first [ constr_eq e (src + (len - ai))%Z | replace e with (src + (len - ai))%Z by lia ] end).
    wstepl. clear RD.
    pose proof (bv_unsigned_in_range 8 b8) as Rb8; unfold bv_modulus in Rb8; cbn in Rb8.
    (* [comment removed for export] *)
    brun. if_cases K3; zify_cond_z K3; [| exfalso; clear - K3 Hai G3 AI1; lia]. clear K3.
    lazymatch goal with H : rw_cells _ _ S _ |- _ => rewrite (lor_shl8_byte' bb (bv_unsigned b8)) in H by lia end.
    (* [comment removed for export] *)
    brun. rewrite (land_div1_byte bb (bv_unsigned b8)) by lia.
    if_cases K4; zify_cond_z K4.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX (-5)%Z _ (bb * 256 + bv_unsigned b8)%Z (sh_n h) (ai - 1)%Z (Z_to_bv 64 (len - ai + 1)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | right; split; [reflexivity| exists b8; split; [exact NTH| clear - K4 Rb8; lia]] ]. }
    assert (E8 : bv_unsigned b8 = 104%Z) by (clear - K4 Rb8; lia). clear K4.
    brun_to 0xa9eb4%Z.
    eapply evt_eq; [ | eapply (HN' _ b8) ];
      [ st_eq | rewrite <- E8; g_head Hstrm | exact NTH | exact E8 | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0F_g10_M4 : forall (x1 x2 gp tp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x23 x24 x25 x28 x29 x30 x31 : word)
      (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h : dsh) (b : bzs)
      (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 : word)
      (w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 : word),
    munch (W10 A) m0 m -> wmono b0segs m0 m ->
    rw_cells b0segs m S (HEAD_CELLS h) -> sh_strm h = strm -> sh_bsLive h = 0%Z -> (0 <= sh_bsBuff h < 2 ^ 23)%Z -> (0 <= sh_n h < 2 ^ 32)%Z ->
    length (sh_p1 h) = 3%nat -> length (sh_p2 h) = 3%nat -> length (sh_p3 h) = 3%nat ->
    rw_cells b0segs m strm (STRM_CELLS b) -> bs_src b = src -> bs_len b = len -> (0 <= bs_ai b <= len)%Z ->
    bs_til b = Z_to_bv 64 (len - bs_ai b) ->
    bytes_at b0segs m src payload ->
    B0FL A m w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 ->
    B0FH A m w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
    stk b0segs m (a_lo A) P -> mem_inv b0segs m ->
    B0F_g10_KX (fun rc => (rc = 0 /\ bs_ai b = 0) \/ (rc = -5 /\ exists b8, nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 /\ ~ (49 <= bv_unsigned b8 <= 57)))%Z
      m h b 13 x2 gp tp x8 Fr fc w0 w8 w16 w24 w64 w72 w80 w88 w96 w104 w112 w120 w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 w720 w728 w736 w744 w752 ->
    (forall (m' : word -> option byte) (b8 : byte) (uc : Z) (y1 y5 y6 y7 y12 y13 y14 y15 y16 y18 y21 y23 y25 y28 y29 y30 y31 yw32 yw40 yw48 yw56 : word),
        let h' := DSH (sh_strm h) 13 (sh_soch h) (sh_p1 h) (sh_solen h) (sh_brand h) (sh_p2 h) (sh_rNToGo h) (sh_rTPos h) (sh_bsBuff h * 256 + uc)%Z 0 uc (sh_small h) (sh_p3 h) (sh_cbn h) (sh_verb h) (sh_origPtr h) (sh_tPos h) (sh_k0 h) in
        rw_cells b0segs m' S (HEAD_CELLS h') -> (49 <= uc <= 57)%Z ->
        nth_error payload (Z.to_nat (len - bs_ai b)) = Some b8 -> bv_unsigned b8 = uc ->
        rw_cells b0segs m' strm (STRM_CELLS (bupd b (bs_ai b - 1) (Z_to_bv 64 (len - (bs_ai b - 1))) (bs_tih b))) -> (1 <= bs_ai b)%Z ->
        bytes_at b0segs m' src payload ->
        B0FL A m' w0 w8 w16 w24 yw32 yw40 yw48 yw56 w64 w72 w80 w88 w96 w104 w112 w120 ->
        B0FH A m' w344 w352 w360 w368 w376 w384 w392 w400 w408 w416 w424 w432 w440 w448 w456 w464 w472 w480 w488 w496 w504 w512 w520 w528 (Z_to_bv 64 (a_shs A + 1)) w720 w728 w736 w744 w752 ->
        stk b0segs m' (a_lo A) P -> munch (W10 A) m0 m' -> wmono b0segs m0 m' -> munch (W10m A) m m' -> wmono b0segs m m' -> mem_inv b0segs m' ->
        evt b0segs Q (MS (mkR y1 x2 gp tp y5 y6 y7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) (Z_to_bv 64 uc) y12 y13 y14 y15 y16 (Z_to_bv 64 0) y18 (Z_to_bv 64 (a_shs A + 5)) (Z_to_bv 64 (S + 64036)) y21 (Z_to_bv 64 2147450880) y23 (Z_to_bv 64 (S + 40)) y25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) y28 y29 y30 y31) Fr (Z_to_bv 64 0xaa45c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (Z_to_bv 64 P) (Z_to_bv 64 strm) x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (S + 64036)) x21 (Z_to_bv 64 2147450880) x23 x24 x25 (Z_to_bv 64 S) (Z_to_bv 64 (a_shf A)) x28 x29 x30 x31) Fr (Z_to_bv 64 0xa9eb4) fc None m (seg_rom b0segs)).
  Proof.
    intros until w752. intros MU WM HD Hstrm HBL HBB HN L1 L2 L3 STRM Hsrc Hlen Hai TIL PAY FRL FRH ST MI HX HN'.
    pose proof GL as LIN. unfold g10_lin in LIN. pose proof alloc_ceiling_range as ACR.
    cps_pose GS as (G1 & G2 & G3 & G4).
    pose proof (proj2 ANS : saddr S (a_shs A)) as ANS0. pose proof (proj1 ANT) as STRM8. pose proof (proj2 ANT : saddr strm (a_sht A)) as ANT0.
    unfold W10 in MU, SHS, SHT, SHP. unfold B0F_g10_KX in HX.
    pose proof (SEPst : id _) as BXst. pose proof (SEPsrc : id _) as BXsrc. pose proof (SEPtsrc : id _) as BXtsrc.
    rewrite Hstrm, HBL in HD. rewrite TIL, Hsrc, Hlen in STRM.
    set (ai := bs_ai b) in *. set (bb := sh_bsBuff h) in *.
    pose proof (munch_refl (W10m A) m) as MUL. pose proof (wmono_refl b0segs m) as WML. unfold W10m in MUL.
    (* [comment removed for export] *)
    bstep. park FRH.
    brun. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      brun_to 0xafb90%Z.
      eapply evt_eq; [ | eapply (HX 0%Z _ bb (sh_n h) ai (Z_to_bv 64 (len - ai)) (bs_tih b)) ];
        [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
        | left; split; [reflexivity| clear - K2 Hai G3; zb_masks; mlia] ]. }
    assert (AI1 : (1 <= ai)%Z) by (clear - K2 Hai G3; zb_masks; mlia). clear K2.
    (* [comment removed for export] *)
    brun_to 0xaa040%Z. forget_reg 1%Z wj1. forget_reg 24%Z wj24.
    ack_rd (src + (len - ai))%Z 1%Z.
    brun_to 0xaa048%Z. ack_merge.
    brun_to 0xaa04c%Z.
    destruct (nth_error_ok payload (len - ai)%Z (length payload) eq_refl ltac:(lia)) as [b8 NTH].
    pose proof (u8ro_read b0segs _ src payload (len - ai)%Z b8 _ PAY NTH ltac:(lia) eq_refl) as RD.
    (let pv := reg_val 16%Z in lazymatch pv with Z_to_bv 64 ?e => first [ constr_eq e (src + (len - ai))%Z | replace e with (src + (len - ai))%Z by lia ] end).
    wstepl. clear RD.
    pose proof (bv_unsigned_in_range 8 b8) as Rb8; unfold bv_modulus in Rb8; cbn in Rb8.
    (* [comment removed for export] *)
    brun. if_cases K3; zify_cond_z K3; [| exfalso; clear - K3 Hai G3 AI1; lia]. clear K3.
    lazymatch goal with H : rw_cells _ _ S _ |- _ => rewrite (lor_shl8_byte' bb (bv_unsigned b8)) in H by lia end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    brun_to 0xa9f5c%Z. rewrite ?(land_div1_byte bb (bv_unsigned b8)) by lia.
    lazymatch goal with H : rw_cells _ _ S _ |- _ => rewrite ?(land_div1_byte bb (bv_unsigned b8)) in H by lia end.
    sh_norm.
    brun. if_cases K4; zify_cond_z K4.
    { (* [comment removed for export] *)
      eapply evt_eq; [ | eapply (HN' _ b8 (bv_unsigned b8)) ];
        [ st_eq | g_head Hstrm | clear - K4 Rb8; zb_masks; mlia | exact NTH | reflexivity | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi ]. }
    (* [comment removed for export] *)
    brun_to 0xafb90%Z.
    eapply evt_eq; [ | eapply (HX (-5)%Z _ (bb * 256 + bv_unsigned b8)%Z (bv_unsigned b8) (ai - 1)%Z (Z_to_bv 64 (len - ai + 1)) (bs_tih b)) ];
      [ st_eq | g_head Hstrm | lia | lia | g_strm Hsrc Hlen | lia | exact PAY | exact FRL | g_frh FRH MUL WML | exact ST | exact MU | exact WM | exact MUL | exact WML | g_mi | lia
      | right; split; [reflexivity| exists b8; split; [exact NTH| clear - K4 Rb8; zb_masks; mlia]] ].
  Qed.

End M.
End ACeilS2.
