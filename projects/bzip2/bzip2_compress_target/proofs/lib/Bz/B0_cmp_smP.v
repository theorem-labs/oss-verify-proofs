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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpSmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smP.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

(* [comment removed for export] *)
Ltac abs_skipn H base :=
  lazymatch type of H with
  | context [skipn ?a base] => let r := fresh "rr" in set (r := skipn a base) in H; abs_skipn H r
  | _ => idtac
  end.


Section B0SMP1.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P lo : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx).
  Hypothesis CEL : (CEIL <= lo)%Z. Hypothesis PLO : (lo <= P)%Z.
  Hypothesis USPQ : exists q, usp = (16 * q)%Z. Hypothesis PQ : exists q, P = (32 * q)%Z.
  Hypothesis PCASE : (P = usp - 1696 \/ P = usp - 1712)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  (* [comment removed for export] *)
  Ltac in1_walk FR ST ELAND GOT SBV GOTU UARV :=
      cbn [mk_CB_cells app] in FR;
      lazymatch type of FR with context [skipn _ ?base] => is_var base; abs_skipn FR base end;
      repeat lazymatch type of FR with context [CB ?n (firstn ?a ?b)] => let j := fresh "jj" in set (j := firstn a b) in FR; clearbody j end;
      lazymatch type of FR with rw_cells _ _ _ [CB 136 ?b0; ?c1; CB 312 ?b2; ?c3; CB 104 ?b4] =>
        let FR1 := fresh "FR1" in
        destruct (rw_cells_CB_C8s 17 b0segs _ _ [] b0 [c1; CB 312 b2; c3; CB 104 b4] FR) as (w0 & w8 & w16 & w24 & w32 & w40 & w48 & w56 & w64 & w72 & w80 & w88 & w96 & w104 & w112 & w120 & w128 & FR1);
        clear FR; cbn [map app] in FR1;
        let pre := constr:([C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; c1]) in
        let FR2 := fresh "FR2" in
        destruct (rw_cells_CB_C8s 39 b0segs _ _ pre b2 [c3; CB 104 b4] FR1) as (w1264 & w1272 & w1280 & w1288 & w1296 & w1304 & w1312 & w1320 & w1328 & w1336 & w1344 & w1352 & w1360 & w1368 & w1376 & w1384 & w1392 & w1400 & w1408 & w1416 & w1424 & w1432 & w1440 & w1448 & w1456 & w1464 & w1472 & w1480 & w1488 & w1496 & w1504 & w1512 & w1520 & w1528 & w1536 & w1544 & w1552 & w1560 & w1568 & FR2);
        clear FR1; cbn [map app] in FR2;
        let pre2 := constr:([C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; c1; C8 w1264; C8 w1272; C8 w1280; C8 w1288; C8 w1296; C8 w1304; C8 w1312; C8 w1320; C8 w1328; C8 w1336; C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 w1480; C8 w1488; C8 w1496; C8 w1504; C8 w1512; C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 w1552; C8 w1560; C8 w1568; c3]) in
        let FR3 := fresh "FR3" in
        destruct (rw_cells_CB_C8s 13 b0segs _ _ pre2 b4 [] FR2) as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & FR3);
        clear FR2; cbn [map app] in FR3; rename FR3 into FR
      end;
      (* [comment removed for export] *)
      wstep; wstep; lit_store; do 13 wstep; wstep; wstep;
      rewrite ELAND;
      first [ replace (usp + -1696)%Z with P in FR, ST by lia | replace (usp + -1712)%Z with P in FR, ST by lia ];
      (* [comment removed for export] *)
      wstep; brun_to 0x3de08%Z.

  Lemma B0_smA_in1 : forall (m : word -> option byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    stk b0segs m lo usp -> mem_inv b0segs m -> aconsts B0C m -> aconsts_uar B0C m ->
    (forall m' (jsp jg : list byte) (ng : nat) (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word) (w1264 w1272 w1280 w1288 w1296 w1304 w1312 w1320 w1328 w1336 w1344 w1352 w1360 w1368 w1376 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 : word) (a1 a2 : word),
      (P + 1576 + Z.of_nat ng + 104 = usp)%Z ->
      rw_cells b0segs m' P
        [C8 w0; C8 w8; C8 w16; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128; CB 1128 jsp; C8 w1264; C8 w1272; C8 w1280; C8 w1288; C8 w1296; C8 w1304; C8 w1312; C8 w1320; C8 w1328; C8 w1336; C8 w1344; C8 w1352; C8 w1360; C8 w1368; C8 w1376; C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 w1480; C8 w1488; C8 w1496; C8 w1504; C8 w1512; C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 w1552; C8 w1560; C8 w1568; CB ng jg;
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      stk b0segs m' lo P -> mem_inv b0segs m' -> munch [(P, usp)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 0x8bcb0) cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 160) a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3de08) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8bc40) fc None m (seg_rom b0segs)).
  Proof.
    intros m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI AC AU K.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar B0C ci_segs] in GOT, SBV, GOTU, UARV.
    bz_ceil. unfold CEIL in CEL. destruct USPQ as [qu EU]. destruct PQ as [qp EP].
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RSP.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    assert (ELAND : Z.land (usp + -1696) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - PCASE EU EP. Z.div_mod_to_equations. lia. }
    destruct PCASE as [EPc|EPc].
    - (* [comment removed for export] *)
      carve_frame 1696%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 1696 _ [] [136;1128;312;16;104]%nat) in FR; [| reflexivity].
      in1_walk FR ST ELAND GOT SBV GOTU UARV.
      eapply (K _ _ _ 16%nat); [lia| exact FR| exact ST| assumption| exact MU| exact WM].
    - (* [comment removed for export] *)
      carve_frame 1712%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 1712 _ [] [136;1128;312;32;104]%nat) in FR; [| reflexivity].
      in1_walk FR ST ELAND GOT SBV GOTU UARV.
      eapply (K _ _ _ 32%nat); [lia| exact FR| exact ST| assumption| exact MU| exact WM].
  Qed.
End B0SMP1.
(* [comment removed for export] *)
Ltac sb_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite (le1_lit w); mem_after_store
  end.
Ltac sb_z :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 0))) _) => change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 0)) _) => change (Z_to_le_bytes 1 0) with [z8]; mem_after_store
  end.
Ltac sb_4 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 4))) _) => change (le1 (Z_to_bv 64 4)) with [Z_to_bv 8 4]; mem_after_store
  end.


Section B0SMP2.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis FBL : (0 < FB)%Z. Hypothesis FBH : (FB + 160 <= CEIL)%Z.
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 20 <= SH_HI)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE. Hypothesis AF : sanchor FB SHF.
  (* [comment removed for export] *)
  Hypothesis SEFB : id ((c_E cx + 55768 <= FB)%Z \/ (FB + 160 <= c_E cx)%Z).
  Hypothesis SESH : id ((c_E cx + 55768 <= SHF)%Z \/ (SHF + 20 <= c_E cx)%Z).
  Hypothesis SFSH : id ((FB + 160 <= SHF)%Z \/ (SHF + 20 <= FB)%Z).
  Hypothesis SPSH : id ((SHF + 20 <= P)%Z \/ (P + 1712 <= SHF)%Z).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac sdw_to p := brun_to p; wstep; lit_store.
  Notation Wp2 := [(P + 32, P + 136); (P + 1384, P + 1576); (FB, FB + 24); (SHF, SHF + 20)]%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_smA_in2 : forall (m : word -> option byte) (w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word) (w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 : word) (h0 h1 h2 : word) (bs : list byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m (P + 32) [C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128] -> rw_cells b0segs m (P + 1384) [C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 w1480; C8 w1488; C8 w1496; C8 w1504; C8 w1512; C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 w1552; C8 w1560; C8 w1568] ->
    rw_cells b0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells b0segs m SHF [CB 20 bs] ->
    mem_inv b0segs m -> shzW b0segs Wp2 m E (E + ESTATE_SIZE) ->
    (forall m',
      rw_cells b0segs m' E (EHEAD1 cx g e) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells b0segs m' (P + 32) [C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 E); C8 w64; C8 w72; C8 (Z_to_bv 64 (FB + 128)); C8 w88; C8 (Z_to_bv 64 (E + 668)); C8 w104;
                                   C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 w128] ->
      rw_cells b0segs m' (P + 1384) [C8 w1384; C8 w1392; C8 (Z_to_bv 64 (FB + 64)); C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 (Z_to_bv 64 (E + 37708)); C8 (Z_to_bv 64 (E + 37708));
                                     C8 w1480; C8 w1488; C8 (Z_to_bv 64 (A * 4294967296)); C8 w1504; C8 (Z_to_bv 64 A); C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 (Z_to_bv 64 A1); C8 (NOT (E + 37708));
                                     C8 (Z_to_bv 64 FB)] ->
      rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x148b3); C8 (Z_to_bv 64 0x8bc40)] -> rw_cells b0segs m' SHF sm_shadow ->
      mem_inv b0segs m' -> munch Wp2 m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP (NOT (E + 37708)) (Z_to_bv 64 0) (Z_to_bv 64 258) (Z_to_bv 64 15) (Z_to_bv 64 6) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 FB)
                            cSB (Z_to_bv 64 (E + 656)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (E + 124)) (Z_to_bv 64 A) s7 s8 (Z_to_bv 64 (FB + 32)) s10 s11 (Z_to_bv 64 A) t4 t5 t6)
                       F (Z_to_bv 64 0x8be70) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 E) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x8bcb0) fc None m (seg_rom b0segs)).
  Proof.
    intros m w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 h0 h1 h2 bs ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EH1 EH2 LOW HI HD SH20 MI SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA1 MA2 MF Mb Mf LJb. openSF. assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof CEP as CEP'. pose proof FBH as FBH'. unfold CEIL in CEP', FBH'. unfold SH_LO, SH_HI in SHL, SHH. unfold ESTATE_SIZE in SHe.
    pose proof (munch_refl Wp2 m) as MU. pose proof (wmono_refl b0segs m) as WM.
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. rewrite GM in EH1, EH2.
    apply (rw_cells_split_CB b0segs _ _ [] 20 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in SH20; [| reflexivity]. cbn [mk_CB_cells app] in SH20.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep; lit_store. wstep; lit_store.
    (* [comment removed for export] *)
    sdw_to 0x8bd0c%Z. wstep; lit_store. wstep; lit_store. wstep; lit_store.
    (* [comment removed for export] *)
    wstep. wstep. sh_norm.
    (* [comment removed for export] *)
    wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit.
    wstep.
    wstep. sb_z. wstep. sb_4. wstep. sb_lit. wstep. sb_lit.
    wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit.
    wstep. sb_z. wstep. sb_z. wstep. sb_z. wstep. sb_lit.
    wstep; lit_store. wstep.
    wstep. sb_lit. wstep. sb_lit. wstep. sb_lit.
    wstep; lit_store.
    wstep. sb_lit.
    (* [comment removed for export] *)
    assert (EL7 : Z.land E 7 = 0%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME. Z.div_mod_to_equations. lia. }
    rewrite EL7. brun_to 0x8bdb4%Z. sh_norm. wstep; lit_store.
    (* [comment removed for export] *)
    sdw_to 0x8bdc0%Z. brun_to 0x8bddc%Z. wstep; first [ if_cases Kv; zify_cond_z Kv; [| exfalso; lia] | idtac ].
    (* [comment removed for export] *)
    wstep; lit_store. wstep; lit_store.
    brun_to 0x8be04%Z. try rewrite (sx32_of_Z nInUse) by lia. wstep. try rewrite (sx32_of_Z (nInUse + 2)) by lia. wstep; lit_store.
    (* [comment removed for export] *)
    sdw_to 0x8be24%Z. sdw_to 0x8be2c%Z.
    (* [comment removed for export] *)
    sdw_to 0x8be50%Z. sdw_to 0x8be60%Z. sdw_to 0x8be68%Z. wstep; lit_store.
    replace ((nInUse + 2) * 4294967296 / 4294967296)%Z with (nInUse + 2)%Z by (rewrite Z.div_mul; lia).
    rewrite <- HA in HI |- *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm); [st_eq| unfold EHEAD1; rewrite GM; exact EH1| unfold EHEAD2; rewrite GM; exact EH2| exact LOW| exact HI| exact HD| exact SH20| assumption| exact MU| exact WM] end.
  Qed.
End B0SMP2.
End ACeilS1.
