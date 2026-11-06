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


Section B0SMA.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation LR t := (E + 37708 + 258 * t)%Z.
  Notation Wl := [(E + 37708, E + 39256)]%Z.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)

  Section LROWS.
  Variables (ra t2 s3 s4 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word).
  (* [comment removed for export] *)
  Notation RLb t0 t1 a0 t a5 a6 a7 s6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 (Z_to_bv 64 t) (Z_to_bv 64 258) (Z_to_bv 64 15) (Z_to_bv 64 6) a5 a6 a7 cSB s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 A) t4 t5 t6).

  Lemma B0_smA_lenrow : forall (n : nat) (v t : Z) (len : zarr) (me m : word -> option byte) (t1 a0 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < 6)%Z ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    mem_inv b0segs m -> munch Wl me m -> wmono b0segs me m ->
    shzW b0segs Wl me E (E + ESTATE_SIZE) ->
    (forall m' (t1' a0' : word),
      u8arr b0segs m' (E + 37708) (ovb (sm_len_init_row n len t v) (jseg J 37708 1548) 1548) ->
      mem_inv b0segs m' -> munch Wl me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RLb (NOT (LR t)) t1' a0' t (Z_to_bv 64 (LR t)) (Z_to_bv 64 (LR t)) (Z_to_bv 64 A) (Z_to_bv 64 A)) F (Z_to_bv 64 0x8bed8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RLb (NOT (LR t)) t1 a0 t (Z_to_bv 64 (LR t)) (Z_to_bv 64 (LR t)) (Z_to_bv 64 v) (Z_to_bv 64 A)) F (Z_to_bv 64 0x8be94) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t len me m t1 a0 Hv Hv0 Hn Ht LEN MI MU WM SHe K.
    openCX. openSF. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe. unfold sm_alpha in *.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_len_init_row_S in K.
    (* [comment removed for export] *)
    brun_to 0x8bec0%Z.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok b0segs m (E + 37708) _ (258 * t + v) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    wstep. store_addr (E + 37708 + (258 * t + v))%Z. ovb_store1 LEN (258 * t + v)%Z.
    lazymatch type of LEN with context [wr8 ?l0 ?i0 ?w] =>
      replace (wr8 l0 i0 w) with (zset l0 i0 BZ_GREATER_ICOST) in LEN
        by (unfold wr8, BZ_GREATER_ICOST; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity) end.
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (v + 1)%Z t (zset len (258 * t + v) BZ_GREATER_ICOST) me); [st_eq| lia| lia| lia| lia| exact LEN| assumption| exact MU| exact WM| exact SHe| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_len_init_row] in K.
      wstep.
      enter_with (K _ _ _); [st_eq| exact LEN| assumption| exact MU| exact WM].
  Qed.

  Lemma B0_smA_lenrows : forall (n : nat) (t : Z) (len : zarr) (me m : word -> option byte) (t0 t1 a0 a7 : word),
    (t + Z.of_nat n = 6)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    mem_inv b0segs m -> munch Wl me m -> wmono b0segs me m ->
    shzW b0segs Wl me E (E + ESTATE_SIZE) ->
    frdW b0segs Wl me (P + 1464) [C8 (Z_to_bv 64 (E + 37708))] -> frdW b0segs Wl me (P + 1512) [C8 (Z_to_bv 64 A)] -> frdW b0segs Wl me (P + 1560) [C8 (NOT (E + 37708))] ->
    (forall m' (t0' t1' a0' a7' : word),
      u8arr b0segs m' (E + 37708) (ovb (sm_len_init n len A t) (jseg J 37708 1548) 1548) ->
      mem_inv b0segs m' -> munch Wl me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (RLb t0' t1' a0' 6 (Z_to_bv 64 (LR 6)) (Z_to_bv 64 (LR 6)) a7' (Z_to_bv 64 A)) F (Z_to_bv 64 0x8beec) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RLb t0 t1 a0 t (Z_to_bv 64 (LR t)) (Z_to_bv 64 (LR t)) a7 (Z_to_bv 64 A)) F (Z_to_bv 64 0x8be70) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t len me m t0 t1 a0 a7 Ht Ht0 Hn LEN MI MU WM SHe V1464 V1512 V1560 K.
    openCX. openSF. unfold CEIL in CEP. assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_len_init_S in K.
    (* [comment removed for export] *)
    wstep; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    wstep. pose proof (V1560 m MU) as RO. wstep. clear RO.
    brun_to 0x8be88%Z. pose proof (V1464 m MU) as RO. wstep. clear RO. brun_to 0x8be94%Z.
    (* [comment removed for export] *)
    enter_with (B0_smA_lenrow (Z.to_nat A) 0 t len me m _ _); [st_eq| lia| lia| lia| lia| exact LEN| exact MI| exact MU| exact WM| exact SHe|].
    clear LEN MI MU WM. intros m1 t1' a0' LEN MI MU WM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. pose proof (V1512 m1 MU) as RO. wstep. clear RO. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z (sm_len_init_row (Z.to_nat A) len t 0) me m1 _ _ _ _); [st_eq| lia| lia| lia| exact LEN| exact MI| exact MU| exact WM| exact SHe| exact V1464| exact V1512| exact V1560| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_len_init] in K.
      enter_with (K m1 _ _ _ _); [st_eq| exact LEN| exact MI| exact MU| exact WM].
  Qed.
  End LROWS.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section DISP.
  Variables (g : eg) (SHE FB SHF : Z).
  Hypothesis AE : sanchor (c_E cx) SHE. Hypothesis GM : g_mtf g = true.
  Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation Wd := [(P + 32, P + 136); (P + 1384, P + 1576)]%Z.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac sdw_to p := brun_to p; wstep; lit_store.

  Lemma B0_smA_disp : forall (m : word -> option byte) (w64 w72 w88 w104 w128 : word) (w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word),
    rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m (P + 32) [C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 E); C8 w64; C8 w72; C8 (Z_to_bv 64 (FB + 128)); C8 w88; C8 (Z_to_bv 64 (E + 668)); C8 w104; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 w128] -> rw_cells b0segs m (P + 1384) [C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 w1416; C8 w1424; C8 w1432; C8 w1440; C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 w1480; C8 w1488; C8 w1496; C8 w1504; C8 w1512; C8 w1520; C8 w1528; C8 w1536; C8 w1544; C8 w1552; C8 w1560; C8 w1568] ->
    mem_inv b0segs m -> shzW b0segs Wd m E (E + ESTATE_SIZE) ->
    (forall m' (a4' a5' a6' a7' s7' : word),
      rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells b0segs m' (P + 32) [C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 E); C8 w64; C8 w72; C8 (Z_to_bv 64 (FB + 128)); C8 (Z_to_bv 64 (SHE + 83)); C8 (Z_to_bv 64 (E + 668)); C8 w104; C8 (Z_to_bv 64 (SHE + 82)); C8 (Z_to_bv 64 (E + 656)); C8 w128] -> rw_cells b0segs m' (P + 1384) [C8 w1384; C8 w1392; C8 w1400; C8 w1408; C8 (Z_to_bv 64 A); C8 w1424; C8 w1432; C8 (Z_to_bv 64 (flag6 nG)); C8 w1448; C8 w1456; C8 w1464; C8 w1472; C8 (Z_to_bv 64 nG); C8 (Z_to_bv 64 37450); C8 w1496; C8 (Z_to_bv 64 (E + 672)); C8 w1512; C8 (Z_to_bv 64 (A + -1)); C8 w1528; C8 (Z_to_bv 64 18446744071562067969); C8 (Z_to_bv 64 0); C8 w1552; C8 w1560; C8 w1568] ->
      mem_inv b0segs m' -> munch Wd m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 15) cP gp tp (Z_to_bv 64 (A + -1)) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 258) s0 cP (Z_to_bv 64 (-2147483647)) (Z_to_bv 64 nG) (Z_to_bv 64 nG) (Z_to_bv 64 E) a4' a5' a6' a7'
                            cSB (Z_to_bv 64 nMTF) (Z_to_bv 64 257) (Z_to_bv 64 0) (Z_to_bv 64 A) s7' (NOT (E + 672)) s9 (Z_to_bv 64 (E + nG * 258 + 37450)) (Z_to_bv 64 (E + nG * 258 + 37450))
                            (Z_to_bv 64 A) (Z_to_bv 64 1) (Z_to_bv 64 3) (Z_to_bv 64 6))
                       F (Z_to_bv 64 0x8c000) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB s3 s4 s5 (Z_to_bv 64 A) s7 s8 s9 s10 s11 (Z_to_bv 64 A) t4 t5 t6)
                     F (Z_to_bv 64 0x8beec) fc None m (seg_rom b0segs)).
  Proof.
    intros m w64 w72 w88 w104 w128 w1384 w1392 w1400 w1408 w1416 w1424 w1432 w1440 w1448 w1456 w1464 w1472 w1480 w1488 w1496 w1504 w1512 w1520 w1528 w1536 w1544 w1552 w1560 w1568 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t4 t5 t6 EH2 LOW HI MI SHe K.
    openCX. openSF. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe. assert (HA : A = (nInUse + 2)%Z) by reflexivity.
    pose proof (munch_refl Wd m) as MU. pose proof (wmono_refl b0segs m) as WM.
    unfold EHEAD2 in EH2. rewrite GM in EH2.
    bz_ceil; bz_params.
    assert (HNM : (1 <= nMTF < 2147483648)%Z) by lia.
    (* [comment removed for export] *)
    brun_to 0x8bef8%Z. sh_norm. wstep; lit_store.
    sdw_to 0x8bf10%Z. change (e_nMTF e) with nMTF. rewrite (sx32_of_Z nMTF) by lia.
    wstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    (* [comment removed for export] *)
    assert (HNG : (2 <= nG <= 6)%Z) by (unfold smA_ng, sm_nGroups; repeat (destruct (_ <? _)%Z); lia).
    Ltac arm_end K ENG EFL k fl :=
      let HI := ident:(HI) in
      replace (Z_to_bv 64 fl) with (Z_to_bv 64 (flag6 nG)) in HI by (rewrite EFL; reflexivity);
      replace (Z_to_bv 64 k) with (Z_to_bv 64 nG) by (rewrite ENG; reflexivity);
      sdw_to 0x8bfd0%Z; sdw_to 0x8bfd8%Z; sdw_to 0x8bfe8%Z; sdw_to 0x8bff0%Z; sdw_to 0x8bff8%Z; wstep; lit_store;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _); [st_eq| unfold EHEAD2; rewrite GM; eassumption| eassumption| eassumption| assumption| eassumption| eassumption] end.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases K2; zify_cond_z K2.
    - (* [comment removed for export] *)
      wstep. wstep; if_cases K3; zify_cond_z K3.
      + (* [comment removed for export] *)
        wstep. wstep; if_cases K4; zify_cond_z K4.
        * (* [comment removed for export] *)
          destruct (Z.ltb_spec nMTF 2400) as [L24|L24].
          { assert (ENG : nG = 5%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
            assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
            wstep. wstep. wstep.
            replace (Z.lxor (Z.b2z (nMTF / 32 <? 75)) 1) with 0%Z by (replace (nMTF / 32 <? 75)%Z with true by (symmetry; apply Z.ltb_lt; Z.div_mod_to_equations; lia); reflexivity).
            wstep; lit_store. wstep. arm_end K ENG EFL 5%Z 0%Z. }
          { assert (ENG : nG = 6%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
            assert (EFL : flag6 nG = 1%Z) by (rewrite ENG; reflexivity).
            wstep. wstep. wstep.
            replace (Z.lxor (Z.b2z (nMTF / 32 <? 75)) 1) with 1%Z by (replace (nMTF / 32 <? 75)%Z with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia); reflexivity).
            wstep; lit_store. wstep. arm_end K ENG EFL 6%Z 1%Z. }
        * (* [comment removed for export] *)
          assert (ENG : nG = 4%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
          assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
          wstep; lit_store. wstep. wstep. arm_end K ENG EFL 4%Z 0%Z.
      + assert (ENG : nG = 3%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
        assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
        wstep; lit_store. wstep. wstep. arm_end K ENG EFL 3%Z 0%Z.
    - assert (ENG : nG = 2%Z) by (unfold smA_ng, sm_nGroups; repeat match goal with |- context [(?a <? ?b)%Z] => destruct (Z.ltb_spec a b) end; lia).
      assert (EFL : flag6 nG = 0%Z) by (rewrite ENG; reflexivity).
      wstep; lit_store. wstep. wstep. arm_end K ENG EFL 2%Z 0%Z.
  Qed.
  End DISP.
End B0SMA.
End ACeilS1.
