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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpHmKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma rw_cells_cat : forall segs (m : word -> option byte) A cs1 B cs2,
  rw_cells segs m A cs1 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells segs m B cs2 -> rw_cells segs m A (cs1 ++ cs2).
Proof.
  intros segs m A cs1 B cs2 [[W1 B1] R1] -> [[W2 B2] R2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact W1. exact B2.
  - destruct R1 as (R1a & R1b & R1c). destruct R2 as (R2a & R2b & R2c). rewrite cells_size_app.
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [Hl|Hg]; [apply R1c; lia|].
    replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply R2c. lia.
Qed.

Section FC6.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 s1 s3 s4 s9 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Variables (lp cb : zarr) (gs : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs). Notation p := (PV arr1 lp gs).
  Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Hypothesis PB : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> (0 <= p k j < 2097152)%Z.
  Hypothesis PD : forall k j, (0 <= k < 50)%Z -> (0 <= j < 3)%Z -> zdef lp (4 * q k + j) = true.
  Notation cSP := (Z_to_bv 64 SP).
  Notation S6 := (Z_to_bv 64 (4 * A)).
  Notation R k := (Z_to_bv 64 (c_E cx + 51640 + 16 * QV (e_arr1 e) gs k)).
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
  Ltac fstep := let R := u_regs in u_zstep_nofb; bzl; u_flags R; u_try_lit_branch; u_try_guard.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac RDP VLPK k j :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let LPKv := fresh "LPKv" in let RD := fresh "RD" in
      pose proof (VLPK mm MU') as LPKv;
      pose proof (ovw_read s0segs mm (E + 51640) lp (jseg J 51640 4128) 1032 (4 * q k + j) _ LPKv ltac:(pose proof (QB k ltac:(lia)); lia) (PD k j ltac:(lia) ltac:(lia)) ltac:(unfold wa; f_equal; lia)) as RD;
      clear LPKv;
      change (zget lp (4 * q k + j)) with (p k j) in RD;
      pose proof (PB k j ltac:(lia) ltac:(lia)) as ?PBk;
      lstep; clear RD; rewrite (sx32_of_Z (p k j)) by (change (2^31)%Z with 2147483648%Z; lia) end.
  Ltac RDV V :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RO := fresh "RO" in pose proof (V mm MU') as RO; lstep; clear RO end.
  Ltac SST := lstep; lit_store.
  Ltac CST COST i :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_storeN_ok s0segs mm (SP + 1084) _ i 2 _ COST ltac:(lia) ltac:(rewrite zb8_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
    lstep; store_addr (SP + 1084 + i)%Z; zb8_store2 COST i; rewrite unsigned_lit in COST by lia end.

  Notation Wfc := [(SP + 48, SP + 528); (SP + 584, SP + 800); (SP + 832, SP + 888); (SP + 1084, SP + 1096)]%Z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_fc6_raw : forall (m me : word -> option byte) (Jlo : list byte) (ra a0 a1 a3 a5 s6 s11 : word),
    length Jlo = 472%nat -> u8arr s0segs m (SP + 48) Jlo ->
    rw_cells s0segs m (SP + 520) [C8 (R 49)] ->
    rw_cells s0segs m (SP + 584) [C8 (R 45)] ->
    rw_cells s0segs m (SP + 592) [C8 (R 44)] ->
    rw_cells s0segs m (SP + 600) [C8 (R 41)] ->
    rw_cells s0segs m (SP + 608) [C8 (R 36)] ->
    rw_cells s0segs m (SP + 616) [C8 (R 35)] ->
    rw_cells s0segs m (SP + 624) [C8 (R 34)] ->
    rw_cells s0segs m (SP + 632) [C8 (R 33)] ->
    rw_cells s0segs m (SP + 640) [C8 (R 32)] ->
    rw_cells s0segs m (SP + 648) [C8 (R 31)] ->
    rw_cells s0segs m (SP + 656) [C8 (R 28)] ->
    rw_cells s0segs m (SP + 664) [C8 (R 27)] ->
    rw_cells s0segs m (SP + 672) [C8 (R 26)] ->
    rw_cells s0segs m (SP + 680) [C8 (R 25)] ->
    rw_cells s0segs m (SP + 688) [C8 (R 24)] ->
    rw_cells s0segs m (SP + 696) [C8 (R 21)] ->
    rw_cells s0segs m (SP + 704) [C8 (R 20)] ->
    rw_cells s0segs m (SP + 712) [C8 (R 19)] ->
    rw_cells s0segs m (SP + 720) [C8 (R 18)] ->
    rw_cells s0segs m (SP + 728) [C8 (R 16)] ->
    rw_cells s0segs m (SP + 736) [C8 (R 15)] ->
    rw_cells s0segs m (SP + 744) [C8 (R 14)] ->
    rw_cells s0segs m (SP + 752) [C8 (R 12)] ->
    rw_cells s0segs m (SP + 760) [C8 (R 11)] ->
    rw_cells s0segs m (SP + 768) [C8 (R 8)] ->
    rw_cells s0segs m (SP + 776) [C8 (R 7)] ->
    rw_cells s0segs m (SP + 784) [C8 (R 6)] ->
    rw_cells s0segs m (SP + 792) [C8 (R 4)] ->
    rw_cells s0segs m (SP + 832) [C8 (R 38)] ->
    rw_cells s0segs m (SP + 840) [C8 (R 30)] ->
    rw_cells s0segs m (SP + 848) [C8 (R 29)] ->
    rw_cells s0segs m (SP + 856) [C8 (R 22)] ->
    rw_cells s0segs m (SP + 864) [C8 (R 17)] ->
    rw_cells s0segs m (SP + 872) [C8 (R 9)] ->
    rw_cells s0segs m (SP + 880) [C8 (R 5)] ->
    u8arr s0segs m (SP + 1084) (zb8 cb 12) ->
    mem_inv s0segs m -> munch Wfc me m -> wmono s0segs me m ->
    (forall m', munch Wfc me m' -> u32arr s0segs m' (E + 51640) (ovw lp (jseg J 51640 4128) 1032)) ->
    frdW s0segs Wfc me (SP + 40) [C8 S6] ->
    (forall m' (S0 S1 S2 : Z) (J1' J2' J3' : list byte) (ra t0 t1 t2 a0 a1 a2 a3 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
      S0 = psum arr1 lp gs 0 0 50 -> S1 = psum arr1 lp gs 1 0 50 -> S2 = psum arr1 lp gs 2 0 50 ->
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      u8arr s0segs m' (SP + 1084) (zb8 (wr16 (wr16 (wr16 (wr16 (wr16 (wr16 cb 0 S0) 2 (S0 / 65536)) 4 S1) 6 (S1 / 65536)) 8 S2) 10 (S2 / 65536)) 12) ->
      mem_inv s0segs m' -> munch Wfc me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (mkR ra cSP gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s3 s4 s5 S6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x19870) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cSP gp tp (R 1) (R 2) (R 48) s0 s1 a0 a1 (R 46) a3 (Z_to_bv 64 gs) a5 (R 39) (R 43) (R 0) s3 s4 (R 42) s6 (R 40) (R 10) s9 (R 3) s11 (R 13) (R 47) (R 23) (R 37))
                     F (Z_to_bv 64 0x18ee0) fc None m (seg_rom s0segs)).
  Proof.
    intros m me Jlo ra a0 a1 a3 a5 s6 s11 LJ SJ C520 C584 C592 C600 C608 C616 C624 C632 C640 C648 C656 C664 C672 C680 C688 C696 C704 C712 C720 C728 C736 C744 C752 C760 C768 C776 C784 C792 C832 C840 C848 C856 C864 C872 C880 COST MI MU WM VLPK V40 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (zb8_length_nat cb 12) as LC.
    destruct (u8arr_C8s 59 s0segs m (SP + 48) Jlo SJ ltac:(rewrite LJ; reflexivity)) as (x48 & x56 & x64 & x72 & x80 & x88 & x96 & x104 & x112 & x120 & x128 & x136 & x144 & x152 & x160 & x168 & x176 & x184 & x192 & x200 & x208 & x216 & x224 & x232 & x240 & x248 & x256 & x264 & x272 & x280 & x288 & x296 & x304 & x312 & x320 & x328 & x336 & x344 & x352 & x360 & x368 & x376 & x384 & x392 & x400 & x408 & x416 & x424 & x432 & x440 & x448 & x456 & x464 & x472 & x480 & x488 & x496 & x504 & x512 & SA). clear SJ. cbn [map] in SA.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 520) _ SA ltac:(cbn [cells_size csize app Nat.add]; lia) C520) as SAx. clear SA C520. rename SAx into SA. cbn [app] in SA.
    rename C584 into SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 592) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C592) as SBx. clear SB C592. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 600) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C600) as SBx. clear SB C600. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 608) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C608) as SBx. clear SB C608. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 616) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C616) as SBx. clear SB C616. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 624) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C624) as SBx. clear SB C624. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 632) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C632) as SBx. clear SB C632. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 640) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C640) as SBx. clear SB C640. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 648) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C648) as SBx. clear SB C648. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 656) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C656) as SBx. clear SB C656. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 664) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C664) as SBx. clear SB C664. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 672) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C672) as SBx. clear SB C672. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 680) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C680) as SBx. clear SB C680. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 688) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C688) as SBx. clear SB C688. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 696) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C696) as SBx. clear SB C696. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 704) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C704) as SBx. clear SB C704. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 712) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C712) as SBx. clear SB C712. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 720) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C720) as SBx. clear SB C720. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 728) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C728) as SBx. clear SB C728. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 736) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C736) as SBx. clear SB C736. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 744) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C744) as SBx. clear SB C744. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 752) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C752) as SBx. clear SB C752. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 760) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C760) as SBx. clear SB C760. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 768) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C768) as SBx. clear SB C768. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 776) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C776) as SBx. clear SB C776. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 784) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C784) as SBx. clear SB C784. rename SBx into SB. cbn [app] in SB.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 792) _ SB ltac:(cbn [cells_size csize app Nat.add]; lia) C792) as SBx. clear SB C792. rename SBx into SB. cbn [app] in SB.
    rename C832 into SC.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 840) _ SC ltac:(cbn [cells_size csize app Nat.add]; lia) C840) as SCx. clear SC C840. rename SCx into SC. cbn [app] in SC.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 848) _ SC ltac:(cbn [cells_size csize app Nat.add]; lia) C848) as SCx. clear SC C848. rename SCx into SC. cbn [app] in SC.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 856) _ SC ltac:(cbn [cells_size csize app Nat.add]; lia) C856) as SCx. clear SC C856. rename SCx into SC. cbn [app] in SC.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 864) _ SC ltac:(cbn [cells_size csize app Nat.add]; lia) C864) as SCx. clear SC C864. rename SCx into SC. cbn [app] in SC.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 872) _ SC ltac:(cbn [cells_size csize app Nat.add]; lia) C872) as SCx. clear SC C872. rename SCx into SC. cbn [app] in SC.
    pose proof (rw_cells_cat s0segs m _ _ (SP + 880) _ SC ltac:(cbn [cells_size csize app Nat.add]; lia) C880) as SCx. clear SC C880. rename SCx into SC. cbn [app] in SC.
    RDP VLPK 1%Z 0%Z.
    RDP VLPK 0%Z 0%Z.
    RDP VLPK 0%Z 1%Z.
    SST.
    RDP VLPK 0%Z 2%Z.
    SST.
    fstep.
    SST.
    SST.
    RDP VLPK 3%Z 0%Z.
    RDP VLPK 3%Z 1%Z.
    SST.
    RDP VLPK 3%Z 2%Z.
    SST.
    RDP VLPK 2%Z 0%Z.
    RDP VLPK 2%Z 1%Z.
    SST.
    lstep.
    RDP VLPK 5%Z 0%Z.
    lstep.
    RDP VLPK 4%Z 0%Z.
    fstep.
    RDP VLPK 4%Z 1%Z.
    SST.
    RDP VLPK 4%Z 2%Z.
    SST.
    fstep.
    SST.
    SST.
    lstep.
    RDP VLPK 7%Z 0%Z.
    RDP VLPK 7%Z 1%Z.
    SST.
    RDP VLPK 7%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 8%Z 0%Z.
    RDP VLPK 8%Z 1%Z.
    SST.
    RDP VLPK 8%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 9%Z 0%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 11%Z 0%Z.
    RDP VLPK 11%Z 1%Z.
    SST.
    RDP VLPK 11%Z 2%Z.
    SST.
    SST.
    lstep.
    RDP VLPK 12%Z 0%Z.
    RDP VLPK 12%Z 1%Z.
    SST.
    RDP VLPK 12%Z 2%Z.
    SST.
    RDP VLPK 13%Z 0%Z.
    SST.
    lstep.
    RDP VLPK 17%Z 0%Z.
    lstep.
    RDP VLPK 16%Z 0%Z.
    fstep.
    RDP VLPK 16%Z 1%Z.
    SST.
    RDP VLPK 16%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 22%Z 0%Z.
    RDP VLPK 23%Z 0%Z.
    RDP VLPK 23%Z 1%Z.
    SST.
    RDP VLPK 23%Z 2%Z.
    SST.
    RDP VLPK 22%Z 1%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 29%Z 0%Z.
    lstep.
    lstep.
    RDP VLPK 30%Z 0%Z.
    SST.
    RDP VLPK 37%Z 0%Z.
    lstep.
    RDP VLPK 38%Z 0%Z.
    RDP VLPK 30%Z 1%Z.
    SST.
    fstep.
    RDP VLPK 38%Z 1%Z.
    SST.
    fstep.
    fstep.
    SST.
    RDP VLPK 46%Z 0%Z.
    RDP VLPK 47%Z 0%Z.
    RDP VLPK 47%Z 1%Z.
    SST.
    RDP VLPK 47%Z 2%Z.
    SST.
    RDP VLPK 46%Z 1%Z.
    SST.
    RDP VLPK 6%Z 0%Z.
    fstep.
    lstep.
    fstep.
    RDP VLPK 6%Z 1%Z.
    SST.
    lstep.
    fstep.
    lstep.
    RDP VLPK 18%Z 0%Z.
    lstep.
    fstep.
    fstep.
    RDP VLPK 18%Z 1%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 24%Z 0%Z.
    RDP VLPK 24%Z 1%Z.
    SST.
    RDP VLPK 24%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 25%Z 0%Z.
    fstep.
    lstep.
    RDP VLPK 31%Z 0%Z.
    RDP VLPK 31%Z 1%Z.
    SST.
    RDP VLPK 31%Z 2%Z.
    SST.
    RDP VLPK 39%Z 0%Z.
    fstep.
    RDP VLPK 39%Z 1%Z.
    SST.
    RDP VLPK 39%Z 2%Z.
    SST.
    fstep.
    RDP VLPK 48%Z 0%Z.
    RDP VLPK 48%Z 1%Z.
    SST.
    RDP VLPK 48%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 49%Z 0%Z.
    SST.
    fstep.
    SST.
    lstep.
    RDP VLPK 10%Z 0%Z.
    fstep.
    RDP VLPK 10%Z 1%Z.
    SST.
    lstep.
    RDP VLPK 14%Z 0%Z.
    fstep.
    RDP VLPK 14%Z 1%Z.
    SST.
    lstep.
    RDP VLPK 19%Z 0%Z.
    fstep.
    RDP VLPK 19%Z 1%Z.
    SST.
    RDP VLPK 19%Z 2%Z.
    SST.
    fstep.
    fstep.
    lstep.
    RDP VLPK 32%Z 0%Z.
    RDP VLPK 32%Z 1%Z.
    SST.
    RDP VLPK 32%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 33%Z 0%Z.
    fstep.
    RDP VLPK 40%Z 0%Z.
    RDP VLPK 40%Z 1%Z.
    SST.
    RDP VLPK 40%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 41%Z 0%Z.
    fstep.
    lstep.
    RDP VLPK 15%Z 0%Z.
    fstep.
    RDP VLPK 15%Z 1%Z.
    SST.
    RDP VLPK 15%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 20%Z 0%Z.
    RDP VLPK 20%Z 1%Z.
    SST.
    RDP VLPK 20%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 26%Z 0%Z.
    lstep.
    RDP VLPK 21%Z 0%Z.
    fstep.
    RDP VLPK 26%Z 1%Z.
    SST.
    fstep.
    fstep.
    fstep.
    fstep.
    fstep.
    lstep.
    RDP VLPK 27%Z 0%Z.
    RDP VLPK 27%Z 1%Z.
    SST.
    RDP VLPK 27%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 34%Z 0%Z.
    fstep.
    RDP VLPK 42%Z 0%Z.
    RDP VLPK 34%Z 1%Z.
    SST.
    fstep.
    RDP VLPK 42%Z 1%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 28%Z 0%Z.
    fstep.
    RDP VLPK 28%Z 1%Z.
    SST.
    RDP VLPK 28%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 35%Z 0%Z.
    RDP VLPK 35%Z 1%Z.
    SST.
    RDP VLPK 35%Z 2%Z.
    SST.
    RDP VLPK 43%Z 0%Z.
    fstep.
    RDP VLPK 43%Z 1%Z.
    SST.
    RDP VLPK 43%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 36%Z 0%Z.
    fstep.
    RDP VLPK 36%Z 1%Z.
    SST.
    RDP VLPK 36%Z 2%Z.
    SST.
    fstep.
    lstep.
    RDP VLPK 44%Z 0%Z.
    lstep.
    RDP VLPK 45%Z 0%Z.
    RDP VLPK 44%Z 1%Z.
    SST.
    RDP VLPK 44%Z 2%Z.
    SST.
    fstep.
    fstep.
    fstep.
    fstep.
    lstep.
    RDP VLPK 1%Z 1%Z.
    RDP VLPK 1%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 2%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 5%Z 1%Z.
    RDP VLPK 5%Z 2%Z.
    SST.
    RDP VLPK 6%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 9%Z 1%Z.
    RDP VLPK 9%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 10%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 13%Z 1%Z.
    RDP VLPK 13%Z 2%Z.
    SST.
    RDP VLPK 14%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 17%Z 1%Z.
    RDP VLPK 17%Z 2%Z.
    SST.
    RDP VLPK 18%Z 2%Z.
    SST.
    RDP VLPK 21%Z 1%Z.
    RDP VLPK 21%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 22%Z 2%Z.
    SST.
    RDP VLPK 25%Z 1%Z.
    RDP VLPK 25%Z 2%Z.
    SST.
    RDP VLPK 26%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 29%Z 1%Z.
    RDP VLPK 29%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 30%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 37%Z 1%Z.
    RDP VLPK 37%Z 2%Z.
    lstep.
    RDP VLPK 38%Z 2%Z.
    RDP VLPK 33%Z 1%Z.
    RDP VLPK 33%Z 2%Z.
    SST.
    RDV V40.
    RDP VLPK 41%Z 1%Z.
    RDP VLPK 41%Z 2%Z.
    SST.
    RDP VLPK 34%Z 2%Z.
    SST.
    RDP VLPK 42%Z 2%Z.
    SST.
    RDP VLPK 45%Z 1%Z.
    RDP VLPK 45%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 46%Z 2%Z.
    SST.
    lstep.
    RDP VLPK 49%Z 1%Z.
    RDP VLPK 49%Z 2%Z.
    SST.
    lstep.
    lstep.
    fstep.
    fstep.
    CST COST 0%Z.
    fstep.
    fstep.
    fstep.
    fstep.
    CST COST 2%Z.
    fstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    fstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    fstep.
    fstep.
    fstep.
    fstep.
    CST COST 4%Z.
    fstep.
    fstep.
    fstep.
    fstep.
    CST COST 6%Z.
    fstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    fstep.
    lstep.
    fstep.
    fstep.
    CST COST 8%Z.
    fstep.
    fstep.
    fstep.
    fstep.
    CST COST 10%Z.
    fstep.
    destruct (u8arr_of_cells s0segs _ _ _ SA) as [UA LA]. destruct (u8arr_of_cells s0segs _ _ _ SB) as [UB LB]. destruct (u8arr_of_cells s0segs _ _ _ SC) as [UC LC'].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of SA with rw_cells _ _ _ ?cA => lazymatch type of SB with rw_cells _ _ _ ?cB => lazymatch type of SC with rw_cells _ _ _ ?cC =>
      enter_with (K mm (p 0 0 + p 1 0 + p 2 0 + p 3 0 + p 4 0 + p 5 0 + p 6 0 + p 7 0 + p 8 0 + p 9 0 + p 10 0 + p 11 0 + p 12 0 + p 13 0 + p 14 0 + p 15 0 + p 16 0 + p 17 0 + p 18 0 + p 19 0 + p 20 0 + p 21 0 + p 22 0 + p 23 0 + p 24 0 + p 25 0 + p 26 0 + p 27 0 + p 28 0 + p 29 0 + p 30 0 + p 31 0 + p 32 0 + p 33 0 + p 34 0 + p 35 0 + p 36 0 + p 37 0 + p 38 0 + p 39 0 + p 40 0 + p 41 0 + p 42 0 + p 43 0 + p 44 0 + p 45 0 + p 46 0 + p 47 0 + p 48 0 + p 49 0)%Z (p 0 1 + p 1 1 + p 2 1 + p 3 1 + p 4 1 + p 5 1 + p 6 1 + p 7 1 + p 8 1 + p 9 1 + p 10 1 + p 11 1 + p 12 1 + p 13 1 + p 14 1 + p 15 1 + p 16 1 + p 17 1 + p 18 1 + p 19 1 + p 20 1 + p 21 1 + p 22 1 + p 23 1 + p 24 1 + p 25 1 + p 26 1 + p 27 1 + p 28 1 + p 29 1 + p 30 1 + p 31 1 + p 32 1 + p 33 1 + p 34 1 + p 35 1 + p 36 1 + p 37 1 + p 38 1 + p 39 1 + p 40 1 + p 41 1 + p 42 1 + p 43 1 + p 44 1 + p 45 1 + p 46 1 + p 47 1 + p 48 1 + p 49 1)%Z (p 0 2 + p 1 2 + p 2 2 + p 3 2 + p 4 2 + p 5 2 + p 6 2 + p 7 2 + p 8 2 + p 9 2 + p 10 2 + p 11 2 + p 12 2 + p 13 2 + p 14 2 + p 15 2 + p 16 2 + p 17 2 + p 18 2 + p 19 2 + p 20 2 + p 21 2 + p 22 2 + p 23 2 + p 24 2 + p 25 2 + p 26 2 + p 27 2 + p 28 2 + p 29 2 + p 30 2 + p 31 2 + p 32 2 + p 33 2 + p 34 2 + p 35 2 + p 36 2 + p 37 2 + p 38 2 + p 39 2 + p 40 2 + p 41 2 + p 42 2 + p 43 2 + p 44 2 + p 45 2 + p 46 2 + p 47 2 + p 48 2 + p 49 2)%Z (cells_bytes cA) (cells_bytes cB) (cells_bytes cC) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end end end end;
      [ st_eq
      | rewrite psum50_eq; lia | rewrite psum50_eq; lia | rewrite psum50_eq; lia
      | rewrite LA; reflexivity | rewrite LB; reflexivity | rewrite LC'; reflexivity
      | exact UA | exact UB | exact UC
      | first [exact COST | lazymatch type of COST with u8arr _ _ _ ?L => lazymatch goal with |- u8arr _ _ _ ?L2 => replace L2 with L; [exact COST| CmpFast.rlf] end end]
      | assumption | assumption | assumption ].
  Qed.
End FC6.
End ACeilS1.
