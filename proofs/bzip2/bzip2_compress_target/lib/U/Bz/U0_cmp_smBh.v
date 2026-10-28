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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpSmKit CmpCutSmB BzCFactsSmB CmpSmKit2.
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
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section U0SMBH.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation J := (c_J cx).
  Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation S6 := (Z_to_bv 64 (4 * A)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac lit_store2 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?v)) _) => change (Z_to_le_bytes 2 v) with (le2 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  Notation RG t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).

  Notation Wh := [(SP + 896, SP + 904); (SP + 936, SP + 944); (SP + 1024, SP + 1032); (SP + 1084, SP + 1096)]%Z.
  Lemma U0_sm_head : forall (gs : Z) (jc : list byte) (v896 v936 : word) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> length jc = 12%nat ->
    u8arr s0segs m (SP + 1084) jc ->
    rw_cells s0segs m (SP + 1024) [C8 (Z_to_bv 64 gs)] -> rw_cells s0segs m (SP + 936) [C8 v936] -> rw_cells s0segs m (SP + 896) [C8 v896] ->
    mem_inv s0segs m -> munch Wh me m -> wmono s0segs me m ->
    frdW s0segs Wh me (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> frdW s0segs Wh me (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
    (forall m' (a0 a1 s6 : word), let ge := GE nMTF gs in fastb nG nMTF gs = true ->
      u8arr s0segs m' (SP + 1084) (zb8 znew 12) ->
      rw_cells s0segs m' (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] -> rw_cells s0segs m' (SP + 936) [C8 (Z_to_bv 64 (gs + 50))] ->
      rw_cells s0segs m' (SP + 896) [C8 (Z_to_bv 64 ge)] ->
      mem_inv s0segs m' -> munch Wh me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17688) fc None m' (seg_rom s0segs))) ->
    (forall m' (a1 : word), let ge := GE nMTF gs in fastb nG nMTF gs = false ->
      u8arr s0segs m' (SP + 1084) (zb8 znew 12) ->
      rw_cells s0segs m' (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] -> rw_cells s0segs m' (SP + 936) [C8 (Z_to_bv 64 (gs + 50))] ->
      rw_cells s0segs m' (SP + 896) [C8 (Z_to_bv 64 ge)] ->
      mem_inv s0segs m' -> munch Wh me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG t0 t1 t2 (Z_to_bv 64 (ge + 1)) a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x197bc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17600) fc None m (seg_rom s0segs)).
  Proof.
    intros gs jc v896 v936 me m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 Hgs Ljc COST C1024 C936 C896 MI MU WM V904 V920 KF KS.
    openCX. try clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    assert (HMd : nMTF = e_nMTF e) by reflexivity.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3).
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    set (ge := GE nMTF gs) in *.
    (* [comment removed for export] *)
    assert (REST : forall m1 (x0 x1 : word),
      rw_cells s0segs m1 (SP + 1024) [C8 (Z_to_bv 64 (ge + 1))] -> rw_cells s0segs m1 (SP + 936) [C8 (Z_to_bv 64 (gs + 50))] ->
      rw_cells s0segs m1 (SP + 896) [C8 v896] -> u8arr s0segs m1 (SP + 1084) jc ->
      mem_inv s0segs m1 -> munch Wh me m1 -> wmono s0segs me m1 ->
      evt s0segs Q (MS (RG t0 t1 t2 x0 x1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1762c) fc None m1 (seg_rom s0segs))).
    { intros m1 x0 x1 R1024 R936 R896 COST1 MI1 MU1 WM1. clear COST C1024 C936 C896 MI MU WM.
      wstep. wstep. try rewrite (sx32_of_Z_signed (ge + 1 + -1)) by lia. try rewrite (sx32_of_Z (ge + 1 + -1)) by lia.
      replace (ge + 1 + -1)%Z with ge by lia.
      wstep; lit_store.
      cps_destruct (cost_cells_of_junk6 s0segs _ (SP + 1084) jc COST1 Ljc) as (c1 & c2 & c3 & c4 & c5 & c6 & CC). clear COST1.
      wstep. wstep.
      (* [comment removed for export] *)
      do 5 ((wstep; lit_store2); wstep; wstep; if_cases Kl; zify_cond_z Kl; [clear Kl| exfalso; lia]).
      (wstep; lit_store2). wstep. wstep; if_cases Kl; zify_cond_z Kl; [exfalso; lia| clear Kl].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (cost_zero_cells6 s0segs mm (SP + 1084) CC) as COST end. clear CC.
      (* [comment removed for export] *)
      poseV V904 RO. wstep. clear RO.
      wstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
      - (* [comment removed for export] *)
        destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
        urun_to 0x17680%Z.
        wstep; if_cases K50; zify_cond_z K50.
        + assert (FB : fastb nG nMTF gs = true) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KF mm _ _ _ FB) end;
            [st_eq| exact COST| eassumption| eassumption| eassumption| assumption| assumption| assumption].
        + urun_to 0x197bc%Z.
          assert (FB : fastb nG nMTF gs = false) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ FB) end;
            [st_eq| exact COST| eassumption| eassumption| eassumption| assumption| assumption| assumption].
      - (* [comment removed for export] *)
        destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
        urun_to 0x197bc%Z.
        assert (FB : fastb nG nMTF gs = false) by (unfold fastb; replace (nG =? 6)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ FB) end;
          [st_eq| exact COST| eassumption| eassumption| eassumption| assumption| assumption| assumption]. }
    (* [comment removed for export] *)
    wstep. wstep. try rewrite (sx32_of_Z (gs + 50)) by lia. wstep; lit_store.
    wstep; u_guard.
    wstep. wstep; lit_store.
    poseV V920 RO. wstep. clear RO.
    wstep; if_cases Kn; zify_cond_z Kn.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST mm _ _) end;
        [st_eq| replace (ge + 1)%Z with (gs + 50)%Z by lia; eassumption| eassumption| eassumption| eassumption| assumption| assumption| assumption].
    - poseV V920 RO. wstep. clear RO. wstep; lit_store.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (REST mm _ _) end;
        [st_eq| replace (ge + 1)%Z with nMTF by lia; eassumption| eassumption| eassumption| eassumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wpo := [(E + 1704, E + 19706); (SP + 912, SP + 920); (SP + 1060, SP + 1084)]%Z.
  Lemma U0_sm_post : forall (gs bt bc totc nSel : Z) (fave sel : zarr) (me m : word -> option byte)
      (t0 t1 t2 a2 a3 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> (0 <= bt < nG)%Z -> (0 <= bc <= 65535)%Z -> (0 <= totc)%Z -> (totc + bc < 2147483648)%Z -> (0 <= nSel < 18002)%Z ->
    (0 <= zget fave bt <= 18001)%Z ->
    u32arr s0segs m (SP + 1060) (zw32 fave 6) ->
    u8arr s0segs m (E + 1704) (ovb sel (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (SP + 912) [C8 (Z_to_bv 64 totc)] ->
    mem_inv s0segs m -> munch Wpo me m -> wmono s0segs me m ->
    frdW s0segs Wpo me (SP + 800) [C8 (Z_to_bv 64 18002)] -> frdW s0segs Wpo me (SP + 808) [C8 (NOT (SP + 1060))] ->
    frdW s0segs Wpo me (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs Wpo me (SP + 824) [C8 (NOT (E + 1704))] ->
    frdW s0segs Wpo me (SP + 896) [C8 (Z_to_bv 64 (GE nMTF gs))] -> frdW s0segs Wpo me (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] ->
    frdW s0segs Wpo me (SP + 944) [C8 (NOT (E + 45448))] -> frdW s0segs Wpo me (SP + 976) [C8 (Z_to_bv 64 nSel)] ->
    frdW s0segs Wpo me (SP + 1024) [C8 (Z_to_bv 64 (GE nMTF gs + 1))] ->
    (forall m' (a0 a1 a3 : word), fastb nG nMTF gs = true ->
      u32arr s0segs m' (SP + 1060) (zw32 (zincr fave bt) 6) ->
      u8arr s0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (SP + 912) [C8 (Z_to_bv 64 (totc + bc))] ->
      mem_inv s0segs m' -> munch Wpo me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 gs) (Z_to_bv 64 (1032 * bt)) a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x199fc) fc None m' (seg_rom s0segs))) ->
    (forall m' (a3 a5 : word), fastb nG nMTF gs = false ->
      u32arr s0segs m' (SP + 1060) (zw32 (zincr fave bt) 6) ->
      u8arr s0segs m' (E + 1704) (ovb (zset sel nSel (bt mod 256)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (SP + 912) [C8 (Z_to_bv 64 (totc + bc))] ->
      mem_inv s0segs m' -> munch Wpo me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG t0 t1 t2 (Z_to_bv 64 bt) (Z_to_bv 64 (GE nMTF gs + 1)) a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b250) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 (Z_to_bv 64 bt) (Z_to_bv 64 bc) a2 a3 (Z_to_bv 64 gs) a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x19920) fc None m (seg_rom s0segs)).
  Proof.
    intros gs bt bc totc nSel fave sel me m t0 t1 t2 a2 a3 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 Hgs Hbt Hbc Htc Htb HnS Hfv FAVE SEL C912 MI MU WM
      V800 V808 V816 V824 V896 V904 V944 V976 V1024 KF KS.
    openCX. try clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    assert (HMd : nMTF = e_nMTF e) by reflexivity.
    cps_pose (GE_facts nMTF gs ltac:(lia)) as (G1 & G2 & G3). set (ge := GE nMTF gs) in *.
    pose proof (zw32_length_nat fave 6) as LFV. pose proof (jseg_length J 1704 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ4. pose proof (ovb_length sel (jseg J 1704 18002) 18002 ltac:(lia)) as LSL.
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    (* [comment removed for export] *)
    pose proof (rw_cells_lw_C8 s0segs m (SP + 912) [] _ [] (wa (SP + 912)) C912 ltac:(cbn [cells_size]; unfold wa; f_equal; lia)) as RD.
    wstep. clear RD.
    (* [comment removed for export] *)
    wstep. wstep. wstep; lit_store.
    (* [comment removed for export] *)
    poseV V808 RO. urun_to 0x1995c%Z. clear RO.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (zw32_read s0segs mm (SP + 1060) fave 6 bt _ FAVE ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    wstep. clear RD. try rewrite (sx32_of_Z (zget fave bt)) by lia.
    (* [comment removed for export] *)
    urun_to 0x1996c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok s0segs mm (SP + 1060) _ bt _ FAVE ltac:(rewrite zw32_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO2 end.
    wstep. store_addr (SP + 1060 + 4 * bt)%Z. zw32_store FAVE bt (zget fave bt + 1)%Z (rewrite unsigned_lit by lia; reflexivity).
    change (zset fave bt (zget fave bt + 1)) with (zincr fave bt) in FAVE.
    (* [comment removed for export] *)
    poseV V976 R1. poseV V800 R2. poseV V824 R3. poseV V816 R4. urun_to 0x1999c%Z. clear R1 R2 R3 R4.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok s0segs mm (E + 1704) _ nSel _ SEL ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    wstep. store_addr (E + 1704 + nSel)%Z. ovb_store1 SEL nSel.
    replace (wr8 sel nSel (bv_unsigned (Z_to_bv 64 bt))) with (zset sel nSel (bt mod 256)) in SEL by (unfold wr8; rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    poseV V904 RO. wstep. clear RO.
    wstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
      (* [comment removed for export] *)
      poseV V896 RO. urun_to 0x199d4%Z. clear RO.
      wstep; if_cases K50; zify_cond_z K50.
      + assert (FB : fastb nG nMTF gs = true) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
        (* [comment removed for export] *)
        poseV V944 RO. urun_to 0x199fc%Z. clear RO.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KF mm _ _ _ FB) end;
          [st_eq| exact FAVE| exact SEL| eassumption| assumption| assumption| assumption].
      + assert (FB : fastb nG nMTF gs = false) by (unfold fastb; change (GE nMTF gs) with ge; rewrite E6; replace (ge - gs =? 49)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
        poseV V1024 RO. urun_to 0x1b250%Z. clear RO.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ _ FB) end;
          [st_eq| exact FAVE| exact SEL| eassumption| assumption| assumption| assumption].
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
      assert (FB : fastb nG nMTF gs = false) by (unfold fastb; replace (nG =? 6)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      poseV V1024 RO. urun_to 0x1b250%Z. clear RO.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KS mm _ _ FB) end;
        [st_eq| exact FAVE| exact SEL| eassumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wt := [(SP + 976, SP + 984)]%Z.
  Lemma U0_sm_tail : forall (gs nSel : Z) (me m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= gs < nMTF)%Z -> (0 <= nSel < 18002)%Z ->
    rw_cells s0segs m (SP + 976) [C8 (Z_to_bv 64 nSel)] ->
    mem_inv s0segs m -> munch Wt me m -> wmono s0segs me m ->
    frdW s0segs Wt me (SP + 920) [C8 (Z_to_bv 64 nMTF)] -> frdW s0segs Wt me (SP + 936) [C8 (Z_to_bv 64 (gs + 50))] ->
    (forall m' (a0 a1 : word), (gs + 50 < nMTF)%Z ->
      rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (nSel + 1))] ->
      mem_inv s0segs m' -> munch Wt me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17600) fc None m' (seg_rom s0segs))) ->
    (forall m' (a0 a1 : word), (nMTF <= gs + 50)%Z ->
      rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (nSel + 1))] ->
      mem_inv s0segs m' -> munch Wt me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RG t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b32c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 S6 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b310) fc None m (seg_rom s0segs)).
  Proof.
    intros gs nSel me m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 Hgs HnS C976 MI MU WM V920 V936 KN KX.
    openCX. try clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    (* [comment removed for export] *)
    wstep. wstep. wstep; lit_store.
    poseV V920 R1. poseV V936 R2. wstep. wstep. clear R1 R2.
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KX mm _ _ ltac:(lia)) end;
        [st_eq| eassumption| assumption| assumption| assumption].
    - (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KN mm _ _ ltac:(lia)) end;
        [st_eq| eassumption| assumption| assumption| assumption].
  Qed.
End U0SMBH.
End ACeilS1.
