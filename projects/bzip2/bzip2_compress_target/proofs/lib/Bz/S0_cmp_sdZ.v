(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SegsS0 StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4 BzCLemmasSd BzCLemmasSd2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsSd.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4 BzCLemmasSd BzCSmF1 S0_cmp_sdA. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_sdC. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_sdC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_sdC2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.S0_cmp_sdB5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.
 Unset Lia Cache.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
#[local] Ltac2 Set RangeFast.RF.rc_skip_hyps := fun () => [@USP2].   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.



(* [comment removed for export] *)
Lemma fast_cond_iff : forall nG ge gs, (2 <= nG <= 6)%Z -> (gs <= ge <= gs + 49)%Z ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (flag6 nG mod 18446744073709551616) (Z.b2z ((ge - gs + -49) mod 18446744073709551616 <? 1)%Z))) (Z_to_bv 64 0)) = true
  <-> (nG = 6 /\ ge = gs + 49)%Z.
Proof.
  intros nG ge gs HG Hge. unfold flag6.
  assert (B : forall b, Z.b2z b = (if b then 1 else 0)%Z) by (intros [|]; reflexivity).
  rewrite B. clear B.
  destruct (Z.eqb_spec nG 6) as [E6|N6].
  - rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec ((ge - gs + -49) mod 18446744073709551616) 1) as [L|L].
    + assert (ge = gs + 49)%Z.
      { destruct (Z.eq_dec ge (gs + 49)); [assumption|].
        replace ((ge - gs + -49) mod 18446744073709551616)%Z with (18446744073709551616 + (ge - gs + -49))%Z in L by (apply (Z.mod_unique_pos _ _ (-1)); lia). lia. }
      change (Z.land 1 1) with 1%Z. split; [intros _; lia| intros _; vm_compute; reflexivity].
    + assert (ge <> gs + 49)%Z.
      { intros E. rewrite E in L. replace (gs + 49 - gs + -49)%Z with 0%Z in L by lia. rewrite Z.mod_0_l in L; lia. }
      change (Z.land 1 0) with 0%Z. split; [intros C; vm_compute in C; discriminate| intros [_ ?]; lia].
  - rewrite Z.mod_small by lia. rewrite Z.land_0_l.
    split; [intros C; vm_compute in C; discriminate| intros [? _]; lia].
Qed.

Section SDC2.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variable NM : Z.
  Hypothesis HNM : (1 <= NM)%Z. Hypothesis HNMe : e_nMTF e = NM. Hypothesis HNMA : (2 * (NM + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFVN : forall i, (0 <= i < NM)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.

  (* [comment removed for export] *)
  Notation RY ra t0 t1 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 sc s9 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         s9 (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation APPF f sc gs H1 H2 H3 H4 := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG HNS LENF CODF SELF ZB1 sc gs H1 H2 H3 H4) (only parsing).
  Notation APPS f sc gs ge H1 H2 H3 H4 H5 := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG HNS LENF CODF SELF ZB1 sc gs ge H1 H2 H3 H4 H5) (only parsing).

  (* [comment removed for export] *)
  Lemma S0_group_tail : forall (Q : machine_state -> Prop) (sc gs : Z) (b : bw) (m : word -> option byte)
      (ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 : word),
    (0 <= sc < nSel)%Z -> (0 <= gs < NM)%Z ->
    let ge := GE NM gs in
    let bf := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs in
    (ge = GE NM gs) ->
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    MD b m ->
    (forall m' (t0' t1' s1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RY ra t0' t1' s1' (Z_to_bv 64 (ge + 1)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (E + 1704 + sc)) s4 sc (Z_to_bv 64 ge) t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RY ra t0 t1 (Z_to_bv 64 gs) a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 sc (Z_to_bv 64 ge) t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17a70) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG HNS LENF CODF SELF ZB1 NM HNM HNMA MTFVN.
    intros Q sc gs b m ra t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 t3 t4 t5 t6 Hsc Hgs. cbv zeta. intros _ OK NL MEM K.
    cps_pose (GE_facts NM gs Hgs) as (G1 & G2 & G3).
    set (ge := GE NM gs) in *.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose OK as (OKb & OKl & OKn). pose proof (SELF sc Hsc) as [SD SR].
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD eq_refl) as RD0.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 (zget SELA sc)) by lia.
    (* [comment removed for export] *)
    wstep. wstep; notrap.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kc.
    - (* [comment removed for export] *)
      destruct (proj1 (fast_cond_iff nG ge gs HG ltac:(lia)) Kc) as [F6 Ege].
      replace (Z.to_nat (ge - gs + 1)) with 50%nat in NL, K by lia.
      enter_with (APPF S0_fast50 sc gs Hsc ltac:(lia) ltac:(bz_params; lia) ltac:(intros i Hi; apply MTFVN; lia) Q b m);
        [st_eq| exact OK| exact NL| closeMD|].
      intros m' t0' t1' a1' a2' a3' a4' a5' a6' a7' MEM' OK'.
      enter_with (K m' t0' t1' _ a1' a2' a3' a4' a5' a6' a7'); [st_eq| exact MEM'| exact OK'].
    - (* [comment removed for export] *)
      wstep. wstep; if_cases Kc2; zify_cond_z Kc2; [exfalso; lia|].
      wstep. wstep.
      enter_with (APPS S0_slow_loop sc gs ge Hsc ltac:(lia) ltac:(lia) ltac:(bz_params; lia) ltac:(intros i Hi; apply MTFVN; lia)
                    (Z.to_nat (ge - gs + 1)) Q gs b m);
        [st_eq| lia| lia| lia| exact OK| exact NL| | closeMD|].
      { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
      intros m' t0' t1' a1' a2' a3' a4' a5' a6' a7' MEM' OK'.
      eapply (K m' t0' t1' _ a1' a2' a3' a4' a5' a6' a7'); [exact MEM'| exact OK'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_group : forall (Q : machine_state -> Prop) (sc gs : Z) (b : bw) (m : word -> option byte)
      (ra t0 t1 s1 a2 a3 a4 a5 a6 a7 s2 s4 s9 t3 t4 t5 t6 : word),
    (0 <= sc < nSel)%Z -> (0 <= gs < NM)%Z ->
    let ge := GE NM gs in
    let bf := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs in
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    MD b m ->
    (forall m' (t0' t1' s1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RY ra t0' t1' s1' (Z_to_bv 64 (ge + 1)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (E + 1704 + sc)) s4 sc (Z_to_bv 64 ge) t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RY ra t0 t1 s1 (Z_to_bv 64 gs) (Z_to_bv 64 NM) a2 a3 a4 a5 a6 a7 s2 s4 sc s9 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17a60) fc None m (seg_rom s0segs)).
  Proof.
    intros Q sc gs b m ra t0 t1 s1 a2 a3 a4 a5 a6 a7 s2 s4 s9 t3 t4 t5 t6 Hsc Hgs. cbv zeta. intros OK NL MEM K.
    cps_pose (GE_facts NM gs Hgs) as (G1 & G2 & G3).
    set (ge := GE NM gs) in *.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose OK as (OKb & OKl & OKn). pose proof (SELF sc Hsc) as [SD SR].
    (* [comment removed for export] *)
    wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ege : ge = (gs + 49)%Z) by (subst ge; unfold GE, BZ_G_SIZE; destruct (Z.leb_spec NM (gs + 50 - 1)); lia).
      enter_with (S0_group_tail Q sc gs b m); [st_eq| exact Hsc| exact Hgs| fold ge; lia| exact OK| fold ge; exact NL| closeMD| exact K].
    - (* [comment removed for export] *)
      wstep.
      assert (Ege : ge = (NM - 1)%Z) by (subst ge; unfold GE, BZ_G_SIZE; destruct (Z.leb_spec NM (gs + 50 - 1)); lia).
      enter_with (S0_group_tail Q sc gs b m); [st_eq| exact Hsc| exact Hgs| fold ge; lia| exact OK| fold ge; exact NL| closeMD| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_data_loop : forall (f : nat) (Q : machine_state -> Prop) (gs sc : Z) (b : bw) (m : word -> option byte)
      (ra t0 t1 s1 a2 a3 a4 a5 a6 a7 s2 s4 s9 t3 t4 t5 t6 : word),
    (0 <= sc)%Z -> (0 <= gs < NM)%Z -> (NM - gs <= Z.of_nat f)%Z ->
    let r := sm_put_data f b LENA CODA ARR1 SELA NM gs sc in
    (snd r <= nSel)%Z ->
    bw_ok b -> (bw_numZ (fst r) <= LIM)%Z ->
    MD b m ->
    (forall m' (t0' t1' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s9' : word),
        MD (fst r) m' -> bw_ok (fst r) ->
        evt s0segs Q (MS (RY ra t0' t1' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s4 (snd r) s9' t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19174) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RY ra t0 t1 s1 (Z_to_bv 64 gs) (Z_to_bv 64 NM) a2 a3 a4 a5 a6 a7 s2 s4 sc s9 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17a60) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; [lia|].
    intros Q gs sc b m ra t0 t1 s1 a2 a3 a4 a5 a6 a7 s2 s4 s9 t3 t4 t5 t6 Hsc Hgs Hf. cbv zeta. intros SCN OK NL MEM K.
    pose proof (put_data_snd_step f b LENA CODA ARR1 SELA NM gs sc ltac:(lia)) as SC1.
    rewrite put_data_S in SCN, NL, K, SC1. fold BZ_G_SIZE in SCN, NL, K, SC1.
    destruct (Z.leb_spec NM gs) as [Xg|Xg]; [lia|]. cbv zeta in SCN, NL, K, SC1.
    change (if NM <=? gs + BZ_G_SIZE - 1 then NM - 1 else gs + BZ_G_SIZE - 1)%Z with (GE NM gs) in SCN, NL, K, SC1.
    cps_pose (GE_facts NM gs ltac:(lia)) as (G1 & G2 & G3). set (ge := GE NM gs) in *.
    set (b1 := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs) in *.
    pose proof (put_data_NZM f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (put_data_snd_ge f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1)) as SG.
    eapply (S0_group Q sc gs b m); [lia| lia| exact OK| subst ge b1; lia| exact MEM|].
    fold ge. fold b1. clear MEM. intros m1 t0' t1' s1' a1' a2' a3' a4' a5' a6' a7' MEM OK1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK1 as (OK1b & OK1l & OK1n).
    (* [comment removed for export] *)
    wstep. rewrite HNMe. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (ER : sm_put_data f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1) = (b1, (sc + 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_data_S. destruct (Z.leb_spec NM (ge + 1)); [reflexivity| lia]. }
      rewrite ER in K. cbn [fst snd] in K.
      eapply K; [closeMD| exact OK1].
    - (* [comment removed for export] *)
      wstep.
      eapply (IH Q (ge + 1)%Z (sc + 1)%Z b1 m1); [lia| lia| lia| exact SCN| exact OK1| exact NL| closeMD| exact K].
  Qed.
End SDC2.

End ACeilS1.
End S0_cmp_sdC2.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_sdD.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_sdD.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
Module S0_cmp_sdE.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith.
 Unset Lia Cache.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
#[local] Ltac2 Set RangeFast.RF.rc_skip_hyps := fun () => [@USP2].   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDE.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Notation SLMA := (e_selectorMtf e).
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef SLMA i = true /\ (0 <= zget SLMA i < nG)%Z.

  (* [comment removed for export] *)
  Notation RQ ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_b3_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a1 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 : word) (xb a30 a50 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' a5' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b1)) a1 xb' (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 15) a5' a6 a7 s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 0x176d8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b)) a1 xb a30 (Z_to_bv 64 15) a50 a6 a7 s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 0x176a0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t0 t1 t2 a1 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb a30 a50 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' a5' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma S0_b15_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a1 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 : word) (xb a40 a50 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' a5' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b1)) a1 xb' (Z_to_bv 64 15) (Z_to_bv 64 (bw_live b1)) a5' a6 a7 s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 0x17740) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b)) a1 xb (Z_to_bv 64 15) a40 a50 a6 a7 s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 0x17708) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t0 t1 t2 a1 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb a40 a50 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' a5' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_bsw3_tail : forall (Q : machine_state -> Prop) (b b1 : bw) (m : word -> option byte)
      (ra t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb : word),
    let bf := bsW b 3 nG in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (forall m' (xb' : word) (b1 : bw),
        b1 = bs_needw BS_FUEL b -> MD bf m' -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ bf)) (Z_to_bv 64 (bw_numZ b)) xb' (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 5) a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                          F (Z_to_bv 64 0x17700) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b1)) a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x176e0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b b1 m ra t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb. cbv zeta. intros OK Eb1 NL L1 XB MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 3 nG = BW (Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296)) (bw_live b1 + 3) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.mod_small (29 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl nG (32 - bw_live b1 - 3) mod 4294967296))%Z.
    { rewrite (low32_or_shifted nG _ xb (bw_buff b1) XB) by lia. replace (29 - bw_live b1)%Z with (32 - bw_live b1 - 3)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rewrite EBW in K. cbn [bw_numZ bw_live bw_buff] in K.
    eapply (K _ _ b1); [exact Eb1| closeMD|].
    rewrite (low32_or_shifted nG _ xb (bw_buff b1) XB) by lia. replace (29 - bw_live b1)%Z with (32 - bw_live b1 - 3)%Z by lia.
    apply low32_small. exact XR.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_bsw3 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb : word),
    let bf := bsW b 3 nG in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (xb' : word) (b1 : bw),
        b1 = bs_needw BS_FUEL b -> MD bf m' -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ bf)) (Z_to_bv 64 (bw_numZ b)) xb' (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 5) a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                          F (Z_to_bv 64 0x17700) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) a0 (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b)) a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x17680) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 t2 a0 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb. cbv zeta. intros OK L25 NL XB MEM K.
    pose proof (bsW_NZM b 3 nG) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kv; zify_cond_z Kv; [| exfalso; revert Kv; vm_compute; lia].
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep.
      eapply (S0_bsw3_tail Q b b); [exact OK| | exact NL| lia| exact XB| closeMD| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - (* [comment removed for export] *)
      wstep. wstep.
      eapply (S0_b3_flush Q BS_FUEL b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b 3 nG) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' a5' Eb1 MEM' XB' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OKb1 & _ & _). rewrite <- Eb1 in OKb1. cps_destruct OKb1 as (OKb1 & OKl1 & OKn1).
      clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
      wstep. (* [comment removed for export] *)
      eapply (S0_bsw3_tail Q b b1); [exact OK| exact Eb1| exact NL| lia| exact XB'| closeMD| exact K].
  Qed.
  (* [comment removed for export] *)
  Lemma S0_bsw15_tail : forall (Q : machine_state -> Prop) (b b1 : bw) (m : word -> option byte)
      (ra t0 t1 t2 a1 a3 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb : word),
    let bf := bsW b 15 nSel in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (forall m' (a3' xb' : word),
        MD bf m' -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ bf)) a1 xb' a3' (Z_to_bv 64 (bw_live b1)) a5 a6 a7 s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live bf)) t6)
                          F (Z_to_bv 64 0x1775c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b1)) a1 xb a3 (Z_to_bv 64 (bw_live b1)) a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x17740) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b b1 m ra t0 t1 t2 a1 a3 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb. cbv zeta. intros OK Eb1 NL L1 XB MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 15 nSel = BW (Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296)) (bw_live b1 + 15) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.mod_small (17 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl nSel (32 - bw_live b1 - 15) mod 4294967296))%Z.
    { rewrite (low32_or_shifted nSel _ xb (bw_buff b1) XB) by lia. replace (17 - bw_live b1)%Z with (32 - bw_live b1 - 15)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rewrite EBW in K. cbn [bw_numZ bw_live bw_buff] in K.
    eapply K; [closeMD|].
    rewrite (low32_or_shifted nSel _ xb (bw_buff b1) XB) by lia. replace (17 - bw_live b1)%Z with (32 - bw_live b1 - 15)%Z by lia.
    apply low32_small. exact XR.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_bsw15 : forall (Q : machine_state -> Prop) (b : bw) (l0 : Z) (m : word -> option byte)
      (ra t0 t1 t2 a1 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb : word),
    let bf := bsW b 15 nSel in
    bw_ok b -> (bw_live b = l0 + 3)%Z -> (0 <= l0)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (a3' a4' a5' xb' : word),
        MD bf m' -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z -> bw_ok bf -> (bw_live bf <= 22)%Z ->
        evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ bf)) a1 xb' a3' a4' a5' a6 a7 s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live bf)) t6)
                          F (Z_to_bv 64 0x1775c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RQ ra t0 t1 t2 (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b)) a1 xb (Z_to_bv 64 l0) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 5) a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x17700) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b l0 m ra t0 t1 t2 a1 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 xb. cbv zeta. intros OK El0 Hl0 NL XB MEM K.
    pose proof (bsW_NZM b 15 nSel) as NZ0. unfold NZM in NZ0.
    cps_pose (bsW_facts b 15 nSel OK ltac:(lia) ltac:(lia)) as (_ & OKf & LVf & _).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (S0_bsw15_tail Q b b m); [st_eq| exact OK| | exact NL| lia| exact XB| closeMD|].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' a3' xb' MEM' XB'. eapply K; [exact MEM'| exact XB'| exact OKf| lia].
    - (* [comment removed for export] *)
      wstep.
      enter_with (S0_b15_flush Q BS_FUEL b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b 15 nSel) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' a5' Eb1 MEM' XB' L1.
      eapply (S0_bsw15_tail Q b b1 m'); [exact OK| exact Eb1| exact NL| exact L1| exact XB'| exact MEM'|].
      intros m'' a3'' xb'' MEM'' XB''. eapply K; [exact MEM''| exact XB''| exact OKf| lia].
  Qed.
End SDE.

End ACeilS1.
End S0_cmp_sdE.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
Module S0_cmp_sdE2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith.
 Unset Lia Cache.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
#[local] Ltac2 Set RangeFast.RF.rc_skip_hyps := fun () => [@USP2].   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDE2.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Notation SLMA := (e_selectorMtf e).
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef SLMA i = true /\ (0 <= zget SLMA i < nG)%Z.

  (* [comment removed for export] *)
  Notation RS ra t0 t1 t2 a0 a1 a2 a3 s2 s3 s4 s9 s10 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 a1 a2 a3 (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (-2147483648))
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_ones_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t0 t1 a1 a3 s2 s3 s4 s9 s10 t3 t5 t6 : word) (xb t20 t40 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' t2' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2' (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b1)) a1 xb' a3 (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (-2147483648)) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 (Z_to_bv 64 (bw_live b1)) t5 t6)
            F (Z_to_bv 64 0x177c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t20 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b)) a1 xb a3 (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (-2147483648)) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t40 t5 t6)
            F (Z_to_bv 64 0x17790) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t0 t1 a1 a3 s2 s3 s4 s9 s10 t3 t5 t6 xb t20 t40 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' t2' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma S0_sel0_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t1 t2 a1 a3 s2 s3 s4 s9 s10 t4 t5 t6 : word) (xb t00 t30 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' t0' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b1)) a1 xb' a3 (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (-2147483648)) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) (Z_to_bv 64 (bw_live b1)) t4 t5 t6)
            F (Z_to_bv 64 0x1782c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t00 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) (Z_to_bv 64 (bw_numZ b)) a1 xb a3 (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 (E + 19706)) (Z_to_bv 64 (-2147483648)) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t30 t4 t5 t6)
            F (Z_to_bv 64 0x177f4) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t1 t2 a1 a3 s2 s3 s4 s9 s10 t4 t5 t6 xb t00 t30 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' t0' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_ones_tail : forall (Q : machine_state -> Prop) (i j s : Z) (n : nat) (b b1 : bw) (m : word -> option byte)
      (ra a1 s2 s3 s4 s9 s10 t3 t5 t6 xb : word),
    (j + Z.of_nat (S n) = s)%Z -> (0 <= j)%Z -> (0 <= i < nSel)%Z -> (s = zget SLMA i) ->
    let bf := sm_put_ones n (bsW b 1 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (forall (Q : machine_state -> Prop) (i j s : Z) (b : bw) (m : word -> option byte)
      (ra a1 s2 s3 s4 s9 s10 t3 t5 t6 xb : word),
      (j + Z.of_nat n = s)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < nSel)%Z -> (s = zget SLMA i) ->
      let bf := sm_put_ones n b in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
      (forall m' (t2' t5' xb' : word),
          MD bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
          evt s0segs Q (MS (RS ra (Z_to_bv 64 (E + 19706 + i)) (Z_to_bv 64 s) t2' (Z_to_bv 64 (bw_numZ bf)) a1 xb' (Z_to_bv 64 i) s2 s3 s4 s9 s10 (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 (bw_live bf)) t5' t6)
                            F (Z_to_bv 64 0x177f0) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RS ra (Z_to_bv 64 (E + 19706 + i)) (Z_to_bv 64 j) (Z_to_bv 64 s) (Z_to_bv 64 (bw_numZ b)) a1 xb (Z_to_bv 64 i) s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live b)) t5 t6)
                        F (Z_to_bv 64 0x1778c) fc None m (seg_rom s0segs))) ->
    (forall m' (t2' t5' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS ra (Z_to_bv 64 (E + 19706 + i)) (Z_to_bv 64 s) t2' (Z_to_bv 64 (bw_numZ bf)) a1 xb' (Z_to_bv 64 i) s2 s3 s4 s9 s10 (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 (bw_live bf)) t5' t6)
                          F (Z_to_bv 64 0x177f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS ra (Z_to_bv 64 (E + 19706 + i)) (Z_to_bv 64 j) (Z_to_bv 64 s) (Z_to_bv 64 (bw_numZ b1)) a1 xb (Z_to_bv 64 i) s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live b1)) t5 t6)
                      F (Z_to_bv 64 0x177cc) fc None m (seg_rom s0segs)).
  Proof.
    intros Q i j s n b b1 m ra a1 s2 s3 s4 s9 s10 t3 t5 t6 xb Hj Hj0 Hi Hs. cbv zeta. intros OK Eb1 NL L1 XB MEM IHn K.
    destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR.
    pose proof (put_ones_NZM n (bsW b 1 1)) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 1 = BW (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 1)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    pose proof (lor_bit_range (bw_buff b1) (bw_live b1) ltac:(lia) ltac:(lia)) as XR.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite land255_mod, (Z.mod_small s 256) by lia. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_bit (bw_live b1) xb (bw_buff b1)); [| lia| exact XB| lia]. symmetry. apply Z.mod_small. exact XR. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (IHn Q i (j + 1)%Z s (bsW b 1 1) _ _ _ _ _ _ _ _ _ _ _);
        [st_eq; rewrite ?EBW; reflexivity| lia| lia| lia| exact Hi| exact Hs| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| | rewrite EBW; closeMD| exact K].
      rewrite EBW. cbn [bw_buff]. apply (low32_or_bit (bw_live b1) xb (bw_buff b1)); [lia| exact XB| lia].
    - (* [comment removed for export] *)
      assert (n = 0%nat) by lia. subst n. cbn [sm_put_ones] in K.
      enter_with (K _ _ _ _); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia|].
      rewrite EBW. cbn [bw_buff]. apply (low32_or_bit (bw_live b1) xb (bw_buff b1)); [lia| exact XB| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_ones_loop : forall (n : nat) (Q : machine_state -> Prop) (i j s : Z) (b : bw) (m : word -> option byte)
      (ra a1 s2 s3 s4 s9 s10 t3 t5 t6 xb : word),
    (j + Z.of_nat n = s)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < nSel)%Z -> (s = zget SLMA i) ->
    let bf := sm_put_ones n b in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (t2' t5' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS ra (Z_to_bv 64 (E + 19706 + i)) (Z_to_bv 64 s) t2' (Z_to_bv 64 (bw_numZ bf)) a1 xb' (Z_to_bv 64 i) s2 s3 s4 s9 s10 (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 (bw_live bf)) t5' t6)
                          F (Z_to_bv 64 0x177f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS ra (Z_to_bv 64 (E + 19706 + i)) (Z_to_bv 64 j) (Z_to_bv 64 s) (Z_to_bv 64 (bw_numZ b)) a1 xb (Z_to_bv 64 i) s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live b)) t5 t6)
                      F (Z_to_bv 64 0x1778c) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i j s b m ra a1 s2 s3 s4 s9 s10 t3 t5 t6 xb Hj Hj0 _ Hi Hs. cbv zeta. intros OK L25 NL XB MEM K.
    destruct (SLMF i Hi) as [ZD ZR]. rewrite <- Hs in ZR.
    rewrite put_ones_S in NL, K.
    pose proof (put_ones_NZM n (bsW b 1 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 1) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      eapply (S0_ones_tail Q i j s n b b m); [lia| lia| exact Hi| exact Hs| exact OK| | exact NL| lia| exact XB| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - (* [comment removed for export] *)
      eapply (S0_ones_flush Q BS_FUEL b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' t2' Eb1 MEM' XB' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OKb1 & _ & _). rewrite <- Eb1 in OKb1. cps_destruct OKb1 as (OKb1 & OKl1 & OKn1).
      clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
      pose proof (ovb_read1 s0segs m' (E + 19706) SLMA (jseg J 19706 18002) 18002 i _ SLM ltac:(lia) ZD eq_refl) as RD.
      wstep. clear RD. cbv beta. rewrite <- Hs. rewrite (unsigned_lit8 s) by lia.
      eapply (S0_ones_tail Q i j s n b b1 m'); [lia| lia| exact Hi| exact Hs| exact OK| exact Eb1| exact NL| exact L1| exact XB'| closeMD| exact IH| exact K].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sels_fin : forall (Q : machine_state -> Prop) (i : Z) (n : nat) (bo b1 : bw) (m : word -> option byte)
      (ra t0 t1 t2 a1 s2 s3 s4 s9 s10 t4 t5 t6 xb : word),
    (i + Z.of_nat (S n) = nSel)%Z -> (0 <= i)%Z ->
    let bf := sm_put_sels n (bsW bo 1 0) SLMA (i + 1) in
    bw_ok bo -> b1 = bs_needw BS_FUEL bo -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (* [comment removed for export] *)
    (forall (Q : machine_state -> Prop) (i : Z) (b : bw) (m : word -> option byte) (ra t0 t1 t2 a1 s2 s3 s4 s9 s10 t3 t5 t6 xb : word),
      (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
      let bf := sm_put_sels n b SLMA i in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
      (forall m' (t0' t1' t2' t3' t5' xb' : word),
          MD bf m' -> bw_ok bf -> (bw_live bf <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
          evt s0segs Q (MS (RS ra t0' t1' t2' (Z_to_bv 64 (bw_numZ bf)) a1 xb' (Z_to_bv 64 nSel) s2 s3 s4 s9 s10 t3' (Z_to_bv 64 (bw_live bf)) t5' t6)
                            F (Z_to_bv 64 0x17850) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RS ra t0 t1 t2 (Z_to_bv 64 (bw_numZ b)) a1 xb (Z_to_bv 64 i) s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live b)) t5 t6)
                        F (Z_to_bv 64 0x1777c) fc None m (seg_rom s0segs))) ->
    (forall m' (t0' t1' t2' t3' t5' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS ra t0' t1' t2' (Z_to_bv 64 (bw_numZ bf)) a1 xb' (Z_to_bv 64 nSel) s2 s3 s4 s9 s10 t3' (Z_to_bv 64 (bw_live bf)) t5' t6)
                          F (Z_to_bv 64 0x17850) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS ra t0 t1 t2 (Z_to_bv 64 (bw_numZ b1)) a1 xb (Z_to_bv 64 i) s2 s3 s4 s9 s10 (Z_to_bv 64 (bw_live b1)) t4 t5 t6)
                      F (Z_to_bv 64 0x1782c) fc None m (seg_rom s0segs)).
  Proof.
    intros Q i n bo b1 m ra t0 t1 t2 a1 s2 s3 s4 s9 s10 t4 t5 t6 xb Hi Hi0. cbv zeta. intros OK Eb1 NL XB MEM IHn K.
    pose proof (put_sels_NZM n (bsW bo 1 0) SLMA (i + 1)) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live bo) 8 ltac:(lia)) as MB.
    assert (EBW : bsW bo 1 0 = BW (bw_buff b1) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1)).
    { unfold bsW. rewrite <- Eb1. f_equal. change 4294967296%Z with M32. rewrite lor_shl0. reflexivity. }
    assert (OK2 : bw_ok (bsW bo 1 0)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (bw_buff b1). { rewrite XB. symmetry. apply Z.mod_small. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IHn Q (i + 1)%Z (bsW bo 1 0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ xb);
        [st_eq; rewrite ?EBW; reflexivity| lia| lia| lia| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| rewrite EBW; cbn [bw_buff]; exact XB| rewrite EBW; closeMD| exact K].
    - (* [comment removed for export] *)
      assert (n = 0%nat) by lia. subst n. cbn [sm_put_sels] in K.
      wstep.
      enter_with (K _ _ _ _ _ _ xb); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia| rewrite EBW; cbn [bw_buff]; exact XB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sels_outer : forall (n : nat) (Q : machine_state -> Prop) (i : Z) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a1 s2 s3 s4 s9 s10 t3 t5 t6 xb : word),
    (i + Z.of_nat n = nSel)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    let bf := sm_put_sels n b SLMA i in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (t0' t1' t2' t3' t5' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RS ra t0' t1' t2' (Z_to_bv 64 (bw_numZ bf)) a1 xb' (Z_to_bv 64 nSel) s2 s3 s4 s9 s10 t3' (Z_to_bv 64 (bw_live bf)) t5' t6)
                          F (Z_to_bv 64 0x17850) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RS ra t0 t1 t2 (Z_to_bv 64 (bw_numZ b)) a1 xb (Z_to_bv 64 i) s2 s3 s4 s9 s10 t3 (Z_to_bv 64 (bw_live b)) t5 t6)
                      F (Z_to_bv 64 0x1777c) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i b m ra t0 t1 t2 a1 s2 s3 s4 s9 s10 t3 t5 t6 xb Hi Hi0 _. cbv zeta. intros OK L25 NL XB MEM K.
    destruct (SLMF i ltac:(lia)) as [ZD ZR].
    rewrite put_sels_S in NL, K.
    set (s := zget SLMA i) in *.
    set (bo := sm_put_ones (Z.to_nat s) b) in NL, K.
    pose proof (put_sels_NZM n (bsW bo 1 0) SLMA (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM bo 1 0) as NZ0. unfold NZM in NZ0.
    pose proof (put_ones_NZM (Z.to_nat s) b) as NZo. unfold NZM in NZo. fold bo in NZo.
    destruct (put_ones_ok (Z.to_nat s) b OK) as [OKo LVo]. fold bo in OKo, LVo.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    wstep.
    pose proof (ovb_read1 s0segs m (E + 19706) SLMA (jseg J 19706 18002) 18002 i _ SLM ltac:(lia) ZD eq_refl) as RD.
    wstep. clear RD. cbv beta. fold s. rewrite (unsigned_lit8 s) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ebo : bo = b) by (subst bo; rewrite Kc; reflexivity).
      rewrite Ebo in *.
      wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        enter_with (S0_sel0_flush Q BS_FUEL b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' xb' t0' Eb1 MEM' XB' L1.
        eapply (S0_sels_fin Q i n b b1 m'); [lia| lia| exact OK| exact Eb1| exact NL| exact XB'| exact MEM'| exact IH| exact K].
      + (* [comment removed for export] *)
        wstep.
        enter_with (S0_sels_fin Q i n b b m); [st_eq| lia| lia| exact OK| | exact NL| exact XB| closeMD| exact IH| exact K].
        unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - (* [comment removed for export] *)
      wstep.
      enter_with (S0_ones_loop (Z.to_nat s) Q i 0 s b m); [st_eq| lia| lia| lia| lia| reflexivity| exact OK| lia| fold bo; lia| exact XB| closeMD|].
      fold bo. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI.
      intros m' t2' t5' xb' MEM' OK' L8 XB'.
      cps_pose OK' as (OKb' & OKl' & OKn').
      cps_pose (bs_needw_post BS_FUEL bo OK' ltac:(unfold BS_FUEL; cbn; lia)) as (OK1' & M1' & N1').
      openMD MEM'.
      (* [comment removed for export] *)
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (S0_sels_fin Q i n bo bo m'); [st_eq| lia| lia| exact OK'| | exact NL| exact XB'| closeMD| exact IH| exact K].
        unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live bo)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + enter_with (S0_sel0_flush Q BS_FUEL bo m'); [st_eq| exact OK'| lia| unfold BS_FUEL; cbn; lia| | exact XB'| closeMD|].
        { pose proof (bsW_bytes bo 1 0) as [BB _]. rewrite <- BB. lia. }
        intros b1 m'' xb'' t0'' Eb1 MEM'' XB'' L1.
        eapply (S0_sels_fin Q i n bo b1 m''); [lia| lia| exact OK'| exact Eb1| exact NL| exact XB''| exact MEM''| exact IH| exact K].
  Qed.
End SDE2.

End ACeilS1.
End S0_cmp_sdE2.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_sdF4.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdZ.S0_cmp_sdC2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdD.S0_cmp_sdD2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdZ.S0_cmp_sdE OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdZ.S0_cmp_sdE2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.
From Stdlib Require Lia. Unset Lia Cache.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
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
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDZ.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Variable NM : Z. Hypothesis HNM : (1 <= NM)%Z. Hypothesis HNMe : e_nMTF e = NM. Hypothesis HNMA : (2 * (NM + 50) <= ARR1_SIZE)%Z.
  Hypothesis ZB1 : zbok ARR1.
  Hypothesis MTFVN : forall i, (0 <= i < NM)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef (e_inUse e) k = true /\ (0 <= zget (e_inUse e) k < 256)%Z.
  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef (e_selectorMtf e) i = true /\ (0 <= zget (e_selectorMtf e) i < nG)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SCN : forall b, snd (sm_put_data (Z.to_nat (NM + 1)) b LENA CODA ARR1 SELA NM 0 0) = nSel.
  Hypothesis Li16 : Z.of_nat (length i16) = 16%Z.
  (* [comment removed for export] *)
  Variable in160 : zarr.
  Hypothesis OK0 : bw_ok (e_bw e).

  (* [comment removed for export] *)
  Let Lin16 := S0_in16_outer cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb USP1 USP2 nG nSel sv W m0 i16 INUF A.
  Let Lpin16 := S0_pin16_loop cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A.
  Let Lpinuse := S0_pinuse_outer cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 INUF A.

  (* [comment removed for export] *)
  Definition IN16 : zarr := sm_in16 16 in160 (e_inUse e) 0.
  Definition BA : bw := sm_put_in16 16 (e_bw e) IN16 0.
  Definition BB : bw := sm_put_inuse 16 BA IN16 (e_inUse e) 0.
  Definition BC3 : bw := bsW BB 3 nG.
  Definition BC : bw := bsW BC3 15 nSel.
  Definition BD : bw := sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0.
  Definition BE : bw := sm_put_lens (Z.to_nat nG) BD LENA A 0.
  Definition RF : bw * Z := sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0.
  Hypothesis ELIM : bw_numZ (fst RF) = LIM.

  Lemma IN16R : forall k, (0 <= k < 16)%Z -> zget IN16 k = ROW16 (e_inUse e) k.
  Proof. intros k Hk. unfold IN16. apply smD_in16_row. exact Hk. Qed.

  (* [comment removed for export] *)
  Lemma NZ_chain : (bw_numZ (e_bw e) <= bw_numZ BA /\ bw_numZ BA <= bw_numZ BB /\ bw_numZ BB <= bw_numZ BC3 /\ bw_numZ BC3 <= bw_numZ BC /\
                    bw_numZ BC <= bw_numZ BD /\ bw_numZ BD <= bw_numZ BE /\ bw_numZ BE <= bw_numZ (fst RF))%Z.
  Proof.
    repeat split.
    - exact (put_in16_NZM 16 (e_bw e) IN16 0).
    - exact (put_inuse_NZM 16 BA IN16 (e_inUse e) 0).
    - exact (bsW_NZM BB 3 nG).
    - exact (bsW_NZM BC3 15 nSel).
    - exact (put_sels_NZM (Z.to_nat nSel) BC (e_selectorMtf e) 0).
    - exact (put_lens_NZM (Z.to_nat nG) BD LENA A 0).
    - exact (put_data_NZM (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0).
  Qed.
  (* [comment removed for export] *)
  Lemma BB_unfold : sm_put_inuse 16 BA IN16 (e_inUse e) 0 = BB.
  Proof. unfold BB. reflexivity. Qed.
  #[local] Opaque IN16 BA BB BC3 BC BD BE RF.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smD_seg : forall (Q : machine_state -> Prop)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    MS3 cx g e nG nSel usp sv W m0 i16 (e_bw e) m0 ->
    (forall m' i16' (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
        MS3 cx g e nG nSel usp sv W m0 i16' (fst RF) m' -> Z.of_nat (length i16') = 16%Z -> bw_ok (fst RF) ->
        evt s0segs Q (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                          F (Z_to_bv 64 0x19190) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 nG) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17474) fc None m0 (seg_rom s0segs)).
  Proof.
    intros Q ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 MEM K.
    cps_pose NZ_chain as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6). pose proof HLIM as HLIM'. bz_params. rewrite <- ELIM in HLIM'.
    cps_pose OK0 as (OKb & OKl & OKn).
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    (* [comment removed for export] *)
    do 11 wstep.
    rewrite HAe.
    enter_with (Lin16 16%nat Q 0%Z i16 (e_bw e) m0); [st_eq| lia| lia| lia| exact Li16| intros; lia| closeMD|].
    clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI MU WM.
    intros m1 bs1 t0_1 a5_1 a6_1 a7_1 MEM L1 ROWS1.
    pose proof (S0_bsw3 cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 bs1 A HG) as Lbsw3.
    pose proof (S0_bsw15 cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 bs1 A HNS) as Lbsw15.
    pose proof (S0_sels_outer cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 bs1 A HG HNS SLMF) as Lsels.
    pose proof (S0_lens_outer cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 bs1 A HAe HA HG LENF) as Llens.
    pose proof (S0_data_loop cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 bs1 A HA HG HNS LENF CODF SELF ZB1 NM HNM HNMe HNMA MTFVN) as Ldata.
    openMD MEM.
    (* [comment removed for export] *)
    do 10 wstep.
    enter_with (Lpin16 16%nat Q 0%Z IN16 bs1 (e_bw e) m1);
      [st_eq| lia| lia| lia| exact L1| exact ROWS1| exact IN16R| exact OK0| lia| change (sm_put_in16 16 (e_bw e) IN16 0) with BA; lia| | closeMD|].
    { rewrite ?low32_sx32, ?low32_lit. apply Z.mod_small. lia. }
    change (sm_put_in16 16 (e_bw e) IN16 0) with BA. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI MU WM.
    intros m2 a1_2 t2_2 xb2 MEM OKA LA XA ->.
    cps_pose OKA as (OKAb & OKAl & OKAn). openMD MEM.
    (* [comment removed for export] *)
    do 6 wstep.
    enter_with (Lpinuse 16%nat Q 0%Z IN16 bs1 BA m2);
      [st_eq| lia| lia| lia| exact L1| exact ROWS1| exact IN16R| exact OKA| lia| rewrite BB_unfold; lia| exact XA| closeMD|].
    rewrite BB_unfold. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI MU WM.
    intros m3 t2_3 t3_3 t4_3 xb3 MEM OKB LB XB.
    (* [comment removed for export] *)
    eapply (Lbsw3 Q BB m3); [exact OKB| exact LB| change (bsW BB 3 nG) with BC3; lia| exact XB| exact MEM|].
    clear MEM. intros m4 xb4 bB1 EbB1 MEM X4.
    cps_pose (bs_needw_post BS_FUEL BB OKB ltac:(change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OKB1 & MB1 & _). rewrite <- EbB1 in OKB1, MB1.
    pose proof (Z.mod_pos_bound (bw_live BB) 8 ltac:(lia)) as MB8.
    assert (OKC3 : bw_ok (bsW BB 3 nG)) by (apply bw_ok_bsW; [exact OKB| lia| lia]).
    assert (LC3 : bw_live (bsW BB 3 nG) = (bw_live bB1 + 3)%Z) by (unfold bsW; rewrite <- EbB1; reflexivity).
    (* [comment removed for export] *)
    eapply (Lbsw15 Q (bsW BB 3 nG) (bw_live bB1) m4); [exact OKC3| exact LC3| cps_destruct OKB1 as (?&?&?); lia| change (bsW (bsW BB 3 nG) 15 nSel) with BC; lia| exact X4| exact MEM|].
    change (bsW (bsW BB 3 nG) 15 nSel) with BC. clear MEM. intros m5 a3_5 a4_5 a5_5 xb5 MEM XC OKC LC.
    cps_pose OKC as (OKCb & OKCl & OKCn). openMD MEM.
    (* [comment removed for export] *)
    wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    do 7 wstep.
    enter_with (Lsels (Z.to_nat nSel) Q 0%Z BC m5);
      [st_eq| lia| lia| lia| exact OKC| lia| change (sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0) with BD; lia| exact XC| closeMD|].
    change (sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0) with BD. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI MU WM.
    intros m6 t0_6 t1_6 t2_6 t3_6 t5_6 xb6 MEM OKD LD XD.
    cps_pose OKD as (OKDb & OKDl & OKDn). openMD MEM.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kv; zify_cond_z Kv; [| exfalso; revert Kv; vm_compute; lia].
    do 9 wstep.
    enter_with (Llens (Z.to_nat nG) Q 0%Z BD m6);
      [st_eq| lia| lia| lia| exact OKD| lia| change (sm_put_lens (Z.to_nat nG) BD LENA A 0) with BE; lia| exact XD| closeMD|].
    change (sm_put_lens (Z.to_nat nG) BD LENA A 0) with BE. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI MU WM.
    intros m7 s2_7 s3_7 t2_7 t3_7 t5_7 t6_7 xb7 MEM OKE LE XE.
    cps_pose OKE as (OKEb & OKEl & OKEn). openMD MEM.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kv2; zify_cond_z Kv2; [| exfalso; revert Kv2; vm_compute; lia].
    wstep. rewrite HNMe. wstep. wstep. wstep; if_cases Kn; zify_cond_z Kn; [| exfalso; lia].
    do 7 wstep.
    enter_with (Ldata (Z.to_nat (NM + 1)) Q 0%Z 0%Z BE m7);
      [st_eq| lia| lia| lia| rewrite SCN; lia| exact OKE| change (sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0) with RF; lia| closeMD|].
    change (sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0) with RF. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI MU WM.
    intros m8 t0_8 t1_8 s1_8 a0_8 a1_8 a2_8 a3_8 a4_8 a5_8 a6_8 a7_8 s2_8 s9_8 MEM OKF.
    replace (snd RF) with nSel by (change RF with (sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0); symmetry; apply SCN).
    openMD MEM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases Ke; zify_cond_z Ke; [| exfalso; lia].
    eapply K; [closeMD| exact L1| exact OKF].
  Qed.
End SDZ.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Transparent IN16 BA BB BC3 BC BD BE RF.
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Lemma RF_smD_bd : forall e0 c0 f0 p0 i0 h0 w0 q0,
  RF (est_C e0 c0 f0 p0 h0 w0 q0) (smA_ng e0) (smB_nsel e0 c0 f0 h0 w0 q0) (e_nInUse (est_C e0 c0 f0 p0 h0 w0 q0) + 2) (e_nMTF (est_C e0 c0 f0 p0 h0 w0 q0)) i0
  = smD_bd e0 c0 f0 p0 i0 h0 w0 q0.
Proof.
  intros. unfold RF, BE, BD, BC, BC3, BB, BA, IN16, smD_bd, smD_b4, smD_b3, smD_b2, smD_b1, smD_b0, smD_in16, sm_nmtf, sm_alpha.
  cbn [e_nMTF e_len e_code e_arr1 e_selector e_selectorMtf e_inUse e_bw e_nInUse est_C]. reflexivity.
Qed.
End ACeilS2.

#[local] Opaque IN16 BA BB BC3 BC BD BE RF.
Section ACeilS3. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Theorem S0_smD : S0_smD_spec sd_facts.
Proof.
  unfold S0_smD_spec. intros Q cx g e0 c0 f0 p0 i0 h0 w0 q0 m sv W i16.
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc. cbv zeta.
  intros Gmtf Gbs Gzb CX SEP USP1 USP2 Hnb ROOM OK0 Li16 SDF MEM K.
  unfold sd_facts in SDF. cbv zeta in SDF.
  cps_destruct SDF as (HA & HG & HNS & HNM & HNMA & ZB1 & MTFVN & INUF & SLMF & SELF & LENF & CODF & SCN).
  set (e := est_C e0 c0 f0 p0 h0 w0 q0) in *.
  assert (EbD : e_bw (est_D e0 c0 f0 p0 i0 h0 w0 q0) = fst (RF e (smA_ng e0) (smB_nsel e0 c0 f0 h0 w0 q0) (e_nInUse e + 2) (e_nMTF e) i0)).
  { subst e. rewrite RF_smD_bd. reflexivity. }
  rewrite EbD in ROOM, K.
  assert (Gzb' : g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e)) by exact Gzb.
  assert (Hnb' : (0 <= e_nblock e)%Z) by exact Hnb.
  assert (OK0' : bw_ok (e_bw e)) by exact OK0.
  assert (ROOM' : (e_nblock e + bw_numZ (fst (RF e (smA_ng e0) (smB_nsel e0 c0 f0 h0 w0 q0) (e_nInUse e + 2) (e_nMTF e) i0)) <= ARR2_SIZE)%Z) by exact ROOM.
  assert (MEM' : MS3 cx g e (smA_ng e0) (smB_nsel e0 c0 f0 h0 w0 q0) (bv_unsigned sp) sv W m i16 (e_bw e) m) by exact MEM.
  clear Gzb Hnb OK0 ROOM MEM.
  eapply (S0_smD_seg cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb' Hnb' USP1 USP2 _ ROOM'
            (smA_ng e0) (smB_nsel e0 c0 f0 h0 w0 q0) sv W m i16 (e_nInUse e + 2)%Z eq_refl HA HG HNS (e_nMTF e) HNM eq_refl
            HNMA ZB1 MTFVN INUF SLMF SELF LENF CODF SCN Li16 i0 OK0' eq_refl Q).
  - exact MEM'.
  - intros m' i16'. intros. eapply K; [eassumption| assumption| assumption].
Qed.

End ACeilS3.
