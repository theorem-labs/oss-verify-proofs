(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require list.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib FPSteps LibIface LibBudget LibEff MmapSim LibMaskBits
  ZStores SymExec3 SymExec3Sound SymRun3 U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HCommonU1 HLib HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds PrsInv PrsStmts PmBaseU1 PmHyps PmHypsU1 PmCoreU1 PmStepU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.

Module Ly := U1Layout.

Section PM.
Context {AC : AllocCeiling}.
  Context {MI : MallocIface SEGS Ly.L} {ST : StaticsIface SEGS Ly.L}.

  Lemma cellw_frame : forall M M' a (wd : N) v,
    cellw SEGS M a wd v -> 0 <= a -> a + Z.of_N wd < 2 ^ 64 -> CRep.agree_on (zwin a (a + Z.of_N wd)) M M' -> cellw SEGS M' a wd v.
  Proof using.
    intros M M' a wd v [Hv Hr] Ha Hw AG. split; [exact Hv|]. rewrite (rdn_agree_win SEGS M M' a (N.to_nat wd)); [exact Hr | lia | rewrite N_nat_Z; lia |].
    rewrite N_nat_Z. exact AG.
  Qed.

  Lemma loop_mem_frame : forall (w : pmw MI ST) M M',
    loop_mem w M -> 0 <= w_sp w -> w_sp w + 128 < 2 ^ 64 -> CRep.agree_on (zwin (w_sp w + 24) (w_sp w + 128)) M M' -> loop_mem w M'.
  Proof using AC MI ST.
    intros w M M' LM Hlo Hhi AG. unfold loop_mem, hdr_consts in *.
    repeat match goal with |- Forall _ (_ :: _) => apply Forall_cons; [| ] | |- Forall _ [] => apply Forall_nil end;
    match goal with |- fld _ _ (w_sp w + fst ?oc) 8 _ =>
      pose proof (proj1 (Forall_forall _ _) LM oc ltac:(first [solve [clear; cbn; tauto] | cbn; tauto])) as F; cbn [fst snd] in F |- *;
      eapply fld_agree; [lia | cbn; lia | exact F | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]] end.
  Qed.

  Definition SREGS : list reg := [9; 18; 19; 20; 21; 25]%bv.
  Lemma loop_regs_glue : forall (w : pmw MI ST) R R1,
    loop_regs w R -> (forall r, In r SREGS -> getr R1 r = getr R r) ->
    getr R1 2%bv = Z_to_bv 64 (w_sp w) -> getr R1 3%bv = getr R 3%bv -> getr R1 4%bv = getr R 4%bv -> getr R1 8%bv = Z_to_bv 64 (w_p w) ->
    loop_regs w R1.
  Proof using AC MI ST.
    intros w R R1 LR GS G2 G3 G4 G8. destruct LR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9).
    unfold loop_regs. rewrite G2, G3, G4, G8, Qgp, Qtp. rewrite !GS by (unfold SREGS; (first [solve [clear; cbn; tauto] | cbn; tauto])).
    rewrite Qs1, Qs2, Qs3, Qs4, Qs5, Qs9. repeat split; reflexivity.
  Qed.
  Lemma loop_regs_kept : forall (w : pmw MI ST) R R', loop_regs w R -> kept R R' -> loop_regs w R'.
  Proof using AC MI ST.
    intros w R R' LR KP. destruct LR as (Qsp & Qgp & Qtp & Qs0 & Qs1 & Qs2 & Qs3 & Qs4 & Qs5 & Qs9). unfold loop_regs.
    rewrite !KP by (first [solve [clear; cbv; tauto] | cbv; tauto]). repeat split; assumption.
  Qed.
  Lemma loop_mem_cell : forall (w : pmw MI ST) M o v,
    loop_mem w M -> In (o, v) (hdr_consts w) -> 0 <= v < 2 ^ 64 -> cellw SEGS M (w_sp w + o) 8 v.
  Proof using AC MI ST. intros w M o v LM Hin Hv. split; [cbn; lia|]. exact (proj1 (Forall_forall _ _) LM (o, v) Hin). Qed.

  Lemma ext_val_zx2 : forall v, 0 <= v < 2 ^ 16 -> ext_val false 0 2 (Z_to_bv 64 v) = Z_to_bv 64 v.
  Proof using. intros v Hv. apply ext_val_zx_id. rewrite u64_of_Z by lia. cbn. lia. Qed.
  Lemma w2lb4_sx32 : forall v, 0 <= v < 2 ^ 32 -> word_to_le_bytes 4 (Z_to_bv 64 (PrsNeeds.sx32 v)) = word_to_le_bytes 4 (Z_to_bv 64 v).
  Proof using. intros v Hv. rewrite <- (sxw_sx32 v Hv). unfold sxw. change 32%N with (8 * 4)%N. apply (word_to_le_bytes_swrap 4). cbn; lia. Qed.
  Lemma hi16_range : forall v, 0 <= v < 2 ^ 32 -> 0 <= v / 2 ^ 16 < 2 ^ 16.
  Proof using. intros v Hv. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
  Lemma lo16_range : forall v, 0 <= v mod 2 ^ 16 < 2 ^ 16.
  Proof using. intros v. apply Z.mod_pos_bound. lia. Qed.

  Definition WIX : expr := EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit 4) (EVar 38)).
  Lemma wix_val : forall E words widx, ev E 34 = Z_to_bv 64 words -> ev E 38 = Z_to_bv 64 widx ->
    0 <= words -> 0 <= widx -> words + 4 * widx < 2 ^ 64 -> edenot E WIX = Z_to_bv 64 (words + 4 * widx).
  Proof using.
    intros E words widx H34 H38 Hw Hi Hhi. cbn [edenot WIX]. rewrite H34, H38. rewrite w_mul by lia. rewrite w_add by lia. reflexivity.
  Qed.

  Definition izero (w : pmw MI ST) (M : mem) : Prop :=
    cellw SEGS M (w_sp w + 240) 8 0 /\ cellw SEGS M (w_sp w + 248) 2 0 /\ cellw SEGS M (w_sp w + 252) 4 0 /\
    cellw SEGS M (w_sp w + 256) 4 0 /\ cellw SEGS M (w_sp w + 260) 4 0 /\ cellw SEGS M (w_sp w + 264) 8 0 /\ cellw SEGS M (w_sp w + 272) 8 0.
  Lemma izero_agree : forall (w : pmw MI ST) M M', izero w M -> 0 <= w_sp w -> w_sp w + 280 < 2 ^ 64 ->
    CRep.agree_on (fun a => zwin (w_sp w + 240) (w_sp w + 280) a /\ ~ zwin (w_sp w + 250) (w_sp w + 252) a) M M' -> izero w M'.
  Proof using AC MI ST.
    intros w M M' IZ Hlo Hhi AG. destruct IZ as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold izero.
    repeat match goal with |- _ /\ _ => split end;
      (eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]]).
  Qed.

  Definition ictx (w : pmw MI ST) (M : mem) (io fw iwc op d : Z) : Prop :=
    cellw SEGS M (w_sp w + 216) 8 io /\ cellw SEGS M (w_sp w + 236) 4 fw /\ cellw SEGS M (w_sp w + 234) 2 iwc /\
    cellw SEGS M (w_sp w + 250) 2 op /\ fld SEGS M (w_sp w + 224) 8 d.
  Lemma ictx_agree : forall (w : pmw MI ST) M M' io fw iwc op d, ictx w M io fw iwc op d -> 0 <= w_sp w -> w_sp w + 280 < 2 ^ 64 ->
    CRep.agree_on (fun a => zwin (w_sp w + 216) (w_sp w + 240) a \/ zwin (w_sp w + 250) (w_sp w + 252) a) M M' -> ictx w M' io fw iwc op d.
  Proof using AC MI ST.
    intros w M M' io fw iwc op d IC Hlo Hhi AG. destruct IC as (C1 & C2 & C3 & C4 & C5). unfold ictx.
    repeat match goal with |- _ /\ _ => split end;
      [ eapply (cellw_frame M M'); [eassumption | lia | cbn; lia | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]] .. |].
    eapply fld_agree; [lia | cbn; lia | exact C5 | eapply agree_on_weaken; [exact AG | unfold zwin; cbn; intros; lia]].
  Qed.
End PM.

Ltac rdbackz := unfold CRep.fld; repeat (rewrite rdn_wbytes_out_Z by (w2blen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia));
                first [ apply rdn_wbytes_self; w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                      | rewrite rdn_wbytes_prefix; [ reflexivity | w2blen; rewrite u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | w2blen; lia ]
                      | change (word_to_le_bytes 8 (Z_to_bv 64 0)) with (zeros 8); rewrite rdn_wbytes_zeros_in;
                        [ reflexivity | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u64_of_Z by lia; lia | rewrite !u64_of_Z by lia; lia
                        | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u64_of_Z by lia; lia ] ].
