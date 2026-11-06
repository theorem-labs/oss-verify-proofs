(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.

Module A_Leaf.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition crc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] v v' /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ stk rsegs v' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition crc0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] v v' /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ stk rsegs v' lo (bv_unsigned sp).

  Lemma crc32_buf : crc32_stmt ->
    forall (B : Z) (inp : list byte) (lo : Z)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a1 = Z_to_bv 64 B -> bv_unsigned a2 mod 2^32 = Z.of_nat (length inp) ->
      bytes_at rsegs v B inp -> shadowed LPA v B (Z.of_nat (length inp)) ->
      cenv v -> stk rsegs v lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      evt rsegs (crc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 crc32_entry) fc None v (seg_rom rsegs)).
  Proof.
    intros HCRC. intros until v. intros EA1 EA2 BY SH CE ST W CEIL MI.
    eapply evt_mono.
    { eapply (HCRC B inp lo); [exact EA1| exact EA2| right; split; [exact BY| exact SH]| exact CE| exact ST
                              | unfold CRC_STACK; lia| exact CEIL| exact MI]. }
    intros ms' PO. unfold leaf_post, CRC_STACK in PO. unfold crc_post.
    (first [ dex16 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v'; dand5 PO as E MU WM MI' ST' | dand21 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v' E MU WM MI' ST' | destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & v' & E & MU & WM & MI' & ST') ]).
    do 16 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
  Qed.

  Lemma crc32_null : crc32_stmt ->
    forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
      cenv v -> stk rsegs v lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> alloc_ceiling <= lo -> mem_inv rsegs v ->
      evt rsegs (crc0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 crc32_entry) fc None v (seg_rom rsegs)).
  Proof.
    intros HCRC. intros until v. intros -> -> CE ST W CEIL MI.
    eapply evt_mono.
    { eapply (HCRC 0 [] lo); [reflexivity| reflexivity| left; reflexivity| exact CE| exact ST| unfold CRC_STACK; lia| exact CEIL| exact MI]. }
    intros ms' PO. unfold leaf_post, CRC_STACK in PO. cbn [Z.eqb] in PO. unfold crc0_post.
    (first [ dex16 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v'; dand5 PO as E MU WM MI' ST' | dand21 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v' E MU WM MI' ST' | destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & v' & E & MU & WM & MI' & ST') ]).
    do 15 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
  Qed.
  (* [comment removed for export] *)
  Definition c64_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] v v' /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ stk rsegs v' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition crc32_combine_stmt2 : Prop :=
    forall (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> lo + C64_STACK <= bv_unsigned sp -> alloc_ceiling <= lo ->
      mem_inv rsegs v ->
      bv_unsigned a2 < 2^63 ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None C64_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 crc32_combine_entry) fc None v (seg_rom rsegs)).

  Lemma crc32_combine_w2 : crc32_combine_stmt2 ->
    forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      cenv v -> stk rsegs v lo (bv_unsigned sp) -> lo + 48 <= bv_unsigned sp -> alloc_ceiling <= lo -> mem_inv rsegs v ->
      bv_unsigned a2 < 2^63 ->
      evt rsegs (c64_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 crc32_combine_entry) fc None v (seg_rom rsegs)).
  Proof.
    intros HC64. intros until v. intros CE ST W CEIL MI LEN.
    eapply evt_mono.
    { eapply (HC64 lo); [exact CE| exact ST| unfold C64_STACK; lia| exact CEIL| exact MI| exact LEN]. }
    intros ms' PO. unfold leaf_post, C64_STACK in PO. unfold c64_post.
    (first [ dex16 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v'; dand5 PO as E MU WM MI' ST' | dand21 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v' E MU WM MI' ST' | destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & v' & E & MU & WM & MI' & ST') ]).
    do 16 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
  Qed.

  (* [comment removed for export] *)
End S.
End A_Leaf.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59.A_Leaf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, vep_default_cb_post, CB_STACK, CRC_STACK, C64_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sx32_small : forall z, (0 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32)%Z with 4294967296%Z. change (4294967296 `div` 2)%Z with 2147483648%Z. lia.
Qed.

Lemma swrap32_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 (z + 0) = z.
Proof.
  intros z Hz. rewrite Z.add_0_r. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648. lia.
Qed.

Lemma vkeep_refl : forall (v : vep) ch, vkeep v v ch.
Proof. intros v ch f _. reflexivity. Qed.
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma vkeep_fupd : forall (v v' : vep) ch f x, vkeep v v' ch -> In f ch -> vkeep v (fupd v' f x) ch.
Proof.
  intros v v' ch f x VK IN g NG. unfold fupd. destruct (vf_beq g f) eqn:E; [| apply VK, NG].
  apply vf_beq_eq in E. subst g. contradiction.
Qed.

End CEIL.
(* [comment removed for export] *)
Ltac in_tac := cbn; repeat first [ left; reflexivity | right ]; reflexivity.
Ltac notin_tac := cbn; let X := fresh "X" in intros X; repeat (destruct X as [X|X]; [discriminate X|]); first [discriminate X | destruct X].
Ltac vkeep_tac VK := repeat (apply vkeep_fupd; [| in_tac]); exact VK.

(* [comment removed for export] *)
Ltac hide_neqs := repeat match goal with H : (?x <> ?y) |- _ => hide H end.
Ltac unhide_neqs := repeat match goal with H : kept (?x <> ?y) |- _ => unhide H end.
Ltac hide_mods := repeat match goal with H : (?x mod ?y = ?z)%Z |- _ => hide H end.
Ltac unhide_mods := repeat match goal with H : kept (?x mod ?y = ?z)%Z |- _ => unhide H end.
Ltac hide_slow := hide_neqs; hide_mods.
Ltac unhide_slow := unhide_neqs; unhide_mods.

(* [comment removed for export] *)
Ltac lit0 := try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
Ltac chk_branch :=
  let K := fresh "KS" in
  zstep; if_cases K; zify_cond K;
  [ first [ shadow_fast K; clear K | (exfalso; lia) ]
  | first [ shadow_fast K; clear K | (exfalso; lia) ] ];
  shadow_cleanup.
(* [comment removed for export] *)
Tactic Notation "vchk" constr(SRC) constr(E) constr(k) integer(n) :=
  let T := fresh "SHT" in pose proof SRC as T; rewrite E in T;
  zstep; zstep; shadow_addr T k; clear T; zstep; lit0; do n zstep; chk_branch.
Tactic Notation "vrechk" constr(SRC) constr(E) constr(X) constr(k) integer(n) :=
  let T := fresh "SHT" in pose proof SRC as T; rewrite E in T;
  shadow_addr_at T X k; clear T; zstep; lit0; do n zstep; chk_branch.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (vv : vsb_rec) (H : henv) (p mark n : Z) (seg : list byte) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis HEC : vep_emit_common_stmt.
  Hypothesis HCRC : crc32_stmt.
  Hypothesis HC64 : crc32_combine_stmt2.   (* [comment removed for export] *)
  Hypothesis HCB : vep_default_cb_stmt.
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs (aview A m).
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 p.
  Hypothesis A2 : a2 = Z_to_bv 64 mark.
  Hypothesis HMK : bool01 mark.
  Hypothesis VOBJ : vep_obj LPA A (aview A m) VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LPA VIA H A (aview A m).
  Hypothesis HLM : bool01 (v Flast_mark).
  Hypothesis CNT : vep_cnt v n.
  Hypothesis N0 : 0 <= n.
  Hypothesis NMX : n + (p - v Fver_p) < NMAX.
  Hypothesis SOBJ : vsb_obj LPA A (aview A m) (v Fvsb) vv false.
  Hypothesis NES : VEP <> v Fvsb.
  Hypothesis NEB : VEP <> vb_buf vv.
  Hypothesis EM : vb_size vv + 9 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A + vsb_extendsize (vb_size vv + 9) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A.
  Hypothesis PCM : PRIM_ROOM <= a_primcred A.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A 2 0.
  Hypothesis BSEG : bytes_at rsegs (aview A m) (v Fver_p) seg.
  Hypothesis LSEG : Z.of_nat (length seg) = p - v Fver_p.
  Hypothesis VPLO : 4096 <= v Fver_p.
  Hypothesis PHI : p <= alloc_ceiling.
  Hypothesis SHSEG : shadowed LPA (aview A m) (v Fver_p) (p - v Fver_p).
  Hypothesis SEGH : (v Fver_p = vi_empty VIA /\ seg = []) \/
                    (exists d k, a_live A d = Some k /\ 0 < k /\ d <= v Fver_p /\ p <= d + k /\ d <> VEP /\ d <> v Fvsb /\ d <> vb_buf vv).
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk rsegs (aview A m) lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + MARK_STACK <= bv_unsigned sp.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vv' : vsb_rec),
          let w' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs w' -> amd_frame md md' ->
          stk rsegs w' lo (bv_unsigned sp) ->
          vep_obj LPA A' w' VEP v' tag q -> vkeep v v' MARK_FIELDS ->
          v' Fver_p = p -> v' Flast_mark = mark -> v' Fo_pending = 0 -> vep_cnt v' (n + (p - v Fver_p)) ->
          0 <= v' Fcrc < 2^64 -> 0 <= v' Fcrcp < 2^64 ->
          vsb_obj LPA A' w' (v Fvsb) vv' false ->
          vb_len vv <= vb_len vv' <= vb_len vv + Z.min 9 (3 * (v' Fo_last - v Fo_last)) ->
          vb_size vv <= vb_size vv' <= Z.max (vb_size vv) (vb_len vv' + 4096) ->
          (vb_buf vv' = vb_buf vv \/ (a_live A (vb_buf vv') = None /\ a_live A' (vb_buf vv) = None)) ->
          (forall r, r <> vb_buf vv -> r <> vb_buf vv' -> a_live A' r = a_live A r) ->
          frames_aged A A' 2 0 ->
          a_livebytes A' = a_livebytes A + vb_size vv' - vb_size vv ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A ->
          a_seccred A - (vsb_pot vv' - vsb_pot vv) <= a_seccred A' <= a_seccred A ->
          a_primcred A - (vsb_ppot vv' - vsb_ppot vv) <= a_primcred A' <= a_primcred A ->   (* [comment removed for export] *)
          henv_ok LPA VIA H A' w' -> bytes_at rsegs w' (v Fver_p) seg ->
          cframe LPA (owned A) (owned A') (bv_unsigned sp) MARK_STACK
                 (fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40))
                 (newblk (vb_buf vv') (vb_size vv')) (aview A m) w' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Let Vmc : Z -> Prop := fun a => blk VEP 312 a \/ newblk (vb_buf vv) (vb_size vv) a \/ (v Fvsb <= a < v Fvsb + 40).
  Let l : Z := p - v Fver_p.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="l SEGH LSEG sp seg VEP"] Lemma seg_shadowed : forall Ax mx mdx,
    ainv Ax mx mdx -> (forall r, r <> vb_buf vv -> a_live A r = None \/ a_live Ax r = a_live A r) ->
    shadowed LPA (aview Ax mx) (v Fver_p) (p - v Fver_p).
  Proof.
    intros Ax mx mdx AIx LQ. pose proof alloc_ceiling_num as ACV.
    destruct SEGH as [[EV ES] | (d & k & LD & K0 & D0 & D1 & N1 & N2 & N3)].
    - rewrite ES in LSEG. cbn in LSEG. rewrite EV.
      eapply shadowed_sub; [apply shadowed_empty; exact (proj1 (cenv_intro Ax mx mdx AIx))| lia| lia].
    - destruct (LQ d N3) as [X|X]; [rewrite X in LD; discriminate|].
      rewrite <- X in LD. (first [ pose proof ((live_geomP LPA Ax mx mdx d k AIx LD)) as dR_3; dand5 dR_3 as _ D16 DLO DHI _ | destruct (live_geomP LPA Ax mx mdx d k AIx LD) as (_ & D16 & DLO & DHI & _) ]).
      exists d, k. split; [exact (as_live_shadow LPA Ax mx mdx d k AIx LD)|].
      split; [exact (mod8_of_mod16 d D16)|]. unfold kHighMemBeg in DLO. all_app_facts. lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj HEC (conj HCRC (conj HC64 (conj HCB (conj AINV (conj MI (conj A0 (conj A1 (conj A2 (conj HMK (conj VOBJ
      (conj VBASE (conj HENV (conj HLM (conj CNT (conj N0 (conj NMX (conj SOBJ (conj NES (conj NEB (conj EM (conj LBM (conj NLV (conj SCM (conj PCM
      (conj FY (conj BSEG (conj LSEG (conj VPLO (conj PHI (conj SHSEG (conj SEGH (conj TP (conj SP16 (conj ST (conj CEIL
      (conj LO K))))))))))))))))))))))))))))))))))))) as ALL_HYPS; clear ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (henv_geom_of_frame LPA A m md H AINV (proj1 HENV)) as HG;
    pose proof HG as (G1 & G2 & G3); unfold HFSIZE in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VIA] in ECB, EURL;
    pose proof CNT as (CN1 & CN2 & CN3 & CN4 & CN5 & CN6 & CN7);
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold NMAX in *.

  (* [comment removed for export] *)
  Local Ltac seg_prelims AINVx VLVx SOBJx NEBx BSEGx :=
    prelims;
    pose proof (live_geomP LPA _ _ _ VEP _ AINVx VLVx) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    pose proof (mod8_of_mod16 VEP V16) as V8;
    pose proof VOBJ as (_ & _ & TAG & PADS); (first [ pose proof (PADS) as dR_4; dand7 dR_4 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    pose proof (bytes_at_bound _ _ _ _ BSEGx) as SEGBD;
    (first [ pose proof ((vsb_obj_geom LPA _ _ _ (v Fvsb) _ false AINVx SOBJx)) as dR_5; dand11 dR_5 as S16 Slo Shi Simg B16 Blo Bhi Bimg _ Smap Bmap | pose proof (vsb_obj_geom LPA _ _ _ (v Fvsb) _ false AINVx SOBJx) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & _ & Smap & Bmap) ]);
    pose proof (proj1 (proj2 SOBJx)) as VINVx; (first [ pose proof (VINVx) as dR_6; dand3 dR_6 as Vsz Vlen _ | pose proof VINVx as (Vsz & Vlen & _) ]);
    pose proof (proj1 (proj2 (proj2 (proj2 SOBJx)))) as VLBx;
    pose proof (as_live_disjoint LPA _ _ _ VEP 312 (v Fvsb) 40 AINVx VLVx (proj1 (proj2 (proj2 SOBJx))) NES) as DVS;
    pose proof (as_live_disjoint LPA _ _ _ VEP 312 _ _ AINVx VLVx VLBx NEBx) as DVB;
    unfold kHighMemBeg in *; all_app_facts;
    pose proof (sh_bound (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact Vhi)) as SHVB; rewrite SHMAX_val in SHVB;
    change ((312 + 7) / 8) with 39 in SHVB;
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVx VLVx) as SHV0; fold_cl_segs; fold_aview;
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0;
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0;
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity);
    pose proof BSEGx as BSEG0; hide BSEG0; hide DVS; hide DVB.

  (* [comment removed for export] *)
  #[using="l K LO CEIL ST SP16 TP SEGH SHSEG PHI VPLO LSEG BSEG FY SCM PCM NLV LBM EM NEB NES SOBJ NMX N0 CNT HLM HENV VBASE VOBJ HMK A2 A1 A0 MI AINV HCB HC64 HCRC HEC a2 a1 a0"] Lemma mc_stepC :
    forall (xra xs1 xs3 xs4 xs9 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (ja jb : list byte)
           (Ax : AS) (mx : mem) (mdx : Model) (vx : vep) (vvx : vsb_rec),
      ainv Ax mx mdx -> mem_inv rsegs (aview Ax mx) -> amd_frame md mdx ->
      stk rsegs (aview Ax mx) lo (bv_unsigned sp + -160) ->
      rw_cells rsegs (aview Ax mx) (bv_unsigned sp + -160)
        [CB 8 ja; C8 (Z_to_bv 64 (VEP + 304)); CB 8 jb; C8 (Z_to_bv 64 ((VEP + 304) / 8 + 2147450880));
         C8 (Z_to_bv 64 (VEP + 40)); C8 (Z_to_bv 64 (VEP + 24)); C8 (Z_to_bv 64 p);
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs (aview Ax mx) VEP (vep_cells vx tag q) -> a_live Ax VEP = Some 312 ->
      vkeep v vx MARK_FIELDS -> vx Fver_p = v Fver_p -> vx Fo_pending = 0 -> vep_cnt vx n ->
      vsb_obj LPA Ax (aview Ax mx) (v Fvsb) vvx false ->
      vb_len vv <= vb_len vvx <= vb_len vv + Z.min 9 (3 * (vx Fo_last - v Fo_last)) ->
      vb_size vv <= vb_size vvx <= Z.max (vb_size vv) (vb_len vvx + 4096) -> VEP <> vb_buf vvx ->
      (vb_buf vvx = vb_buf vv \/ (a_live A (vb_buf vvx) = None /\ a_live Ax (vb_buf vv) = None)) ->
      (forall r, r <> vb_buf vv -> r <> vb_buf vvx -> a_live Ax r = a_live A r) ->
      frames_aged A Ax 2 0 ->
      a_livebytes Ax = a_livebytes A + vb_size vvx - vb_size vv ->
      a_tinycred Ax = a_tinycred A -> a_nlive Ax = a_nlive A ->
      a_seccred A - (vsb_pot vvx - vsb_pot vv) <= a_seccred Ax <= a_seccred A ->
      a_primcred A - (vsb_ppot vvx - vsb_ppot vv) <= a_primcred Ax <= a_primcred A ->   (* [comment removed for export] *)
      henv_ok LPA VIA H Ax (aview Ax mx) -> bytes_at rsegs (aview Ax mx) (v Fver_p) seg ->
      (v Fver_p + Z.of_nat (length seg) <= VEP \/ VEP + 312 <= v Fver_p) ->
      cframe LPA (owned A) (owned Ax) (bv_unsigned sp) MARK_STACK Vmc (newblk (vb_buf vvx) (vb_size vvx)) (aview A m) (aview Ax mx) ->
      srealizes rsegs
        (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp xt0 xt1 xt2
                        (Z_to_bv 64 VEP) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        (Z_to_bv 64 mark) xs3 xs4 (Z_to_bv 64 2147450880) (Z_to_bv 64 (VEP + 48)) (Z_to_bv 64 (VEP + 96))
                        (Z_to_bv 64 (VEP + 160)) xs9 (Z_to_bv 64 (VEP + 128)) (Z_to_bv 64 (VEP + 120)) xt3 xt4 xt5 xt6)
                   F (Z_to_bv 64 0x8e5e8) fc None mx (seg_rom rsegs)) mdx) T.
  Proof.
    touch_all.
    intros until vvx. intros AINVx MIx MDFx STx FR VEPC VLVx VK EVP EPEND CNTx SOBJx LENx SZx NEBx RELx LIVEx FAx LBx TCx NLx SCx PCx HENVx BSEGx SEGV CFx.
    seg_prelims AINVx VLVx SOBJx NEBx BSEGx. hide HMK. hide HLM.
    (first [ pose proof (CNTx) as dR_7; dand7 dR_7 as D1 D2 D3 D4 D5 D6 D7 | pose proof CNTx as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
    assert (EVCx : vx Fvc = h_vc H) by (rewrite (VK Fvc ltac:(notin_tac)); exact EVC).
    assert (ECBx : vx Fcb = 591312) by (rewrite (VK Fcb ltac:(notin_tac)); exact ECB).
    assert (EPRx : vx Fcb_priv = VEP + 56) by (rewrite (VK Fcb_priv ltac:(notin_tac)); exact EPRIV).
    (* [comment removed for export] *)
    assert (SHD : shadowed LPA (aview Ax mx) (v Fver_p) (p - v Fver_p)).
    { apply (seg_shadowed Ax mx mdx AINVx). intros r Hr.
      destruct (Z.eq_dec r (vb_buf vvx)) as [->|Hr2]; [| right; apply LIVEx; assumption].
      destruct RELx as [E|[FR' _]]; [exfalso; apply Hr; rewrite <- E; reflexivity| left; exact FR']. }
    pose proof (cenv_intro Ax mx mdx AINVx) as CEx.
    unfold vep_cells in VEPC. rewrite EVP in VEPC.
    hide SEGV. hide_slow. unhide V8.
    pose proof (munch_refl [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)] (aview Ax mx)) as MU.
    pose proof (wmono_refl rsegs (aview Ax mx)) as WM.
    assert (WMAPx : mapped (aview Ax mx) (bv_unsigned sp - 8800) 8800).
    { eapply (window_mapped LPA _ lo); [exact STx | exact FR | cbn; lia | exact CEIL | lia | lia]. }
    assert (CFP : client_fp LPA Ax (aview Ax mx) [(bv_unsigned sp - 8800, bv_unsigned sp); (VEP, VEP + 312)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8800)) with 8800 by lia; exact WMAPx |].
      split; [right; left; exists VEP, 312; split; [exact VLVx|lia]| exact I]. }
    ago AINVx. fold_cl_segs.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0.
    zstep. zstep. zstep. kdead. zstep. zstep. kdead.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0.
    zstep. zstep. rewrite (swrap32_small (p - v Fver_p)) by lia. zstep.
    icall (crc32_buf HCRC (v Fver_p) seg lo) by
      (rewrite ?unsigned_lit by lia;
       first [ reflexivity | exact BSEGx | rewrite LSEG; exact SHD | exact CEx | eassumption | lia
             | (rewrite LSEG, Z.mod_small by lia; reflexivity) ]).
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (VEP + 120) 4 0. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 2.
    (* [comment removed for export] *)
    zstep. zstep. zstep. vrechk SHV0 EzsV (VEP + 160) 8 0. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. vrechk SHV0 EzsV (VEP + 304) 4 0. zstep.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    do 14 zstep.
    try replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    release_frame FR STq (bv_unsigned sp).
    rewrite EVCx, ECBx, EPRx. zstep.
    (* [comment removed for export] *)
    pose proof (proj1 HENVx) as [agex HFRx].
    pose proof (as_frame_blk_disjoint LPA Ax mx mdx (h_ff H) HCLASS agex VEP 312 AINVx HFRx VLVx) as DJv.
    change (fsize HCLASS) with 8192 in DJv.
    pose proof (sh_bound (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in G3; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    lazymatch goal with VEPC : rw_cells _ ?mq VEP ?cs |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch cs with context [C8 (Z_to_bv 64 (vx Fo_total)) :: C4 ?cw :: _] =>
      set (v4 := fupd (fupd (fupd (fupd (fupd (fupd vx Fo_wait (vx Fo_wait + (p - v Fver_p))) Fcrc (bv_unsigned cw))
                   Fo_crc (vx Fo_crc + (p - v Fver_p))) Fver_p p) Flast_mark mark) Fcrcp ((vx Fcrcp) mod 2^64));
      assert (VEPC4 : rw_cells rsegs mq VEP (vep_cells v4 tag q))
        by (unfold vep_cells, v4; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite Z_to_bv_mod64, Z_to_bv_bv_unsigned; exact VEPC);
      clear VEPC;
      assert (HENVq : henv_ok LPA VIA H Ax mq)
        by (eapply henv_ok_munch; [exact HENVx| exact MU| exact WM| exact HG|];
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
            change (8192 / 8) with 1024 in Ha__; cbn; lia);
      (first [ pose proof (HENVq) as dR_8; dand4 dR_8 as _ _ HOBJq HSHq | pose proof HENVq as (_ & _ & HOBJq & HSHq) ])
    end end.
    icall (HCB VEP v4 tag q H (p - v Fver_p) lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact VEPC4
       | |- length _ = _ => exact TAG
       | |- vep_pads_wf _ => exact PADS
       | |- hobj_ok _ _ _ _ => exact HOBJq
       | |- hshadow _ _ _ => exact HSHq
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => eapply cenv_munch; [exact CEx| exact MU| repeat constructor; unfold const_free_ivl, CONSTS_TOP; cbn; lia]
       | |- shadowed _ _ _ _ => exists VEP, 312; split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|]; lia
       | |- stk _ _ _ _ => exact STq
       | |- mem_inv _ _ => assumption
       | |- _ => unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold kHighMemBeg, HFSIZE, CB_STACK; lia
       end).
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STf end.
    lazymatch goal with X : rw_cells _ ?mq VEP (vep_cells _ tag q) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into VEPC5 end.
    astop AINVx MU WM CFP.
    (* [comment removed for export] *)
    unhide BSEG0. unhide SEGV. unhide DVS. unhide DVB.
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mf _) ?mdf) _ =>
      lazymatch type of VEPC5 with rw_cells _ _ VEP (vep_cells ?v5 tag q) =>
      assert (MP : mapped (aview Ax mf) (bv_unsigned sp - 8800) 8800) by (eapply (stk_mapped (L:=LPA)); [exact STf | exact CEIL | lia | lia]);
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ax mf mdf v5 vvx);
      [ assumption | assumption
      | eapply amd_frame_sbm_r; [exact MDFx | eassumption]
      | exact STf
      | split; [exact VLVx|]; split; [exact VEPC5|]; split; [exact TAG| exact PADS]
      | unfold v4; vkeep_tac VK
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; reflexivity
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact EPEND
      | unfold vep_cnt, v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; lia
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb];
        match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range _ w) as UR; unfold bv_modulus in UR; cbn in UR; lia end
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; apply Z.mod_pos_bound; lia
      | eapply vsb_obj_munch; [exact SOBJx| exact MU| exact WM| intros a__ Ha__; cbn; lia]
      | unfold v4, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact LENx
      | exact SZx | exact RELx | exact LIVEx | exact FAx | exact LBx | exact TCx | exact NLx | exact SCx | exact PCx (* [comment removed for export] *)
      | eapply henv_ok_munch; [exact HENVx| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia
      | eapply (bytes_at_munch LPA); [exact BSEG0| exact MU| intros a__ Ha__; cbn; lia]
      | assert (CF2 : cframe LPA (owned Ax) (owned Ax) (bv_unsigned sp) 8800 Vmc nowhere (aview Ax mx) (aview Ax mf))
          by (eapply (cframe_noalloc LPA); [exact MU | | exact MP | intros a X; destruct X];
              intros a Ha NO; cbn [outside] in NO; unfold Vmc, blk; lia);
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview Ax mx) (aview Ax mf) CFx CF2);
        [ lia | lia | exact MP | intros a X; exact X | intros a X; right; exact X | intros a X; left; exact X ] ]
    end end.
  Qed.
End S.
