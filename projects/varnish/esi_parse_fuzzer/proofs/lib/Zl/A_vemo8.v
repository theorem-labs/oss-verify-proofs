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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.A_Leaf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.

Module A_VE0r6.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Ma6xg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp0e6 AIcpnnp AIcpya4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Po6qc A_Img A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac icall_consts_in H ::= unfold leaf_post, asan_memset_post, ASAN_MEMSET_STACK, CRC_STACK in H.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_mlia ].
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac akit_plia := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker.
Ltac akit_avoids_false X :=
  lazymatch type of X with
  | _ \/ _ => destruct X as [X|X]; akit_avoids_false X
  | False => destruct X
  | _ => try (lazymatch type of X with (_ <> _) /\ _ => destruct X as [_ X] end);
         first [ match goal with D : _ \/ _ |- _ => solve [ destruct D; akit_plia ] end | akit_plia ]
  end.
Local Ltac avoids_solve ::=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold newblk, frm in X; unfold blk, nowhere in X; cbn beta in X; first [ solve [ akit_avoids_false X ] | lia ] ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition q0 : vep_pads := VPADS (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4)
                                  (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 4).
Lemma q0_wf : vep_pads_wf q0. Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Definition ztag : list byte := repeat (Z_to_bv 8 0) 8.
(* [comment removed for export] *)
Definition vep_tail0 : list cell :=
  Eval cbv [skipn vep_cells q0 p36 p124 p140 p196 p236 p268 p308] in skipn 2 (vep_cells (fun _ => 0) ztag q0).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vep_all0 : list cell := Eval cbv [vep_tail0] in C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: vep_tail0.
Lemma vep_all0_wf : cells_wf vep_all0. Proof. cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vep_all0_bytes : cells_bytes vep_all0 = repeat (Z_to_bv 8 0) 312. Proof. vm_compute. reflexivity. Qed.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HWA : WS_Alloc_stmt.
  Hypothesis HNA : VSB_new_auto_stmt.
  Hypothesis HCRC : crc32_stmt.

  (* [comment removed for export] *)
  Definition crc0_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (v : mem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 v',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None v' (seg_rom rsegs)
      /\ munch [(bv_unsigned sp - 128, bv_unsigned sp)] v v' /\ wmono rsegs v v' /\ mem_inv rsegs v'
      /\ stk rsegs v' lo (bv_unsigned sp).

  #[using="HCRC"] Lemma crc32_null : forall (lo : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (v : mem),
    a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
    cenv v -> stk rsegs v lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> alloc_ceiling <= lo -> mem_inv rsegs v ->
    evt rsegs (crc0_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo v)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 crc32_entry) fc None v (seg_rom rsegs)).
  Proof.
    intros until v. intros -> -> CE ST W CEIL MI.
    eapply evt_mono.
    { eapply (HCRC 0 [] lo); [reflexivity| reflexivity| left; reflexivity| exact CE| exact ST| unfold CRC_STACK; lia| exact CEIL| exact MI]. }
    intros ms' PO. unfold leaf_post, CRC_STACK in PO. cbn [Z.eqb] in PO. unfold crc0_post.
    (first [ dex16 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v'; dand5 PO as E MU WM MI' ST' | dand21 PO as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 v' E MU WM MI' ST' | destruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & v' & E & MU & WM & MI' & ST') ]).
    do 15 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'| exact ST'].
  Qed.

  #[using="HCRC HNA HWA"] Lemma VEP_Init_ok : VEP_Init_stmt.
  Proof.
    unfold VEP_Init_stmt, frames_same.
    intros H flags lo. intros until T. cbv zeta. intros AINV MI Ha0 Ha1 Ha2 Ha3 Ha4 FL WS0 HENV LBMAX NLVX PCM TP SP16 ST CEIL LO K.   (* [comment removed for export] *)
    rewrite Ha0, Ha1, Ha2, Ha3, Ha4. unfold VEP_Init_entry in *.
    assert (WIN : lo + 8704 <= bv_unsigned sp) by (revert LO; unfold_stacks; lia). clear LO.   (* [comment removed for export] *)
    pose proof alloc_ceiling_num as ACV.
    (first [ pose proof (HENV) as dR_2; dand4 dR_2 as HFR GLOB HOBJ HSH | pose proof HENV as (HFR & GLOB & HOBJ & HSH) ]).
    pose proof (henv_geom_of_frame LPA A m md H AINV HFR) as HG.
    (first [ pose proof (HG) as dR_3; dand3 dR_3 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE, kHighMemBeg in G2, G3. all_app_facts.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(lia)) as SHFR.
    change ((8192 + 7) / 8) with 1024 in SHFR. rewrite SHMAX_val in SHFR.
    pose proof HFR as [age HFR'].
    (* [comment removed for export] *)
    pose proof (cenv_intro A m md AINV) as CE.
    (* [comment removed for export] *)
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2416) 56 ltac:(lia) ltac:(lia) ltac:(lia)) as SHrqR. rewrite SHMAX_val in SHrqR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2512) 56 ltac:(lia) ltac:(lia) ltac:(lia)) as SHrsR. rewrite SHMAX_val in SHrsR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2608) 72 ltac:(lia) ltac:(lia) ltac:(lia)) as SHvcR. rewrite SHMAX_val in SHvcR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 2720) 184 ltac:(lia) ltac:(lia) ltac:(lia)) as SHwkR. rewrite SHMAX_val in SHwkR.
    pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff H + 3088) 32 ltac:(lia) ltac:(lia) ltac:(lia)) as SHhdR. rewrite SHMAX_val in SHhdR.
    pose proof (hff_al8 H 2416 HG eq_refl) as ALrq. pose proof (hff_al8 H 2512 HG eq_refl) as ALrs.
    pose proof (hff_al8 H 2608 HG eq_refl) as ALvc. pose proof (hff_al8 H 2720 HG eq_refl) as ALwk. pose proof (hff_al8 H 3088 HG eq_refl) as ALhd.
    pose proof (munch_refl [(bv_unsigned sp - 8704, bv_unsigned sp)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CFP : client_fp LPA A (aview A m) [(bv_unsigned sp - 8704, bv_unsigned sp)]).
    { cbn. split; [left; split; [lia|]; split; [lia|]; eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] | exact I]. }
    unfold h_vc, h_req in *.
    ago AINV. fold_cl_segs.
    carve_frame 64%nat ST.
    (* [comment removed for export] *)
    do 9 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HENVp : henv_ok LPA VIA H A mx) by
       (eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia);
      assert (CEp : cenv mx) by
       (eapply cenv_munch; [exact CE| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
    end.
    pose proof (map_cells_of_consts _ (proj1 CEp)) as MC. open_map_cells MC.
    (first [ pose proof (HENVp) as dR_4; dand4 dR_4 as _ _ HOBJp HSHp | pose proof HENVp as (_ & _ & HOBJp & HSHp) ]).
    (first [ pose proof (HSHp) as dR_5; dand10 dR_5 as _ _ SHrq SHrs SHvc SHwk _ _ SHhd _ | pose proof HSHp as (_ & _ & SHrq & SHrs & SHvc & SHwk & _ & _ & SHhd & _) ]). fold_cl_segs.
    unfold h_req, h_resp, h_vc, h_wrk, h_hd in SHrq, SHrs, SHvc, SHwk, SHhd.
    (first [ pose proof (HOBJp) as dR_6; dand5 dR_6 as VC WK RQ RS HD | pose proof HOBJp as (VC & WK & RQ & RS & HD) ]).
    (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
    (first [ dex3 RQ as rqmid rqtl rqpad; dand4 RQ as LM3 LT3 LP3 RQ | dand7 RQ as rqmid rqtl rqpad LM3 LT3 LP3 RQ | destruct RQ as (rqmid & rqtl & rqpad & LM3 & LT3 & LP3 & RQ) ]). (first [ dex4 RS as rshd rsmid rstl rspad; dand4 RS as LM4 LT4 LP4 RS | dand8 RS as rshd rsmid rstl rspad LM4 LT4 LP4 RS | destruct RS as (rshd & rsmid & rstl & rspad & LM4 & LT4 & LP4 & RS) ]).
    fold_cl_segs. unfold vc_cells in VC. unfold wrk_cells in WK. unfold http_cells in RQ, RS.
    unfold h_vc, h_resp, h_wrk, h_req, h_hd, h_ws in VC, WK, RQ, RS, HD. cbn [vi_url VIA] in HD.
    replace (h_ff H + 3088 + 16) with (h_ff H + 3104) in HD by lia.   (* [comment removed for export] *)
    clear HENVp HOBJp HSHp CEp.
    (* [comment removed for export] *)
    zstep. kdead. zstep. zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact ALvc]. } clear KU.
    (* [comment removed for export] *)
    do 4 zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    shadow_chk SHvc 4 10. zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. zstep. kdead.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact ALrq]. } clear KU.
    shadow_chk SHrq 4 10. zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHvc 8. zstep.
    zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
    zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact ALrs]. } clear KU.
    (* [comment removed for export] *)
    zstep. shadow_chk0 SHrs 8. zstep. zstep. zstep.

    (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    pose proof (as_minv LPA A _ _ AINV) as [_ MH].
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
      assert (HENV0 : henv_ok LPA VIA H A (aview A mx)) by
       (eapply henv_ok_munch; [exact HENV| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia);
      assert (WS00 : ws0_obj LPA H (aview A mx)) by
       (eapply ws0_obj_munch; [exact WS0| exact MU| exact WM| intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn; lia]);
      pose proof (crange_stack (Clg:=Clg) (L:=LPA) A _ _ (aview A mx) (bv_unsigned sp - 64) 64 AINV0 ltac:(lia) ltac:(lia)
                    (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF;
      pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A _ _ _ _ _ (h_ff H + 2608) 72 AINV0 HFR' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRvc;
      pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A _ _ _ _ _ (h_ff H + 2720) 184 AINV0 HFR' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRwk;
      pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A _ _ _ _ _ (h_ff H + 2416) 56 AINV0 HFR' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRrq;
      pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A _ _ _ _ _ (h_ff H + 2512) 56 AINV0 HFR' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRrs;
      pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A _ _ _ _ _ (h_ff H + 3104) 8 AINV0 HFR' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRhd
    end.
    (first [ pose proof (HENV0) as dR_11; dand4 dR_11 as _ GLOB0 HOBJ0 HSH0 | pose proof HENV0 as (_ & GLOB0 & HOBJ0 & HSH0) ]).
    eapply (HWA H lo);
      [ exact AINV0 | exact MI | reflexivity | reflexivity | exact WS00 | exact GLOB0 | exact HSH0 | exact HFR | lia | try (generalize alloc_ceiling_val); clear - NLVX; try pose proof alloc_ceiling_val as ACV__; lia | clear - PCM; lia (* [comment removed for export] *) | exact TP
      | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
      | rewrite unsigned_lit by lia; exact ST | exact CEIL
      | rewrite unsigned_lit by lia; unfold_stacks; lia
      | ].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A1 mr mdr. cbv zeta.
    intros AINV1 MI1 MDF1 FRS1 TCR1 SC1 PC1 ST1 GLOB1 HSH1 OUT1.   (* [comment removed for export] *)
    fold_cl_segs. fold_aview. rewrite unsigned_lit in ST1 by lia. rewrite unsigned_lit in OUT1 by lia.
    assert (HFR1 : hframe LPA A1 H) by (eapply hframe_keep; [exact HFR| exact FRS1]). pose proof HFR1 as [age1 HFR1'].
    pose proof (cenv_intro A1 mr mdr AINV1) as CE1.
    (first [ pose proof (HSH1) as dR_12; dand10 dR_12 as _ _ SHrq1 SHrs1 SHvc1 SHwk1 _ _ SHhd1 _ | pose proof HSH1 as (_ & _ & SHrq1 & SHrs1 & SHvc1 & SHwk1 & _ & _ & SHhd1 & _) ]). fold_cl_segs. fold_aview.
    unfold h_req, h_resp, h_vc, h_wrk, h_hd in SHrq1, SHrs1, SHvc1, SHwk1, SHhd1.
    clear ST.
    destruct OUT1 as (wa & vjunk & NZ & WS11 & VEPC & FRESHw & FRESHr & LIVEq1 & LBY1 & NL1 & CF1).
    (* [comment removed for export] *)
    - (* [comment removed for export] *)
      unfold WSALLOC_STACK, WSEMUALLOC_STACK, ASTK, h_ws, h_wsbuf in CF1.
      (first [ pose proof (WS11) as dR_13; dex2 dR_13 as id1 pad1; dand7 dR_13 as IDOK1 PADL1 WSC1 WEC1 LIVEwa WAC1 LIVEr | pose proof (WS11) as dR_13; dand9 dR_13 as id1 pad1 IDOK1 PADL1 WSC1 WEC1 LIVEwa WAC1 LIVEr | pose proof WS11 as (id1 & pad1 & IDOK1 & PADL1 & WSC1 & WEC1 & LIVEwa & WAC1 & LIVEr) ]). fold_cl_segs. fold_aview.
      clear WSC1 WEC1 WAC1.
      (first [ pose proof ((live_geomP LPA A1 mr mdr r _ AINV1 LIVEr)) as dR_14; dand7 dR_14 as _ R16 Rlo Rhi _ _ _ | pose proof (live_geomP LPA A1 mr mdr r _ AINV1 LIVEr) as (_ & R16 & Rlo & Rhi & _ & _ & _) ]).
      (first [ pose proof ((live_geomP LPA A1 mr mdr wa _ AINV1 LIVEwa)) as dR_15; dand7 dR_15 as _ W16 Wlo Whi _ _ _ | pose proof (live_geomP LPA A1 mr mdr wa _ AINV1 LIVEwa) as (_ & W16 & Wlo & Whi & _ & _ & _) ]).
      unfold kHighMemBeg in Rlo, Wlo. all_app_facts. pose proof (mod8_of_mod16 r R16) as R8.
      assert (NEwr : wa <> r) by (intros ->; rewrite LIVEr in LIVEwa; discriminate).
      pose proof (as_live_disjoint LPA A1 mr mdr wa 40 r 312 AINV1 LIVEwa LIVEr NEwr) as DWR.
      pose proof (as_frame_blk_disjoint LPA A1 mr mdr (h_ff H) HCLASS age1 r 312 AINV1 HFR1' LIVEr) as DJr.
      pose proof (as_frame_blk_disjoint LPA A1 mr mdr (h_ff H) HCLASS age1 wa 40 AINV1 HFR1' LIVEwa) as DJw.
      change (fsize HCLASS) with 8192 in DJr, DJw.
      pose proof (sh_boundL (Clg:=Clg) r 312 ltac:(lia) ltac:(lia) ltac:(lia)) as SHRN. rewrite SHMAX_val in SHRN.
      pose proof (sh_boundL (Clg:=Clg) wa 40 ltac:(lia) ltac:(lia) ltac:(lia)) as SHWN. rewrite SHMAX_val in SHWN.
      acall_xfer CF1. rename ST1 into ST.
      assert (HOBJ1 : hobj_ok LPA VIA H (aview A1 mr)).
      { eapply hobj_ok_ccall; [exact AINV0| exact HFR| exact CF1| exact HOBJ0| lia| intros a__ Ha__ X; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha__; cbn beta in X; lia]. }
      assert (HENV1 : henv_ok LPA VIA H A1 (aview A1 mr)) by (split; [exact HFR1| split; [exact GLOB1| split; [exact HOBJ1| exact HSH1]]]).
      pose proof (as_live_shadow LPA A1 mr mdr r 312 AINV1 LIVEr) as SHR. fold_cl_segs. fold_aview.
      pose proof (shpat_sh_boundL (Clg:=Clg) r 312 ltac:(lia) ltac:(lia) ltac:(lia)) as SHRB. rewrite SHMAX_val in SHRB.
      pose proof (live_range_ok (Clg:=Clg) A1 mr mdr r 312 r 312 AINV1 LIVEr ltac:(lia) ltac:(lia) ltac:(lia)) as RW304.   (* [comment removed for export] *)
      pose proof (munch_refl [(bv_unsigned sp - 8704, bv_unsigned sp); (r, r + 312)] (aview A1 mr)) as MU2.
      pose proof (wmono_refl rsegs (aview A1 mr)) as WM2.
      assert (WMAP2 : mapped (aview A1 mr) (bv_unsigned sp - 8704) 8704).
      { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
      assert (CFP2 : client_fp LPA A1 (aview A1 mr) [(bv_unsigned sp - 8704, bv_unsigned sp); (r, r + 312)]).
      { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8704)) with 8704 by lia; exact WMAP2 |].
        split; [right; left; exists r, 312; split; [exact LIVEr|lia]| exact I]. }
      pose proof (map_cells_of_consts _ (proj1 CE1)) as MC1. fold_aview. open_map_cells MC1.
      (first [ pose proof ((asan_memset_cells_of_consts _ (proj1 CE1))) as dR_16; dand4 dR_16 as Gric Cric Crms _ | destruct (asan_memset_cells_of_consts _ (proj1 CE1)) as (Gric & Cric & Crms & _) ]). fold_aview.
      (* [comment removed for export] *)
      rename VEPC into VEPT.
      ago AINV1. fold_cl_segs. fix_ret_pc.
      (* [comment removed for export] *)
      zstep. zstep. kdead. zstep. zstep. zstep. zstep.
      icall asan_memset_spec by
        (rewrite ?unsigned_lit by lia;
         first [ exact VEPT | exact ST | exact CEIL | rebundle
               | unfold ASAN_MEMSET_STACK; lia
               | (left; lia)
               | lia
               | (right; eapply range_ok_high_munch; [exact RW304| exact MU2| lia| lia| lia| repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; rewrite SHMAX_val; lia])
               | assumption ]).
      lazymatch goal with X : rw_cells _ ?mx r [CB _ (repeat _ _)] |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into VEPZ end.
      lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
      change (Z.to_nat 312) with 312%nat in VEPZ. change (0 mod 256) with 0 in VEPZ.
      apply (rw_cells_recast rsegs _ _ _ vep_all0) in VEPZ; [| exact vep_all0_wf | exact vep_all0_bytes].
      unfold vep_all0 in VEPZ.
      (* [comment removed for export] *)
      zstep. zstep. if_cases KU; zify_cond KU. { exfalso. apply KU. apply land7_of_mod8; [lia| exact R8]. } clear KU.
      shadow_chk SHR 4 10. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      shadow_chk SHR 4 12. zstep.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHrq1 8. zstep.
      zstep. if_cases KU; zify_cond KU. { dead KU. } clear KU.
      zstep. zstep. if_cases KU; zify_cond KU. { kill KU. } clear KU.
      zstep.
      zstep. zstep. if_cases KU; zify_cond KU.
      { exfalso. apply KU. apply land7_of_mod8; [lia|]. pose proof (hff_al8 H 3104 HG eq_refl) as ALhd16.
        first [exact ALhd16 | (replace (h_ff H + 3088 + 16) with (h_ff H + 3104) by lia; exact ALhd16)]. } clear KU.
      shadow_chk0 SHhd1 8.
      (* [comment removed for export] *)
      zstep. shadow_chk0 SHR 8. zstep. zstep. zstep. shadow_chk0 SHR 8. zstep.
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      astop AINV1 MU2 WM2 CFP2. fold_cl_segs.
      pose proof (as_minv LPA A1 _ _ AINV1) as [_ MH1].
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
        assert (HENV2 : henv_ok LPA VIA H A1 (aview A1 mx)) by
         (eapply henv_ok_munch; [exact HENV1| exact MU2| exact WM2| exact HG|];
          intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
          change (8192 / 8) with 1024 in Ha__; cbn; lia);
        assert (WS12 : ws1_obj LPA H A1 (aview A1 mx) wa r) by
         (eapply ws1_obj_munch; [exact WS11| exact MU2| exact WM2| intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn; lia]);
        pose proof (crange_stack (Clg:=Clg) (L:=LPA) A1 _ _ (aview A1 mx) (bv_unsigned sp - 64) 64 AINV2 ltac:(lia) ltac:(lia)
                      (rw_cells_mapped (Clg:=Clg) LPA _ _ _ FR ltac:(off_image_solve LPA))) as CRF2;
        pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A1 _ _ _ _ _ (h_ff H + 2608) 72 AINV2 HFR1' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRvc2;
        pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A1 _ _ _ _ _ (h_ff H + 2720) 184 AINV2 HFR1' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRwk2;
        pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A1 _ _ _ _ _ (h_ff H + 2416) 56 AINV2 HFR1' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRrq2;
        pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A1 _ _ _ _ _ (h_ff H + 2512) 56 AINV2 HFR1' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRrs2;
        pose proof (crange_fframe (Clg:=Clg) (L:=LPA) A1 _ _ _ _ _ (h_ff H + 3104) 8 AINV2 HFR1' ltac:(lia) ltac:(change (fsize HCLASS) with 8192; lia) ltac:(lia)) as CRhd2;
        pose proof (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ r 312 r 312 AINV2 LIVEr ltac:(lia) ltac:(lia) ltac:(lia)) as CRrA;   (* [comment removed for export] *)
        pose proof (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ r 312 r 8 AINV2 LIVEr ltac:(lia) ltac:(lia) ltac:(lia)) as CRrH;
        pose proof (crange_block (Clg:=Clg) (L:=LPA) A1 _ _ r 312 (r + 8) 304 AINV2 LIVEr ltac:(lia) ltac:(lia) ltac:(lia)) as CRrT;
        assert (CFa : cframe LPA (owned A) (owned A1) (bv_unsigned sp) 8704
                        (fun a => h_ff H + 2976 <= a < h_ff H + 2976 + 40 \/ h_ff H + 3152 <= a < h_ff H + 3152 + 32)
                        (fun a => newblk wa 40 a \/ newblk r 312 a) (aview A m) (aview A1 mx))
          by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A m) _ (aview A1 mr) _ _ _);
              [ exact MU | | exact CF1 | lia | lia | intros a X; exact X | intros a X; left; exact X
              | exact MU2 | | eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia] ];
              [ intros a Ha NO; cbn [outside] in NO; lia
              | intros a Ha NO; cbn [outside] in NO; unfold newblk, blk; lia ])
      end.
      eapply HNA;
        [ exact AINV2 | assumption | rewrite LBY1; lia | try (generalize alloc_ceiling_val); clear - NL1 NLVX; try pose proof alloc_ceiling_val as ACV__; lia
        | clear - PCM PC1; lia (* [comment removed for export] *)
        | rewrite unsigned_lit by lia; lia
        | exact TP
        | rewrite unsigned_lit by lia; apply align16_add; [exact SP16|reflexivity]
        | rewrite unsigned_lit by lia; exact ST | exact CEIL
        | rewrite unsigned_lit by lia; unfold_stacks; lia
        | ].
      clear MU WM CFP CF1 MU2 WM2 CFP2 HENV0 GLOB0 HOBJ0 HSH0 WS00.
      intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S A2 mS mdS. cbv zeta.
      intros AINV3 MI3 MDF3 FRS3 TCR3 SC3 PC3 ST3 OUT3.   (* [comment removed for export] *)
      fold_cl_segs. fold_aview. rewrite unsigned_lit in ST3 by lia. rewrite unsigned_lit in OUT3 by lia. unfold NEWAUTO_STACK, ASTK in OUT3.
      assert (HFR3 : hframe LPA A2 H) by (eapply hframe_keep; [exact HFR1| exact FRS3]). pose proof HFR3 as [age3 HFR3'].
      pose proof (cenv_intro A2 mS mdS AINV3) as CE3.
      clear ST.
      destruct OUT3 as (b & NZS & VSBO & FRESHS & FRESHb & LIVEq3 & LBY3 & NL3 & CF3).
      (* [comment removed for export] *)
      + (* [comment removed for export] *)
        assert (NESv : S <> r) by (intros ->; rewrite LIVEr in FRESHS; discriminate FRESHS).
        assert (NEbv : b <> r) by (intros ->; rewrite LIVEr in FRESHb; discriminate FRESHb).
        assert (NESw : S <> wa) by (intros ->; rewrite LIVEwa in FRESHS; discriminate FRESHS).
        assert (NEbw : b <> wa) by (intros ->; rewrite LIVEwa in FRESHb; discriminate FRESHb).
        assert (LIVEr3 : a_live A2 r = Some 312) by (rewrite (LIVEq3 r (not_eq_sym NESv) (not_eq_sym NEbv)); exact LIVEr).
        assert (LIVEwa3 : a_live A2 wa = Some 40) by (rewrite (LIVEq3 wa (not_eq_sym NESw) (not_eq_sym NEbw)); exact LIVEwa).
        assert (HENV3 : henv_ok LPA VIA H A2 (aview A2 mS)).
        { eapply henv_ok_acall0; [exact AINV2| exact CF3| exact HENV2| lia| exact FRS3]. }
        assert (WS13 : ws1_obj LPA H A2 (aview A2 mS) wa r).
        { eapply ws1_obj_ccall; [exact AINV2| exact HFR1| exact CF3| exact WS12| lia| exact LIVEwa3| exact LIVEr3| intros a__ _ X; exact X]. }
        pose proof VSBO as VSBx. (first [ dand6 VSBx as _ _ LS3 LB3 NESb _ | destruct VSBx as (_ & _ & LS3 & LB3 & NESb & _) ]). cbn [vb_buf vb_size vsb_fresh] in LB3, NESb.
        (first [ pose proof ((live_geomP LPA A2 mS mdS S _ AINV3 LS3)) as dR_23; dand7 dR_23 as _ S16 Slo Shi _ _ _ | pose proof (live_geomP LPA A2 mS mdS S _ AINV3 LS3) as (_ & S16 & Slo & Shi & _ & _ & _) ]).
        (first [ pose proof ((live_geomP LPA A2 mS mdS b _ AINV3 LB3)) as dR_24; dand7 dR_24 as _ B16 Blo Bhi _ _ _ | pose proof (live_geomP LPA A2 mS mdS b _ AINV3 LB3) as (_ & B16 & Blo & Bhi & _ & _ & _) ]).
        unfold kHighMemBeg in Slo, Blo. all_app_facts.
        pose proof (as_live_disjoint LPA A2 mS mdS S 40 r 312 AINV3 LS3 LIVEr3 NESv) as DJS.
        pose proof (as_live_disjoint LPA A2 mS mdS b 16 r 312 AINV3 LB3 LIVEr3 NEbv) as DJb.
        acall_xfer CF3. rename ST3 into ST.
        (first [ pose proof (HENV3) as dR_25; dand4 dR_25 as _ GLOB3 HOBJ3 HSH3 | pose proof HENV3 as (_ & GLOB3 & HOBJ3 & HSH3) ]).
        pose proof (as_live_shadow LPA A2 mS mdS r 312 AINV3 LIVEr3) as SHR3. fold_cl_segs. fold_aview.
        pose proof (munch_refl [(bv_unsigned sp - 8704, bv_unsigned sp); (r, r + 312)] (aview A2 mS)) as MU3.
        pose proof (wmono_refl rsegs (aview A2 mS)) as WM3.
        assert (WMAP3 : mapped (aview A2 mS) (bv_unsigned sp - 8704) 8704).
        { eapply (window_mapped LPA _ lo); [exact ST | exact FR | cbn; lia | exact CEIL | lia | lia]. }
        assert (CFP3 : client_fp LPA A2 (aview A2 mS) [(bv_unsigned sp - 8704, bv_unsigned sp); (r, r + 312)]).
        { cbn. split; [left; split; [lia|]; split; [lia|]; replace (bv_unsigned sp - (bv_unsigned sp - 8704)) with 8704 by lia; exact WMAP3 |].
          split; [right; left; exists r, 312; split; [exact LIVEr3|lia]| exact I]. }
        (* [comment removed for export] *)
        try clear VC; try clear WK; try clear RQ; try clear RS; try clear HD; try clear Gsh; try clear Csh; try clear Gmb; try clear Cmb; try clear Gme; try clear Cme; try clear Ghe; try clear Che.
        hide DWR. hide DJr. hide DJw. hide DJS. hide DJb. hide Blo_l. hide Slo_l. hide Wlo_l.
        ago AINV3. fold_cl_segs. fix_ret_pc.
        (* [comment removed for export] *)
        zstep. shadow_chk0 SHR3 8. zstep. zstep. kdead. zstep. kdead2.
        (* [comment removed for export] *)
        zstep. shadow_chk0 SHR3 8. zstep. zstep. zstep. zstep.
        (* [comment removed for export] *)
        shadow_chk0 SHR3 8. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. shadow_addr SHR3 8.
        lazymatch goal with SOK : shadow_val_ok ?b_ _ _ |- _ =>
          assert (SBZ : b_ = Z_to_bv 8 0)
            by (destruct SOK as [Z0|[R1 R2]];
                [ apply bv_eq; rewrite Z_to_bv_unsigned, Z0; reflexivity
                | exfalso; pose proof (Z.mod_pos_bound (r + 64) 8 ltac:(lia)); lia ]);
          subst b_; clear SOK end.
        zstep. try change (bv_unsigned (Z_to_bv 8 0)) with 0.
        let K := fresh "KS" in
        zstep; if_cases K; zify_cond K;
          [ first [ shadow_fast K; clear K; shadow_cleanup | (exfalso; lia) ]
          | first [ shadow_fast K; clear K; shadow_cleanup | (exfalso; lia) ] ].
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep.
        icall (crc32_null lo) by
          (rewrite ?unsigned_lit by lia;
           first [ reflexivity
                 | (eapply cenv_munch; [exact CE3| exact MU3| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                 | exact ST | assumption | lia ]).
        lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
        (* [comment removed for export] *)
        zstep. shadow_chk SHR3 4 13. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        icall (crc32_null lo) by
          (rewrite ?unsigned_lit by lia;
           first [ reflexivity
                 | (eapply cenv_munch; [exact CE3| exact MU3| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia])
                 | exact ST | assumption | lia ]).
        lazymatch goal with X : stk _ ?mx _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename X into ST end.
        (* [comment removed for export] *)
        zstep. shadow_chk SHR3 4 13. zstep. zstep. shadow_chk SHR3 4 12. zstep. zstep.
        (* [comment removed for export] *)
        zstep. do 10 zstep.
        try replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
        release_frame FR ST (bv_unsigned sp).
        unhide DWR. unhide DJr. unhide DJw. unhide DJS. unhide DJb. unhide Blo_l. unhide Slo_l. unhide Wlo_l.
        astop AINV3 MU3 WM3 CFP3.
        (* [comment removed for export] *)
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
          lazymatch goal with VX : rw_cells _ (aview A2 mx) r _ |- _ => pose proof VX as NB end end.
        lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mx _) ?mdx) _ =>
          eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r A2 mx mdx) end;
          [ assumption | assumption
          | eapply amd_frame_sbm_l; [exact SBM | exact MH |];
            eapply amd_frame_trans; [exact MDF1|]; eapply amd_frame_sbm_l; [exact SBM0 | exact MH1 |];
            eapply amd_frame_sbm_r; [exact MDF3 | eassumption]
          | exact ST
          | eapply henv_ok_munch; [exact HENV3| exact MU3| exact WM3| exact HG|];
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
            change (8192 / 8) with 1024 in Ha__; cbn; clear - CEIL WIN G2 Rlo DJr Ha__; lia
          | intros ff; rewrite FRS3; apply FRS1 | rewrite TCR3, TCR1; reflexivity | rewrite SC3, SC1; reflexivity | rewrite PC3, PC1; clear; lia (* [comment removed for export] *) | ].
        exists wa, ztag, q0, b. split; [exact NZ|].
        split. { eapply ws1_obj_munch; [exact WS13| exact MU3| exact WM3| intros a__ Ha__; unfold h_ws, h_wsbuf in Ha__; cbn; clear - CEIL WIN G3 Whi DWR DJr Ha__; lia]. }
        exists S.
        split. { split; [exact LIVEr3|]. split; [exact NB| split; [reflexivity| exact q0_wf]]. }
        split; [exact NZS|].
        split. { eapply vsb_obj_munch; [exact VSBO| exact MU3| exact WM3| cbn [vb_buf vb_size vsb_fresh]; intros a__ Ha__; cbn; clear - CEIL WIN Shi Bhi DJS DJb Ha__; lia]. }
        split; [rewrite <- (LIVEq1 S NESw NESv); exact FRESHS|].
        split; [rewrite <- (LIVEq1 b NEbw NEbv); exact FRESHb|].
        split; [exact NESv|]. split; [exact NEbv|]. split; [exact NESw|]. split; [exact NEbw|].
        split; [exact FRESHw|]. split; [exact FRESHr|].
        split; [intros p P1 P2 P3 P4; rewrite (LIVEq3 p P3 P4); apply LIVEq1; [exact P1| exact P2]|].
        split; [rewrite LBY3, LBY1; lia|]. split; [rewrite NL3, NL1; lia|].
        unfold_stacks. unfold h_ws, h_wsbuf.
        lazymatch goal with |- cframe _ _ _ _ _ _ _ _ ?vfin =>
          lazymatch type of CFa with cframe _ _ _ _ _ _ _ _ (aview A1 ?mp) =>
          assert (CFb : cframe LPA (owned A1) (owned A2) (bv_unsigned sp) 8704 (newblk r 312)
                          (fun a => newblk S 40 a \/ newblk b 16 a) (aview A1 mp) vfin)
            by (eapply (cframe_extend LPA _ _ _ _ _ _ _ _ _ _ (aview A1 mp) (aview A1 mp) (aview A2 mS) _ [] _);
                [ apply munch_refl | intros a _ X; exfalso; apply X; exact I | exact CF3 | lia | lia
                | intros a X; destruct X | intros a X; left; exact X | exact MU3 |
                | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia] ];
                intros a Ha NO; cbn [outside] in NO; unfold newblk, blk; clear - Ha NO Rlo Slo Blo; lia); (* [comment removed for export] *)
          eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview A1 mp) vfin CFa CFb); [lia | lia
              | eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | lia | lia]
              | intros a X; exact X | intros a X; left; right; exact X
              | intros a [X|[X|[X|X]]]; [left; left; exact X| left; right; exact X| right; left; left; exact X| right; left; right; exact X] ]
        end end.
  Qed.
End S.
End A_VE0r6.

   (* [comment removed for export] *)
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Vlo; @LO; @ACV; @CEIL; @TAG; @P36; @P124; @P140; @P196; @P236; @P268; @P308; @KS; @SPR; @G2; @Vsz; @Vhi; @LSEG; @Vlo_l; @Ha__; @D3; @NMX; @D1; @G3; @D2; @D6; @DJv; @D7; @PHI; @H0; @CNTx; @SZx; @Shi; @Vlen; @DVS; @DVB; @Blo; @SEGV; @NO; @V8; @D4; @D5; @KC])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require DietDL3.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sec_local := Ltac2.Init.true.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.sep_idents_hide.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

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
  (* [comment removed for export] *)

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
    pose proof (sh_boundL (Clg:=Clg) VEP 312 ltac:(lia) ltac:(lia) ltac:(exact Vhi)) as SHVB; rewrite SHMAX_val in SHVB;
    change ((312 + 7) / 8) with 39 in SHVB;
    pose proof (as_live_shadow LPA _ _ _ VEP 312 AINVx VLVx) as SHV0; fold_cl_segs; fold_aview;
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0;
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0;
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity);
    pose proof BSEGx as BSEG0; hide BSEG0; hide DVS; hide DVB.

  (* [comment removed for export] *)
  Local Definition mc_stepC' := mc_stepC (* [comment removed for export] *) VEP v tag q vv H p mark n seg lo ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md A T
                     HEC HCRC HC64 HCB AINV MI A0 A1 A2 HMK VOBJ VBASE HENV HLM CNT N0 NMX SOBJ NES NEB EM LBM NLV SCM PCM FY BSEG LSEG VPLO PHI SHSEG SEGH TP SP16 ST CEIL LO K.

  (* [comment removed for export] *)
  Local Ltac to_stepC v3 :=
    lazymatch goal with
    | AINV1 : ainv ?Ax ?m1 ?md1, SBM : same_but_materialized ?mdx ?md1, MDFx : amd_frame md ?mdx,
      STq : stk _ (aview ?Ax ?m1) lo _, FR : rw_cells _ (aview ?Ax ?m1) (bv_unsigned sp + -160) _,
      VEPC : rw_cells _ (aview ?Ax ?m1) VEP ?cs, VLVx : a_live ?Ax VEP = Some 312,
      VK : vkeep v ?vx MARK_FIELDS, EVP : ?vx Fver_p = v Fver_p, CNTx : vep_cnt ?vx n,
      SOBJx : vsb_obj _ ?Ax (aview ?Ax ?mx) (v Fvsb) ?vvx false,
      LENx : (vb_len vv <= vb_len ?vvx <= _)%Z, SZx : (vb_size vv <= vb_size ?vvx <= _)%Z,
      NEBx : kept (VEP <> vb_buf ?vvx), RELx : (vb_buf ?vvx = vb_buf vv \/ _),
      LIVEx : (forall r, r <> vb_buf vv -> r <> vb_buf ?vvx -> a_live ?Ax r = a_live A r),
      FAx : frames_aged A ?Ax 2%nat 0%nat, LBx : a_livebytes ?Ax = _, TCx : a_tinycred ?Ax = _, NLx : a_nlive ?Ax = _, SCx : (_ <= a_seccred ?Ax <= _)%Z, PCx : (_ <= a_primcred ?Ax <= _)%Z,
      HENVx : henv_ok _ _ H ?Ax (aview ?Ax ?mx), B0 : kept (bytes_at _ (aview ?Ax ?mx) (v Fver_p) seg),
      SV : kept ((v Fver_p + _ <= VEP \/ _)%Z), DS : kept ((VEP + 312 <= v Fvsb \/ _)%Z), DB : kept ((VEP + 312 <= vb_buf _ \/ _)%Z),
      CFx : cframe _ (owned A) (owned ?Ax) _ _ _ _ (aview A m) (aview ?Ax ?mx),
      MU : munch ?W (aview ?Ax ?mx) (aview ?Ax ?m1), WM : wmono _ (aview ?Ax ?mx) (aview ?Ax ?m1), HG : henv_geom LPA H
      |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
      assert (VEPC3 : rw_cells rsegs (aview Ax m1) VEP (vep_cells v3 tag q))
        by (unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite ?Z_to_bv_mod64, ?Z_to_bv_bv_unsigned; exact VEPC);
      clear VEPC;
      assert (MP : mapped (aview Ax m1) (bv_unsigned sp - 8800) 8800)
        by (eapply (window_mapped LPA _ lo); [exact STq | exact FR | cbn; lia | exact CEIL | lia | lia]);
      unhide B0; unhide SV; unhide DS; unhide DB;
      eapply (mc_stepC' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ax m1 md1 v3 vvx);
      [ exact AINV1 | assumption
      | eapply amd_frame_sbm_r; [exact MDFx | exact SBM]
      | exact STq | exact FR | exact VEPC3 | exact VLVx
      | vkeep_tac VK
      | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact EVP
      | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; first [reflexivity | assumption | lia]
      | unfold vep_cnt, fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold vep_cnt in CNTx; lia
      | eapply vsb_obj_munch; [exact SOBJx| exact MU| exact WM| intros a__ Ha__; cbn; lia]
      | unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; exact LENx
      | exact SZx | unhide NEBx; exact NEBx | exact RELx | exact LIVEx | exact FAx | exact LBx | exact TCx | exact NLx | exact SCx | exact PCx (* [comment removed for export] *)
      | eapply henv_ok_munch; [exact HENVx| exact MU| exact WM| exact HG|];
        intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
        change (8192 / 8) with 1024 in Ha__; cbn; lia
      | eapply (bytes_at_munch LPA); [exact B0| exact MU| intros a__ Ha__; cbn; lia]
      | exact SV
      | assert (CF2 : cframe LPA (owned Ax) (owned Ax) (bv_unsigned sp) 8800 Vmc nowhere (aview Ax mx) (aview Ax m1))
          by (eapply (cframe_noalloc LPA); [exact MU | | exact MP | intros a X; destruct X];
              intros a Ha NO; cbn [outside] in NO; unfold Vmc, blk; lia);
        unfold_stacks;
        eapply (cframe_seq LPA _ _ _ _ _ _ _ _ _ _ _ _ _ (aview A m) (aview Ax mx) (aview Ax m1) CFx CF2);
        [ lia | lia | exact MP | intros a X; exact X | intros a X; right; exact X | intros a X; left; exact X ] ]
    end.

  (* [comment removed for export] *)
  Local Ltac g5kill vx KU :=
    exfalso; revert KU;
    lazymatch goal with
    | Da : (0 <= vx Fo_pending)%Z, Db : (0 <= vx Fcb_x)%Z, Dc : (vx Fcb_x + vx Fo_pending = n)%Z, Dd : (0 <= vx Fo_total <= vx Fo_last)%Z,
      De : (vx Fo_last <= vx Fcb_x)%Z, Df : (vx Fo_wait = vx Fcb_x - vx Fo_last)%Z, Dg : (vx Fo_crc = vx Fo_wait)%Z |- _ =>
      clear - Da Db Dc Dd De Df Dg NMX N0 LSEG; dead_b2z
    end.
  Local Ltac g5 vx :=
    let KU := fresh "KU" in zstep; if_cases KU; zify_cond KU;
    [ first [ g5kill vx KU | clear KU ] | first [ g5kill vx KU | clear KU ] ].

  (* [comment removed for export] *)
  Local Ltac stepB_tail SHV0 EzsV CEx MU WM CFP AINVx vx :=
    let ST1 := fresh "STq" in let ST2 := fresh "STr" in
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (VEP + 128) 8 0; zstep; zstep; zstep; zstep;
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into ST1 end;
    icall (crc32_null HCRC lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- cenv _ => eapply cenv_munch; [exact CEx| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia]
       | |- stk _ _ _ _ => exact ST1
       | |- mem_inv _ _ => assumption
       | |- _ => lia
       end);
    try clear ST1;
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into ST2 end;
    (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0; zstep; vrechk SHV0 EzsV (VEP + 104) 8 0; vchk SHV0 EzsV 8 0;
    zstep; zstep; zstep; zstep; zstep; g5 vx;
    (* [comment removed for export] *)
    vrechk SHV0 EzsV (VEP + 96) 8 0; zstep; vrechk SHV0 EzsV (VEP + 104) 8 1; zstep;
    astop AINVx MU WM CFP;
    (* [comment removed for export] *)
    lazymatch goal with
    | FR : rw_cells _ ?mq (bv_unsigned sp + -160) (CB 8 ?j8 :: C8 ?w8 :: ?rest) |- _ =>
      let WF0 := fresh "WF0" in let WFa := fresh "WFa" in
      pose proof (proj1 (proj1 FR)) as WF0; cbn [cells_wf cell_wf] in WF0;
      apply (rw_cells_recast rsegs _ _ _ (CB 16 (j8 ++ le8 w8) :: rest)) in FR;
      [ clear WF0
      | destruct WF0 as [WFa _]; cbn [cells_wf cell_wf]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption;
        rewrite length_app, length_le8, WFa; reflexivity
      | cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity ]
    | |- _ => idtac
    end;
    (* [comment removed for export] *)
    lazymatch goal with VEPC : rw_cells _ _ VEP ?cs |- _ =>
      lazymatch cs with context [C8 (Z_to_bv 64 (vx Fcb_x + ?pend)) :: C8 (Z_to_bv 64 (vx Fstate)) :: _] =>
      lazymatch cs with context [C8 (Z_to_bv 64 ?ow) :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 (vx Fo_total)) :: C4 ?cw :: CB 4 (p124 q) :: C8 (Z_to_bv 64 ?oc) :: C4 ?pw :: _] =>
        to_stepC (fupd (fupd (fupd (fupd (fupd (fupd vx Fcb_x (vx Fcb_x + pend)) Fcrc (bv_unsigned cw)) Fo_crc oc)
                       Fo_wait ow) Fo_pending 0) Fcrcp (bv_unsigned pw))
      end end
    end.

  (* [comment removed for export] *)
  #[using="l K LO CEIL ST SP16 TP SEGH SHSEG PHI VPLO LSEG BSEG FY SCM PCM NLV LBM EM NEB NES SOBJ NMX N0 CNT HLM HENV VBASE VOBJ HMK A2 A1 A0 MI AINV HCB HC64 HCRC HEC a2 a1 a0"] Lemma mc_stepB :
    forall (xra xs3 xs5 xs7 xs10 xt0 xt1 xt2 xa0 xa1 xa2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word) (j0 : list byte)
           (Ax : AS) (mx : mem) (mdx : Model) (vx : vep) (vvx : vsb_rec),
      ainv Ax mx mdx -> mem_inv rsegs (aview Ax mx) -> amd_frame md mdx ->
      stk rsegs (aview Ax mx) lo (bv_unsigned sp + -160) ->
      rw_cells rsegs (aview Ax mx) (bv_unsigned sp + -160)
        [CB 24 j0; C8 (Z_to_bv 64 (VEP + 160)); C8 (Z_to_bv 64 ((VEP + 304) / 8 + 2147450880));
         C8 (Z_to_bv 64 (VEP + 40)); C8 (Z_to_bv 64 p);
         C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs (aview Ax mx) VEP (vep_cells vx tag q) -> a_live Ax VEP = Some 312 ->
      vkeep v vx MARK_FIELDS -> vx Fver_p = v Fver_p -> vep_cnt vx n ->
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
                        (Z_to_bv 64 VEP) (Z_to_bv 64 mark) xa0 xa1 xa2 (Z_to_bv 64 (VEP + 40)) (Z_to_bv 64 (VEP + 160)) xa5 xa6 xa7
                        (Z_to_bv 64 (VEP + 24)) xs3 (Z_to_bv 64 2147450880) xs5 (Z_to_bv 64 (VEP + 96)) xs7
                        (Z_to_bv 64 (VEP + 48)) (Z_to_bv 64 (VEP + 104)) xs10 (Z_to_bv 64 (VEP + 304)) xt3 xt4 xt5 xt6)
                   F (Z_to_bv 64 0x8e2e8) fc None mx (seg_rom rsegs)) mdx) T.
  Proof.
    touch_all.
    intros until vvx. intros AINVx MIx MDFx STx FR VEPC VLVx VK EVP CNTx SOBJx LENx SZx NEBx RELx LIVEx FAx LBx TCx NLx SCx PCx HENVx BSEGx SEGV CFx.
    seg_prelims AINVx VLVx SOBJx NEBx BSEGx. hide HMK. hide HLM.
    (first [ pose proof (CNTx) as dR_7; dand7 dR_7 as D1 D2 D3 D4 D5 D6 D7 | pose proof CNTx as (D1 & D2 & D3 & D4 & D5 & D6 & D7) ]).
    assert (EVCx : vx Fvc = h_vc H) by (rewrite (VK Fvc ltac:(notin_tac)); exact EVC).
    assert (ECBx : vx Fcb = 589220) by (rewrite (VK Fcb ltac:(notin_tac)); exact ECB).
    assert (EPRx : vx Fcb_priv = VEP + 56) by (rewrite (VK Fcb_priv ltac:(notin_tac)); exact EPRIV).
    pose proof (cenv_intro Ax mx mdx AINVx) as CEx.
    pose proof (proj1 HENVx) as [agex HFRx].
    pose proof (as_frame_blk_disjoint LPA Ax mx mdx (h_ff H) HCLASS agex VEP 312 AINVx HFRx VLVx) as DJv.
    change (fsize HCLASS) with 8192 in DJv.
    pose proof (sh_boundL (Clg:=Clg) (h_ff H) 8192 ltac:(lia) ltac:(lia) ltac:(unfold HFSIZE in G3; lia)) as SHF.
    rewrite SHMAX_val in SHF. change ((8192 + 7) / 8) with 1024 in SHF.
    unfold vep_cells in VEPC.
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
    zstep. vchk SHV0 EzsV 8 0. zstep. zstep. zstep.
    zstep. if_cases KP; zify_cond KP.
    { (* [comment removed for export] *)
      lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
      astop AINVx MU WM CFP.
      to_stepC vx. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0. vchk SHV0 EzsV 8 0.
    zstep. zstep. zstep. zstep. rewrite EVCx, ECBx, EPRx. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (HENVq : henv_ok LPA VIA H Ax mq)
        by (eapply henv_ok_munch; [exact HENVx| exact MU| exact WM| exact HG|];
            intros a__ Ha__; cbn [vi_bss_vsc vi_bss_cp VIA] in Ha__; unfold h_vsc, h_cp, HOBJ_END, HFSIZE in Ha__;
            change (8192 / 8) with 1024 in Ha__; cbn; lia);
      (first [ pose proof (HENVq) as dR_8; dand4 dR_8 as _ _ HOBJq HSHq | pose proof HENVq as (_ & _ & HOBJq & HSHq) ])
    end.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    icall (HCB VEP vx tag q H (vx Fo_pending) lo) by
      (rewrite ?unsigned_lit by lia;
       lazymatch goal with
       | |- @eq (bv _) _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact VEPC
       | |- length _ = _ => exact TAG
       | |- vep_pads_wf _ => exact PADS
       | |- hobj_ok _ _ _ _ => exact HOBJq
       | |- hshadow _ _ _ => exact HSHq
       | |- henv_geom LPA _ => exact HG
       | |- cenv _ => eapply cenv_munch; [exact CEx| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia]
       | |- shadowed _ _ _ _ => exists VEP, 312; split; [pose proof SHV0 as T__; rewrite EzsV in T__; exact T__|]; lia
       | |- stk _ _ _ _ => exact STq
       | |- mem_inv _ _ => assumption
       | |- _ => unfold fupd; cbn [vf_beq vf_index N.eqb Pos.eqb]; unfold kHighMemBeg, HFSIZE, CB_STACK; lia
       end).
    clear HENVq HOBJq HSHq.
    lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
    lazymatch goal with X : rw_cells _ ?mq VEP (vep_cells _ tag q) |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into VEPC end.
    unfold vep_cells in VEPC. cbn [fupd vf_beq vf_index N.eqb Pos.eqb] in VEPC.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. zstep. zstep.
    zstep. if_cases KC; zify_cond KC.
    - (* [comment removed for export] *)
      vchk SHV0 EzsV 4 0. vchk SHV0 EzsV 4 1. zstep. vrechk SHV0 EzsV (VEP + 104) 8 0. zstep.
      stepB_tail SHV0 EzsV CEx MU WM CFP AINVx vx.
    - (* [comment removed for export] *)
      zstep. zstep. vchk SHV0 EzsV 4 0. vchk SHV0 EzsV 4 1. vrechk SHV0 EzsV (VEP + 104) 8 0. zstep. zstep. zstep.
      icall (crc32_combine_w2 HC64 lo) by
        (rewrite ?unsigned_lit by lia;
         lazymatch goal with
         | |- cenv _ => eapply cenv_munch; [exact CEx| exact MU| repeat (apply Forall_cons); try apply Forall_nil; unfold const_free_ivl, CONSTS_TOP; cbn; lia]
         | |- stk _ _ _ _ => exact STq
         | |- mem_inv _ _ => assumption
         | |- (bv_unsigned _ < _)%Z => try rewrite unsigned_lit by lia; lia   (* [comment removed for export] *)
         | |- _ => lia
         end).
      try clear STq.
      lazymatch goal with X : stk _ ?mq _ _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename X into STq end.
      (* [comment removed for export] *)
      vrechk SHV0 EzsV (VEP + 120) 4 0. zstep. vrechk SHV0 EzsV (VEP + 104) 8 0. zstep. vrechk SHV0 EzsV (VEP + 128) 8 1.
      zstep. zstep. zstep. zstep. zstep. g5 vx.
      stepB_tail SHV0 EzsV CEx MU WM CFP AINVx vx.
  Qed.
End S.
