(* reloc-zl14c ca3b0478ef776d603f8c09eec3874a89 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge Tac InitMem StoreFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg RtCells ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AKit U2AArr U2AStore InfAGlue InfPure InfPure_w7 InfPure_w7d InfPure_w7e InfPure_w7f InfAGlue_w7 InfAGlue_w7b.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AObj U2AClient U2AIface InfABase InfAKit InfATables InfA_w7base InfA_w7tab InfA_w7pull.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AIface_fit2_draft InfA_len_ InfA_lenx InfA_distx InfA_dist6 InfA_len6 InfA_lenF InfA_match4.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import InfA_garmc InfA_garmv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac solve_load_hyp :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] => match goal with HR : ov_read_bytes segs m a n = Some _ |- _ => rewrite HR end
  end; load_post.
Local Ltac solve_load ::= first [ solve_load_hyp | solve_load_sh0 | solve_load_shlit | solve_load_base | solve_load_image ].
Local Ltac acc_hint_hyp := lazymatch goal with |- acc_in ?R ?x => match goal with HA : acc_in R x |- _ => exact HA end end.
Local Ltac acc_hint ::= first [ acc_hint_hyp | acc_hint_sh ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= farr_store_extra m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= farr_call_extra segs W m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Notation GARMG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly,
       garm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation ARMG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh, rng_fs L RNG -> atmost1_c2 LB -> tp = Z_to_bv 64 ATP ->
     forall cx ly, l_SP ly + 16 < al_top L -> rng RNG (l_lo ly) (al_top L - l_lo ly) ->
     arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  (* [U14] (an earlier development run): LENEXT / DIST / DISTEXT / MATCH are proved against garmV (slot 504
     free, t2 = S+56) and LEN / LEN_ against garmC (t2 and slot 504 free); garmv_garm / garmc_garm give back the arm
     statements *)
  Notation GARMVG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly,
       garmv_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Notation GARMCG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly,
       garmc_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Lemma HMATCH : GARMVG 0x91680 MATCH.
  Proof. intros. apply garmvf_garmv. apply match_garm. Qed.
  (* [comment removed for export] *)
  Hypothesis IFAST : inflate_fast_stmtA.
  Lemma HFAST : forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly,
    LFAST_STMT AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh cx ly.
  Proof. intros. apply lfast. exact IFAST. Qed.

  Lemma g_DISTEXT : GARMVG 0x8e440 DISTEXT.
  Proof. intros. apply garmvf_garmv. apply distx_garm. apply match_garm. Qed.
  Lemma g_DIST : GARMVG 0x9122c DIST.
  Proof. intros. apply garmvf_garmv. apply dist_garm. apply match_garm. Qed.
  Lemma g_LENEXT : GARMVG 0x8e464 LENEXT.
  Proof. intros. apply garmvf_garmv. apply lenx_garm. apply dist_garm. apply match_garm. Qed.
  Lemma g_LEN : GARMCG 0x90cc8 LEN.
  Proof. intros. apply garmcf_garmc. apply len_garm; [apply dist_garm; apply match_garm| apply HFAST]. Qed.
  Lemma g_LEN_ : GARMCG 0x90cb0 LEN_.
  Proof. intros. apply garmcf_garmc. apply len__garm. apply len_garm; [apply dist_garm; apply match_garm| apply HFAST]. Qed.

  Theorem A_MATCH : ARMG 0x91680 MATCH.   Proof. intros. apply garm_arm. apply garmv_garm. apply HMATCH. Qed.
  Theorem A_DISTEXT : ARMG 0x8e440 DISTEXT. Proof. intros. apply garm_arm. apply garmv_garm. apply g_DISTEXT. Qed.
  Theorem A_DIST : ARMG 0x9122c DIST.     Proof. intros. apply garm_arm. apply garmv_garm. apply g_DIST. Qed.
  Theorem A_LENEXT : ARMG 0x8e464 LENEXT. Proof. intros. apply garm_arm. apply garmv_garm. apply g_LENEXT. Qed.
  Theorem A_LEN : ARMG 0x90cc8 LEN.       Proof. intros. apply garm_arm. apply garmc_garm. apply g_LEN. Qed.
  Theorem A_LEN_ : ARMG 0x90cb0 LEN_.     Proof. intros. apply garm_arm. apply garmc_garm. apply g_LEN_. Qed.
End T.
End CANSEC1.
