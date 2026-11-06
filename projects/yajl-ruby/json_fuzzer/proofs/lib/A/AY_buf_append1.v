(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AAPP_EPILOGUE : Z := 0x869f4.

(* [comment removed for export] *)
End RC__1.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.

Section Fn.
(* [comment removed for export] *)
Variables (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (mo : Model) (s : y_APS Y).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : mem) (mo' : Model) (s' : y_APS Y) (b' : ybuf) (mb' : mbuf) (LK : list ablock),
  aybuf_append_rpost Y sp m mo s LF REST mb b AF S src lo RR a0' fc' m' mo' s' b' mb' LK ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AY_BUF_APPEND_STACK.
Hypothesis SPH : bv_unsigned sp <= 2^47.

(* [comment removed for export] *)
Definition aapp_frame (m1 : mem) (junk : list byte) : Prop :=
  rw_cells asegs m1 (bv_unsigned sp + -128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma aapp_ret : forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (sv : list word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (b' : ybuf) (mb' : mbuf) (LK : list ablock) (junk : list byte)
    (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word),
  y_AHK Y s1' (abl (buf_blocks mb' b') ++ LK ++ REST) LF m1 mo1 -> aystatics m1 ->
  aapp_frame m1 junk -> stk asegs m1 lo (bv_unsigned sp + -128) -> mem_inv asegs m1 -> frm0 fc1 ->
  True -> ay_pres REST LF (bv_unsigned sp) [] m m1 ->   (* [comment removed for export] *)
  rw_cells asegs m1 AF (alloc_cells ayc) ->
  y_SO Y s1' = y_SO Y s -> y_ayR Y s mo s1' mo1 -> y_phi_buf Y b' + RR <= y_acredit Y s1' ->
  yleaf (ybuf_append b src) b' -> buf_rep asegs m1 mb' b' AF -> mb_same mb mb' ->
  oshadow m1 (mb_addr mb') SIZEOF_BUF ->
  (yb_data b' <> None -> oshadow m1 (mb_data mb') (yb_len b') /\ amem (mb_data mb') (yb_len b')) ->
  (LK <> [] -> yb_state b' <> BS_ok /\ length LK = 1%nat) -> (LK <> [] -> yb_state b = BS_ok) ->
  LK = [] ->   (* [comment removed for export] *)
  realizes_cfg acfg asegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                          F1 (Z_to_bv 64 AAPP_EPILOGUE) fc1 None m1 (seg_rom asegs)) mo1) K.
Proof. aceil.
  intros until x27. intros AHK1 YS1 FR ST MI FRM WM0 PRES YAF SO1 R1 CRED HL BR MBS OSB OSD LKP LKB LKZ.
  unfold aapp_frame, AAPP_EPILOGUE, wz in *. pose proof LO as LO'. unfold AY_BUF_APPEND_STACK, AMALLOC_STACK in LO'.
  aceil.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  arz_seg KIPY AHK1.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  unfold pol in PSTK. clear Hh HLI Hmi.
  do 13 stepA.                                        (* [comment removed for export] *)
  stepA. stepA.                                       (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2.
  destruct (BACK mo2 Hag2 HLI2) as [AHK2 R2].
  assert (AHK2' : y_AHK Y s1' (abl (buf_blocks mb' b') ++ LK ++ REST) LF m1 mo2) by (eapply FRAMEY; [exact AHK2| exact MU| exact WM| constructor]).
  eapply CONT. unfold aybuf_append_rpost.
  split; [exact SO1|]. split; [eapply RRT; [exact R1| exact R2]|]. split; [exact CRED|].
  split. { split; [exact MI|]. split; [assumption|]. split; [exact FRM|]. split; [exact I| exact PRES]. }
  split; [exact YAF|]. split; [exact HL|]. split; [exact BR|]. split; [exact MBS|]. split; [exact OSB|]. split; [exact OSD|].
  split; [exact LKZ|]. split; [| split; [exact LKP| exact LKB]]. apply AYST_split. split; [exact AHK2'| exact YS1].
Qed.
End Fn.
End W.
End RC__2.
