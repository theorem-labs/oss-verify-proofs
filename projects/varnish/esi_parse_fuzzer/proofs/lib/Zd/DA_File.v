(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg Shapi1s PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Se7o DA_S5tv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.

Module DA_M9wy.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg Shapi1s PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Se7o DA_S5tv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Walk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Se7o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_S5tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk.DA_Hbsz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Loop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

Section Walks.
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32).
  #[local] Notation rom := (seg_rom rsegs).

  Definition mret_post (st : Z) (d1 : byte) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (x1 x10 x11 : word) m',
      ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 (if 128 <=? bv_unsigned d1 then 0 else st)) s1 x10 x11 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x869ec) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

  Lemma mret_walk : forall (ra : word) (st : Z) (d1 : byte) (m : word -> option byte),
    mem_inv rsegs m -> 0 <= st < 251 ->
    evt rsegs (mret_post st d1 m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 st) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (sxb d1) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8696c) fc None m rom).
  Proof.
    intros ra st d1 m MI ST.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (cntu_val d1) as CV.
    azstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      assert (E : (128 <=? bv_unsigned d1) = true) by (rewrite <- CV; apply Z.leb_le; exact K).
      bstep. bstep. bstep. bstep. bstep. azstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
      apply evt_done. unfold mret_post. rewrite E.
      eexists _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
    - assert (E : (128 <=? bv_unsigned d1) = false) by (rewrite <- CV; apply Z.leb_gt; lia).
      bstep. bstep. apply evt_done. unfold mret_post. rewrite E.
      eexists _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.
End Walks.

Section MainRet.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Variables (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte).
  Variables (gp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).   (* [comment removed for export] *)
  Hypothesis FREE1 : free1_stmt.   (* [comment removed for export] *)
  Hypothesis EXIT : exit_spec_stmt.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation FV := (fview usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).
  Ltac name_state m md AI :=
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ =>
      lazymatch goal with H : ainv _ mm mdd |- _ => rename H into AI end; rename mm into m; rename mdd into md end.

  Lemma fds_std_1 : fd_lookup fds_std (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition mainret_stmt : Prop :=
    forall A m md tid (sof : stdout_form) (ini : Z) (b n0 st : Z) (d1 : byte)
           (zra z0 z1 z2 x8 za1 za2 za3 za4 za5 za6 za7 x18 x19 x20 x22 x23 zt3 zt4 zt5 zt6 : word),
      FV A m md fds_std sof ini tid -> a_live A b = Some n0 -> (st = 0 \/ st = 2) ->
      srealizes rsegs
        (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 x8 (Z_to_bv 64 b) (Z_to_bv 64 st)
                        za1 za2 za3 za4 za5 za6 za7 x18 x19 x20 (sxb d1) x22 x23 s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x8696c) fc None m rom) md)
        (t_emit (W 1 (pending_of sof)) (t_exit (exit_code (if 128 <=? bv_unsigned d1 then 0 else st)) fs)).

  #[using="EXIT FREE1 HCEIL"] Theorem mainret_ok : mainret_stmt.
  Proof.
    unfold mainret_stmt. intros until zt6. intros FV0 LV ST01.
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof FV0 as [AINV MI FS FDS CC AR SH STK FR].
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall mret_walk by (first [exact MI | lia]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_2; dand3 dR_2 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    assert (FV1 : FV A m1 md1 fds_std sof ini tid).
    { eapply (fview_stack usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 A m md); try eassumption.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
    replace (exit_code (if 128 <=? bv_unsigned d1 then 0 else st))
      with (bv_and (Z_to_bv 64 (if 128 <=? bv_unsigned d1 then 0 else st)) (Z_to_bv 64 255)).
    2:{ destruct (128 <=? bv_unsigned d1); [| destruct ST01 as [-> | ->]]; apply bv_eq; vm_compute; reflexivity. }
    eapply (ret_tail usp HCEIL argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 gp s8 s9 s10 s11 F fc FREE1 EXIT A m1 md1 tid fds_std sof ini b n0);
      [exact FV1| exact LV| | intros _; apply fds_std_1].
    destruct (128 <=? bv_unsigned d1); [| destruct ST01 as [-> | ->]]; rewrite unsigned_lit by lia; lia.
  Qed.
End MainRet.
End DA_M9wy.


Module DA_Tfuf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame SysStep RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg Shapi1s PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AIcpm9j AIcpnnp AIcpghc AIcp3q7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpwpz.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_Se7o DA_S5tv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Walk.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Se7o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_S5tv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk.DA_Hbsz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Ejgo DA_Main DA_Am90 DA_FKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.DA_R1e4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Loop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_File.DA_M9wy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Definition TRUN_RET : Z := 0x8696c.
Definition EMITPF_ENTRY : Z := 0x86c50.

(* [comment removed for export] *)
Local Ltac icall_consts_in H ::= unfold MEMCPY_ICPT_STACK, LIB_STACK in H.
Section Walks.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (lo : Z).
  Hypothesis CEIL : alloc_ceiling <= lo.
  #[local] Notation rom := (seg_rom rsegs).

  (* [comment removed for export] *)
  Definition TFR (j0 : list byte) (v7 v6 v5 v4 v3 v2 v1 v0 vra : word) : list cell :=
    [CB 8 j0; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra].

  (* [comment removed for export] *)
  Definition tr1_post (b c pay plen calls : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (x10 x11 x12 x13 : word) (j0 : list byte) m',
      ms' = MS (mkR (Z_to_bv 64 0x86b5c) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 plen) (Z_to_bv 64 pay) x10 x11
                    x12 x13 a4 a5 a6 a7
                    (Z_to_bv 64 c) (Z_to_bv 64 (b + 2)) (Z_to_bv 64 TR_INITIALIZED) (Z_to_bv 64 calls) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if plen =? 0 then 0x86b70 else 0x86b24)) fc None m' rom
      /\ munch [(bv_unsigned sp + -128, bv_unsigned sp); (TR_INITIALIZED, TR_INITIALIZED + 1);
                (ATEXIT + 8, ATEXIT + 12); (ATEXIT + 40, ATEXIT + 48); (ATEXIT + 296, ATEXIT + 304)] m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells rsegs m' (bv_unsigned sp + -80) (TFR j0 s7 s6 s5 (Z_to_bv 64 plen) (Z_to_bv 64 pay) (Z_to_bv 64 c) (Z_to_bv 64 b) (Z_to_bv 64 (b + 2)) (Z_to_bv 64 TRUN_RET))
      /\ rw_cells rsegs m' TR_INITIALIZED [C1 (Z_to_bv 8 1)]
      /\ rw_cells rsegs m' (ATEXIT + 8) [C4 (Z_to_bv 64 2)]
      /\ rw_cells rsegs m' (ATEXIT + 40) [C8 (Z_to_bv 64 CALL_TRAMP)]
      /\ rw_cells rsegs m' (ATEXIT + 296) [C8 (Z_to_bv 64 AEF_GUARD)].

  #[using="CEIL Clg"] Lemma tr1_walk : forall (b c pay plen : Z) (data : list byte) (m : word -> option byte),
    lo + 128 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    0x60a000 <= b -> b + Z.of_nat (length data) <= lo -> (3 <= length data)%nat ->
    0 <= c < 32768 -> 0 <= plen < 2^26 -> 0 <= pay < 2^47 ->
    bytes_at rsegs m b data ->
    rw_cells rsegs m TR_INITIALIZED [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m GOT_WEAKINIT [C8 (Z_to_bv 64 0)] ->
    (* [comment removed for export] *)
    rw_cells rsegs m ATEXIT [C1 (Z_to_bv 8 0)] ->
    ro_cells rsegs m (ATEXIT + 4) [C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (ATEXIT + 8) [C4 (Z_to_bv 64 1)] ->
    rw_cells rsegs m (ATEXIT + 16) [C8 (Z_to_bv 64 (ATEXIT + 24))] ->
    rw_cells rsegs m (ATEXIT + 40) [C8 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (ATEXIT + 296) [C8 (Z_to_bv 64 0)] ->
    ro_cells rsegs m NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    evt rsegs (tr1_post b c pay plen (if c =? 0 then 1 else bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4 + 1) m)
        (MS (mkR (Z_to_bv 64 TRUN_RET) sp gp tp t0 t1 t2 (Z_to_bv 64 (b + 2)) (Z_to_bv 64 b)
                 (Z_to_bv 64 (b + 2)) (Z_to_bv 64 c) (Z_to_bv 64 pay) (Z_to_bv 64 plen) a4 a5 a6 a7
                 (Z_to_bv 64 c) (Z_to_bv 64 pay) (Z_to_bv 64 plen) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86ac8) fc None m rom).
  Proof.
    intros b c pay plen data m LO SPH MI ST B0 B1 DL3 CR PR PYR BS TRC GOT FIN ALK SLT HD BF1 BA1 NLK.
    unfold TRUN_RET, GOT_WEAKINIT, TR_INITIALIZED, ATEXIT, NEED_LOCKS, CALL_TRAMP, AEF_GUARD in *.
    assert (CEILv : alloc_ceiling <= lo) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact CEIL).
    lit_addrs.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (0x5e7210, 0x5e7210 + 1);
                            (0x607c30, 0x607c30 + 4); (0x607c50, 0x607c50 + 8); (0x607d50, 0x607d50 + 8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range _ (nth 2 data (Z_to_bv 8 0))) as D2R. unfold bv_modulus in D2R. cbn in D2R.
    carve_frame 80%nat ST.
    (* [comment removed for export] *)
    run_to 0x86b0c. at_pc 0x86b0c.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    run_to 0x9825c. at_pc 0x9825c.
    carve_frame 48%nat ST.
    (* [comment removed for export] *)
    run_to 0x98294. at_pc 0x98294.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x9829c. at_pc 0x9829c.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x982b0. at_pc 0x982b0.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86b5c. at_pc 0x86b5c.
    release_frame FR0 ST (bv_unsigned sp + -80).
    (* [comment removed for export] *)
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86c00. at_pc 0x86c00.
    azstep. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    at_pc 0x86b10.
    azstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia. replace (c =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      azstep. azstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + apply evt_done. unfold tr1_post, TFR, TRUN_RET, TR_INITIALIZED, ATEXIT, CALL_TRAMP, AEF_GUARD. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        eexists _, _, _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
      + apply evt_done. unfold tr1_post, TFR, TRUN_RET, TR_INITIALIZED, ATEXIT, CALL_TRAMP, AEF_GUARD. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        eexists _, _, _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
    - rewrite ?unsigned_lit in K by lia. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (data_read mm b data 2 ltac:(first [exact BS | eapply (bytes_at_transport rsegs); [exact BS | exact MU | exact WM | cbn [disjoint_from]; lia]]) ltac:(lia)) as HR2;
        change (Z.to_nat 2) with 2%nat in HR2 end.
      azstep. azstep. azstep.
      replace (Z.land (bv_unsigned (nth 2 data (Z_to_bv 8 0))) 3) with (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4)
        by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
      azstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + apply evt_done. unfold tr1_post, TFR, TRUN_RET, TR_INITIALIZED, ATEXIT, CALL_TRAMP, AEF_GUARD. replace (plen =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        eexists _, _, _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
      + apply evt_done. unfold tr1_post, TFR, TRUN_RET, TR_INITIALIZED, ATEXIT, CALL_TRAMP, AEF_GUARD. replace (plen =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        eexists _, _, _, _, _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition tr2a_post (x1 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 (Z_to_bv 64 TR_EMPTY) a0 a1 a2 a3 a4 a5 a6 a7
                    (Z_to_bv 64 0) s3 (Z_to_bv 64 TR_INITIALIZED) s5 (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x86b80) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma tr2a_walk : forall (x1 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (tr2a_post x1 m)
        (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 TR_INITIALIZED) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86b70) fc None m rom).
  Proof.
    intros x1 m MI. unfold TR_INITIALIZED.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. bstep. bstep. apply evt_done. unfold tr2a_post, TR_EMPTY, TR_INITIALIZED.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition tr2b_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86b2c) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (cl_malloc_pc LPA) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma tr2b_walk : forall (x1 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (tr2b_post m)
        (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86b24) fc None m rom).
  Proof.
    intros x1 m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. apply evt_done. unfold tr2b_post. cbn [cl_malloc_pc LPA].
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition trret_post (rv : Z) (j0 : list byte) (v7 v6 v5 v4 v3 v2 v1 v0 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 v0 v1 (Z_to_bv 64 rv) a1 a2 a3 a4 a5 a6 a7
                    v2 v3 v4 v5 v6 v7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 TRUN_RET) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + 80).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition tr3b_post (r : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86b40) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) s1 s0 a3 a4 a5 a6 a7 (Z_to_bv 64 r) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 MEMCPY_ICPT_ENTRY) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma tr3b_walk : forall (r : Z) (m : word -> option byte),
    mem_inv rsegs m -> 0 < r < 2^64 ->
    evt rsegs (tr3b_post r m)
        (MS (mkR (Z_to_bv 64 0x86b2c) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86b2c) fc None m rom).
  Proof.
    intros r m MI R.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    run_to 0x86b3c. at_pc 0x86b3c. bstep. apply evt_done. unfold tr3b_post, MEMCPY_ICPT_ENTRY.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition tr4_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86b40) sp gp tp t0 t1 t2 s0 s2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x86b80) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma tr4_walk : forall (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (tr4_post m)
        (MS (mkR (Z_to_bv 64 0x86b40) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86b40) fc None m rom).
  Proof.
    intros m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. bstep. bstep. apply evt_done. unfold tr4_post.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  Definition tr5_post (x1 : word) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86b94) sp gp tp t0 t1 t2 s0 s1 s1 s0 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 TR_INITIALIZED) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 LIB_ENTRY) fc None m' rom
      /\ munch [(TR_INCB, TR_INCB + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ rw_cells rsegs m' TR_INCB [C1 (Z_to_bv 8 1)].
  Lemma tr5_walk : forall (x1 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    rw_cells rsegs m TR_INCB [C1 (Z_to_bv 8 0)] ->
    evt rsegs (tr5_post x1 m)
        (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 TR_INITIALIZED) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86b80) fc None m rom).
  Proof.
    intros x1 m MI INCB. unfold TR_INITIALIZED, TR_INCB in *. lit_addrs.
    pose proof (munch_refl [(0x5e7214, 0x5e7214 + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x86cdc. at_pc 0x86cdc. apply evt_done. unfold tr5_post, LIB_ENTRY, TR_INITIALIZED, TR_INCB.
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition EFR (x16 : list byte) (va2 va3 va4 va5 va6 va7 : word) : list cell :=
    [C8 (Z_to_bv 64 (bv_unsigned sp + -56)); C8 (Z_to_bv 64 0x86ba4); CB 8 x16; C8 (Z_to_bv 64 0);
     C8 va2; C8 va3; C8 va4; C8 va5; C8 va6; C8 va7].
  Definition tr6_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (x16 : list byte) m',
      ms' = MS (mkR (Z_to_bv 64 0x86c8c) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0 s1
                    (Z_to_bv 64 FMT_D) (Z_to_bv 64 (bv_unsigned sp + -56)) a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 0) (Z_to_bv 64 TR_INITIALIZED) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 VPRINTF_ICPT_ENTRY) fc None m' rom
      /\ munch [(bv_unsigned sp + -80, bv_unsigned sp); (TR_INCB, TR_INCB + 1)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp + -80)
      /\ rw_cells rsegs m' (bv_unsigned sp + -80) (EFR x16 a2 a3 a4 a5 a6 a7)
      /\ rw_cells rsegs m' TR_INCB [C1 (Z_to_bv 8 0)].
  #[using="CEIL Clg"] Lemma tr6_walk : forall (m : word -> option byte),
    lo + 80 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m TR_INCB [C1 (Z_to_bv 8 1)] ->
    evt rsegs (tr6_post m)
        (MS (mkR (Z_to_bv 64 0x86b94) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 TR_INITIALIZED) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86b94) fc None m rom).
  Proof.
    intros m LO SPH MI ST INCB. unfold TR_INITIALIZED, TR_INCB in *. lit_addrs.
    assert (CEILv : 0x7fff7f800000 <= lo) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia).   (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp); (0x5e7214, 0x5e7214 + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x86c50. at_pc 0x86c50.
    carve_frame 80%nat ST.
    run_to 0x86c88. at_pc 0x86c88. bstep. apply evt_done. unfold tr6_post, EFR, VPRINTF_ICPT_ENTRY, FMT_D, TR_INITIALIZED, TR_INCB.
    eexists _, _. split; [reflexivity|]. repeat (split; [eassumption|]). eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition tr7_post (j : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86ba4) (Z_to_bv 64 (bv_unsigned sp + 80)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 (-1)) s4 (Z_to_bv 64 (j - 1)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if j - 1 =? 0 then 0x86bb8 else 0x86b80)) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp + 80).
  #[using="CEIL Clg"] Lemma tr7_walk : forall (j : Z) (x16 : list byte) (va2 va3 va4 va5 va6 va7 : word) (m : word -> option byte),
    lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> 1 <= j <= 4 ->
    rw_cells rsegs m (bv_unsigned sp) [C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 0x86ba4); CB 8 x16; C8 (Z_to_bv 64 0);
                                      C8 va2; C8 va3; C8 va4; C8 va5; C8 va6; C8 va7] ->
    evt rsegs (tr7_post j m)
        (MS (mkR (Z_to_bv 64 0x86c8c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 (Z_to_bv 64 j) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86c8c) fc None m rom).
  Proof.
    intros j x16 va2 va3 va4 va5 va6 va7 m LO HI MI ST J FR.
    assert (CEILv : alloc_ceiling <= lo) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact CEIL).
    pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 80)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep.
    release_frame FR ST (bv_unsigned sp + 80).
    bstep.
    (* [comment removed for export] *)
    azstep.
    run_to 0x86bb0. at_pc 0x86bb0.
    azstep.
    assert (SW : bv_swrap 32 (j + -1) = j - 1) by (rewrite bv_swrap_small by (rewrite bv_half_modulus_32; lia); lia).
    rewrite SW.
    azstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - apply evt_done. unfold tr7_post. replace (j - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exists m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| assumption].
    - apply evt_done. unfold tr7_post. replace (j - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). exists m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| assumption].
  Qed.

  (* [comment removed for export] *)
  Definition tr8_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x86bc0) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (cl_free_pc LPA) fc None m' rom
      /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.
  Lemma tr8_walk : forall (x1 : word) (m : word -> option byte),
    mem_inv rsegs m ->
    evt rsegs (tr8_post m)
        (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86bb8) fc None m rom).
  Proof.
    intros x1 m MI.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    bstep. bstep. apply evt_done. unfold tr8_post. cbn [cl_free_pc LPA].
    eexists. split; [reflexivity|]. repeat (split; [eassumption|]). exact MI.
  Qed.

  (* [comment removed for export] *)
  #[using="CEIL Clg"] Lemma tr9_walk : forall (j0 : list byte) (v7 v6 v5 v4 v3 v2 v1 v0 x10 : word) (m : word -> option byte),
    lo <= bv_unsigned sp -> bv_unsigned sp + 80 <= 2^64 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m (bv_unsigned sp) (TFR j0 v7 v6 v5 v4 v3 v2 v1 v0 (Z_to_bv 64 TRUN_RET)) ->
    evt rsegs (trret_post 0 j0 v7 v6 v5 v4 v3 v2 v1 v0 m)
        (MS (mkR (Z_to_bv 64 0x86bc0) sp gp tp t0 t1 t2 s0 s1 x10 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x86bc0) fc None m rom).
  Proof.
    intros j0 v7 v6 v5 v4 v3 v2 v1 v0 x10 m LO HI MI ST FR. unfold TRUN_RET, TFR in *.
    assert (CEILv : alloc_ceiling <= lo) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact CEIL).
    pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 80)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    run_to 0x86bf0. at_pc 0x86bf0.
    release_frame FR ST (bv_unsigned sp + 80).
    bstep. bstep. apply evt_done. unfold trret_post, TRUN_RET. exists m. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI| assumption].
  Qed.
End Walks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TargetRun.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Variables (e0 e1 e2 e3 e4 e5 e6 e7 : word) (j8 : list byte).
  Variables (path data : list byte).
  Variables (gp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).   (* [comment removed for export] *)
  Hypothesis MALLOC1 : malloc1_stmt.   (* [comment removed for export] *)
  Hypothesis FREE1 : free1_stmt.
  Hypothesis EXIT : exit_spec_stmt.
  Hypothesis LIB : alib_call_ok.
  Hypothesis VPF1 : vprintf_first_stmt.
  Hypothesis VPF2 : vprintf_next_stmt.
  Hypothesis MAINRET : mainret_stmt usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 gp s8 s9 s10 s11 F fc.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation L := (Z.of_nat (length data)).
  #[local] Notation FV := (fview usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8).
  #[local] Notation MFRv := (MFR e0 e1 e2 e3 e4 e5 e6 e7 j8).
  #[local] Notation BST := (bst usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 data).

  Ltac ulit := rewrite ?unsigned_lit by (unfold SPF, STK_LO in *; lia).
  Ltac split_assum := first [assumption | split; [assumption | split_assum]].
  Ltac name_state m md AI :=
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ =>
      lazymatch goal with H : ainv _ mm mdd |- _ => rename H into AI end; rename mm into m; rename mdd into md end.

  (* [comment removed for export] *)
  Record tview (A : AS) (m : word -> option byte) (md : Model) (sof : stdout_form) (tid : Z) (tfr : list cell) (cb : Z) : Prop := {
    tv_ainv : ainv A m md;
    tv_mi   : mem_inv rsegs (aview A m);
    tv_fs   : m_fs md = fs;
    tv_fds  : m_fds md = fds_std;
    tv_cc   : ccells_x (aview A m) tid sof 1 cb;
    tv_args : args_at usp argv envp (aview A m);
    tv_sh   : forall a, in_stksh a -> aview A m (Z_to_bv 64 a) = Some (Z_to_bv 8 0);
    tv_stk  : stk rsegs (aview A m) (STK_LO usp) (SPF usp + -80);
    tv_mfr  : rw_cells rsegs (aview A m) (SPF usp) MFRv;
    tv_tfr  : rw_cells rsegs (aview A m) (SPF usp + -80) tfr
  }.

  #[using="HCEIL"] Lemma tview_stack : forall A m md sof tidq tfr cb m' md' W,
    tview A m md sof tidq tfr cb -> cells_size tfr = 80%nat ->
    ainv A m' md' -> mem_inv rsegs (aview A m') -> m_fs md' = fs -> m_fds md' = fds_std ->
    munch W (aview A m) (aview A m') -> wmono rsegs (aview A m) (aview A m') ->
    stack_only usp W -> disjoint_from W (SPF usp + -80) 160 ->
    stk rsegs (aview A m') (STK_LO usp) (SPF usp + -80) ->
    tview A m' md' sof tidq tfr cb.
  Proof.
    intros A m md sof tidq tfr cb m' md' W TV SZ AINV' MI' FS' FDS' MU WM SO DJ ST'.
    destruct TV as [AINV MI FS FDS CC AR SH ST MFR0 TFR0].
    (first [ pose proof ((aa_usp _ _ _ _ AR)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (aa_usp _ _ _ _ AR) as (U1 & U2 & U3 & U4) ]).
    (first [ pose proof ((bundle_stack_x usp argv envp HCEIL W _ _ tidq sof 1 cb MU SO U1 U2 CC AR SH)) as dR_2; dand4 dR_2 as CC' AR' SH' _ | destruct (bundle_stack_x usp argv envp HCEIL W _ _ tidq sof 1 cb MU SO U1 U2 CC AR SH) as (CC' & AR' & SH' & _) ]).
    assert (DJ1 : disjoint_from W (SPF usp) 80).
    { clear - DJ. induction W as [|[lo hi] W IH]; [exact I|]. cbn in DJ |- *. destruct DJ as [D1 D2]. split; [lia| exact (IH D2)]. }
    assert (DJ2 : disjoint_from W (SPF usp + -80) 80).
    { clear - DJ. induction W as [|[lo hi] W IH]; [exact I|]. cbn in DJ |- *. destruct DJ as [D1 D2]. split; [lia| exact (IH D2)]. }
    constructor; try assumption.
    - eapply (rw_cells_transport rsegs); [exact MFR0| exact MU| exact WM| exact DJ1].
    - eapply (rw_cells_transport rsegs); [exact TFR0| exact MU| exact WM|]. rewrite SZ. exact DJ2.
  Qed.

  #[using="HCEIL"] Lemma tview_ccall : forall A A' m md m' md' sof tidq tfr cb (sp win : Z) (V N : Z -> Prop),
    tview A m md sof tidq tfr cb -> cells_size tfr = 80%nat ->
    ainv A' m' md' -> mem_inv rsegs (aview A' m') -> m_fs md' = fs -> m_fds md' = fds_std ->
    cframe LPA (owned A) (owned A') sp win V N (aview A m) (aview A' m') -> heapish V ->
    STK_LO usp <= sp - win -> sp <= SPF usp + -80 ->
    tview A' m' md' sof tidq tfr cb.
  Proof.
    intros A A' m md m' md' sof tidq tfr cb sp win V N TV SZ AINV' MI' FS' FDS' CF HV WLO SPU.
    destruct TV as [AINV MI FS FDS CC AR SH ST MFR0 TFR0].
    (first [ pose proof ((aa_usp _ _ _ _ AR)) as dR_3; dand4 dR_3 as U1 U2 U3 U4 | pose proof (aa_usp _ _ _ _ AR) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    assert (CE : alloc_ceiling <= STK_LO usp) by ((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO; lia).
    (first [ pose proof ((bundle_cframe_x usp argv envp HCEIL A A' m md (aview A' m') sp win V N tidq sof 1 cb AINV CF ltac:(lia) ltac:(unfold SPF in SPU; lia) HV CC AR SH)) as dR_4; dand4 dR_4 as CC' AR' SH' _ | destruct (bundle_cframe_x usp argv envp HCEIL A A' m md (aview A' m') sp win V N tidq sof 1 cb AINV CF ltac:(lia) ltac:(unfold SPF in SPU; lia) HV CC AR SH)
      as (CC' & AR' & SH' & _) ]).
    constructor; try assumption.
    - eapply (stk_ccall LPA A A' m md); [exact AINV| exact CF| exact ST| exact CE| lia| exact SPU|].
      intros a Ha Va. heapish_elim HV a Va; (unfold STK_LO, SPF in *; heapish_case).
    - eapply (rw_cells_cframe A A' m md (aview A' m') sp win V N); try eassumption.
      + (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold SPF. lia. + unfold SPF in *. lia. + cbn [cells_size MFR csize Nat.add]. cbn. unfold SPF. lia.
    - eapply (rw_cells_cframe A A' m md (aview A' m') sp win V N); try eassumption.
      + (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold SPF. lia. + rewrite SZ. unfold SPF. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sof_after (i : nat) : stdout_form :=
    match i with O => SO_pristine | S i' => SO_buffered (zero_lines i') end.
  Lemma zero_lines_length : forall n, length (zero_lines n) = (2 * n)%nat.
  Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.
  Lemma zero_lines_snoc : forall n, zero_lines n ++ [Z_to_bv 8 48; Z_to_bv 8 10] = zero_lines (S n).
  Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ccells_set_tr1 : forall (v v' : word -> option byte) tidq sof (lo hi : Z),
    ccells v tidq sof 0 -> 0x60a000 <= lo ->
    munch [(lo, hi); (TR_INITIALIZED, TR_INITIALIZED + 1); (ATEXIT + 8, ATEXIT + 12); (ATEXIT + 40, ATEXIT + 48); (ATEXIT + 296, ATEXIT + 304)] v v' ->
    rw_cells rsegs v' TR_INITIALIZED [C1 (Z_to_bv 8 1)] ->
    rw_cells rsegs v' (ATEXIT + 8) [C4 (Z_to_bv 64 2)] ->
    rw_cells rsegs v' (ATEXIT + 40) [C8 (Z_to_bv 64 CALL_TRAMP)] ->
    rw_cells rsegs v' (ATEXIT + 296) [C8 (Z_to_bv 64 AEF_GUARD)] ->
    ccells v' tidq sof 1.
  Proof.
    (intros v v' tidq sof lo hi; (first [ intro dR_40; dand4 dR_40 as MC1 FE1 SOUT1 TR1 | intros (MC1 & FE1 & SOUT1 & TR1) ]); intros LO MU TRI' SLT' BF1' BA1').
    assert (AGM : agree_on (in_ranges MC_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGE : agree_on (in_ranges STDERR_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGO : agree_on (in_ranges STDOUT_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGI : agree_on (in_ranges [(TR_INCB, TR_INCB + 1)]) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [destruct FE1 as [fe [FOK FE]]; exists fe; split; [exact FOK| eapply stderr_agree; [exact AGE| exact FE]]|].
    split; [eapply stdout_at_agree; [exact AGO| exact SOUT1]|].
    destruct TR1 as (_ & _ & INCB & _ & _ & _).
    split; [right; reflexivity|]. split; [exact TRI'|]. split.
    { refine (rw_cells_agree rsegs _ _ _ _ _ INCB). intros i Hi. apply AGI. exists TR_INCB, (TR_INCB + 1). split; [left; reflexivity| cbn in Hi; lia]. }
    split; [exact SLT'|]. split; [exact BF1'| exact BA1'].
  Qed.

  (* [comment removed for export] *)
  Lemma ccells_set_incb : forall (v v' : word -> option byte) tidq sof ini cb cb' (lo hi : Z),
    ccells_x v tidq sof ini cb -> 0x60a000 <= lo ->
    munch [(lo, hi); (TR_INCB, TR_INCB + 1)] v v' ->
    rw_cells rsegs v' TR_INCB [C1 (Z_to_bv 8 cb')] -> ccells_x v' tidq sof ini cb'.
  Proof.
    (intros v v' tidq sof ini cb cb' lo hi; (first [ intro dR_40; dand4 dR_40 as MC1 FE1 SOUT1 TR1 | intros (MC1 & FE1 & SOUT1 & TR1) ]); intros LO MU INCB').
    assert (AGM : agree_on (in_ranges MC_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGE : agree_on (in_ranges STDERR_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGO : agree_on (in_ranges STDOUT_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGI : agree_on (in_ranges [(TR_INITIALIZED, TR_INITIALIZED + 1); (ATEXIT + 8, ATEXIT + 12); (ATEXIT + 40, ATEXIT + 48); (ATEXIT + 296, ATEXIT + 304)]) v v')
      by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [destruct FE1 as [fe [FOK FE]]; exists fe; split; [exact FOK| eapply stderr_agree; [exact AGE| exact FE]]|].
    split; [eapply stdout_at_agree; [exact AGO| exact SOUT1]|].
    destruct TR1 as (I01 & TRI & _ & SLT & BF1 & BA1).
    split; [exact I01|].
    split; [refine (rw_cells_agree rsegs _ _ _ _ _ TRI); intros i Hi; apply AGI; exists TR_INITIALIZED, (TR_INITIALIZED + 1); split; [cbn; tauto| cbn in Hi; lia]|].
    split; [exact INCB'|].
    split; [refine (rw_cells_agree rsegs _ _ _ _ _ SLT); intros i Hi; apply AGI; exists (ATEXIT + 8), (ATEXIT + 12); split; [cbn; tauto| cbn in Hi; lia]|].
    split; [refine (rw_cells_agree rsegs _ _ _ _ _ BF1); intros i Hi; apply AGI; exists (ATEXIT + 40), (ATEXIT + 48); split; [cbn; tauto| cbn in Hi; lia]|].
    refine (rw_cells_agree rsegs _ _ _ _ _ BA1); intros i Hi; apply AGI; exists (ATEXIT + 296), (ATEXIT + 304); split; [cbn; tauto| cbn in Hi; lia].
  Qed.

  Lemma ccells_after_stdout : forall (v v' : word -> option byte) tidq sof sof' ini cb (lo hi : Z),
    ccells_x v tidq sof ini cb -> 0x60a000 <= lo ->
    munch [(lo, hi); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 1024)] v v' ->
    stdout_at v' sof' -> ccells_x v' tidq sof' ini cb.
  Proof.
    (intros v v' tidq sof sof' ini cb lo hi; (first [ intro dR_41; dand4 dR_41 as MC1 FE1 SOUT1 TR1 | intros (MC1 & FE1 & SOUT1 & TR1) ]); intros LO MU SO').
    assert (AGM : agree_on (in_ranges MC_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGE : agree_on (in_ranges STDERR_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    assert (AGT : agree_on (in_ranges TR_RANGES) v v') by (apply (agree_of_munch _ _ _ _ MU); ranges_outside).
    split; [eapply mcells_agree; [exact AGM| exact MC1]|]. split; [destruct FE1 as [fe [FOK FE]]; exists fe; split; [exact FOK| eapply stderr_agree; [exact AGE| exact FE]]|].
    split; [exact SO'|]. revert TR1 AGT. clear. intros TR1 AGT.
    exact (trcells_x_agree _ _ _ _ AGT TR1).
  Qed.

  (* [comment removed for export] *)
  #[using="HCEIL"] Lemma tview_incb : forall A m md sof tidq tfr cb cb' m' md',
    tview A m md sof tidq tfr cb -> cells_size tfr = 80%nat ->
    ainv A m' md' -> mem_inv rsegs (aview A m') -> m_fs md' = fs -> m_fds md' = fds_std ->
    munch [(TR_INCB, TR_INCB + 1)] (aview A m) (aview A m') -> wmono rsegs (aview A m) (aview A m') ->
    stk rsegs (aview A m') (STK_LO usp) (SPF usp + -80) ->
    rw_cells rsegs (aview A m') TR_INCB [C1 (Z_to_bv 8 cb')] ->
    tview A m' md' sof tidq tfr cb'.
  Proof.
    intros A m md sof tidq tfr cb cb' m' md' TV SZ AINV' MI' FS' FDS' MU WM ST' INCB'.
    destruct TV as [AINV MI FS FDS CC AR SH ST MFR0 TFR0].
    (first [ pose proof ((aa_usp _ _ _ _ AR)) as dR_1; dand4 dR_1 as U1 U2 U3 U4 | pose proof (aa_usp _ _ _ _ AR) as (U1 & U2 & U3 & U4) ]).
    pose proof U1 as U1'. unfold sp_window_lo in U1'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    assert (MU2 : munch [(usp, usp); (TR_INCB, TR_INCB + 1)] (aview A m) (aview A m')).
    { intros x Hx. apply (MU x). revert Hx. unfold TR_INCB. cbn [outside]. tauto. }
    constructor; try assumption.
    - exact (ccells_set_incb (aview A m) (aview A m') tidq sof 1 cb cb' usp usp CC ltac:(lia) MU2 INCB').
    - apply (args_at_agree usp argv envp (aview A m)); [| exact AR]. apply (agree_of_munch _ _ _ _ MU).
      pose proof (aa_b0 _ _ _ _ AR) as B0. pose proof (aa_b1 _ _ _ _ AR) as B1.
      intros a Ha. unfold in_args, e_p1a in *. unfold e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, TR_INCB, SPF, STK_LO in *. cbn [outside].
      destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [| | | specialize (B1 H2)]; (split; [lia| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia]).
    - intros a Ha. rewrite <- (SH a Ha). apply (MU (Z_to_bv 64 a)). unfold in_stksh, STKSH_LO, STKSH_HI, sh, kShadowOffset in Ha. rewrite unsigned_lit by lia.
      unfold TR_INCB. cbn [outside]. split; [lia| exact I].
    - eapply (rw_cells_transport rsegs); [exact MFR0| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add MFR]. unfold TR_INCB, SPF in *. lia.
    - eapply (rw_cells_transport rsegs); [exact TFR0| exact MU| exact WM|]. rewrite SZ. cbn [disjoint_from]. unfold TR_INCB, SPF in *. lia.
  Qed.

  (* [comment removed for export] *)
  Section Run.
  Variables (k : nat) (b tid : Z).
  Hypothesis K10 : (k <= 10)%nat.
  Hypothesis LK : L < cap k.
  Hypothesis L6 : 6 <= L.
  Hypothesis BNZ : b <> 0.

  (* [comment removed for export] *)
  Let c : Z := clen_of data.
  Let plen : Z := L - c + -6.
  Let d1 : byte := nth 1 data (Z_to_bv 8 0).
  Let d2 : Z := bv_unsigned (nth 2 data (Z_to_bv 8 0)).
  Let calls : Z := if c =? 0 then 1 else d2 mod 4 + 1.
  Let inp : list byte := skipn (Z.to_nat (c + 6)) data.
  Let cnt : bool := 128 <=? bv_unsigned d1.
  Definition TSUCC : TSet := t_emit (W 1 (zero_lines (Z.to_nat calls))) (t_exit (exit_code 0) fs).

  #[using="plen K10 k"] Lemma calls_range : 1 <= calls <= 4.
  Proof. subst calls. destruct (c =? 0); [lia|]. pose proof (Z.mod_pos_bound d2 4 ltac:(lia)). lia. Qed.

  Hypothesis CL : c + 6 <= L.

  #[using="CL calls d2 LK K10 k"] Lemma plen_range : 0 <= plen < 2^26.
  Proof. pose proof (cap_range k K10). pose proof (cfgv_range (dbyte data 0) (dbyte data 1)). subst plen c. unfold clen_of in *. lia. Qed.

  #[using="CL K10 k plen"] Lemma t_tail_eq :
    t_tail data fs = TSUCC.   (* [comment removed for export] *)
  Proof.
    unfold t_tail, TSUCC. rewrite <- (clen_of_cfg data). fold c.
    pose proof (cfgv_range (dbyte data 0) (dbyte data 1)) as CR. change (cfgv (dbyte data 0) (dbyte data 1)) with c in CR.
    replace (match Z.to_nat c with 0%nat => 1%nat | S _ => S (Z.to_nat (bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4)) end) with (Z.to_nat calls).
    2:{ subst calls d2. destruct (Z.eqb_spec c 0) as [E|NE]; [rewrite E; reflexivity|].
        destruct (Z.to_nat c) eqn:EC; [lia|]. pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 data (Z_to_bv 8 0))) 4 ltac:(lia)). lia. }
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition TFRv (j0 : list byte) : list cell :=
    TFR j0 (Z_to_bv 64 0) (Z_to_bv 64 READ_STAGE) (sxb d1) (Z_to_bv 64 plen) (Z_to_bv 64 (b + 2 + c + 4)) (Z_to_bv 64 c) (Z_to_bv 64 b) (Z_to_bv 64 (b + 2)) (Z_to_bv 64 TRUN_RET).

  (* [comment removed for export] *)
  #[using="MAINRET"] Lemma tr_return : forall A m md sof (st : Z) (n0 : Z) (zra z0 z1 z2 xa1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word) x18 x19 x20,
      ainv A m md -> mem_inv rsegs (aview A m) -> m_fs md = fs -> m_fds md = fds_std ->
      ccells (aview A m) tid sof 1 -> args_at usp argv envp (aview A m) ->
      (forall a, in_stksh a -> aview A m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
      stk rsegs (aview A m) (STK_LO usp) (SPF usp) -> rw_cells rsegs (aview A m) (SPF usp) MFRv ->
      a_live A b = Some n0 -> (st = 0 \/ st = 2) ->
      srealizes rsegs
        (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 (b + 2)) (Z_to_bv 64 b) (Z_to_bv 64 st)
                        xa1 za2 za3 za4 za5 za6 za7 x18 x19 x20 (sxb d1) (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 0) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 TRUN_RET) fc None m rom) md)
        (t_emit (W 1 (pending_of sof)) (t_exit (exit_code (if cnt then 0 else st)) fs)).
  Proof.
    intros until x20. intros AINV MI FS FDS CC AR SH ST FR LV ST01.
    unfold TRUN_RET. subst cnt.
    apply (MAINRET A m md tid sof 1 b n0 st d1); [| exact LV| exact ST01].
    constructor; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="CL calls d2 LK K10 MAINRET FREE1 HCEIL"] Lemma tr_tail : forall A m md sof (j0 : list byte) (aligned owned nown : Z)
           (zra z0 z1 z2 xa0 za1 za2 za3 za4 za5 za6 za7 x19 x20 x21 x23 zt3 zt4 zt5 zt6 : word),
      tview A m md sof tid (TFRv j0) 0 ->
      a_live A b = Some (cap k) -> owned <> b -> ((owned = 0 /\ nown = 0) \/ a_live A owned = Some nown) ->
      srealizes rsegs
        (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp + -80)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 plen) (Z_to_bv 64 aligned) xa0
                        za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 owned) x19 x20 x21 (Z_to_bv 64 0) x23 s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x86bb8) fc None m rom) md)
        (t_emit (W 1 (pending_of sof)) (t_exit (exit_code (if cnt then 0 else 0)) fs)).
  Proof.
    intros until zt6. intros TV LVb OB OWN.
    pose proof (cap_range k K10) as CKR. pose proof plen_range as PLR.
    pose proof TV as [AINV MI FS FDS CC AR SH ST MFR0 TFR0].
    (first [ pose proof ((aa_usp _ _ _ _ AR)) as dR_5; dand4 dR_5 as U1 U2 U3 U4 | pose proof (aa_usp _ _ _ _ AR) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    assert (SPFV : SPF usp = usp - 128) by reflexivity.
    (* [comment removed for export] *)
    pose proof (munch_refl [] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) []) by exact I.
    ago AINV. fold_cl_segs.
    icall tr8_walk by (exact MI).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_6; dand3 dR_6 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    lazymatch goal with H : stk _ (aview A m1) _ _ |- _ => rename H into ST1 end.
    assert (TV1 : tview A m1 md1 sof tid (TFRv j0) 0).
    { eapply (tview_stack A m md); try eassumption; try reflexivity.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS | apply stack_only_nil | exact I]. }
    clear CC AR SH MFR0 TFR0 MU WM CF. pose proof TV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ MFR1 TFR1].
    (* [comment removed for export] *)
    pose proof FREE1 as FRE. unfold free1_stmt in FRE. cbv zeta in FRE.
    eapply FRE with (p := owned) (n0 := nown); clear FRE.
    all: lazymatch goal with
         | |- ainv _ _ _ => exact AINV1
         | |- mem_inv _ _ => exact MI1
         | |- @eq word _ _ => reflexivity
         | |- _ \/ a_live _ _ = Some _ => exact OWN
         | |- In _ (cl_sites LPA) => rewrite unsigned_lit by lia; cbn; tauto
         | |- mapped _ _ _ => ulit; eapply (stk_mapped (L:=LPA)); [exact ST1| exact CEIL| unfold ASTK, STK_LO, SPF; lia| lia]
         | |- forall t0', _ => idtac
         | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold ASTK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
         end.
    intros v0 v1 v2 va0 va1 va2 va3 va4 va5 va6 va7 vt3 vt4 vt5 vt6 A' m2 md2 AINV2 MI2 MDF FRS LV2 LVO2 LB2 TC2 NL2 SC2 PC2 FRK.   (* [comment removed for export] *)
    (first [ pose proof ((amd_frame_io md1 md2 MDF)) as dR_7; dand3 dR_7 as FS2 FDS2 _ | pose proof (amd_frame_io md1 md2 MDF) as (FS2 & FDS2 & _) ]).
    replace (ret_pc (Z_to_bv 64 0x86bc0)) with (Z_to_bv 64 0x86bc0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cframe_of_frame_ok LPA) in FRK. rewrite ?unsigned_lit in FRK by (unfold SPF, STK_LO in *; lia).
    assert (HVB : heapish (newblk owned nown)).
    { destruct OWN as [[-> ->]|LVO]; [| exact (heapish_newblk A m1 md1 owned nown AINV1 LVO)].
      intros a [[X _]|[X _]]; exfalso; apply X; reflexivity. }
    assert (TV2 : tview A' m2 md2 sof tid (TFRv j0) 0).
    { eapply (tview_ccall A A' m1 md1 m2 md2); try eassumption; try reflexivity.
      all: first [rewrite FS2; exact FS1q | rewrite FDS2; exact FDS1q | unfold ASTK, STK_LO, SPF; lia]. }
    pose proof TV2 as [_ _ FS2q FDS2q CC2 AR2 SH2 ST2 MFR2 TFR2].
    assert (LVb2 : a_live A' b = Some (cap k)) by (rewrite (LVO2 b (fun X => OB (eq_sym X))); exact LVb).
    (* [comment removed for export] *)
    pose proof (munch_refl [(SPF usp + -80, SPF usp + -80 + 80)] (aview A' m2)) as MU. pose proof (wmono_refl rsegs (aview A' m2)) as WM.
    assert (CF : client_fpx (L:=LPA) A' (aview A' m2) [(SPF usp + -80, SPF usp + -80 + 80)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
      replace (SPF usp + -80 + 80 - (SPF usp + -80)) with 80 by lia.
      destruct TFR2 as [[_ _] (W0 & W1 & W)]. intros i Hi E. apply (W i); [cbn; lia|]. unfold wa.
      rewrite pa_wview_overlay by (rewrite unsigned_lit by (unfold SPF, STK_LO in *; lia); unfold SPF, STK_LO in *; lia). exact E. }
    ago AINV2. fold_cl_segs.
    icall tr9_walk by (first [exact CEIL | exact MI2 | ulit; first [exact ST2 | exact TFR2 | unfold STK_LO, SPF in *; lia]]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST3 end.
    astopx AINV2 MU WM CF. name_state m3 md3 AINV3.
    (first [ pose proof ((sbm_io md2 md3 SBM0)) as dR_8; dand3 dR_8 as FS3 FDS3 _ | pose proof (sbm_io md2 md3 SBM0) as (FS3 & FDS3 & _) ]).
    rewrite ?unsigned_lit in ST3 by (unfold SPF, STK_LO in *; lia). replace (SPF usp + -80 + 80) with (SPF usp) in ST3 by lia.
    assert (SO3 : stack_only usp [(SPF usp + -80, SPF usp + -80 + 80)]) by (apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]).
    (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid sof 1 MU SO3 U1 U2 CC2 AR2 SH2)) as dR_9; dand4 dR_9 as CC3 AR3 SH3 _ | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid sof 1 MU SO3 U1 U2 CC2 AR2 SH2) as (CC3 & AR3 & SH3 & _) ]).
    replace (Z_to_bv 64 (SPF usp + -80 + 80)) with (Z_to_bv 64 (SPF usp)) by (f_equal; lia).
    eapply (tr_return A' m3 md3 sof 0 (cap k)); try eassumption.
    - rewrite FS3. exact FS2q. - rewrite FDS3. exact FDS2q. - left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition FIN : TSet := t_emit (W 1 (zero_lines (Z.to_nat calls - 1))) (t_exit (exit_code (if cnt then 0 else 0)) fs).
  Definition TI (i : nat) : TSet := match i with O => t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) FIN | S _ => FIN end.

  (* [comment removed for export] *)
  Definition pay_ok (A : AS) (v : word -> option byte) (aligned owned nown : Z) : Prop :=
       (plen = 0 /\ owned = 0 /\ nown = 0 /\ aligned = TR_EMPTY)
    \/ (0 < plen /\ owned = aligned /\ nown = plen /\ a_live A owned = Some plen /\ rw_cells rsegs v aligned [CB (Z.to_nat plen) inp]).

  #[using="CL calls d2 K10 k"] Lemma inp_length : Z.of_nat (length inp) = plen.
  Proof. subst inp plen. rewrite length_skipn. pose proof (cfgv_range (dbyte data 0) (dbyte data 1)). subst c. unfold clen_of in *. lia. Qed.

  Lemma rw_C8_bytes : forall (v : word -> option byte) a w, rw_cells rsegs v a [C8 w] -> bytes_at rsegs v a (le8 w).
  Proof. intros v a w [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.

  Lemma fds_std_1 : fd_lookup fds_std (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma zeros_eq_repeat : forall n, zeros n = repeat (Z_to_bv 8 0) n.
  Proof. reflexivity. Qed.

  #[using="CL BNZ LK K10 MAINRET VPF2 VPF1 LIB FREE1 HCEIL"] Lemma tr_loop : forall (jn i : nat) A m md (j0 : list byte) (aligned owned nown : Z)
           (zra z0 z1 z2 xa0 xa1 za2 za3 za4 za5 za6 za7 x19 zt3 zt4 zt5 zt6 : word),
      1 <= Z.of_nat jn -> (i + jn)%nat = Z.to_nat calls ->
      tview A m md (sof_after i) tid (TFRv j0) 0 ->
      a_live A b = Some (cap k) -> pay_ok A (aview A m) aligned owned nown -> owned <> b ->
      a_livebytes A = cap k + plen -> a_nlive A <= 2 -> (forall ff, a_frame A ff = None) ->
      Z.of_nat jn * LIB_SECC (Z.of_nat (length (if plen =? 0 then [] else inp))) <= a_seccred A ->
      Z.of_nat jn * LIB_PRIM (Z.of_nat (length (if plen =? 0 then [] else inp))) <= a_primcred A ->   (* [comment removed for export] *)
      srealizes rsegs
        (mkCfg (MS (mkR zra (Z_to_bv 64 (SPF usp + -80)) gp (Z_to_bv 64 TPV) z0 z1 z2 (Z_to_bv 64 plen) (Z_to_bv 64 aligned) xa0 xa1
                        za2 za3 za4 za5 za6 za7 (Z_to_bv 64 owned) x19 (Z_to_bv 64 TR_INITIALIZED) (Z_to_bv 64 (Z.of_nat jn)) (Z_to_bv 64 0)
                        (Z_to_bv 64 (-2)) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x86b80) fc None m rom) md)
        (TI i).
  Proof.
    induction jn as [|jn IH]; intros until zt6; intros J IJ TV LVb PAY OB LB NL FRS SCC PCC; [lia|].   (* [comment removed for export] *)
    pose proof calls_range as CAR. pose proof (cap_range k K10) as CKR. pose proof plen_range as PLR.
    pose proof TV as [AINV MI FS FDS CC AR SH ST MFR0 TFR0].
    (first [ pose proof ((aa_usp _ _ _ _ AR)) as dR_10; dand4 dR_10 as U1 U2 U3 U4 | pose proof (aa_usp _ _ _ _ AR) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    assert (SPFV : SPF usp = usp - 128) by reflexivity.
    (first [ pose proof ((as_live_ok LPA A m md b (cap k) AINV LVb)) as dR_11; dand5 dR_11 as _ BAL BLO BHI _ | destruct (as_live_ok LPA A m md b (cap k) AINV LVb) as (_ & BAL & BLO & BHI & _) ]).
    rename BLO into BAPP. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    assert (BLO : 0x60a000 <= b).
    { pose proof (cap_range k K10) as CKR'. clear - BAPP CKR'. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BAPP; cbn [cl_image_lo cl_image_hi LPA] in BAPP. lia. }
    (* [comment removed for export] *)
    pose proof CC as (_ & _ & _ & (_ & _ & INCB0 & _)).
    pose proof (munch_refl [(TR_INCB, TR_INCB + 1)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(TR_INCB, TR_INCB + 1)]).
    { cbn. split; [| exact I]. right. unfold TR_INCB. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    ago AINV. fold_cl_segs.
    icall tr5_walk by (first [exact MI | exact INCB0]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    lazymatch goal with H : rw_cells _ _ TR_INCB [C1 (Z_to_bv 8 1)] |- _ => rename H into INCB1 end.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_12; dand3 dR_12 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    try clear ST.   (* [comment removed for export] *)
    assert (ST1 : stk rsegs (aview A m1) (STK_LO usp) (SPF usp + -80)).
    { apply (stk_transport_disjoint rsegs _ _ _ _ _ (tv_stk _ _ _ _ _ _ _ TV) MU WM). cbn [disjoint_from]. unfold TR_INCB, STK_LO, SPF in *. lia. }
    assert (TV1 : tview A m1 md1 (sof_after i) tid (TFRv j0) 1).
    { eapply (tview_incb A m md); try eassumption; try reflexivity.
      all: first [rewrite FS1; exact FS | rewrite FDS1; exact FDS]. }
    assert (PAY1 : pay_ok A (aview A m1) aligned owned nown).
    { destruct PAY as [X|(P1 & P2 & P3 & P4 & P5)]; [left; exact X| right]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      subst owned. (first [ pose proof ((as_live_ok LPA A m md aligned plen AINV P4)) as dR_19; dand5 dR_19 as _ _ ALO AHI _ | destruct (as_live_ok LPA A m md aligned plen AINV P4) as (_ & _ & ALO & AHI & _) ]). unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in ALO; cbn [cl_image_lo cl_image_hi LPA] in ALO.
      eapply (rw_cells_transport rsegs); [exact P5| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold TR_INCB. lia. }
    clear CC AR SH MU WM CF PAY. try clear MFR0. try clear TFR0. pose proof TV1 as [_ _ FS1q FDS1q CC1 AR1 SH1 _ MFR1 TFR1].
    (* [comment removed for export] *)
    apply (LIB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 md1 A aligned (if plen =? 0 then [] else inp)
                 (sh alloc_ceiling) ((2^47 - alloc_ceiling) / 8) (TI i)).
    { (* [comment removed for export] *)
      constructor.
      - reflexivity.
      - destruct (Z.eqb_spec plen 0) as [P0|P0]; [rewrite P0; reflexivity| rewrite inp_length; reflexivity].
      - reflexivity.
      - ulit. unfold SPF. Z.div_mod_to_equations. lia.
      - ulit. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold LIB_STACK, SPF, STK_LO in *. lia.
      - ulit. unfold SPF. lia.
      - exact AINV1.
      - exact MI1.
      - ulit. destruct (stk_split rsegs (aview A m1) (STK_LO usp) (SPF usp + -80 - LIB_STACK) (SPF usp + -80) ST1) as [_ X];
          [unfold LIB_STACK, STK_LO, SPF; lia| exact X].
      - pose proof (stksh_bytes _ SH1) as SB0. rewrite zeros_eq_repeat in SB0.
        split; [exact SB0|]. clear SB0. ulit. unfold LIB_STACK, sh, kShadowOffset, kHighMemBeg, SPF, STK_LO in *. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; Z.div_mod_to_equations; lia.
      - apply rw_errno_any.
      - apply rw_C8_any; [cbn; lia| cbn; lia| vm_compute; reflexivity| vm_compute; reflexivity].
      - apply rw_C8_any; [cbn; lia| cbn; lia| vm_compute; reflexivity| vm_compute; reflexivity].
      - exact FRS.
      - destruct (Z.eqb_spec plen 0) as [P0|P0]; [cbn; unfold NMAX; lia| rewrite inp_length; unfold NMAX; lia].
      - destruct (Z.eqb_spec plen 0) as [P0|P0]; [cbn; intros X; exfalso; apply X; reflexivity|].
        intros _. destruct PAY1 as [(X & _)|(P1 & P2 & P3 & P4 & P5)]; [lia|]. rewrite inp_length. subst owned.
        split; [| split; [exact P4|]].
        + intros E0. rewrite E0 in P4. (first [ pose proof ((as_live_ok LPA A m1 md1 0 plen AINV1 P4)) as dR_13; dand4 dR_13 as _ _ X _ | destruct (as_live_ok LPA A m1 md1 0 plen AINV1 P4) as (_ & _ & X & _) ]). clear - X.
          unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in X; cbn [cl_image_lo cl_image_hi LPA] in X. lia.
        + (first [ pose proof ((rwCB_elim _ _ _ _ P5)) as dR_14; dand3 dR_14 as _ B _ | destruct (rwCB_elim _ _ _ _ P5) as (_ & B & _) ]). exact B.
      - split.
        + rewrite LB, LIVE_MAX_eq. unfold LIB_LIVE, PARSE_LIVE. destruct (plen =? 0); [cbn [length Z.of_nat]; lia| rewrite inp_length; lia].
        + rewrite NLIVE_MAX_eq. unfold LIB_NLIVE. lia.
      - (* [comment removed for export] *)
        assert (LSP : 0 <= LIB_SECC (Z.of_nat (length (if plen =? 0 then [] else inp)))) by (unfold LIB_SECC; apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
        nia.
      - (* [comment removed for export] *)
        assert (LPP : 0 <= LIB_PRIM (Z.of_nat (length (if plen =? 0 then [] else inp)))) by (unfold LIB_PRIM; lia).
        nia. }
    (* [comment removed for export] *)
    intros y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 m' md' A' PO.
    destruct PO as [AINV' MI' MDF LVE LVB FRS' (LB' & NL' & TC') SCq PCq STK' STKSH' ERR' BSS1 BSS2 CFR].   (* [comment removed for export] *)
    (first [ pose proof ((amd_frame_io md1 md' MDF)) as dR_15; dand3 dR_15 as FS' FDS' _ | pose proof (amd_frame_io md1 md' MDF) as (FS' & FDS' & _) ]).
    replace (ret_pc (Z_to_bv 64 0x86b94)) with (Z_to_bv 64 0x86b94) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ?unsigned_lit in CFR by (unfold SPF, STK_LO in *; lia).
    assert (TV' : tview A' m' md' (sof_after i) tid (TFRv j0) 1).
    { eapply (tview_ccall A A' m1 md1 m' md'); try eassumption; try reflexivity.
      all: first [rewrite FS'; exact FS1q | rewrite FDS'; exact FDS1q | unfold LIB_STACK, STK_LO, SPF; lia | idtac].
      intros a Ha. do 6 right. unfold HBSS. cbn [vi_bss_vsc vi_bss_cp VIA] in Ha. lia. }
    assert (LVb' : a_live A' b = Some (cap k)) by (exact (LVE _ _ LVb)).
    assert (PAY' : pay_ok A' (aview A' m') aligned owned nown).
    { destruct PAY1 as [X|(P1 & P2 & P3 & P4 & P5)]; [left; exact X| right]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
      split; [exact (LVE _ _ P4)|]. subst owned.
      refine (rw_cells_agree rsegs _ _ _ _ _ P5). intros q Hq. apply (LVB aligned plen q P4). cbn [cells_size csize Nat.add] in Hq. lia. }
    clear CC1 AR1 SH1 MFR1 TFR1 PAY1. pose proof TV' as [_ _ FSq FDSq CC' AR' SH' ST' _ _].
    (* [comment removed for export] *)
    pose proof CC' as (MCq & _ & _ & (_ & _ & INCB' & _)).
    pose proof (munch_refl [(SPF usp + -80 + -80, SPF usp + -80); (TR_INCB, TR_INCB + 1)] (aview A' m')) as MU. pose proof (wmono_refl rsegs (aview A' m')) as WM.
    assert (CF : client_fpx (L:=LPA) A' (aview A' m') [(SPF usp + -80 + -80, SPF usp + -80); (TR_INCB, TR_INCB + 1)]).
    { cbn. split; [| split; [| exact I]].
      - left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
        replace (SPF usp + -80 - (SPF usp + -80 + -80)) with 80 by lia.
        eapply (stk_mapped (L:=LPA)); [exact ST' | exact CEIL | unfold STK_LO, SPF in *; lia | lia].
      - right. unfold TR_INCB. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    ago AINV'. fold_cl_segs.
    icall tr6_walk by (first [exact CEIL | exact MI' | exact INCB' | ulit; first [exact ST' | unfold STK_LO, SPF in *; lia]]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST2 end.
    lazymatch goal with H : rw_cells _ _ _ (EFR _ _ _ _ _ _ _ _) |- _ => rename H into EFR2 end.
    lazymatch goal with H : rw_cells _ _ TR_INCB [C1 (Z_to_bv 8 0)] |- _ => rename H into INCB2 end.
    astopx AINV' MU WM CF. name_state m2 md2 AINV2.
    (first [ pose proof ((sbm_io md' md2 SBM0)) as dR_16; dand3 dR_16 as FS2 FDS2 _ | pose proof (sbm_io md' md2 SBM0) as (FS2 & FDS2 & _) ]).
    rewrite ?unsigned_lit in ST2, EFR2 by (unfold SPF, STK_LO in *; lia).
    rewrite ?unsigned_lit in MU by (unfold SPF, STK_LO in *; lia).
    assert (CC2 : ccells_x (aview A' m2) tid (sof_after i) 1 0).
    { exact (ccells_set_incb (aview A' m') (aview A' m2) tid (sof_after i) 1 1 0 (SPF usp + -80 + -80) (SPF usp + -80) CC' ltac:(unfold SPF, STK_LO in *; lia) MU INCB2). }
    assert (AR2 : args_at usp argv envp (aview A' m2)).
    { apply (args_at_agree usp argv envp (aview A' m')); [| exact AR']. apply (agree_of_munch _ _ _ _ MU).
      pose proof (aa_b0 _ _ _ _ AR') as B0. pose proof (aa_b1 _ _ _ _ AR') as B1.
      intros a Ha. unfold in_args, e_p1a in *. unfold e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, TR_INCB, SPF, STK_LO in *. cbn [outside].
      destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [| | | specialize (B1 H2)]; (split; [lia| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia]). }
    assert (SH2 : forall a, in_stksh a -> aview A' m2 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite <- (SH' a Ha). apply (MU (Z_to_bv 64 a)). unfold in_stksh, STKSH_LO, STKSH_HI, sh, kShadowOffset in Ha; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). rewrite unsigned_lit by lia.
      unfold TR_INCB, SPF, STK_LO in *. cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia. }
    assert (GOT2 : ro_cells rsegs (aview A' m2) SSP_GOT [C8 (Z_to_bv 64 SSP_GUARD)]).
    { eapply ro_cells_transport; [exact (mc_sspgot _ _ MCq) | exact MU |]. cbn [disjoint_from cells_size csize Nat.add]. unfold SSP_GOT, TR_INCB, SPF, STK_LO in *. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
    (first [ pose proof (CC2) as dR_18; dand4 dR_18 as MC2 _ SOUT2 _ | pose proof CC2 as (MC2 & _ & SOUT2 & _) ]).
    assert (PAY2 : pay_ok A' (aview A' m2) aligned owned nown).
    { destruct PAY' as [X|(P1 & P2 & P3 & P4 & P5)]; [left; exact X| right]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      subst owned. (first [ pose proof ((as_live_ok LPA A' m' md' aligned plen AINV' P4)) as dR_19; dand5 dR_19 as _ _ ALO AHI _ | destruct (as_live_ok LPA A' m' md' aligned plen AINV' P4) as (_ & _ & ALO & AHI & _) ]). unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in ALO; cbn [cl_image_lo cl_image_hi LPA] in ALO. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      eapply (rw_cells_transport rsegs); [exact P5| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold TR_INCB, SPF, STK_LO in *. lia. }
    unfold EFR in EFR2.
    pose proof (rw_C8_bytes _ _ _ (rw_cells_pick rsegs _ _ _ 24%nat _ EFR2 eq_refl)) as VA0.
    (* [comment removed for export] *)
    assert (VP : forall K : TSet,
      (match i with O => t_emit (W 1 [Z_to_bv 8 48; Z_to_bv 8 10]) K | S _ => K end) = TI i ->
      K [] ->
      (forall m3 md3 (r : word), ainv A' m3 md3 -> md_io md2 md3 (m_fds md2) -> stdout_at (aview A' m3) (sof_after (S i)) ->
          forall ms', (exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
              ms' = MS (mkR (Z_to_bv 64 0x86c8c) (Z_to_bv 64 (SPF usp + -80 + -80)) gp (Z_to_bv 64 TPV) t0' t1' t2' (Z_to_bv 64 plen) (Z_to_bv 64 aligned) r
                            a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 owned) (Z_to_bv 64 0) (Z_to_bv 64 TR_INITIALIZED) (Z_to_bv 64 (Z.of_nat (S jn))) (Z_to_bv 64 0)
                            (Z_to_bv 64 (-2)) s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc (Z_to_bv 64 0x86c8c)) fc None m3 rom
              /\ munch [(SPF usp + -80 + -80 - VPRINTF_ICPT_STACK, SPF usp + -80 + -80); (STDOUT_F, STDOUT_F + 152); (STDOUT_BUF, STDOUT_BUF + 1024)] (aview A' m2) (aview A' m3)
              /\ wmono rsegs (aview A' m2) (aview A' m3) /\ mem_inv rsegs (aview A' m3) /\ stk rsegs (aview A' m3) (STK_LO usp) (SPF usp + -80 + -80)) ->
          srealizes rsegs (mkCfg ms' md3) K) ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x86c8c) (Z_to_bv 64 (SPF usp + -80 + -80)) gp (Z_to_bv 64 TPV) y0 y1 y2 (Z_to_bv 64 plen) (Z_to_bv 64 aligned)
                        (Z_to_bv 64 FMT_D) (Z_to_bv 64 (SPF usp + -80 + -56)) ya2 ya3 ya4 ya5 ya6 ya7
                        (Z_to_bv 64 owned) (Z_to_bv 64 0) (Z_to_bv 64 TR_INITIALIZED) (Z_to_bv 64 (Z.of_nat (S jn))) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) s8 s9 s10 s11 yt3 yt4 yt5 yt6)
                   F (Z_to_bv 64 VPRINTF_ICPT_ENTRY) fc None m2 rom) md2) (TI i)).
    { intros K EK KN KK. rewrite <- EK. destruct i as [|i'].
      - pose proof VPF1 as VP1. unfold vprintf_first_stmt in VP1. cbv zeta in VP1.
        eapply VP1 with (va := SPF usp + -80 + -56) (lo := STK_LO usp); clear VP1.
        all: lazymatch goal with
             | |- ainv _ _ _ => exact AINV2
             | |- mem_inv _ _ => exact MI2
             | |- @eq word _ _ => reflexivity
             | |- bytes_at _ _ (SPF usp + -80 + -56) _ => replace (SPF usp + -80 + -56) with (SPF usp + -80 + -80 + Z.of_nat 24) by lia; exact VA0
             | |- forall v', consts_hold LPA v' -> _ => intros v' CH'; split; [apply rodata_range_ok| apply bss_range_ok]; try exact CH'; unfold FMT_D, STDOUT_BUF; lia
             | |- bytes_at _ _ (sh _) _ => apply stksh_bytes; exact SH2
             | |- stdout_at _ _ => exact SOUT2
             | |- fd_lookup _ _ = _ => rewrite FDS2, FDSq; apply fds_std_1
             | |- (exists g, ro_cells _ _ SSP_GUARD _) => exact (mc_canary _ _ MC2)
             | |- ro_cells _ _ SSP_GOT _ => exact GOT2
             | |- stk _ _ _ _ => ulit; exact ST2
             | |- ?T [] => exact KN
             | |- forall m', _ => intros mq mdq rq AIq MDq SOq msq POq; apply (KK mq mdq rq AIq MDq SOq msq);
                                  rewrite ?unsigned_lit in POq by (unfold SPF, STK_LO in *; lia); exact POq
             | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold VPRINTF_ICPT_STACK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
             end.
      - pose proof VPF2 as VP2. unfold vprintf_next_stmt in VP2. cbv zeta in VP2.
        eapply VP2 with (va := SPF usp + -80 + -56) (lo := STK_LO usp) (p := zero_lines i'); clear VP2.
        all: lazymatch goal with
             | |- ainv _ _ _ => exact AINV2
             | |- mem_inv _ _ => exact MI2
             | |- @eq word _ _ => reflexivity
             | |- bytes_at _ _ (SPF usp + -80 + -56) _ => replace (SPF usp + -80 + -56) with (SPF usp + -80 + -80 + Z.of_nat 24) by lia; exact VA0
             | |- forall v', consts_hold LPA v' -> _ => intros v' CH'; split; [apply rodata_range_ok| apply bss_range_ok]; try exact CH'; unfold FMT_D, STDOUT_BUF; lia
             | |- bytes_at _ _ (sh _) _ => apply stksh_bytes; exact SH2
             | |- stdout_at _ _ => exact SOUT2
             | |- (length _ <= 6)%nat => rewrite zero_lines_length; lia
             | |- fd_lookup _ _ = _ => rewrite FDS2, FDSq; apply fds_std_1
             | |- (exists g, ro_cells _ _ SSP_GUARD _) => exact (mc_canary _ _ MC2)
             | |- ro_cells _ _ SSP_GOT _ => exact GOT2
             | |- stk _ _ _ _ => ulit; exact ST2
             | |- forall m', _ => rewrite zero_lines_snoc; intros mq mdq rq AIq MDq SOq msq POq; apply (KK mq mdq rq AIq MDq SOq msq);
                                  rewrite ?unsigned_lit in POq by (unfold SPF, STK_LO in *; lia); exact POq
             | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold VPRINTF_ICPT_STACK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
             end. }
    apply (VP FIN); [destruct i; reflexivity| unfold FIN; apply t_emit_has_nil|].
    clear VP.
    (intros m3 md3 r AINV3; (first [ intro dR_42; dand3 dR_42 as FS3 FDS3 HH3 | intros (FS3 & FDS3 & HH3) ]); intros SOUT3 ms' POST).
    (first [ dex14 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6; dand5 POST as -> MU3 WM3 MI3 ST3 | dand19 POST as w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 -> MU3 WM3 MI3 ST3 | destruct POST as (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & -> & MU3 & WM3 & MI3 & ST3) ]).
    replace (ret_pc (Z_to_bv 64 0x86c8c)) with (Z_to_bv 64 0x86c8c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (CC3 : ccells_x (aview A' m3) tid (sof_after (S i)) 1 0).
    { eapply (ccells_after_stdout (aview A' m2)); [exact CC2| | exact MU3| exact SOUT3]. unfold VPRINTF_ICPT_STACK, STK_LO, SPF in *. lia. }
    assert (AR3 : args_at usp argv envp (aview A' m3)).
    { apply (args_at_agree usp argv envp (aview A' m2)); [| exact AR2]. apply (agree_of_munch _ _ _ _ MU3).
      pose proof (aa_b0 _ _ _ _ AR2) as B0. pose proof (aa_b1 _ _ _ _ AR2) as B1.
      intros a Ha. unfold in_args, e_p1a in *. unfold e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, STDOUT_F, STDOUT_BUF, VPRINTF_ICPT_STACK, SPF, STK_LO in *. cbn [outside].
      destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [| | | specialize (B1 H2)]; (split; [lia| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia]). }
    assert (SH3 : forall a, in_stksh a -> aview A' m3 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite <- (SH2 a Ha). apply (MU3 (Z_to_bv 64 a)). unfold in_stksh, STKSH_LO, STKSH_HI, sh, kShadowOffset in Ha; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). rewrite unsigned_lit by lia.
      unfold STDOUT_F, STDOUT_BUF, VPRINTF_ICPT_STACK, SPF, STK_LO in *. cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia. }
    (* [comment removed for export] *)
    assert (MFR2 : rw_cells rsegs (aview A' m2) (SPF usp) MFRv).
    { eapply (rw_cells_transport rsegs); [exact (tv_mfr _ _ _ _ _ _ _ TV')| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add MFR]. unfold TR_INCB, SPF in *. lia. }
    assert (TFR2 : rw_cells rsegs (aview A' m2) (SPF usp + -80) (TFRv j0)).
    { eapply (rw_cells_transport rsegs); [exact (tv_tfr _ _ _ _ _ _ _ TV')| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add TFRv TFR]. unfold TR_INCB, SPF in *. lia. }
    assert (MFR3 : rw_cells rsegs (aview A' m3) (SPF usp) MFRv).
    { eapply (rw_cells_transport rsegs); [exact MFR2| exact MU3| exact WM3|]. unfold STDOUT_F, STDOUT_BUF, VPRINTF_ICPT_STACK, SPF in *. cbn. lia. }
    assert (TFR3 : rw_cells rsegs (aview A' m3) (SPF usp + -80) (TFRv j0)).
    { eapply (rw_cells_transport rsegs); [exact TFR2| exact MU3| exact WM3|]. unfold STDOUT_F, STDOUT_BUF, VPRINTF_ICPT_STACK, SPF in *. cbn. lia. }
    lazymatch type of EFR2 with rw_cells _ _ _ ?cs => assert (EFR3 : rw_cells rsegs (aview A' m3) (SPF usp + -80 + -80) cs) end.
    { eapply (rw_cells_transport rsegs); [exact EFR2| exact MU3| exact WM3|]. unfold STDOUT_F, STDOUT_BUF, VPRINTF_ICPT_STACK, SPF in *. cbn. lia. }
    assert (PAY3 : pay_ok A' (aview A' m3) aligned owned nown).
    { destruct PAY2 as [X|(P1 & P2 & P3 & P4 & P5)]; [left; exact X| right]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      subst owned. (first [ pose proof ((as_live_ok LPA A' m' md' aligned plen AINV' P4)) as dR_21; dand5 dR_21 as _ _ ALO AHI _ | destruct (as_live_ok LPA A' m' md' aligned plen AINV' P4) as (_ & _ & ALO & AHI & _) ]). unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in ALO; cbn [cl_image_lo cl_image_hi LPA] in ALO. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      eapply (rw_cells_transport rsegs); [exact P5| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. unfold STDOUT_F, STDOUT_BUF, VPRINTF_ICPT_STACK, SPF, STK_LO in *. lia. }
    clear CC2 AR2 SH2 GOT2 MC2 SOUT2 VA0 EFR2 MFR2 TFR2 PAY' PAY2 MU WM CF.
    (* [comment removed for export] *)
    pose proof (munch_refl [(SPF usp + -80 + -80, SPF usp + -80 + -80 + 80)] (aview A' m3)) as MU. pose proof (wmono_refl rsegs (aview A' m3)) as WM.
    assert (CF : client_fpx (L:=LPA) A' (aview A' m3) [(SPF usp + -80 + -80, SPF usp + -80 + -80 + 80)]).
    { cbn. split; [| exact I]. left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
      replace (SPF usp + -80 + -80 + 80 - (SPF usp + -80 + -80)) with 80 by lia.
      destruct EFR3 as [[_ _] (W0 & W1 & W)]. intros q Hq E. apply (W q); [cbn; lia|]. unfold wa.
      rewrite pa_wview_overlay by (rewrite unsigned_lit by (unfold SPF, STK_LO in *; lia); unfold SPF, STK_LO in *; lia). exact E. }
    rewrite ?unsigned_lit in EFR3 by (unfold SPF, STK_LO in *; lia).
    replace (SPF usp + -80 + -56) with (SPF usp + -80 + -80 + 24) in EFR3 by lia.
    ago AINV3. fold_cl_segs.
    icall tr7_walk by (first [exact CEIL | exact MI3 | lia | ulit; first [exact ST3 | exact EFR3 | unfold STK_LO, SPF in *; lia]]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI4 end.
    lazymatch goal with H : stk _ _ _ (_ + 80) |- _ => rename H into ST4 end.
    astopx AINV3 MU WM CF. name_state m4 md4 AINV4.
    (first [ pose proof ((sbm_io md3 md4 SBM1)) as dR_22; dand3 dR_22 as FS4 FDS4 _ | pose proof (sbm_io md3 md4 SBM1) as (FS4 & FDS4 & _) ]).
    rewrite ?unsigned_lit in ST4 by (unfold SPF, STK_LO in *; lia).
    replace (SPF usp + -80 + -80 + 80) with (SPF usp + -80) in ST4 |- * by lia.
    assert (SO4 : stack_only usp [(SPF usp + -80 + -80, SPF usp + -80)]) by (apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]).
    assert (MU' : munch [(SPF usp + -80 + -80, SPF usp + -80)] (aview A' m3) (aview A' m4)).
    { replace (SPF usp + -80) with (SPF usp + -80 + -80 + 80) at 2 by lia. exact MU. }
    (first [ pose proof ((bundle_stack usp argv envp HCEIL _ _ _ tid (sof_after (S i)) 1 MU' SO4 U1 U2 CC3 AR3 SH3)) as dR_23; dand4 dR_23 as CC4 AR4 SH4 _ | destruct (bundle_stack usp argv envp HCEIL _ _ _ tid (sof_after (S i)) 1 MU' SO4 U1 U2 CC3 AR3 SH3) as (CC4 & AR4 & SH4 & _) ]).
    assert (TV4 : tview A' m4 md4 (sof_after (S i)) tid (TFRv j0) 0).
    { constructor; try assumption.
      all: try (rewrite FS4, FS3, FS2; exact FSq).
      all: try (rewrite FDS4, FDS3, FDS2; exact FDSq).
      all: eapply (rw_cells_transport rsegs); [eassumption| exact MU| exact WM|];
           cbn [disjoint_from cells_size csize Nat.add MFR TFRv TFR]; unfold SPF in *; lia. }
    assert (PAY4 : pay_ok A' (aview A' m4) aligned owned nown).
    { destruct PAY3 as [X|(P1 & P2 & P3 & P4 & P5)]; [left; exact X| right]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
      subst owned. (first [ pose proof ((as_live_ok LPA A' m' md' aligned plen AINV' P4)) as dR_24; dand5 dR_24 as _ _ ALO AHI _ | destruct (as_live_ok LPA A' m' md' aligned plen AINV' P4) as (_ & _ & ALO & AHI & _) ]). unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in ALO; cbn [cl_image_lo cl_image_hi LPA] in ALO. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      eapply (rw_cells_transport rsegs); [exact P5| exact MU| exact WM|]. cbn [disjoint_from cells_size csize Nat.add]. unfold SPF, STK_LO in *. lia. }
    replace (Z.of_nat (S jn) - 1) with (Z.of_nat jn) by lia.
    destruct (Z.eqb_spec (Z.of_nat jn) 0) as [J0|J0].
    - (* [comment removed for export] *)
      assert (EI : (S i) = Z.to_nat calls) by lia.
      unfold FIN. replace (Z.to_nat calls - 1)%nat with i by lia.
      change (zero_lines i) with (pending_of (sof_after (S i))).
      eapply (tr_tail A' m4 md4 (sof_after (S i)) j0 aligned owned nown); [exact TV4| exact (LVE _ _ LVb)| exact OB|].
      destruct PAY4 as [(P1 & P2 & P3 & _)|(P1 & P2 & P3 & P4 & P5)]; [left; split; assumption| right; rewrite P3; exact P4].
    - (* [comment removed for export] *)
      change FIN with (TI (S i)).
      apply (IH (S i) A' m4 md4 j0 aligned owned nown); try assumption; try lia.
      all: first [exact (LVE _ _ LVb) | rewrite LB'; exact LB | rewrite NL'; exact NL | intros ff; rewrite FRS'; apply FRS | nia].
  Qed.

  (* [comment removed for export] *)
  #[using="plen K10 k"] Lemma TI0_eq : t_eq (TI 0) TSUCC.
  Proof.
    unfold TI, FIN, TSUCC. pose proof calls_range as CAR.
    replace (if cnt then 0 else 0) with 0 by (destruct cnt; reflexivity).
    replace (Z.to_nat calls) with (S (Z.to_nat calls - 1)) at 2 by lia.
    change (zero_lines (S (Z.to_nat calls - 1))) with ([Z_to_bv 8 48; Z_to_bv 8 10] ++ zero_lines (Z.to_nat calls - 1)).
    apply t_emit_W_app.
  Qed.

  (* [comment removed for export] *)
  #[using="CL cnt inp calls d2 BNZ L6 LK K10 MAINRET VPF2 VPF1 LIB FREE1 MALLOC1 HCEIL"] Lemma trun_one : forall A m md (z0 z1 z2 x14 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
      BST A m md tid k b ->
      srealizes rsegs
        (mkCfg (MS (mkR (Z_to_bv 64 TRUN_RET) (Z_to_bv 64 (SPF usp)) gp (Z_to_bv 64 TPV) z0 z1 z2
                        (Z_to_bv 64 (b + 2)) (Z_to_bv 64 b)
                        (Z_to_bv 64 (b + 2)) (Z_to_bv 64 c) (Z_to_bv 64 (b + 2 + c + 4)) (Z_to_bv 64 plen)
                        x14 za5 za6 za7
                        (Z_to_bv 64 c) (Z_to_bv 64 (b + 2 + c + 4)) (Z_to_bv 64 plen)
                        (sxb d1) (Z_to_bv 64 READ_STAGE) (Z_to_bv 64 0) s8 s9 s10 s11 zt3 zt4 zt5 zt6)
                   F (Z_to_bv 64 0x86ac8) fc None m rom) md)
        (t_tail data fs).
  Proof.
    intros until zt6. intros BS.
    pose proof calls_range as CAR. pose proof (cap_range k K10) as CKR.
    pose proof plen_range as PLR.
    pose proof (cfgv_range (dbyte data 0) (dbyte data 1)) as CR. change (cfgv (dbyte data 0) (dbyte data 1)) with c in CR.
    pose proof inp_length as IL.
    pose proof BS as [FV0 _ LVb LVO LB NL TC SCC PCC FRS DAT _ _ GRW].   (* [comment removed for export] *)
    assert (LSB : forall l : list byte, (Z.of_nat (length l) <= plen)%Z -> 0 <= LIB_SECC (Z.of_nat (length l)) /\ 4 * LIB_SECC (Z.of_nat (length l)) <= a_seccred A - 1).
    { intros l Hl. unfold LIB_SECC. rewrite SECCRED0_eq in SCC.
      assert (0 <= Z.of_nat (length l) / 682 <= 98401) by (split; [apply Z.div_pos; lia|]; apply Z.div_le_upper_bound; [lia|]; pose proof (cap_range 10 ltac:(lia)); unfold cap in *; lia).   (* [comment removed for export] *)
      lia. }
    (* [comment removed for export] *)
    assert (LPB : forall l : list byte, (Z.of_nat (length l) <= plen)%Z -> 0 <= LIB_PRIM (Z.of_nat (length l)) /\ 4 * LIB_PRIM (Z.of_nat (length l)) <= a_primcred A - 65536).
    { intros l Hl. unfold LIB_PRIM. rewrite PCC, PRIMCRED0_eq. pose proof (cap_range 10 ltac:(lia)). unfold cap in *. lia. }
    (first [ pose proof ((fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)) as dR_25; dand4 dR_25 as U1 U2 U3 U4 | pose proof (fv_usp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as (U1 & U2 & U3 & U4) ]). pose proof U1 as U1'. unfold sp_window_lo in U1'.
    pose proof (fv_ceil _ HCEIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0) as CEIL.
    pose proof FV0 as [AINV MI FS FDS CC AR SH ST FR].
    assert (SPFV : SPF usp = usp - 128) by reflexivity.
    (first [ pose proof ((as_live_ok LPA A m md b (cap k) AINV LVb)) as dR_26; dand7 dR_26 as _ BAL BLO BHI _ BMP _ | destruct (as_live_ok LPA A m md b (cap k) AINV LVb) as (_ & BAL & BLO & BHI & _ & BMP & _) ]).
    rename BLO into BAPP. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    assert (BLO : 0x60a000 <= b).
    { pose proof (cap_range k K10) as CKR'. clear - BAPP CKR'. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BAPP; cbn [cl_image_lo cl_image_hi LPA] in BAPP. lia. }
    rewrite t_tail_eq.
    (* [comment removed for export] *)
    (first [ pose proof ((rwCB_elim _ _ _ _ DAT)) as dR_27; dand3 dR_27 as DLEN DB _ | destruct (rwCB_elim _ _ _ _ DAT) as (DLEN & DB & _) ]).
    (first [ pose proof (CC) as dR_28; dand4 dR_28 as MC0 _ _ TRC0 | pose proof CC as (MC0 & _ & _ & TRC0) ]).
    (* [comment removed for export] *)
    pose proof TRC0 as (_ & TRC & INCB0 & SLT0 & BF10 & BA10).
    pose proof (mc_fin _ _ MC0) as FIN0. pose proof (mc_alock _ _ MC0) as ALK0. pose proof (mc_head _ _ MC0) as HD0. pose proof (mc_nlock _ _ MC0) as NLK0.
    change (rw_cells rsegs (aview A m) (ATEXIT + 8) [C4 (Z_to_bv 64 1)]) in SLT0.
    change (rw_cells rsegs (aview A m) (ATEXIT + 40) [C8 (Z_to_bv 64 0)]) in BF10.
    change (rw_cells rsegs (aview A m) (ATEXIT + 296) [C8 (Z_to_bv 64 0)]) in BA10.
    assert (GOTW : ro_cells rsegs (aview A m) GOT_WEAKINIT [C8 (Z_to_bv 64 0)]).
    { apply ro_C8_of_bytes. apply (consts_lookup _ GOT_WEAKINIT _ (consts_hold_ainv LPA A m md AINV)). vm_compute. reflexivity. }
    pose proof (munch_refl [(SPF usp + -128, SPF usp); (TR_INITIALIZED, TR_INITIALIZED + 1);
                            (ATEXIT + 8, ATEXIT + 12); (ATEXIT + 40, ATEXIT + 48); (ATEXIT + 296, ATEXIT + 304)] (aview A m)) as MU.
    pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (CF : client_fpx (L:=LPA) A (aview A m) [(SPF usp + -128, SPF usp); (TR_INITIALIZED, TR_INITIALIZED + 1);
                            (ATEXIT + 8, ATEXIT + 12); (ATEXIT + 40, ATEXIT + 48); (ATEXIT + 296, ATEXIT + 304)]).
    { cbn. split; [| split; [| split; [| split; [| split; [| exact I]]]]].
      - left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
        replace (SPF usp - (SPF usp + -128)) with 128 by lia.
        eapply (stk_mapped (L:=LPA)); [exact ST | exact CEIL | unfold STK_LO, SPF in *; lia | lia].
      - right. unfold TR_INITIALIZED. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia.
      - right. unfold ATEXIT. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia.
      - right. unfold ATEXIT. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia.
      - right. unfold ATEXIT. split; [cbn; lia|]. split; [cbn; lia|]. intros a Ha. cbn [cl_static cl_shared LPA]. unfold pa_static, pa_shared. lia. }
    ago AINV. fold_cl_segs.
    icall (tr1_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc (STK_LO usp) CEIL b c (b + 2 + c + 4) plen data (aview A m))
      by (first [exact CEIL | exact MI | exact DB | exact TRC | exact GOTW | exact FIN0 | exact ALK0 | exact SLT0 | exact HD0 | exact BF10 | exact BA10 | exact NLK0 | lia
                | ulit; first [exact ST | rewrite ?alloc_ceiling_val in *; unfold STK_LO, SPF in *; lia]]).
    lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
    lazymatch goal with H : stk _ _ _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : rw_cells _ _ _ (TFR ?j _ _ _ _ _ _ _ _ _) |- _ => rename H into TFR1; rename j into j0 end.
    lazymatch goal with H : rw_cells _ _ TR_INITIALIZED [C1 (Z_to_bv 8 1)] |- _ => rename H into TRC1 end.
    lazymatch goal with H : rw_cells _ _ (ATEXIT + 8) [C4 (Z_to_bv 64 2)] |- _ => rename H into SLT1 end.
    lazymatch goal with H : rw_cells _ _ (ATEXIT + 40) _ |- _ => rename H into BF11 end.
    lazymatch goal with H : rw_cells _ _ (ATEXIT + 296) _ |- _ => rename H into BA11 end.
    change (if c =? 0 then 1 else bv_unsigned (nth 2 data (Z_to_bv 8 0)) mod 4 + 1) with calls.
    astopx AINV MU WM CF. name_state m1 md1 AINV1.
    (first [ pose proof ((sbm_io md md1 SBM)) as dR_29; dand3 dR_29 as FS1 FDS1 _ | pose proof (sbm_io md md1 SBM) as (FS1 & FDS1 & _) ]).
    (* [comment removed for export] *)
    assert (CC1 : ccells (aview A m1) tid SO_pristine 1).
    { eapply (ccells_set_tr1 (aview A m) (aview A m1) tid SO_pristine (SPF usp + -128) (SPF usp)); [exact CC| unfold SPF, STK_LO in *; lia| exact MU| exact TRC1| exact SLT1| exact BF11| exact BA11]. }
    assert (AR1 : args_at usp argv envp (aview A m1)).
    { apply (args_at_agree usp argv envp (aview A m)); [| exact AR]. apply (agree_of_munch _ _ _ _ MU).
      pose proof (aa_b0 _ _ _ _ AR) as B0. pose proof (aa_b1 _ _ _ _ AR) as B1.
      intros a Ha. unfold in_args, e_p1a in *. unfold e_p0a, e_L0, e_L1, e_argc, e_envc, e_span, TR_INITIALIZED, ATEXIT, SPF, STK_LO in *. cbn [outside].
      destruct Ha as [R|[[_ R]|[R|[H2 R]]]]; [| | | specialize (B1 H2)]; (split; [lia| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia]). }
    assert (SH1 : forall a, in_stksh a -> aview A m1 (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite <- (SH a Ha). apply (MU (Z_to_bv 64 a)). unfold in_stksh, STKSH_LO, STKSH_HI, sh, kShadowOffset in Ha; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). rewrite unsigned_lit by lia.
      unfold TR_INITIALIZED, ATEXIT, SPF, STK_LO in *. cbn [outside]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I; lia. }
    assert (MFR1 : rw_cells rsegs (aview A m1) (SPF usp) MFRv).
    { eapply (rw_cells_transport rsegs); [exact (fv_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FV0)| exact MU| exact WM|].
      cbn [disjoint_from cells_size csize Nat.add MFR]. unfold TR_INITIALIZED, ATEXIT, SPF in *. lia. }
    assert (TV1 : tview A m1 md1 SO_pristine tid (TFRv j0) 0).
    { constructor; try assumption; [rewrite FS1; exact FS| rewrite FDS1; exact FDS]. }
    assert (DAT1 : rw_cells rsegs (aview A m1) b [CB (Z.to_nat L) data]).
    { eapply (rw_cells_transport rsegs); [exact (bs_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS)| exact MU| exact WM|].
      cbn [disjoint_from cells_size csize Nat.add]. unfold TR_INITIALIZED, ATEXIT, SPF, STK_LO in *. lia. }
    clear CC AR SH MU WM CF TRC1 MC0.
    pose proof TV1 as [_ _ FS1q FDS1q _ _ SH1' _ _ _]. clear SH1'.
    fold_cl_segs.
    destruct (Z.eqb_spec plen 0) as [P0|P0].
    - (* [comment removed for export] *)
      pose proof (munch_refl [] (aview A m1)) as MU. pose proof (wmono_refl rsegs (aview A m1)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m1) []) by exact I.
      ago AINV1. fold_cl_segs.
      icall tr2a_walk by (exact MI1).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
      astopx AINV1 MU WM CF. name_state m2 md2 AINV2.
      (first [ pose proof ((sbm_io md1 md2 SBM0)) as dR_30; dand3 dR_30 as FS2 FDS2 _ | pose proof (sbm_io md1 md2 SBM0) as (FS2 & FDS2 & _) ]).
      assert (TV2 : tview A m2 md2 SO_pristine tid (TFRv j0) 0).
      { eapply (tview_stack A m1 md1); try eassumption; try reflexivity.
        all: first [rewrite FS2; exact FS1q | rewrite FDS2; exact FDS1q | apply stack_only_nil | exact I]. }
      eapply srz_conseq; [| exact TI0_eq].
      replace (Z_to_bv 64 calls) with (Z_to_bv 64 (Z.of_nat (Z.to_nat calls))) by (f_equal; lia).
      apply (tr_loop (Z.to_nat calls) 0%nat A m2 md2 j0 TR_EMPTY 0 0); try assumption; try lia; try reflexivity.
      all: first [left; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; exact P0 | unfold TR_EMPTY; lia | rewrite LB; lia
                 | lazymatch goal with |- _ * LIB_PRIM _ <= _ => idtac end;   (* [comment removed for export] *)
                   destruct (LPB (if plen =? 0 then [] else inp) ltac:(destruct (plen =? 0); [cbn; lia| rewrite inp_length; lia])) as [LP0 LP1]; nia
                 | destruct (LSB (if plen =? 0 then [] else inp) ltac:(destruct (plen =? 0); [cbn; lia| rewrite inp_length; lia])) as [LS0 LS1]; nia].
    - (* [comment removed for export] *)
      pose proof (munch_refl [] (aview A m1)) as MU. pose proof (wmono_refl rsegs (aview A m1)) as WM.
      assert (CF : client_fpx (L:=LPA) A (aview A m1) []) by exact I.
      ago AINV1. fold_cl_segs.
      icall tr2b_walk by (exact MI1).
      lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
      astopx AINV1 MU WM CF. name_state m2 md2 AINV2.
      (first [ pose proof ((sbm_io md1 md2 SBM0)) as dR_31; dand3 dR_31 as FS2 FDS2 _ | pose proof (sbm_io md1 md2 SBM0) as (FS2 & FDS2 & _) ]).
      lazymatch goal with H : stk _ (aview A m2) _ _ |- _ => rename H into ST2 end.
      assert (TV2 : tview A m2 md2 SO_pristine tid (TFRv j0) 0).
      { eapply (tview_stack A m1 md1); try eassumption; try reflexivity.
        all: first [rewrite FS2; exact FS1q | rewrite FDS2; exact FDS1q | apply stack_only_nil | exact I]. }
      assert (DAT2 : rw_cells rsegs (aview A m2) b [CB (Z.to_nat L) data]).
      { first [exact DAT1 | eapply (rw_cells_transport rsegs); [exact DAT1| exact MU| exact WM| exact I]]. }
      clear MU WM CF DAT1. pose proof TV2 as [_ _ FS2q FDS2q CC2 AR2 SH2 _ MFR2 TFR2].
      eapply srz_conseq; [| exact TI0_eq].
      pose proof MALLOC1 as MA. unfold malloc1_stmt in MA. cbv zeta in MA.
      eapply MA with (n := plen); clear MA.
      all: lazymatch goal with
           | |- ainv _ _ _ => exact AINV2
           | |- mem_inv _ _ => exact MI2
           | |- @eq word _ _ => reflexivity
           | |- 1 <= _ < REQ_MAX => unfold REQ_MAX; lia
           | |- _ <= NREQ_CAP => rewrite NREQ_CAP_eq; lia
           | |- a_livebytes _ + _ <= LIVE_MAX => rewrite LB, LIVE_MAX_eq; lia
           | |- a_nlive _ + 1 <= NLIVE_MAX => rewrite NL, NLIVE_MAX_eq; lia
           | |- _ < 16 -> _ => intros _; exact TC
           | |- kMaxPrimaryUser < _ -> _ => rewrite SECCRED0_eq in SCC; lia
           | |- prim_cost _ <= a_primcred _ => pose proof (proj1 (prim_cost_range plen ltac:(clear - PLR; lia))) as PCRM; rewrite PCC, PRIMCRED0_eq; clear - PCRM; lia   (* [comment removed for export] *)
           | |- In _ (cl_sites LPA) => rewrite unsigned_lit by lia; cbn; tauto
           | |- mapped _ _ _ => ulit; eapply (stk_mapped (L:=LPA)); [exact ST2| exact CEIL| unfold ASTK, STK_LO, SPF; lia| lia]
           | |- forall t0', _ => idtac
           | |- _ => ulit; rewrite ?alloc_ceiling_val; unfold ASTK, STK_LO, SPF in *; first [lia | Z.div_mod_to_equations; lia]
           end.
      + (* [comment removed for export] *)
        intros w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 wt3 wt4 wt5 wt6 r A' m' md' AINV' MI' MDF HLE FRS' RNZ LVA LV' LVO' LB' TC' NL' SC' PC' FRK.   (* [comment removed for export] *)
        (first [ pose proof ((amd_frame_io md2 md' MDF)) as dR_35; dand3 dR_35 as FS' FDS' _ | pose proof (amd_frame_io md2 md' MDF) as (FS' & FDS' & _) ]).
        replace (ret_pc (Z_to_bv 64 0x86b2c)) with (Z_to_bv 64 0x86b2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        (first [ pose proof ((as_live_ok LPA A' m' md' r plen AINV' LV')) as dR_36; dand7 dR_36 as _ RAL RLO RHI _ RMP _ | destruct (as_live_ok LPA A' m' md' r plen AINV' LV') as (_ & RAL & RLO & RHI & _ & RMP & _) ]).
        rename RLO into RAPP. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
        assert (RLO : 0x60a000 <= r).
        { destruct (Z_lt_le_dec 64512 plen) as [X|X].
          - clear - RAPP X. unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in RAPP; cbn [cl_image_lo cl_image_hi LPA] in RAPP. lia.
          - pose proof (as_live_primary_high LPA A' m' md' r plen AINV' LV' X) as RH. clear - RH. unfold kHighMemBeg in RH. lia. }
        assert (BR : b <> r) by (intros X; rewrite X in LVb; rewrite LVb in LVA; discriminate).
        assert (LVb' : a_live A' b = Some (cap k)) by (rewrite (LVO' b BR); exact LVb).
        pose proof (as_live_disjoint LPA A' m' md' r plen b (cap k) AINV' LV' LVb' (fun X => BR (eq_sym X))) as DISJ.
        apply (cframe_of_frame_ok LPA) in FRK. rewrite ?unsigned_lit in FRK by (unfold SPF, STK_LO in *; lia).
        assert (TV' : tview A' m' md' SO_pristine tid (TFRv j0) 0).
        { eapply (tview_ccall A A' m2 md2 m' md'); try eassumption; try reflexivity.
          all: first [rewrite FS'; exact FS2q | rewrite FDS'; exact FDS2q | apply heapish_nowhere | unfold ASTK, STK_LO, SPF; lia]. }
        assert (DAT' : rw_cells rsegs (aview A' m') b [CB (Z.to_nat L) data]).
        { apply (rw_cells_blk_cframe A A' m2 md2 _ _ _ _ _ b (cap k) _ _ AINV2 FRK LVb DAT2); [lia| cbn [cells_size csize Nat.add]; lia| | intros q Hq X; exact X].
          (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold ASTK, STK_LO, SPF in *. lia. }
        pose proof TV' as [_ _ FSq FDSq CC' AR' SH' ST' MFR' TFR'].
        (* [comment removed for export] *)
        (first [ pose proof ((rwCB_elim _ _ _ _ DAT')) as dR_37; dand3 dR_37 as DLEN' DB' _ | destruct (rwCB_elim _ _ _ _ DAT') as (DLEN' & DB' & _) ]).
        assert (SRC : bytes_at rsegs (aview A' m') (b + 2 + c + 4) inp).
        { pose proof DB' as X. rewrite <- (firstn_skipn (Z.to_nat (c + 6)) data) in X. apply bytes_at_app in X as [_ X].
          rewrite length_firstn in X. replace (b + Z.of_nat (Nat.min (Z.to_nat (c + 6)) (length data))) with (b + 2 + c + 4) in X by lia. exact X. }
        assert (ILN : length inp = Z.to_nat plen) by lia.
        destruct (mapped_rw_cells (aview A' m') r plen RMP ltac:(lia) ltac:(lia) ltac:(lia)) as [junkr RWR].
        pose proof (munch_refl [(r, r + plen); (SPF usp + -80 - MEMCPY_ICPT_STACK, SPF usp + -80)] (aview A' m')) as MU.
        pose proof (wmono_refl rsegs (aview A' m')) as WM.
        assert (CF : client_fpx (L:=LPA) A' (aview A' m') [(r, r + plen); (SPF usp + -80 - MEMCPY_ICPT_STACK, SPF usp + -80)]).
        { cbn. split; [| split; [| exact I]].
          - left. split; [| exact I]. right. left. exists r, plen. split; [exact LV'| lia].
          - left. split; [| exact I]. left. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia|]. split; [unfold SPF; lia|].
            replace (SPF usp + -80 - (SPF usp + -80 - MEMCPY_ICPT_STACK)) with MEMCPY_ICPT_STACK by lia.
            eapply (stk_mapped (L:=LPA)); [exact ST' | exact CEIL | unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia | lia]. }
        unfold MEMCPY_ICPT_STACK in MU, CF.   (* [comment removed for export] *)
        (first [ pose proof ((asan_memcpy_cells_of_consts _ (consts_hold_ainv LPA A' m' md' AINV'))) as dR_38; dand11 dR_38 as MCC1 MCC2 MCC3 MP1 MP2 MP3 MP4 MP5 MP6 MP7 MP8 | pose proof (asan_memcpy_cells_of_consts _ (consts_hold_ainv LPA A' m' md' AINV')) as (MCC1 & MCC2 & MCC3 & MP1 & MP2 & MP3 & MP4 & MP5 & MP6 & MP7 & MP8) ]).
        ago AINV'. fold_cl_segs.
        icall tr3b_walk by (first [exact MI' | lia]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MIa end.
        icall (memcpy_icpt_ok (Z_to_bv 64 0x86b40) (Z_to_bv 64 (SPF usp + -80)) gp (Z_to_bv 64 TPV) w0 w1 w2 (Z_to_bv 64 plen) (Z_to_bv 64 (b + 2 + c + 4))
                 (Z_to_bv 64 r) (Z_to_bv 64 (b + 2 + c + 4)) (Z_to_bv 64 plen) wa3 wa4 wa5 wa6 wa7
                 (Z_to_bv 64 r) (Z_to_bv 64 (b + 2)) (Z_to_bv 64 TR_INITIALIZED) (Z_to_bv 64 calls) (Z_to_bv 64 READ_STAGE)
                 (Z_to_bv 64 0) s8 s9 s10 s11 wt3 wt4 wt5 wt6 F fc _ inp junkr (STK_LO usp))
          by (rewrite ?unsigned_lit by lia;
              first [ exact SRC | exact ILN | exact RWR | exact MIa | lia
                    | lazymatch goal with |- asan_memcpy_cells _ => split_assum end
                    | ulit; assumption
                    | ulit; rewrite ?alloc_ceiling_val; unfold MEMCPY_ICPT_STACK, STK_LO, SPF in *; lia
                    | right; split;
                      (eapply (range_ok_high_munch _ (aview A' m'));
                       [ | eassumption | lia | lia | (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
                         | apply Forall_cons; [cbn [fst snd]; clear - RAPP PLR; unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in RAPP; cbn [cl_image_lo cl_image_hi LPA] in RAPP; unfold SHMAX; lia
                                             | apply Forall_cons; [cbn [fst snd]; clear - ACV U1' SPFV; unfold SHMAX, MEMCPY_ICPT_STACK, SPF, STK_LO in *; lia| apply Forall_nil]] ]);
                      [ eapply (live_range_ok A' m' md' b (cap k)) | eapply (live_range_ok A' m' md' r plen) ]; try eassumption; lia ]).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MIb end.
        lazymatch goal with H : rw_cells _ _ r [CB _ inp] |- _ => rename H into RDAT end.
        icall tr4_walk by (exact MIb).
        lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
        astopx AINV' MU WM CF. name_state m3 md3 AINV3.
        (first [ pose proof ((sbm_io md' md3 SBM1)) as dR_39; dand3 dR_39 as FS3 FDS3 _ | pose proof (sbm_io md' md3 SBM1) as (FS3 & FDS3 & _) ]).
        lazymatch goal with H : stk _ (aview A' m3) _ _ |- _ => rename H into ST3 end.
        assert (TV3 : tview A' m3 md3 SO_pristine tid (TFRv j0) 0).
        { eapply (tview_stack A' m' md'); try eassumption; try reflexivity.
          all: first [rewrite FS3; exact FSq | rewrite FDS3; exact FDSq
                     | apply (stack_only_cons_heap usp HCEIL); [eapply app_range_sub; [exact RAPP| lia| lia| lia]|];
                       unfold MEMCPY_ICPT_STACK; apply stack_only_cons; [unfold SPF, STK_LO; lia| unfold SPF; lia| apply stack_only_nil]
                     | unfold MEMCPY_ICPT_STACK, SPF; cbn; lia]. }
        replace (Z_to_bv 64 calls) with (Z_to_bv 64 (Z.of_nat (Z.to_nat calls))) by (f_equal; lia).
        apply (tr_loop (Z.to_nat calls) 0%nat A' m3 md3 j0 r r plen); try assumption; try lia; try reflexivity.
        (* [comment removed for export] *)
        all: lazymatch goal with
             | |- pay_ok _ _ _ _ _ => right; split; [clear - PLR P0; lia|]; split; [reflexivity|]; split; [reflexivity|]; split; [exact LV'| exact RDAT]
             | |- forall ff : Z, a_frame _ ff = None => intros ff; rewrite FRS'; apply FRS
             | |- _ * LIB_SECC _ <= a_seccred _ =>
                 destruct (LSB (if plen =? 0 then [] else inp) ltac:(destruct (plen =? 0); [cbn; clear - PLR; lia| rewrite inp_length; clear; lia])) as [LS0 LS1];
                 rewrite SC'; destruct (Z.ltb kMaxPrimaryUser plen); clear - CAR LS0 LS1; nia
             | |- _ * LIB_PRIM _ <= a_primcred _ =>   (* [comment removed for export] *)
                 destruct (LPB (if plen =? 0 then [] else inp) ltac:(destruct (plen =? 0); [cbn; clear - PLR; lia| rewrite inp_length; clear; lia])) as [LP0 LP1];
                 pose proof (proj1 (prim_cost_range plen ltac:(clear - PLR; lia))) as PCRM;
                 rewrite PC'; clear - CAR LP0 LP1 PCRM; nia
             | |- _ => first [ intros X; exact (BR (eq_sym X)) | rewrite LB', LB; lia | rewrite NL', NL; lia ]
             end.
  Qed.
  End Run.

  #[using="MAINRET VPF2 VPF1 LIB FREE1 MALLOC1 HCEIL"] Theorem trun_ok : trun_stmt usp argv envp fs e0 e1 e2 e3 e4 e5 e6 e7 j8 data gp s8 s9 s10 s11 F fc.
  Proof.
    unfold trun_stmt. intros A m md tid k b z0 z1 z2 x14 za5 za6 za7 zt3 zt4 zt5 zt6 BS L6 CL.
    exact (trun_one k b tid (bs_k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS) (bs_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS)
             L6 (bs_bnz _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ BS) CL A m md z0 z1 z2 x14 za5 za6 za7 zt3 zt4 zt5 zt6 BS).
  Qed.
End TargetRun.
End DA_Tfuf.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes.DA_Myrk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ejgo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_FKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Tails OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Ouhu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_M0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Loop OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_File.DA_M9wy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_File.DA_Tfuf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Section File.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)
  Variable usp : Z.
  Hypothesis HCEIL : alloc_ceiling = usp - 0x800000.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.
  Hypothesis Hva : valid_argv argv.
  Hypothesis MALLOC1 : malloc1_stmt.   (* [comment removed for export] *)
  Hypothesis FREE1 : free1_stmt.
  Hypothesis LIB : alib_call_ok.
  Hypothesis VPF1 : vprintf_first_stmt.
  Hypothesis VPF2 : vprintf_next_stmt.
  Hypothesis FPRINTF : fprintf_diag_stmt.
  Hypothesis FWRITE : fwrite_diag_stmt.
  Hypothesis EXIT : exit_spec_stmt.
  #[local] Notation rom := (seg_rom rsegs).
  #[local] Notation p1a := (e_p1a usp argv envp).

  (* [comment removed for export] *)
  Lemma rwCB_nil : forall (v : word -> option byte) a, 0 <= a -> a <= 2^64 -> rw_cells rsegs v a [CB 0%nat []].
  Proof.
    intros v a A0 A1. apply rwCB_intro; [reflexivity| apply bytes_at_nil; lia|].
    split; [lia|]. split; [lia|]. intros i Hi. lia.
  Qed.

  Theorem file_ok : file_stmt usp argv envp fs.
  Proof.
    unfold file_stmt. intros until md. intros A a0s path data DI EA AV PNE PND PLEN DATA.
    pose proof DI as DI'. destruct DI' as [AINV MI FS FDS FRN ST SPC SH [tid CC] GOT AR].
    pose proof AR as [P0 P1 S0 S1 K0 K1 B0 B1 (U1 & U2 & U3 & U4)]. pose proof U1 as U1'. unfold sp_window_lo in U1'.
    assert (A2 : e_argc argv = 2) by (rewrite AV; reflexivity).
    assert (P1E : nth 1 argv [] = path) by (rewrite AV; reflexivity).
    assert (CEIL : alloc_ceiling <= STK_LO usp) by (unfold STK_LO; rewrite HCEIL; lia).
    (* [comment removed for export] *)
    rewrite <- P1E.
    apply (open_phase usp HCEIL argv envp fs Hva FPRINTF EXIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md A
             (FdFile (nth 1 argv []) (Z_to_bv 64 0)) _ DI A2);
      [rewrite P1E; lia| right; rewrite P1E; split; [exact PNE|]; split; [exact PND|];
                         pose proof Hva as (_ & _ & _ & _ & APATH); rewrite AV in APATH; pose proof (Forall_inv APATH) as [PS PD];
                         split; [exact PD|]; split; [exact PS|]; split; [exists data; exact DATA| reflexivity]|].
    intros m2 md2 tid2 j8 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 AINV2 MI2 FS2 FDS2 CC2 AR2 SH2 ST2 FR2.
    rewrite P1E in FDS2.
    assert (FV2 : fview usp argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 A m2 md2 (fds3 (FdFile path (Z_to_bv 64 0))) SO_pristine 0 tid2)
      by (constructor; assumption).
    (* [comment removed for export] *)
    set (f := Z.to_nat (Z.of_nat (length data) + 12)).
    eapply srz_conseq.
    2:{ apply (lshape_opened data fs f 0%nat 0); [subst f; lia| lia| unfold cap; cbn; lia| lia| right; unfold cap; cbn; lia]. }
    (* [comment removed for export] *)
    apply (m0_phase usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 MALLOC1
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 md2 A (FdFile path (Z_to_bv 64 0)) tid2 _ FV2
             (ea_live _ _ _ EA) (ea_bytes _ _ _ EA) (ea_nlive _ _ _ EA) ltac:(rewrite (ea_tiny _ _ _ EA), TINYCRED0_eq; lia) (ea_secc _ _ _ EA) (ea_primc _ _ _ EA) (ea_frames _ _ _ EA)).   (* [comment removed for export] *)
    intros A' m3 md3 b zra z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 FV3 BNZ LV LVO LB NL TC SCC PCC FRS.   (* [comment removed for export] *)
    clear dependent m2. clear dependent md2. clear AINV MI FS FDS ST SH CC GOT AR.
    pose proof FV3 as [AINV3 MI3 FS3 FDS3 CC3 AR3 SH3 ST3 FR3].
    (first [ pose proof ((as_live_ok LPA A' m3 md3 b 65536 AINV3 LV)) as dR_1; dand5 dR_1 as _ BAL BLO BHI _ | destruct (as_live_ok LPA A' m3 md3 b 65536 AINV3 LV) as (_ & BAL & BLO & BHI & _) ]).
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    (* [comment removed for export] *)
    assert (C0 : cap 0 = 65536) by reflexivity.
    rewrite <- C0.
    apply (read_loop usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 path data gp s8 s9 s10 s11 F fc
             MALLOC1 FREE1 FPRINTF EXIT DATA
             (body_ok usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 path data gp s8 s9 s10 s11 F fc FREE1 FWRITE EXIT
                (trun_ok usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 data gp s8 s9 s10 s11 F fc MALLOC1 FREE1 LIB VPF1 VPF2
                   (mainret_ok usp HCEIL argv envp fs s0 s1 s2 s3 s4 s5 s6 s7 j8 gp s8 s9 s10 s11 F fc FREE1 EXIT)))
             f A' m3 md3 tid2 0%nat 0 b); [| unfold cap; cbn; lia| subst f; lia].
    constructor; try assumption; rewrite ?C0; try assumption; try lia.
    - cbn [Z.to_nat firstn]. apply rwCB_nil; [clear - BLO; unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in BLO; cbn [cl_image_lo cl_image_hi LPA] in BLO; lia| lia].
  Qed.
End File.
