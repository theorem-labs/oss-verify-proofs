(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_1c000_1d000.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFTow PFSnw PFFwx PFStr PFCore PFInv PFCoreTop.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Ltac indec := apply in_regs_dec; reflexivity.

(* [comment removed for export] *)
Section GD_1.
  Context {RL : Reloc}.
Record VFc (m : word -> option byte) (sp0 : Z) : Prop := VFC {
  Vf_flags : rdn SEGS m (Z_to_bv 64 (sp0 - 2400)) 4 = Some (W4 0);
  Vf_write : rdn SEGS m (Z_to_bv 64 (sp0 - 2328)) 8 = Some (X8 (rl dF_1c80c 0x1c80c));      (* [comment removed for export] *)
  Vf_buf   : rdn SEGS m (Z_to_bv 64 (sp0 - 2312)) 8 = Some (W8 (sp0 - 2145));  (* [comment removed for export] *)
  Vf_bsz   : rdn SEGS m (Z_to_bv 64 (sp0 - 2304)) 8 = Some (W8 0);
  Vf_mode  : rdn SEGS m (Z_to_bv 64 (sp0 - 2264)) 4 = Some (W4 0);
  Vf_lock  : rdn SEGS m (Z_to_bv 64 (sp0 - 2260)) 4 = Some (W4 4294967295);
  Vf_lbf   : rdn SEGS m (Z_to_bv 64 (sp0 - 2256)) 4 = Some (W4 4294967295);
  Vf_ck    : rdn SEGS m (Z_to_bv 64 (sp0 - 2248)) 8 = Some (W8 (sp0 - 2168)) }.
End GD_1.

(* [comment removed for export] *)
Section GD_2.
  Context {RL : Reloc}.
Definition vfp_regions (sp0 : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 3376), 1224%Z); (Z_to_bv 64 (sp0 - 2080), 2000%Z)].
End GD_2.

(* [comment removed for export] *)
Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.
End VP1.
Section VP2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma rdn_w4_byte0 : forall segs m (a : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 (Z_to_bv 64 0))) a 1%nat = Some [Z_to_bv 8 0].
Proof.
  intros segs m a Hnw. rewrite (rdn_firstn segs _ 4%nat a (word_to_le_bytes 4 (Z_to_bv 64 0)) 1%nat).
  - reflexivity.
  - apply rdn_wbytes_hit4. exact Hnw.
  - lia.
Qed.
End VP2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rdn_solve_w :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b ?n = _ =>
      tryif constr_eq a b then
        lazymatch n with
        | 8%nat => apply rdn_wbytes_hit8; zsimp; lia
        | 4%nat => apply rdn_wbytes_hit4; u_norm; lia
        | 1%nat => apply rdn_w4_byte0; u_norm; lia
        | _ => first [ apply rdn_wbytes_hit8; zsimp; lia | apply rdn_wbytes_hit4; u_norm; lia | apply rdn_w4_byte0; u_norm; lia ]
        end
      else (rdn_peel1; rdn_solve_w)
  | |- _ => rdn_hyp
  end.

Section VFP.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Ltac sok := soks CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition vfpM1 (m : word -> option byte) (regs : bvmap 5 word) (ret : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp0 - 2408)) (X8 ret))
      (Z_to_bv 64 (sp0 - 2416)) (X8 (getr regs 8)))
      (Z_to_bv 64 (sp0 - 2424)) (X8 (getr regs 9)))
      (Z_to_bv 64 (sp0 - 2432)) (X8 (getr regs 18)))
      (Z_to_bv 64 (sp0 - 2440)) (X8 (getr regs 19)))
      (Z_to_bv 64 (sp0 - 2448)) (X8 (getr regs 20)))
      (Z_to_bv 64 (sp0 - 2456)) (X8 (getr regs 21)))
      (Z_to_bv 64 (sp0 - 2464)) (W8 cv))                 (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2760)) (W8 (sp0 - 56)))         (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2472)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2504)) (W8 0))
      (Z_to_bv 64 (sp0 - 2496)) (W8 0))
      (Z_to_bv 64 (sp0 - 2488)) (W8 0))
      (Z_to_bv 64 (sp0 - 2480)) (W8 0))
      (Z_to_bv 64 (sp0 - 2768)) (W8 (sp0 - 56)).         (* [comment removed for export] *)

  Lemma vfp_seg_a : forall m regs (ret : word) (fa : Z),
    FRM sp0 mem0 m ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2400) ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2400) -> getr regs 11 = Z_to_bv 64 fa -> getr regs 12 = Z_to_bv 64 (sp0 - 56) ->
    exists r,
      msteps SEGS (mkst regs (rl dF_17dbc 0x17dbc) m rom) (mkst r (rl dF_17f6c 0x17f6c) (vfpM1 m regs ret) rom)
      /\ getr r 1 = (rl dF_17dbc 0x17e24) /\ getr r 2 = Z_to_bv 64 (sp0 - 2768) /\ getr r 10 = Z_to_bv 64 0
      /\ getr r 11 = Z_to_bv 64 fa /\ getr r 12 = Z_to_bv 64 (sp0 - 2768)
      /\ getr r 8 = Z_to_bv 64 (sp0 - 2400) /\ getr r 9 = Z_to_bv 64 fa /\ getr r 18 = Z_to_bv 64 A_CANARY
      /\ (forall x : reg, In x [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x).
  Proof.
    intros m regs ret fa F H1 H2 H10 H11 H12.
    pose proof Hcsp as Hsp0. lay.
    pose proof (FRM_got sp0 mem0 cv CTX m F) as Rgot.
    pose proof (FRM_can sp0 mem0 cv CTX m F) as Rcan.
    pose proof (Ccv _ _ _ CTX) as Hcv. unfold A_CANARY_GOT, A_CANARY in *.
    eexists. split.
    - stepiv F_17dbc D_17dbc (Z_to_bv 64 (sp0 - 2768)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_17dc0 D_17dc0 (Z_to_bv 64 (sp0 - 2408)) ret ltac:(sok).            (* [comment removed for export] *)
      stepST F_17dc4 D_17dc4 (Z_to_bv 64 (sp0 - 2416)) (getr regs 8) ltac:(sok).  (* [comment removed for export] *)
      stepST F_17dc8 D_17dc8 (Z_to_bv 64 (sp0 - 2424)) (getr regs 9) ltac:(sok).  (* [comment removed for export] *)
      stepST F_17dcc D_17dcc (Z_to_bv 64 (sp0 - 2432)) (getr regs 18) ltac:(sok). (* [comment removed for export] *)
      stepST F_17dd0 D_17dd0 (Z_to_bv 64 (sp0 - 2440)) (getr regs 19) ltac:(sok). (* [comment removed for export] *)
      stepST F_17dd4 D_17dd4 (Z_to_bv 64 (sp0 - 2448)) (getr regs 20) ltac:(sok). (* [comment removed for export] *)
      stepST F_17dd8 D_17dd8 (Z_to_bv 64 (sp0 - 2456)) (getr regs 21) ltac:(sok). (* [comment removed for export] *)
      stepn F_17ddc D_17ddc.                                                      (* [comment removed for export] *)
      stepn F_17de0 D_17de0.                                                      (* [comment removed for export] *)
      stepn F_17de4 D_17de4.                                                      (* [comment removed for export] *)
      stepLD8 F_17de8 D_17de8 (rl dA_2f848 0x2f848).                              (* [comment removed for export] *)
      stepLD8 F_17dec D_17dec (Z_to_bv 64 cv).                                   (* [comment removed for export] *)
      stepST F_17df0 D_17df0 (Z_to_bv 64 (sp0 - 2464)) (Z_to_bv 64 cv) ltac:(sok).        (* [comment removed for export] *)
      stepST F_17df4 D_17df4 (Z_to_bv 64 (sp0 - 2760)) (Z_to_bv 64 (sp0 - 56)) ltac:(sok). (* [comment removed for export] *)
      stepST F_17df8 D_17df8 (Z_to_bv 64 (sp0 - 2472)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17dfc D_17dfc (Z_to_bv 64 (sp0 - 2504)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e00 D_17e00 (Z_to_bv 64 (sp0 - 2496)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e04 D_17e04 (Z_to_bv 64 (sp0 - 2488)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e08 D_17e08 (Z_to_bv 64 (sp0 - 2480)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e0c D_17e0c (Z_to_bv 64 (sp0 - 2768)) (Z_to_bv 64 (sp0 - 56)) ltac:(sok). (* [comment removed for export] *)
      stepn F_17e10 D_17e10.                                                      (* [comment removed for export] *)
      stepiv F_17e14 D_17e14 (Z_to_bv 64 (sp0 - 2672)) ltac:(zval).             (* [comment removed for export] *)
      stepiv F_17e18 D_17e18 (Z_to_bv 64 (sp0 - 2504)) ltac:(zval).             (* [comment removed for export] *)
      stepn F_17e1c D_17e1c.                                                      (* [comment removed for export] *)
      stepn F_17e20 D_17e20.                                                      (* [comment removed for export] *)
      unfold vfpM1. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  Lemma vfpM1_frame : forall m regs ret, frame_mod m (vfpM1 m regs ret) [(Z_to_bv 64 (sp0 - 2768), 368%Z)].
  Proof.
    intros m regs ret. pose proof Hcsp as Hsp0. lay. unfold vfpM1.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition segbM (M : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp0 - 2400)) (W4 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2368)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2360)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2344)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2312)) (W8 (sp0 - 2752)))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2304)) (W8 80).                 (* [comment removed for export] *)

  Lemma vfp_seg_b : forall M r,
    FRM sp0 mem0 M -> VFc M sp0 ->
    getr r 2 = Z_to_bv 64 (sp0 - 2768) -> getr r 8 = Z_to_bv 64 (sp0 - 2400) -> getr r 10 = Z_to_bv 64 0 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17dbc 0x17e24) M rom) (mkst r' (rl dF_17aec 0x17aec) (segbM M) rom)
      /\ getr r' 1 = (rl dF_17dbc 0x17e98) /\ getr r' 2 = Z_to_bv 64 (sp0 - 2768) /\ getr r' 10 = Z_to_bv 64 (sp0 - 2400)
      /\ getr r' 19 = Z_to_bv 64 1 /\ getr r' 20 = Z_to_bv 64 (sp0 - 2145) /\ getr r' 21 = Z_to_bv 64 0
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r F VF R2 R8 R10. pose proof Hcsp as Hsp0. lay. destruct VF.
    eexists. split.
    - stepb_ft F_17e24 D_17e24 ltac:(cond_vm).                                  (* [comment removed for export] *)
      stepLD F_17e28 D_17e28 (W4 4294967295) (Z_to_bv 64 4294967295)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia). (* [comment removed for export] *)
      stepb_tk F_17e2c D_17e2c ltac:(cond_vm).                                  (* [comment removed for export] *)
      stepn F_17e48 D_17e48.                                                      (* [comment removed for export] *)
      stepLD F_17e4c D_17e4c (W4 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia). (* [comment removed for export] *)
      stepLD8 F_17e50 D_17e50 (Z_to_bv 64 0).                                    (* [comment removed for export] *)
      stepn F_17e54 D_17e54.                                                      (* [comment removed for export] *)
      stepST F_17e58 D_17e58 (Z_to_bv 64 (sp0 - 2400)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepb_tk F_17e5c D_17e5c ltac:(cond_vm).                                  (* [comment removed for export] *)
      stepLD8 F_17e70 D_17e70 (Z_to_bv 64 (sp0 - 2145)).                         (* [comment removed for export] *)
      stepiv F_17e74 D_17e74 (Z_to_bv 64 (sp0 - 2752)) ltac:(zval).             (* [comment removed for export] *)
      stepST F_17e78 D_17e78 (Z_to_bv 64 (sp0 - 2368)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e7c D_17e7c (Z_to_bv 64 (sp0 - 2360)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e80 D_17e80 (Z_to_bv 64 (sp0 - 2344)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17e84 D_17e84 (Z_to_bv 64 (sp0 - 2312)) (Z_to_bv 64 (sp0 - 2752)) ltac:(sok). (* [comment removed for export] *)
      stepn F_17e88 D_17e88.                                                      (* [comment removed for export] *)
      stepST F_17e8c D_17e8c (Z_to_bv 64 (sp0 - 2304)) (Z_to_bv 64 80) ltac:(sok).        (* [comment removed for export] *)
      stepn F_17e90 D_17e90.                                                      (* [comment removed for export] *)
      stepn F_17e94 D_17e94.                                                      (* [comment removed for export] *)
      unfold segbM. apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  Lemma segbM_frame : forall M, frame_mod M (segbM M) [(Z_to_bv 64 (sp0 - 2400), 140%Z)].
  Proof.
    intros M. pose proof Hcsp as Hsp0. lay. unfold segbM.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.

  (* [comment removed for export] *)
  Definition towM (M : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp0 - 2264)) (W4 18446744073709551615))   (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2344)) (W8 (sp0 - 2752)))             (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2392)) (W8 0))                        (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2384)) (W8 0))                        (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2368)) (W8 (sp0 - 2672)))             (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2360)) (W8 (sp0 - 2752)).             (* [comment removed for export] *)

  Lemma towM_eq : forall M, tow_mem M (sp0 - 2400) (sp0 - 2752) = towM M.
  Proof.
    intros M. unfold tow_mem, towM.
    replace (sp0 - 2400 + 136)%Z with (sp0 - 2264)%Z by lia.
    replace (sp0 - 2400 + 56)%Z with (sp0 - 2344)%Z by lia.
    replace (sp0 - 2400 + 8)%Z with (sp0 - 2392)%Z by lia.
    replace (sp0 - 2400 + 16)%Z with (sp0 - 2384)%Z by lia.
    replace (sp0 - 2400 + 32)%Z with (sp0 - 2368)%Z by lia.
    replace (sp0 - 2400 + 40)%Z with (sp0 - 2360)%Z by lia.
    replace (sp0 - 2752 + 80)%Z with (sp0 - 2672)%Z by lia.
    reflexivity.
  Qed.

  Lemma towM_frame : forall M, frame_mod M (towM M) [(Z_to_bv 64 (sp0 - 2400), 140%Z)].
  Proof.
    intros M. pose proof Hcsp as Hsp0. lay. unfold towM.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vfp_seg_c : forall M r,
    getr r 2 = Z_to_bv 64 (sp0 - 2768) -> getr r 10 = Z_to_bv 64 0 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17dbc 0x17e98) M rom) (mkst r' (rl dF_17f6c 0x17f6c) M rom)
      /\ getr r' 1 = (rl dF_17dbc 0x17ec4) /\ getr r' 2 = Z_to_bv 64 (sp0 - 2768)
      /\ getr r' 10 = getr r 8 /\ getr r' 11 = getr r 9 /\ getr r' 12 = Z_to_bv 64 (sp0 - 2768)
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r R2 R10. pose proof Hcsp as Hsp0. lay.
    eexists. split.
    - stepb_tk F_17e98 D_17e98 ltac:(cond_vm).                                  (* [comment removed for export] *)
      stepn F_17eac D_17eac.                                                      (* [comment removed for export] *)
      stepiv F_17eb0 D_17eb0 (Z_to_bv 64 (sp0 - 2672)) ltac:(zval).             (* [comment removed for export] *)
      stepiv F_17eb4 D_17eb4 (Z_to_bv 64 (sp0 - 2504)) ltac:(zval).             (* [comment removed for export] *)
      stepn F_17eb8 D_17eb8.                                                      (* [comment removed for export] *)
      stepn F_17ebc D_17ebc.                                                      (* [comment removed for export] *)
      stepn F_17ec0 D_17ec0.                                                      (* [comment removed for export] *)
      apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vfp_seg_d : forall M r,
    FILEc M sp0 ->
    getr r 2 = Z_to_bv 64 (sp0 - 2768) -> getr r 8 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 20 = Z_to_bv 64 (sp0 - 2145) -> getr r 21 = Z_to_bv 64 0 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17dbc 0x17ec4) M rom) (mkst r' (rl dF_1c80c 0x1c80c) M rom)
      /\ getr r' 1 = (rl dF_17dbc 0x17ee4) /\ getr r' 2 = Z_to_bv 64 (sp0 - 2768)
      /\ getr r' 10 = Z_to_bv 64 (sp0 - 2400) /\ getr r' 11 = Z_to_bv 64 0 /\ getr r' 12 = Z_to_bv 64 0
      /\ getr r' 21 = Z_to_bv 64 0
      /\ (forall x : reg, In x [3; 4; 8; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r FC R2 R8 R20 R21. pose proof Hcsp as Hsp0. lay. destruct FC.
    eexists. split.
    - stepn F_17ec4 D_17ec4.                                                      (* [comment removed for export] *)
      stepn F_17ec8 D_17ec8.                                                      (* [comment removed for export] *)
      stepb_ft F_17ecc D_17ecc ltac:(rwH; rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).   (* [comment removed for export] *)
      stepLD8 F_17ed0 D_17ed0 (rl dF_1c80c 0x1c80c).                              (* [comment removed for export] *)
      stepn F_17ed4 D_17ed4.                                                      (* [comment removed for export] *)
      stepn F_17ed8 D_17ed8.                                                      (* [comment removed for export] *)
      stepn F_17edc D_17edc.                                                      (* [comment removed for export] *)
      stepretK F_17ee0 D_17ee0 F_1c80c ltac:(rwH; bveq).                 (* [comment removed for export] *)
      apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | bveq] |]).
      intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition segeM (M : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp0 - 2368)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2360)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2344)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2312)) (W8 (sp0 - 2145)))       (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2304)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2400)) (W4 0).                  (* [comment removed for export] *)

  Lemma vfp_seg_e : forall M r regs (ret : word),
    FRM sp0 mem0 M -> ret_ok ret ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2360)) 8 = Some (W8 (sp0 - 2752)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2400)) 4 = Some (W4 0) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2464)) 8 = Some (W8 cv) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2408)) 8 = Some (X8 ret) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2416)) 8 = Some (X8 (getr regs 8)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2424)) 8 = Some (X8 (getr regs 9)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2432)) 8 = Some (X8 (getr regs 18)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2440)) 8 = Some (X8 (getr regs 19)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2448)) 8 = Some (X8 (getr regs 20)) ->
    rdn SEGS M (Z_to_bv 64 (sp0 - 2456)) 8 = Some (X8 (getr regs 21)) ->
    getr r 2 = Z_to_bv 64 (sp0 - 2768) -> getr r 8 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 18 = Z_to_bv 64 A_CANARY -> getr r 19 = Z_to_bv 64 1 ->
    getr r 20 = Z_to_bv 64 (sp0 - 2145) -> getr r 21 = Z_to_bv 64 0 ->
    exists r',
      msteps SEGS (mkst r (rl dF_17dbc 0x17ee4) M rom) (mkst r' ret (segeM M) rom)
      /\ getr r' 2 = Z_to_bv 64 (sp0 - 2400) /\ getr r' 1 = ret
      /\ (forall x : reg, In x [8; 9; 18; 19; 20; 21]%bv -> getr r' x = getr regs x)
      /\ (forall x : reg, In x [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr r x).
  Proof.
    intros M r regs ret F Hret Rwp Rfl Rcv Rra Rs0 Rs1 Rs2 Rs3 Rs4 Rs5 R2 R8 R18 R19 R20 R21.
    pose proof Hcsp as Hsp0. lay.
    pose proof (FRM_can sp0 mem0 cv CTX M F) as Rcan. pose proof (Ccv _ _ _ CTX) as Hcv. unfold A_CANARY in *.
    eexists. split.
    - stepLD8 F_17ee4 D_17ee4 (Z_to_bv 64 (sp0 - 2752)).                         (* [comment removed for export] *)
      stepST F_17ee8 D_17ee8 (Z_to_bv 64 (sp0 - 2368)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17eec D_17eec (Z_to_bv 64 (sp0 - 2360)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17ef0 D_17ef0 (Z_to_bv 64 (sp0 - 2344)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepST F_17ef4 D_17ef4 (Z_to_bv 64 (sp0 - 2312)) (Z_to_bv 64 (sp0 - 2145)) ltac:(sok). (* [comment removed for export] *)
      stepn F_17ef8 D_17ef8.                                                      (* [comment removed for export] *)
      stepn F_17efc D_17efc.                                                      (* [comment removed for export] *)
      stepn F_17f00 D_17f00.                                                      (* [comment removed for export] *)
      stepST F_17f04 D_17f04 (Z_to_bv 64 (sp0 - 2304)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepLD F_17f08 D_17f08 (W4 0) (Z_to_bv 64 0)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia). (* [comment removed for export] *)
      stepn F_17f0c D_17f0c.                                                      (* [comment removed for export] *)
      stepn F_17f10 D_17f10. rwH. vals_lit.                                       (* [comment removed for export] *)
      stepn F_17f14 D_17f14.                                                      (* [comment removed for export] *)
      stepn F_17f18 D_17f18.                                                      (* [comment removed for export] *)
      stepn F_17f1c D_17f1c.                                                      (* [comment removed for export] *)
      stepST F_17f20 D_17f20 (Z_to_bv 64 (sp0 - 2400)) (Z_to_bv 64 0) ltac:(sok).         (* [comment removed for export] *)
      stepb_tk F_17f24 D_17f24 ltac:(cond_vm).                                  (* [comment removed for export] *)
      stepLD8 F_17f38 D_17f38 (Z_to_bv 64 cv).                                   (* [comment removed for export] *)
      stepLD8 F_17f3c D_17f3c (Z_to_bv 64 cv).                                   (* [comment removed for export] *)
      stepb_ft F_17f40 D_17f40 ltac:(rwH; apply c_eq_refl).                      (* [comment removed for export] *)
      stepLD8 F_17f44 D_17f44 ret.                                                (* [comment removed for export] *)
      stepLD8 F_17f48 D_17f48 (getr regs 8).                                      (* [comment removed for export] *)
      stepLD8 F_17f4c D_17f4c (getr regs 9).                                      (* [comment removed for export] *)
      stepLD8 F_17f50 D_17f50 (getr regs 18).                                     (* [comment removed for export] *)
      stepLD8 F_17f54 D_17f54 (getr regs 19).                                     (* [comment removed for export] *)
      stepLD8 F_17f58 D_17f58 (getr regs 20).                                     (* [comment removed for export] *)
      stepLD8 F_17f5c D_17f5c (getr regs 21).                                     (* [comment removed for export] *)
      stepiv F_17f60 D_17f60 (Z_to_bv 64 (sp0 - 2400)) ltac:(zval).             (* [comment removed for export] *)
      stepret F_17f64 D_17f64 ret ltac:(reflexivity).                            (* [comment removed for export] *)
      unfold segeM. apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split.
      + intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
  Qed.

  Lemma segeM_frame : forall M, frame_mod M (segeM M) [(Z_to_bv 64 (sp0 - 2400), 140%Z)].
  Proof.
    intros M. pose proof Hcsp as Hsp0. lay. unfold segeM.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable va : Z -> word.                            (* [comment removed for export] *)
  Variables (nS : Z) (saddr slen : Z -> Z).
  Hypothesis SARGS : forall q, (0 <= q < nS)%Z ->
    va q = Z_to_bv 64 (saddr q) /\ rostr mem0 (saddr q) (slen q) /\ (slen q <= 200)%Z.
  Variables (fa : Z) (fbs : list Z).      (* [comment removed for export] *)
  Hypothesis FMT0 : forall i, (0 <= i < Z.of_nat (length fbs))%Z ->
    mem0 (Z_to_bv 64 (fa + i)) = None /\ seg_rom SEGS (Z_to_bv 64 (fa + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) fbs 0%Z)).
  Hypothesis FMTR : (IMG_LO <= fa /\ fa + Z.of_nat (length fbs) <= IMG_TOP)%Z.
  Hypothesis FBYTE : forall i, (0 <= i < Z.of_nat (length fbs))%Z -> (0 <= nth (Z.to_nat i) fbs 0%Z <= 255)%Z.
  Variable its : list fitem.
  Hypothesis ITS : flat its = fbs.
  Hypothesis WF : wf_items its = true.
  Hypothesis COK0 : convs_ok nS 0 (convs its).
  Hypothesis NC7 : (Z.of_nat (length (convs its)) <= 7)%Z.
  Hypothesis REM : (rem its + 56 <= INT_MAX)%Z.

  (* [comment removed for export] *)
  Ltac fkeep FM := rewrite (frame_mod_rdn SEGS _ _ _ _ _ FM);
    [ | intros i Hi; cbn [outside]; unfold in_rng; unorm; repeat split; lia | unorm; lia ].

  Theorem vfprintf_run : forall m regs (ret : word) (j : Z),
    ret_ok ret -> FRM sp0 mem0 m -> VFc m sp0 -> CKst m sp0 j ->
    (forall q, (0 <= q < 7)%Z -> VAslot m sp0 q (va q)) ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2400) ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2400) -> getr regs 11 = Z_to_bv 64 fa -> getr regs 12 = Z_to_bv 64 (sp0 - 56) ->
    getr regs 3 = g3 -> getr regs 4 = g4 ->
    exists r' m',
      msteps SEGS (mkst regs (rl dF_17dbc 0x17dbc) m rom) (mkst r' ret m' rom)
      /\ getr r' 2 = Z_to_bv 64 (sp0 - 2400)
      /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr regs x)
      /\ frame_mod m m' (vfp_regions sp0).
  Proof.
    intros m regs ret j Hret F VF CK VA H1 H2 H10 H11 H12 H3 H4. pose proof Hcsp as Hsp0.
    assert (SUBv : forall m1 m2 rs, FRM sp0 mem0 m1 -> frame_mod m1 m2 rs ->
              (forall a, outside a (vfp_regions sp0) -> outside a rs) -> FRM sp0 mem0 m2 /\ frame_mod m1 m2 (vfp_regions sp0)).
    { intros m1 m2 rs Fa Fb W. split.
      - eapply FRM_sub; [exact Fa | exact Fb |]. intros a Ho. apply W.
        unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia.
      - eapply frame_mod_weaken; [exact W | exact Fb]. }
    (* [comment removed for export] *)
    destruct (vfp_seg_a m regs ret fa F H1 H2 H10 H11 H12) as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & AK).
    pose proof (vfpM1_frame m regs ret) as FM1.
    set (M1 := vfpM1 m regs ret) in *.
    destruct (SUBv m M1 _ F FM1) as [F1 V1].
    { intros a Ho. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    (* [comment removed for export] *)
    assert (C64 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2464)) 8 = Some (W8 cv)) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C08 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2408)) 8 = Some (X8 ret)) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C16 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2416)) 8 = Some (X8 (getr regs 8))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C24 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2424)) 8 = Some (X8 (getr regs 9))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C32 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2432)) 8 = Some (X8 (getr regs 18))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C40 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2440)) 8 = Some (X8 (getr regs 19))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C48 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2448)) 8 = Some (X8 (getr regs 20))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (C56 : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2456)) 8 = Some (X8 (getr regs 21))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    assert (CAP : rdn SEGS M1 (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56))) by (subst M1; unfold vfpM1; lay; rdn_solve).
    clearbody M1.
    (* [comment removed for export] *)
    destruct (printf_core_p1 sp0 mem0 cv rom CTX g3 g4 nS fa fbs FMT0 FMTR its ITS WF COK0 NC7 REM M1 r1 (rl dF_17dbc 0x17e24)
                ltac:(rl_ret_ok) F1 A1 A2 A10 A11 A12
                ltac:(rewrite AK by indec; exact H3) ltac:(rewrite AK by indec; exact H4)) as (r2 & RUN2 & B2 & B10 & BK).
    pose proof (proM_frame sp0 mem0 cv CTX M1 r1 (rl dF_17dbc 0x17e24)) as FM2.
    set (M2 := proM sp0 cv M1 r1 (rl dF_17dbc 0x17e24)) in *. clearbody M2.
    destruct (SUBv M1 M2 _ F1 FM2) as [F2 V2].
    { intros a Ho. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (VF2 : VFc M2 sp0).
    { destruct VF. lay. split; fkeep FM2; fkeep FM1; assumption. }
    (* [comment removed for export] *)
    assert (B8 : getr r2 8 = Z_to_bv 64 (sp0 - 2400)) by (rewrite BK by indec; exact A8).
    destruct (vfp_seg_b M2 r2 F2 VF2 B2 B8 B10) as (r3 & RUN3 & C1 & C2 & C10 & C19 & C20 & C21 & CK3).
    pose proof (segbM_frame M2) as FM3a.
    destruct (SUBv M2 (segbM M2) _ F2 FM3a) as [F3a V3a].
    { intros a Ho. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    (* [comment removed for export] *)
    pose proof VF2 as [Vfl Vwr Vbuf Vbsz Vmode Vlock Vlbf Vck]. lay.
    assert (T1 : rdn SEGS (segbM M2) (Z_to_bv 64 (sp0 - 2400 + 136)) 4 = Some (W4 0)).
    { replace (sp0 - 2400 + 136)%Z with (sp0 - 2264)%Z by lia. unfold segbM. rdn_solve_w. }
    assert (T2 : rdn SEGS (segbM M2) (Z_to_bv 64 (sp0 - 2400)) 4 = Some (W4 0)) by (unfold segbM; rdn_solve_w).
    assert (T3 : rdn SEGS (segbM M2) (Z_to_bv 64 (sp0 - 2400 + 88)) 8 = Some (W8 (sp0 - 2752))).
    { replace (sp0 - 2400 + 88)%Z with (sp0 - 2312)%Z by lia. unfold segbM. rdn_solve_w. }
    assert (T4 : rdn SEGS (segbM M2) (Z_to_bv 64 (sp0 - 2400 + 96)) 8 = Some (W8 80)).
    { replace (sp0 - 2400 + 96)%Z with (sp0 - 2304)%Z by lia. unfold segbM. rdn_solve_w. }
    assert (SOK3 : store_ok SEGS (segbM M2) (Z_to_bv 64 (sp0 - 2400)) 232 = true) by (unfold segbM; sok).
    destruct (towrite_run (segbM M2) rom (sp0 - 2400) (sp0 - 2752) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                T1 T2 T3 T4 SOK3 r3 (rl dF_17dbc 0x17e98) ltac:(rl_ret_ok) C1 C10)
      as (r4 & RUN4 & K4 & D10).
    rewrite towM_eq in RUN4.
    pose proof (towM_frame (segbM M2)) as FM3b.
    destruct (SUBv (segbM M2) (towM (segbM M2)) _ F3a FM3b) as [F3 V3b].
    { intros a Ho. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    (* [comment removed for export] *)
    set (M3 := towM (segbM M2)) in *.
    assert (FC3 : FILEc M3 sp0).
    { subst M3. unfold towM, segbM. split; rdn_solve_w. }
    assert (FS3 : FILEst M3 sp0 0 j).
    { split; [|split; [|split; [|split]]].
      - rewrite Z.add_0_r. subst M3. unfold towM. rdn_solve_w.
      - subst M3. unfold towM. rdn_solve_w.
      - destruct CK as (K1 & K2 & K3). split; [|split; [|exact K3]];
          (fkeep FM3b; fkeep FM3a; fkeep FM2; fkeep FM1; assumption).
      - lia.
      - intros i Hi. lia. }
    assert (AP3 : rdn SEGS M3 (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56))).
    { fkeep FM3b. fkeep FM3a. fkeep FM2. exact CAP. }
    assert (VA3 : forall q, (0 <= q < 7)%Z -> VAslot M3 sp0 q (va q)).
    { intros q Hq. unfold VAslot. fkeep FM3b. fkeep FM3a. fkeep FM2. fkeep FM1. apply VA. exact Hq. }
    assert (FL3 : rdn SEGS M3 (Z_to_bv 64 (sp0 - 2400)) 4 = Some (W4 0)) by (subst M3; unfold towM; rdn_solve_w).
    clearbody M3.
    (* [comment removed for export] *)
    assert (D2 : getr r4 2 = Z_to_bv 64 (sp0 - 2768)) by (rewrite (K4 2%bv) by kept_reg; exact C2).
    destruct (vfp_seg_c M3 r4 D2 D10) as (r5 & RUN5 & E1 & E2 & E10 & E11 & E12 & EK).
    assert (E10' : getr r5 10 = Z_to_bv 64 (sp0 - 2400)).
    { rewrite E10. rewrite (K4 8%bv) by kept_reg. rewrite CK3 by indec. exact B8. }
    assert (E11' : getr r5 11 = Z_to_bv 64 fa).
    { rewrite E11. rewrite (K4 9%bv) by kept_reg. rewrite CK3 by indec. rewrite BK by indec. exact A9. }
    assert (E3 : getr r5 3 = g3).
    { rewrite EK by indec. rewrite (K4 3%bv) by kept_reg. rewrite CK3 by indec. rewrite BK by indec. rewrite AK by indec. exact H3. }
    assert (E4 : getr r5 4 = g4).
    { rewrite EK by indec. rewrite (K4 4%bv) by kept_reg. rewrite CK3 by indec. rewrite BK by indec. rewrite AK by indec. exact H4. }
    (* [comment removed for export] *)
    destruct (printf_core_p2 sp0 mem0 cv rom CTX g3 g4 r5 (rl dF_17dbc 0x17ec4) va nS saddr slen SARGS fa fbs FMT0 FMTR FBYTE
                its ITS WF COK0 NC7 REM M3 r5 (rl dF_17dbc 0x17ec4) 0 j eq_refl eq_refl
                ltac:(rl_ret_ok) F3 FC3 FS3 AP3 VA3 E1 E2 E10' E11' E12 E3 E4)
      as (r6 & m6 & RUN6 & G2 & GK & PM6 & FC6 & [u6 [j6 [FS6 _]]]).
    destruct (SUBv M3 m6 _ F3 PM6) as [F6 V6].
    { intros a Ho. unfold pcall_regions, pc_regions. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
      revert Ho. unorm. intros Ho. repeat split; lia. }
    (* [comment removed for export] *)
    assert (G8 : getr r6 8 = Z_to_bv 64 (sp0 - 2400)).
    { rewrite GK by indec. rewrite EK by indec. rewrite (K4 8%bv) by kept_reg. rewrite CK3 by indec. exact B8. }
    assert (G20 : getr r6 20 = Z_to_bv 64 (sp0 - 2145)).
    { rewrite GK by indec. rewrite EK by indec. rewrite (K4 20%bv) by kept_reg. exact C20. }
    assert (G21 : getr r6 21 = Z_to_bv 64 0).
    { rewrite GK by indec. rewrite EK by indec. rewrite (K4 21%bv) by kept_reg. exact C21. }
    destruct (vfp_seg_d m6 r6 FC6 G2 G8 G20 G21) as (r7 & RUN7 & I1 & I2 & I10 & I11 & I12 & I21 & IK).
    (* [comment removed for export] *)
    pose proof FS6 as (WP6 & WB6 & CK6 & Hu6 & DEF6).
    destruct (sn_write_run sp0 mem0 cv rom CTX m6 (sp0 - 2768) u6 j6 0 0 [] F6 ltac:(lay; lia)
                (Fc_ck _ _ FC6) WP6 WB6 (Fc_buf _ _ FC6) CK6 Hu6 DEF6 ltac:(lia) ltac:(reflexivity) ltac:(lay; lia)
                r7 (rl dF_17dbc 0x17ee4) ltac:(rl_ret_ok) I1 I2 I10 I11 I12)
      as (r8 & m8 & RUN8 & K8 & _ & WP8 & _ & _ & FM8).
    destruct (SUBv m6 m8 _ F6 FM8) as [F8 V8].
    { intros a Ho. unfold snw_regions. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
      revert Ho. unorm. intros Ho. repeat split; lia. }
    (* [comment removed for export] *)
    assert (KE : forall (a : Z) v, (sp0 - 2464 <= a)%Z -> (a + 8 <= sp0 - 2400)%Z ->
              rdn SEGS M1 (Z_to_bv 64 a) 8 = Some v -> rdn SEGS m8 (Z_to_bv 64 a) 8 = Some v).
    { intros a v Ha1 Ha2 R. unfold snw_regions in FM8. unfold pcall_regions, pc_regions in PM6.
      fkeep FM8. fkeep PM6. fkeep FM3b. fkeep FM3a. fkeep FM2. exact R. }
    assert (Rfl : rdn SEGS m8 (Z_to_bv 64 (sp0 - 2400)) 4 = Some (W4 0)).
    { unfold snw_regions in FM8. unfold pcall_regions, pc_regions in PM6.
      fkeep FM8. fkeep PM6. exact FL3. }
    assert (J2 : getr r8 2 = Z_to_bv 64 (sp0 - 2768)) by (rewrite (K8 2%bv) by kept_reg; exact I2).
    assert (J8 : getr r8 8 = Z_to_bv 64 (sp0 - 2400)) by (rewrite (K8 8%bv) by kept_reg; rewrite IK by indec; exact G8).
    assert (J18 : getr r8 18 = Z_to_bv 64 A_CANARY).
    { rewrite (K8 18%bv) by kept_reg. rewrite IK by indec. rewrite GK by indec. rewrite EK by indec.
      rewrite (K4 18%bv) by kept_reg. rewrite CK3 by indec. rewrite BK by indec. exact A18. }
    assert (J19 : getr r8 19 = Z_to_bv 64 1).
    { rewrite (K8 19%bv) by kept_reg. rewrite IK by indec. rewrite GK by indec. rewrite EK by indec.
      rewrite (K4 19%bv) by kept_reg. exact C19. }
    assert (J20 : getr r8 20 = Z_to_bv 64 (sp0 - 2145)) by (rewrite (K8 20%bv) by kept_reg; rewrite IK by indec; exact G20).
    assert (J21 : getr r8 21 = Z_to_bv 64 0) by (rewrite (K8 21%bv) by kept_reg; exact I21).
    destruct (vfp_seg_e m8 r8 regs ret F8 Hret WP8 Rfl
                (KE (sp0 - 2464)%Z _ ltac:(lia) ltac:(lia) C64) (KE (sp0 - 2408)%Z _ ltac:(lia) ltac:(lia) C08)
                (KE (sp0 - 2416)%Z _ ltac:(lia) ltac:(lia) C16) (KE (sp0 - 2424)%Z _ ltac:(lia) ltac:(lia) C24)
                (KE (sp0 - 2432)%Z _ ltac:(lia) ltac:(lia) C32) (KE (sp0 - 2440)%Z _ ltac:(lia) ltac:(lia) C40)
                (KE (sp0 - 2448)%Z _ ltac:(lia) ltac:(lia) C48) (KE (sp0 - 2456)%Z _ ltac:(lia) ltac:(lia) C56)
                J2 J8 J18 J19 J20 J21)
      as (r9 & RUN9 & Z2 & Z1 & ZK1 & ZK2).
    pose proof (segeM_frame m8) as FM9.
    destruct (SUBv m8 (segeM m8) _ F8 FM9) as [F9 V9].
    { intros a Ho. unfold vfp_regions in *. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    exists r9, (segeM m8). split; [|split; [exact Z2 | split]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. exact RUN9.
    - intros x Hx. cbv [In] in Hx.
      destruct Hx as [<-|[<-|Hx]].
      1,2: rewrite ZK2 by indec; rewrite (K8 _) by kept_reg; rewrite IK by indec; rewrite GK by indec; rewrite EK by indec;
           rewrite (K4 _) by kept_reg; rewrite CK3 by indec; rewrite BK by indec; apply AK; indec.
      destruct Hx as [<-|[<-|[<-|[<-|[<-|[<-|Hx]]]]]]; try (apply ZK1; indec).
      repeat (destruct Hx as [<-|Hx];
        [ rewrite ZK2 by indec; rewrite (K8 _) by kept_reg; rewrite IK by indec; rewrite GK by indec; rewrite EK by indec;
          rewrite (K4 _) by kept_reg; rewrite CK3 by indec; rewrite BK by indec; apply AK; indec |]).
      destruct Hx.
    - eapply frame_mod_trans_same; [exact V1|]. eapply frame_mod_trans_same; [exact V2|].
      eapply frame_mod_trans_same; [exact V3a|]. eapply frame_mod_trans_same; [exact V3b|].
      eapply frame_mod_trans_same; [exact V6|]. eapply frame_mod_trans_same; [exact V8|]. exact V9.
  Qed.
End VFP.
