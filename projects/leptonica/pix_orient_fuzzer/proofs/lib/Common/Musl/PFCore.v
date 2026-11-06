(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation W4 v := (word_to_le_bytes 4 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Section GD_1.
  Context {RL : Reloc}.
Definition INT_MAX : Z := 2147483647.
End GD_1.

(* [comment removed for export] *)
Section GD_2.
  Context {RL : Reloc}.
Definition pc_regions (sp0 : Z) : list (word * Z) :=
  [(Z_to_bv 64 (sp0 - 3376), 104%Z); (Z_to_bv 64 (sp0 - 3200), 16%Z); (Z_to_bv 64 (sp0 - 3160), 25%Z);
   (Z_to_bv 64 (sp0 - 2768), 96%Z); (Z_to_bv 64 (sp0 - 2360), 24%Z); (Z_to_bv 64 (sp0 - 2168), 16%Z);
   (Z_to_bv 64 (sp0 - 2080), 2000%Z)].
End GD_2.

(* [comment removed for export] *)
Section GD_3.
  Context {RL : Reloc}.
Record PCc (m : word -> option byte) (sp0 cv : Z) (regs : bvmap 5 word) (ret : word) : Prop := PCC {
  Pc40  : rdn SEGS m (Z_to_bv 64 (sp0 - 3272)) 8 = Some (W8 18446744072850558157);  (* [comment removed for export] *)
  Pc48  : rdn SEGS m (Z_to_bv 64 (sp0 - 3264)) 8 = Some (W8 18446744073709486079);  (* [comment removed for export] *)
  Pc72  : rdn SEGS m (Z_to_bv 64 (sp0 - 3240)) 8 = Some (W8 (sp0 - 2768));          (* [comment removed for export] *)
  Pc80  : rdn SEGS m (Z_to_bv 64 (sp0 - 3232)) 8 = Some (W8 75913);                 (* [comment removed for export] *)
  Pc88  : rdn SEGS m (Z_to_bv 64 (sp0 - 3224)) 8 = Some (W8 0);                     (* [comment removed for export] *)
  Pc96  : rdn SEGS m (Z_to_bv 64 (sp0 - 3216)) 8 = Some (W8 A_CANARY);
  Pc104 : rdn SEGS m (Z_to_bv 64 (sp0 - 3208)) 8 = Some (W8 214748364);             (* [comment removed for export] *)
  Pc432 : rdn SEGS m (Z_to_bv 64 (sp0 - 2880)) 8 = Some (W8 cv);
  Pra   : rdn SEGS m (Z_to_bv 64 (sp0 - 2776)) 8 = Some (X8 ret);
  Ps0   : rdn SEGS m (Z_to_bv 64 (sp0 - 2784)) 8 = Some (X8 (getr regs 8));
  Ps1   : rdn SEGS m (Z_to_bv 64 (sp0 - 2792)) 8 = Some (X8 (getr regs 9));
  Ps2   : rdn SEGS m (Z_to_bv 64 (sp0 - 2800)) 8 = Some (X8 (getr regs 18));
  Ps3   : rdn SEGS m (Z_to_bv 64 (sp0 - 2808)) 8 = Some (X8 (getr regs 19));
  Ps4   : rdn SEGS m (Z_to_bv 64 (sp0 - 2816)) 8 = Some (X8 (getr regs 20));
  Ps5   : rdn SEGS m (Z_to_bv 64 (sp0 - 2824)) 8 = Some (X8 (getr regs 21));
  Ps6   : rdn SEGS m (Z_to_bv 64 (sp0 - 2832)) 8 = Some (X8 (getr regs 22));
  Ps7   : rdn SEGS m (Z_to_bv 64 (sp0 - 2840)) 8 = Some (X8 (getr regs 23));
  Ps8   : rdn SEGS m (Z_to_bv 64 (sp0 - 2848)) 8 = Some (X8 (getr regs 24));
  Ps9   : rdn SEGS m (Z_to_bv 64 (sp0 - 2856)) 8 = Some (X8 (getr regs 25));
  Ps10  : rdn SEGS m (Z_to_bv 64 (sp0 - 2864)) 8 = Some (X8 (getr regs 26));
  Ps11  : rdn SEGS m (Z_to_bv 64 (sp0 - 2872)) 8 = Some (X8 (getr regs 27)) }.
End GD_3.

(* [comment removed for export] *)
Section GD_4.
  Context {RL : Reloc}.
Definition VAslot (m : word -> option byte) (sp0 : Z) (i : Z) (w : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (sp0 - 56 + 8 * i)) 8 = Some (X8 w).
End GD_4.

(* [comment removed for export] *)
Ltac frame_rdn_keep FM :=
  rewrite (frame_mod_rdn SEGS _ _ _ _ _ FM);
  [ | intros i Hi; cbn [outside]; unfold in_rng; unorm; repeat split; lia | unorm; lia ].

Section VP1.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma PCc_frame : forall m m' sp0 cv regs ret,
  (4096 <= sp0 < 2 ^ 63)%Z ->
  PCc m sp0 cv regs ret -> frame_mod m m' (pc_regions sp0) -> PCc m' sp0 cv regs ret.
Proof.
  intros m m' sp0 cv regs ret H0 PC FM. unfold pc_regions in FM. destruct PC.
  split; frame_rdn_keep FM; assumption.
Qed.
End VP1.

Section VP2.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma FILEc_pc : forall m m' sp0,
  (4096 <= sp0 < 2 ^ 63)%Z ->
  FILEc m sp0 -> frame_mod m m' (pc_regions sp0) -> FILEc m' sp0.
Proof.
  intros m m' sp0 H0 FC FM. unfold pc_regions in FM. destruct FC.
  split; frame_rdn_keep FM; assumption.
Qed.
End VP2.

Section VP3.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma VAslot_pc : forall m m' sp0 q w,
  (4096 <= sp0 < 2 ^ 63)%Z -> (0 <= q < 7)%Z ->
  VAslot m sp0 q w -> frame_mod m m' (pc_regions sp0) -> VAslot m' sp0 q w.
Proof.
  intros m m' sp0 q w H0 Hq V FM. unfold pc_regions in FM. unfold VAslot in *.
  frame_rdn_keep FM. exact V.
Qed.
End VP3.

(* [comment removed for export] *)
Section VP4.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
Lemma fwx_sub_pc : forall sp0 a, (4096 <= sp0 < 2 ^ 63)%Z ->
  outside a (pc_regions sp0) -> outside a (fwx_regions sp0 (sp0 - 3312)).
Proof.
  intros sp0 a H0 Ho. unfold pc_regions, fwx_regions in *. cbn [outside] in *. unfold in_rng in *.
  revert Ho. unorm. intros Ho. repeat split; lia.
Qed.
End VP4.

Section CORE.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.

  Ltac sok := soks CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  Lemma pc_regions_sub : forall a, outside a [(Z_to_bv 64 (sp0 - FR), FR)] -> outside a (pc_regions sp0).
Proof.
    pose proof Hcsp as Hsp0.
    intros a Ho. unfold pc_regions. cbn [outside] in Ho |- *. unfold in_rng in *. lay.
    revert Ho. unorm. intros Ho. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition pcR (r : bvmap 5 word) (f p cnt l : Z) : Prop :=
    getr r 3 = g3 /\ getr r 4 = g4 /\
    getr r 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r 8 = Z_to_bv 64 37 /\ getr r 9 = Z_to_bv 64 INT_MAX
    /\ getr r 19 = Z_to_bv 64 cnt /\ getr r 20 = Z_to_bv 64 f /\ getr r 21 = Z_to_bv 64 p /\ getr r 26 = Z_to_bv 64 l.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition proM (m : word -> option byte) (regs : bvmap 5 word) (ret : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (sp0 - 2776)) (X8 ret))
      (Z_to_bv 64 (sp0 - 2784)) (X8 (getr regs 8)))
      (Z_to_bv 64 (sp0 - 2792)) (X8 (getr regs 9)))
      (Z_to_bv 64 (sp0 - 2800)) (X8 (getr regs 18)))
      (Z_to_bv 64 (sp0 - 2808)) (X8 (getr regs 19)))
      (Z_to_bv 64 (sp0 - 2816)) (X8 (getr regs 20)))
      (Z_to_bv 64 (sp0 - 2824)) (X8 (getr regs 21)))
      (Z_to_bv 64 (sp0 - 2832)) (X8 (getr regs 22)))
      (Z_to_bv 64 (sp0 - 2840)) (X8 (getr regs 23)))
      (Z_to_bv 64 (sp0 - 2848)) (X8 (getr regs 24)))
      (Z_to_bv 64 (sp0 - 2856)) (X8 (getr regs 25)))
      (Z_to_bv 64 (sp0 - 2864)) (X8 (getr regs 26)))
      (Z_to_bv 64 (sp0 - 2872)) (X8 (getr regs 27)))
      (Z_to_bv 64 (sp0 - 3248)) (X8 (getr regs 14)))     (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3256)) (X8 (getr regs 13)))     (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3240)) (W8 (sp0 - 2768)))        (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3224)) (W8 0))                  (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3216)) (W8 A_CANARY))           (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 2880)) (W8 cv))                 (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3232)) (W8 75913))              (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3208)) (W8 214748364))          (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3264)) (W8 18446744073709486079))   (* [comment removed for export] *)
      (Z_to_bv 64 (sp0 - 3272)) (W8 18446744072850558157).   (* [comment removed for export] *)

  Lemma prologue_run : forall m regs (ret : word) (f fa : Z),
    FRM sp0 mem0 m -> getr regs 3 = g3 -> getr regs 4 = g4 ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2768) ->
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 fa -> getr regs 12 = Z_to_bv 64 (sp0 - 2768) ->
    exists r,
      msteps SEGS (mkst regs (rl dF_17f6c 0x17f6c) m rom) (mkst r (rl dF_17f6c 0x1801c) (proM m regs ret) rom)
      /\ pcR r f fa 0 0.
Proof.
    intros m regs ret f fa F H3 H4 H1 H2 H10 H11 H12.
    pose proof Hcsp as Hsp0. lay. destruct CTX as [? ? ? ? Chdl Cgot Ccan Ccv0].
    pose proof (FRM_got sp0 mem0 cv CTX m F) as Rgot.
    pose proof (FRM_can sp0 mem0 cv CTX m F) as Rcan.
    unfold A_CANARY_GOT, A_CANARY in *. rl_zaddr_all.
    eexists. split.
    - stepiv F_17f6c D_17f6c (Z_to_bv 64 (sp0 - 3312)) ltac:(zval).
      stepST F_17f70 D_17f70 (Z_to_bv 64 (sp0 - 2776)) ret ltac:(sok).
      stepST F_17f74 D_17f74 (Z_to_bv 64 (sp0 - 2784)) (getr regs 8) ltac:(sok).
      stepST F_17f78 D_17f78 (Z_to_bv 64 (sp0 - 2792)) (getr regs 9) ltac:(sok).
      stepST F_17f7c D_17f7c (Z_to_bv 64 (sp0 - 2800)) (getr regs 18) ltac:(sok).
      stepST F_17f80 D_17f80 (Z_to_bv 64 (sp0 - 2808)) (getr regs 19) ltac:(sok).
      stepST F_17f84 D_17f84 (Z_to_bv 64 (sp0 - 2816)) (getr regs 20) ltac:(sok).
      stepST F_17f88 D_17f88 (Z_to_bv 64 (sp0 - 2824)) (getr regs 21) ltac:(sok).
      stepST F_17f8c D_17f8c (Z_to_bv 64 (sp0 - 2832)) (getr regs 22) ltac:(sok).
      stepST F_17f90 D_17f90 (Z_to_bv 64 (sp0 - 2840)) (getr regs 23) ltac:(sok).
      stepST F_17f94 D_17f94 (Z_to_bv 64 (sp0 - 2848)) (getr regs 24) ltac:(sok).
      stepST F_17f98 D_17f98 (Z_to_bv 64 (sp0 - 2856)) (getr regs 25) ltac:(sok).
      stepST F_17f9c D_17f9c (Z_to_bv 64 (sp0 - 2864)) (getr regs 26) ltac:(sok).
      stepST F_17fa0 D_17fa0 (Z_to_bv 64 (sp0 - 2872)) (getr regs 27) ltac:(sok).
      stepST F_17fa4 D_17fa4 (Z_to_bv 64 (sp0 - 3248)) (getr regs 14) ltac:(sok).
      stepST F_17fa8 D_17fa8 (Z_to_bv 64 (sp0 - 3256)) (getr regs 13) ltac:(sok).
      stepST F_17fac D_17fac (Z_to_bv 64 (sp0 - 3240)) (Z_to_bv 64 (sp0 - 2768)) ltac:(sok).
      stepn F_17fb0 D_17fb0.
      stepn F_17fb4 D_17fb4.
      stepST F_17fb8 D_17fb8 (Z_to_bv 64 (sp0 - 3224)) (Z_to_bv 64 0) ltac:(sok).
      stepn F_17fbc D_17fbc.
      stepn F_17fc0 D_17fc0.
      stepn F_17fc4 D_17fc4.
      stepn F_17fc8 D_17fc8.
      stepn F_17fcc D_17fcc.
      stepLD8 F_17fd0 D_17fd0 (rl dA_2f848 0x2f848).
      stepn F_17fd4 D_17fd4.
      stepST F_17fd8 D_17fd8 (Z_to_bv 64 (sp0 - 3216)) (rl dA_2f848 0x2f848) ltac:(sok).
      stepLD8 F_17fdc D_17fdc (Z_to_bv 64 cv).
      stepn F_17fe0 D_17fe0.
      stepST F_17fe4 D_17fe4 (Z_to_bv 64 (sp0 - 2880)) (Z_to_bv 64 cv) ltac:(sok).
      stepn F_17fe8 D_17fe8.
      stepn F_17fec D_17fec.
      stepn F_17ff0 D_17ff0.
      stepST F_17ff4 D_17ff4 (Z_to_bv 64 (sp0 - 3232)) (Z_to_bv 64 75913) ltac:(sok).
      stepn F_17ff8 D_17ff8.
      stepST F_17ffc D_17ffc (Z_to_bv 64 (sp0 - 3208)) (Z_to_bv 64 214748364) ltac:(sok).
      stepn F_18000 D_18000.
      stepST F_18004 D_18004 (Z_to_bv 64 (sp0 - 3264)) (Z_to_bv 64 18446744073709486079) ltac:(sok).
      stepn F_18008 D_18008.
      stepST F_1800c D_1800c (Z_to_bv 64 (sp0 - 3272)) (Z_to_bv 64 18446744072850558157) ltac:(sok).
      stepn F_18010 D_18010.
      stepn F_18014 D_18014.
      unfold proM. apply mst_refl.
    - unfold pcR, INT_MAX. postR.
  Qed.

  (* [comment removed for export] *)
  Lemma proM_PCc : forall m regs ret, PCc (proM m regs ret) sp0 cv regs ret.
Proof.
    intros m regs ret. pose proof Hcsp as Hsp0. lay. unfold proM.
    split; rdn_solve.
  Qed.

  Lemma proM_frame : forall m regs ret,
    frame_mod m (proM m regs ret) [(Z_to_bv 64 (sp0 - 3312), 544%Z)].
Proof.
    intros m regs ret. pose proof Hcsp as Hsp0. lay. unfold proM.
    frame_tac Hsp0. apply frame_mod_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac head_steps cnt l :=
      stepn constr:(F_1801c) constr:(D_1801c); rwH; rewrite (v_subw_Z 2147483647 cnt) by lia;                     (* [comment removed for export] *)
      stepiv constr:(F_18020) constr:(D_18020) (Z_to_bv 64 l) ltac:(gres; rwH; imm_norm; rewrite v_addiw_Z by lia; f_equal; lia); (* [comment removed for export] *)
      stepb_ft constr:(F_18024) constr:(D_18024) ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia);             (* [comment removed for export] *)
      stepn constr:(F_18028) constr:(D_18028);                                                                       (* [comment removed for export] *)
      stepLBU constr:(F_1802c) constr:(D_1802c) (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve);                          (* [comment removed for export] *)
      stepn constr:(F_18030) constr:(D_18030); rwH; rewrite (v_addw_Z l cnt) by lia;                              (* [comment removed for export] *)
      stepb_tk constr:(F_18034) constr:(D_18034) ltac:(rwH; apply c_eq_refl).                                           (* [comment removed for export] *)

  Lemma head_end_run : forall m r (f p cnt l : Z),
    pcR r f p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l <= INT_MAX)%Z ->
    (0 <= f < 2 ^ 64)%Z -> (0 <= p < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 0] ->
    (f <> 0%Z -> 
     exists r', msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x18d48) m rom)
                /\ getr r' 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r' 19 = Z_to_bv 64 (cnt + l)
                /\ getr r' 3 = g3 /\ getr r' 4 = g4)
    /\ (f = 0%Z -> rdn SEGS m (Z_to_bv 64 (sp0 - 3224)) 8 = Some (W8 0) ->
     exists r', msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x18d48) m rom)
                /\ getr r' 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r' 19 = Z_to_bv 64 0
                /\ getr r' 3 = g3 /\ getr r' 4 = g4).
Proof.
    intros m r f p cnt l (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26) Hc Hl Hcl Hf Hp Hb.
    pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    split.
    - intros Hf0. eexists. split.
      + head_steps cnt l.
        stepb_tk F_18bf0 D_18bf0 ltac:(cond_lia).
        apply mst_refl.
      + repeat split; gres; rwH; first [reflexivity | f_equal; lia].
    - intros -> H88. eexists. split.
      + head_steps cnt l.
        stepb_ft F_18bf0 D_18bf0 ltac:(rwH; apply c_eq_refl).
        stepLD8 F_18bf4 D_18bf4 (Z_to_bv 64 0).
        stepb_tk F_18bf8 D_18bf8 ltac:(rwH; apply c_eq_refl).
        stepn F_18cc4 D_18cc4.
        stepn F_18cc8 D_18cc8.
        apply mst_refl.
      + repeat split; gres; rwH; first [reflexivity | f_equal; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma epilogue_run : forall m r regs (ret : word) (v : word),
    FRM sp0 mem0 m -> PCc m sp0 cv regs ret -> ret_ok ret ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 19 = v -> getr r 3 = g3 -> getr r 4 = g4 ->
    exists r', msteps SEGS (mkst r (rl dF_17f6c 0x18d48) m rom) (mkst r' ret m rom)
               /\ getr r' 10 = v /\ getr r' 2 = Z_to_bv 64 (sp0 - 2768) /\ getr r' 1 = ret
               /\ (forall x : reg, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr regs x)
               /\ getr r' 3 = g3 /\ getr r' 4 = g4.
Proof.
    intros m r regs ret v F PC Hret R2 R19 R3 R4.
    pose proof Hcsp as Hsp0. lay. destruct PC.
    pose proof (FRM_can sp0 mem0 cv CTX m F) as Rcan. pose proof (Ccv _ _ _ CTX) as Hcv. unfold A_CANARY in *.
    eexists. split.
    - stepLD8 F_18d48 D_18d48 (rl dA_2f848 0x2f848).
      stepLD8 F_18d4c D_18d4c (Z_to_bv 64 cv).
      stepLD8 F_18d50 D_18d50 (Z_to_bv 64 cv).
      stepb_ft F_18d54 D_18d54 ltac:(rwH; apply c_eq_refl).
      stepn F_18d58 D_18d58.
      stepLD8 F_18d5c D_18d5c ret.
      stepLD8 F_18d60 D_18d60 (getr regs 8).
      stepLD8 F_18d64 D_18d64 (getr regs 9).
      stepLD8 F_18d68 D_18d68 (getr regs 18).
      stepLD8 F_18d6c D_18d6c (getr regs 19).
      stepLD8 F_18d70 D_18d70 (getr regs 20).
      stepLD8 F_18d74 D_18d74 (getr regs 21).
      stepLD8 F_18d78 D_18d78 (getr regs 22).
      stepLD8 F_18d7c D_18d7c (getr regs 23).
      stepLD8 F_18d80 D_18d80 (getr regs 24).
      stepLD8 F_18d84 D_18d84 (getr regs 25).
      stepLD8 F_18d88 D_18d88 (getr regs 26).
      stepLD8 F_18d8c D_18d8c (getr regs 27).
      stepiv F_18d90 D_18d90 (Z_to_bv 64 (sp0 - 2768)) ltac:(zval).
      stepret F_18d94 D_18d94 ret ltac:(reflexivity).
      apply mst_refl.
    - split; [gres; exact R19|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split.
      + intros x Hx. cbv [In] in Hx.
        repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]). destruct Hx.
      + split; gres; assumption.
  Qed.
End CORE.
