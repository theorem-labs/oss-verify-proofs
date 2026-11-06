(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17LeptStderr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17LeptErr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17_code_133ec_14000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17_code_14000_15000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17_code_16000_17000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptCredit.
Module V17LeptCmap.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17LeptStderr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17LeptBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17LeptErr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_133ec_14000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_14000_15000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_16000_17000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptCredit.
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].


Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof. intros d [->|[->|[->| ->]]]; apply bv_eq; vm_compute; reflexivity. Qed.

Section Cmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).


(* [comment removed for export] *)
Definition cmap_new (C : lctx) (A A' : AS) (m' : word -> option byte) (cm arr d : Z) : Prop :=
  (1 <= cm)%Z /\ (cm + 24 <= alloc_top (c_vm C))%Z /\ (cm mod 16 = 0)%Z /\
  (1 <= arr)%Z /\ (arr + 4 * 2 ^ d <= alloc_top (c_vm C))%Z /\ (arr mod 16 = 0)%Z /\ cm <> arr /\
  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 arr) = None /\
  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 arr) = None /\
  live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 arr) = Some (4 * 2 ^ d)%Z /\
  (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 arr -> live A' q = live A q) /\
  CMAPat m' cm (CMAPV arr d (2 ^ d) 0 0).





Section SegsD.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma pd_A : forall regs m (s pp cm arr : Z) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (1 <= cm)%Z -> (cm + 24 < 2 ^ 64)%Z -> (0 <= arr < 2 ^ 64)%Z ->
    (pp mod 8 = 0)%Z -> (cm mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cm) ->
    rdn SEGS m (Z_to_bv 64 cm) 8 = Some (Z_to_le_bytes 8 arr) ->
    (cm + 24 <= s - 32 \/ s <= cm)%Z ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14ec0 : word) m rom)
                  (mkst regs' (0x16e80 : word)
                        (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
                                (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x14ef8
      /\ getr regs' 10 = Z_to_bv 64 arr /\ getr regs' 8 = Z_to_bv 64 pp /\ getr regs' 9 = Z_to_bv 64 cm
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s pp cm arr ret Hs Hpp Hpp64 Hcm Hcm64 Harr ALp ALc SOK Rpp Rarr DJ H2 H1 H10.
    eexists. split.
    - zv F_14dc4 D_14dc4 (Z_to_bv 64 (s - 32)).
      stepST F_14dc8 D_14dc8 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_14dcc D_14dcc (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_14dd0 D_14dd0 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_14dd4 D_14dd4 ltac:(condZ).
      sn F_14dd8 D_14dd8.
      stepiv F_14ddc D_14ddc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALp; reflexivity).
      stepb_ft F_14de0 D_14de0 ltac:(condZ).
      stepLD F_14de4 D_14de4 (Z_to_le_bytes 8 cm) (Z_to_bv 64 cm) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      stepb_ft F_14de8 D_14de8 ltac:(condZ).
      stepiv F_14dec D_14dec (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALc; reflexivity).
      stepb_ft F_14df0 D_14df0 ltac:(condZ).
      stepLD F_14df4 D_14df4 (Z_to_le_bytes 8 arr) (Z_to_bv 64 arr) ltac:(addr_norm; rdn_solve) ltac:(apply lez8; lia).
      sn F_14df8 D_14df8.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_B : forall regs m (cm : Z),
    getr regs 9 = Z_to_bv 64 cm ->
    exists regs',
      msteps SEGS (mkst regs (0x14ef8 : word) m rom) (mkst regs' (0x16e80 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x14f00
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m cm H9.
    eexists. split.
    - sn F_14dfc D_14dfc.
      sn F_14e00 D_14e00.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_C : forall regs m (s pp : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> ret_ok ret ->
    store_ok SEGS m (Z_to_bv 64 pp) 8 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pp ->
    exists regs',
      msteps SEGS (mkst regs (0x14f00 : word) m rom)
                  (mkst regs' ret (wbytes m (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs'.
  Proof.
    intros regs m s pp ret s0v s1v Hs Hpp Hpp64 Hret SOK R8 R16 R24 H2 H8.
    eexists. split.
    - stepST F_14e04 D_14e04 (Z_to_bv 64 pp) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_14e08 D_14e08.
      stepLD8 F_14e44 D_14e44 ret.
      stepLD8 F_14e48 D_14e48 s0v.
      stepLD8 F_14e4c D_14e4c s1v.
      zv F_14e50 D_14e50 (Z_to_bv 64 s).
      stepret F_14e54 D_14e54 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsD.

(* [comment removed for export] *)
Theorem pixcmapDestroy_W : forall C A m md regs (s pp cm : Z) (cv : cmapv) (k : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30da0 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 cm) ->
  CMAPat m cm cv -> live A (Z_to_bv 64 cm) = Some 24%Z -> live A (Z_to_bv 64 (c_arr cv)) = Some k ->
  live (c_A0 C) (Z_to_bv 64 cm) = None -> live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None -> cm <> c_arr cv ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 cm) = None -> live A' (Z_to_bv 64 (c_arr cv)) = None ->
     (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' ->
     rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x14ec0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp cm cv k ret S CK HW H2 Hu16 Hlo Hpp Hpphi H1 Hret H4 ALp H10 Rpp CM Lcm Larr L0cm L0arr NE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU17] in *. unfold ALLOC_STACK in Hlo.
  pose proof CM as (Ccm0 & Ccm64 & CWF & _). pose proof (cf_arr _ CWF) as Rarr.
  set (arr := c_arr cv) in *.
  pose proof (alloc_top_lt (m_vmmaps md)) as ATL. unfold two_pow_64 in ATL. destruct (w_vm _ _ _ _ HW) as (_ & VT & _).
  (* [comment removed for export] *)
  destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
  assert (NEw : Z_to_bv 64 cm <> Z_to_bv 64 arr).
  { intros E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lcm) as (_ & ALc & _). rewrite u_Z2bv in ALc by lia.
  assert (ALc8 : (cm mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r cm); apply mod16_plus_mod8; [exact ALc | reflexivity]).
  destruct (pd_A al_rom regs m s pp cm arr ret ltac:(lia) Hpp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ALp ALc8
              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp (CMAP_rd_arr SEGS m cm cv CM) ltac:(lia) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A (pp + 8) m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x30da0) by (rewrite (AG1 4) by notin_lit; exact H4).
  replace (0x16e80 : word) with (Z_to_bv 64 0x16e80) by (apply bv_eq; reflexivity).
  apply (W_free16 C A M1 md r1 (Z_to_bv 64 arr) (Z_to_bv 64 0x14ef8) k (s - 32) S CK HW1 Q10 Larr L0arr Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x14ef8) with (0x14ef8 : word) by (apply bv_eq; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 cm) by (csr; reflexivity).
  destruct (pd_B al_rom r2 m1 cm E9) as (r3 & RUN3 & P10 & P1 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (P4 : getr r3 4 = Z_to_bv 64 0x30da0) by (csr; reflexivity).
  assert (P2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LEQa _ NEw); exact Lcm).
  replace (0x16e80 : word) with (Z_to_bv 64 0x16e80) by (apply bv_eq; reflexivity).
  apply (W_free16 C A1 m1 _ r3 (Z_to_bv 64 cm) (Z_to_bv 64 0x14f00) 24 (s - 32) S CK HWa P10 Lcm1 L0cm P1
           ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hu16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A2 m2 vm2 r4 HWb CSb Lb LEQb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
  replace (Z_to_bv 64 0x14f00) with (0x14f00 : word) by (apply bv_eq; reflexivity).
  assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (V8 : getr r4 8 = Z_to_bv 64 pp) by (csr; reflexivity).
  assert (FR2 : FRM C (s - 32) M1 m2) by (eapply FRM_trans; [exact (proj1 PMa) | exact (proj1 PMb)]).
  destruct (pd_C al_rom r4 m2 s pp ret (getr regs 8) (getr regs 9) ltac:(lia) Hpp ltac:(lia) Hret) as (r5 & RUN5 & X2 & X1 & X8 & X9 & AG5).
  { apply (W_sok_win C A2 m2 _ pp 8 CK HWb); [lia | cbn; lia]. }
  { rewrite (FRM_rdn16 C (s - 32) M1 m2 (s - 8) 8 CK FR2) by (cbn; lia). subst M1. rdn_solve. }
  { rewrite (FRM_rdn16 C (s - 32) M1 m2 (s - 16) 8 CK FR2) by (cbn; lia). subst M1. rdn_solve. }
  { rewrite (FRM_rdn16 C (s - 32) M1 m2 (s - 24) 8 CK FR2) by (cbn; lia). subst M1. rdn_solve. }
  { exact V2. } { exact V8. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
  assert (WP3 : W C A2 (wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm2 md) /\
                POSTM C A2 (pp + 8) m2 (wbytes m2 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
  { apply (WP_win C A2 A2 m2 m2 _ _ _ (pp + 8) CK); [split; [exact HWb | apply POSTM_refl] | apply sub_live_refl | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]. }
  destruct WP3 as [HW3 PM3].
  apply (HK A2 _ vm2 r5).
  - exact HW3.
  - apply cs_kept_intro; csr; try reflexivity.
  - exact Lb.
  - rewrite (LEQb _ (not_eq_sym NEw)). exact La.
  - intros q N1 N2. rewrite (LEQb q N1). apply LEQa. exact N2.
  - (* [comment removed for export] *)
    eapply POSTM_trans; [|exact PM3].
    eapply POSTM_trans; [apply (POSTM_sub C A2 A); [|exact PM1]|].
    { intros q kq Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N1]; [congruence|].
      rewrite (LEQb q N1) in Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 arr)) as [->|N2]; [congruence|].
      rewrite (LEQa q N2) in Lq. exact Lq. }
    eapply POSTM_trans; [apply (POSTM_sub C A2 A1); [| eapply POSTM_mono; [|exact PMa]; lia]|].
    { intros q kq Lq. destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N1]; [congruence|]. rewrite (LEQb q N1) in Lq. exact Lq. }
    eapply POSTM_mono; [|exact PMb]. lia.
  - rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - room_tac.
Qed.

End Cmap.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V17LeptCmap.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17_code_15000_16000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require V17_code_1d000_1e000.
Module V17LeptDeserB.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17LeptStderr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17LeptBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17LeptErr.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_133ec_14000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_14000_15000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_15000_16000.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17.V17_code_1d000_1e000.
(* [comment removed for export] *)
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Section Arith.
Local Open Scope Z_scope.
Lemma lxor_ones64 : forall p, 0 <= p < 2 ^ 64 -> Z.lxor p (2 ^ 64 - 1) = 2 ^ 64 - 1 - p.
Proof.
  intros p Hp. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec.
  replace (2 ^ 64 - 1 - p) with ((Z.lnot p) mod 2 ^ 64).
  2:{ unfold Z.lnot. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  destruct (Z_lt_ge_dec n 64).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia.
    apply Bool.xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
    rewrite Bool.xorb_false_r.
    destruct (Z.eq_dec p 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma zbv_not : forall p, 0 <= p < 2 ^ 64 -> v_xori (Z_to_bv 64 p) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - p).
Proof.
  intros p Hp. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 (-1)) with (2 ^ 64 - 1).
  f_equal. apply lxor_ones64. lia.
Qed.

Lemma lor_mod4_0 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> (Z.lor a b) mod 4 = 0.
Proof.
  intros a b Ha Hb Ma Mb. change 4 with (2 ^ 2) in *. rewrite <- Z.land_ones in * by lia.
  rewrite Z.land_lor_distr_l, Ma, Mb. reflexivity.
Qed.

Lemma zbv_or : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma mod4_plus : forall p k, p mod 4 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof.
  intros p k Hp Hk.
  apply Z.mod_divide in Hp; [|lia]. apply Z.mod_divide in Hk; [|lia]. destruct Hp as [a Ha]. destruct Hk as [b Hb].
  subst. replace (a * 4 + b * 4) with ((a + b) * 4) by lia. apply Z_mod_mult.
Qed.
End Arith.

Section DeserB.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
  Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
  Ltac rdn_out R := rewrite rdn_wbytes_out_Z; [exact R | rewrite ?length_N_to_le_bytes; lia].

  (* [comment removed for export] *)
  Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x159e0 : word) m rom) (mkst regs' (0x13df4 : word) m rom)
      /\ getr regs' 22 = Z_to_bv 64 ncr /\ getr regs' 20 = Z_to_bv 64 nb /\ getr regs' 23 = Z_to_bv 64 dp
      /\ getr regs' 19 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = Z_to_bv 64 0x15a14
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 19; 20; 22; 23]%list) regs regs'.
  Proof.
    intros regs m dp nb ncr q dr wr hr bs20 bs12 Hdp Hdphi Hnb Hq R20 W20 Hncr Hq7 R12 W12 Hdr Hwr Hhr H10 H11 H12 H9 H18.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    eexists. split.
    - stepLD F_158e4 D_158e4 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; rewrite ?Z.add_0_r; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
      sn F_158e8 D_158e8. stepb_ft F_158ec D_158ec ltac:(condZ).
      zv F_158f0 D_158f0 (Z_to_bv 64 (ncr + 7)).
      stepiv F_158f4 D_158f4 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
      stepb_ft F_158f8 D_158f8 ltac:(condZ).
      sn F_158fc D_158fc. sn F_15900 D_15900.
      stepLD F_15904 D_15904 bs12 (Z_to_bv 64 dr) ltac:(addr_norm; exact R12) ltac:(rewrite u_Z2bv by lia; exact W12).
      rewrite (v_lw_Z dr), <- (zbv_zx (sw32 dr)).
      sn F_15908 D_15908. sn F_1590c D_1590c. sn F_15910 D_15910. sn F_15914 D_15914.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    exists regs', msteps SEGS (mkst regs (0x159e0 : word) m rom) (mkst regs' (0x15af0 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13; 22]%list) regs regs'.
  Proof.
    intros regs m dp nb ncr q bs20 Hdp Hdphi Hnb Hq R20 W20 Hncr NC H10 H11 H12.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct (Z_lt_ge_dec 256 ncr) as [BIG|OK].
    - clear NC. eexists. split.
      { stepLD F_158e4 D_158e4 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; rewrite ?Z.add_0_r; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_158e8 D_158e8. stepb_tk F_158ec D_158ec ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
    - assert (NQ : (q <= ncr + 7)%Z) by lia. clear NC. eexists. split.
      { stepLD F_158e4 D_158e4 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; rewrite ?Z.add_0_r; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_158e8 D_158e8. stepb_ft F_158ec D_158ec ltac:(condZ).
        zv F_158f0 D_158f0 (Z_to_bv 64 (ncr + 7)).
        stepiv F_158f4 D_158f4 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
        stepb_tk F_158f8 D_158f8 ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_G0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15a14 : word) m rom)
                              (mkst regs' (0x15b18 : word) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_15918 D_15918 (Z_to_bv 64 (s - 88)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_1591c D_1591c ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 96)%Z -> (pix1 mod 8 = 0)%Z -> p_wpl v1 = wpl ->
    (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 96)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 22 = Z_to_bv 64 nc -> getr regs 20 = Z_to_bv 64 nb ->
    getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x15a14 : word) m rom)
                              (mkst regs' (0x14164 : word) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\ getr regs' 1 = Z_to_bv 64 0x15a68
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 21 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s dp nb nc pix1 wpl hr ir v1 bsi Hs Hs64 SOK PX Gp Hp1 AL8 Hwpl Hhr Hw0 Hsz Hnc Hnb Hnc4 Hdp Hdpnb ALd Ri Wi Hir H2 H10 H22 H20 H23 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rw. rewrite Hwpl in Rw.
    pose proof (zx_range (sw32 ir)) as Hzi.
    assert (PX1 : PIXat (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) pix1 v1).
    { apply PIXat_out; [exact PX | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (ALe : ((dp + (4 * nc + 24)) mod 4 = 0)%Z).
    { apply mod4_plus; [exact ALd|]. replace (4 * nc + 24)%Z with ((nc + 6) * 4)%Z by lia. apply Z_mod_mult. }
    eexists. split.
    - stepST F_15918 D_15918 (Z_to_bv 64 (s - 88)) (Z_to_bv 64 pix1) ltac:(sok_in SOK).
      stepb_ft F_1591c D_1591c ltac:(condZ).
      sn F_15920 D_15920. fixv (Z_to_bv 64 (4 * hr)) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      sn F_15924 D_15924.
      stepb_ft F_1401c D_1401c ltac:(condZ).
      guard8 F_14020 D_14020 AL8. stepb_ft F_14024 D_14024 ltac:(condZ).
      stepLD F_14028 D_14028 (Z_to_le_bytes 4 wpl) (Z_to_bv 64 wpl) ltac:(addr_norm; rewrite <- Hwpl; exact (PIX_rd_wpl SEGS _ _ _ PX1)) ltac:(apply lez4; lia).
      rewrite (v_lw_small wpl) by lia.
      stepret F_1402c D_1402c (0x15a24 : word) ltac:(bveq).
      sn F_15928 D_15928. fixv (Z_to_bv 64 (4 * (wpl * hr))) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
      zv F_1592c D_1592c (Z_to_bv 64 (4 * (wpl * hr))).
      stepb_ft F_15930 D_15930 ltac:(condZ).
      stepiv F_15934 D_15934 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_15938 D_15938 (Z_to_bv 64 (4 * nc + 24)).
      sn F_1593c D_1593c. fixv (Z_to_bv 64 (2 ^ 64 - 1 - dp)) ltac:(apply zbv_not; lia).
      stepb_ft F_15940 D_15940 ltac:(condZ).
      zv F_15944 D_15944 (Z_to_bv 64 (dp + (4 * nc + 24))).
      guard4 F_15948 D_15948 ALe. stepb_ft F_1594c D_1594c ltac:(condZ).
      sn F_15950 D_15950.
      stepLD F_15954 D_15954 bsi (Z_to_bv 64 ir) ltac:(addr_norm; replace (dp + (4 * nc + 24))%Z with (dp + 4 * nc + 24)%Z by lia; rdn_out Ri) ltac:(rewrite u_Z2bv by lia; exact Wi).
      rewrite (v_lw_Z ir), <- (zbv_zx (sw32 ir)).
      stepiv F_15958 D_15958 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_1595c D_1595c. fixv (Z_to_bv 64 (nb - 4 * nc)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_15960 D_15960. fixv (Z_to_bv 64 (nb - 4 * nc - 28)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      zv F_15964 D_15964 (Z_to_bv 64 (s - 88)).
      sn F_15968 D_15968. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz -> getr regs 20 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 19 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (0x15a68 : word) m rom) (mkst regs' (0x13c08 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = Z_to_bv 64 0x15a80
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m sz wr hr d Hsz H8 H21 H20 H9 H18 H19. eexists. split.
    - stepb_ft F_1596c D_1596c ltac:(condZ). stepb_ft F_15970 D_15970 ltac:(condZ).
      sn F_15974 D_15974. sn F_15978 D_15978. sn F_1597c D_1597c. sn F_15980 D_15980. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (Z_to_bv 64 0x1f9d0) 8 = Some (Z_to_le_bytes 8 0x20a40) -> rdn SEGS m (Z_to_bv 64 0x20a40) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 msz -> getr regs 20 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (0x15a68 : word) m rom) (mkst regs' (0x13b08 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x105b2 /\ getr regs' 11 = Z_to_bv 64 0x106ae /\ getr regs' 1 = Z_to_bv 64 0x15b74
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof.
    intros regs m sz msz isz Hsz Hmsz Hisz NE Rg Rs H8 H21 H20.
    destruct (Z.eq_dec sz msz) as [E1|N1].
    - assert (N2 : sz <> isz) by lia. clear NE. eexists. split.
      { stepb_ft F_1596c D_1596c ltac:(condZ). stepb_tk F_15970 D_15970 ltac:(condZ).
        sn F_15a44 D_15a44.
        stepLD F_15a48 D_15a48 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15a4c D_15a4c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15a50 D_15a50. stepb_ft F_15a54 D_15a54 ltac:(condZ).
        sn F_15a58 D_15a58. sn F_15a5c D_15a5c. sn F_15a60 D_15a60. sn F_15a64 D_15a64.
        sn F_15a68 D_15a68. sn F_15a6c D_15a6c. sn F_15a70 D_15a70. sn F_15a74 D_15a74. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - clear NE. eexists. split.
      { stepb_tk F_1596c D_1596c ltac:(condZ).
        sn F_15a44 D_15a44.
        stepLD F_15a48 D_15a48 (Z_to_le_bytes 8 0x20a40) (Z_to_bv 64 0x20a40) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_15a4c D_15a4c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_15a50 D_15a50. stepb_ft F_15a54 D_15a54 ltac:(condZ).
        sn F_15a58 D_15a58. sn F_15a5c D_15a5c. sn F_15a60 D_15a60. sn F_15a64 D_15a64.
        sn F_15a68 D_15a68. sn F_15a6c D_15a6c. sn F_15a70 D_15a70. sn F_15a74 D_15a74. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15a80 : word) m rom)
                              (mkst regs' (0x15b78 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_15984 D_15984 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_15988 D_15988 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15a80 : word) m rom)
                              (mkst regs' (0x15bdc : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [9; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 SOK Hp H2 H10 H22. eexists. split.
    - stepST F_15984 D_15984 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_15988 D_15988 ltac:(condZ).
      sn F_1598c D_1598c. fixv (Z_to_bv 64 0) ltac:(rewrite v_addiw_Z; reflexivity).
      stepb_tk F_15990 D_15990 ltac:(condZ).
      sn F_15aa4 D_15aa4. sn F_15aa8 D_15aa8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    (0 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 nc -> getr regs 23 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x15a80 : word) m rom)
                              (mkst regs' (0x14f58 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = Z_to_bv 64 0x15aa8
      /\ getr regs' 18 = Z_to_bv 64 nc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd dp nc Hs Hs64 SOK Hp Hnc Hdp Hdphi H2 H10 H22 H23. eexists. split.
    - stepST F_15984 D_15984 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_15988 D_15988 ltac:(condZ).
      sn F_1598c D_1598c. fixv (Z_to_bv 64 nc) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_15990 D_15990 ltac:(condZ).
      sn F_15994 D_15994. stepb_ft F_15998 D_15998 ltac:(condZ).
      zv F_1599c D_1599c (Z_to_bv 64 (dp + 24)). sn F_159a0 D_159a0. sn F_159a4 D_159a4. sn F_159a8 D_159a8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15aa8 : word) m rom) (mkst regs' (0x14164 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x15bb0 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2 H10. eexists. split.
    - stepb_tk F_159ac D_159ac ltac:(condZ). zv F_15aac D_15aac (Z_to_bv 64 (s - 96)). sn F_15ab0 D_15ab0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x15aa8 : word) m rom) (mkst regs' (0x14300 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x15abc
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s cm pixd Hs Hs64 Hcm Hp Rp H2 H10. eexists. split.
    - stepb_ft F_159ac D_159ac ltac:(condZ). sn F_159b0 D_159b0.
      stepLD8 F_159b4 D_159b4 (Z_to_bv 64 pixd). sn F_159b8 D_159b8. sn F_159bc D_159bc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_K : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15abc : word) m rom) (mkst regs' (0x15bdc : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rp H2 H10. eexists. split.
    - stepb_tk F_159c0 D_159c0 ltac:(condZ). stepLD8 F_15adc D_15adc (Z_to_bv 64 pixd). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_GD : forall regs m (pixd dp nc sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (pixd mod 8 = 0)%Z -> (0 <= nc <= 256)%Z -> (0 <= dp)%Z -> (dp + 4 * nc + 28 < 2 ^ 64)%Z ->
    (dp mod 4 = 0)%Z -> (p_data v mod 4 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x15bdc : word) m rom) (mkst regs' (0x1dfb4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (dp + 4 * nc + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = Z_to_bv 64 0x15c10
      /\ getr regs' 18 = Z_to_bv 64 (4 * nc)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs m pixd dp nc sz v PX Gp AL8 Hnc Hdp Hdphi ALd ALv H10 H23 H18 H8. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    assert (ALe : ((dp + 4 * nc + 28) mod 4 = 0)%Z).
    { replace (dp + 4 * nc + 28)%Z with (dp + (nc + 7) * 4)%Z by lia. apply mod4_plus; [exact ALd | apply Z_mod_mult]. }
    pose proof (lor_mod4_0 (p_data v) (dp + 4 * nc + 28) ltac:(lia) ltac:(lia) ALv ALe) as ALo.
    pose proof (Z_lor_range (p_data v) (dp + 4 * nc + 28) ltac:(lia) ltac:(lia)) as Ro.
    eexists. split.
    - sn F_15ae0 D_15ae0. stepb_ft F_1451c D_1451c ltac:(condZ).
      guard8 F_14520 D_14520 AL8. stepb_ft F_14524 D_14524 ltac:(condZ).
      stepLD F_14528 D_14528 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepret F_1452c D_1452c (0x15be0 : word) ltac:(bveq).
      sn F_15ae4 D_15ae4. stepb_ft F_15ae8 D_15ae8 ltac:(condZ).
      zv F_15aec D_15aec (Z_to_bv 64 (dp + 28)).
      stepiv F_15af0 D_15af0 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_15af4 D_15af4. fixv (Z_to_bv 64 (2 ^ 64 - 1 - (dp + 28))) ltac:(apply zbv_not; lia).
      stepb_ft F_15af8 D_15af8 ltac:(condZ).
      zv F_15afc D_15afc (Z_to_bv 64 (dp + 4 * nc + 28)).
      sn F_15b00 D_15b00. fixv (Z_to_bv 64 (Z.lor (p_data v) (dp + 4 * nc + 28))) ltac:(apply zbv_or; lia).
      guard4 F_15b04 D_15b04 ALo. stepb_ft F_15b08 D_15b08 ltac:(condZ).
      sn F_15b0c D_15b0c. sn F_15b10 D_15b10. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L0 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x15c10 : word) m rom) (mkst regs' (0x15c70 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rp H2 H22. eexists. split.
    - stepb_tk F_15b14 D_15b14 ltac:(condZ). stepLD8 F_15b30 D_15b30 (Z_to_bv 64 pixd). sn F_15b34 D_15b34. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x15c10 : word) m rom) (mkst regs' (0x14ba8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 76) /\ getr regs' 1 = Z_to_bv 64 0x15c24
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd nc cm Hs Hs64 Hp Hnc Rp H2 H22 H9. eexists. split.
    - stepb_ft F_15b14 D_15b14 ltac:(condZ). stepLD8 F_15b18 D_15b18 (Z_to_bv 64 pixd).
      zv F_15b1c D_15b1c (Z_to_bv 64 (s - 76)). sn F_15b20 D_15b20. sn F_15b24 D_15b24. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x15c24 : word) m rom) (mkst regs' (0x15c70 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rv Rp H2. eexists. split.
    - stepLD F_15b28 D_15b28 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_15b2c D_15b2c ltac:(condZ). stepLD8 F_15b30 D_15b30 (Z_to_bv 64 pixd). sn F_15b34 D_15b34. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x15c24 : word) m rom) (mkst regs' (0x14164 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x15c3c /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 Rv H2. eexists. split.
    - stepLD F_15b28 D_15b28 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_tk F_15b2c D_15b2c ltac:(condZ). zv F_15b38 D_15b38 (Z_to_bv 64 (s - 96)). sn F_15b3c D_15b3c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End DeserB.
End V17LeptDeserB.
