(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_m_a4s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma land_m4096 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x / 4096 * 4096.
Proof.
  intros x Hx. replace 18446744073709547520 with ((-4096) mod 2^64) by reflexivity.
  rewrite land_mod_pow2_r by lia. replace (-4096) with (Z.lnot (Z.ones 12)) by reflexivity. rewrite <- Z.ldiff_land.
  rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Section A4S.
Hypothesis poison_shadow_proof : poison_shadow_spec.

(* [comment removed for export] *)
Lemma alloc_a4s_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n mb P S lo : Z) (j1 : list byte),
  mem_inv asegs m -> icpt_cells m -> poison_cells m ->
  s0 = wz 0 -> s1 = wz (usz n) -> s2 = wz (sec_alloc_beg mb) -> s4 = wz (sec_user mb) -> s6 = wz A_ALLOC ->
  s9 = wz (sec_user mb + usz n) ->
  0 <= n < 2^32 -> bprim n = false ->
  ablk mb (mb + smapsize n) -> mb mod 4096 = 0 -> mb + smapsize n <= alloc_ceiling ->   (* [comment removed for export] *)
  (mb + smapsize n <= P \/ P + PRIM_RES_SIZE <= mb) -> KHIGHMEM_BEG <= P -> P + PRIM_RES_SIZE <= alloc_ceiling -> P <= S -> S + KSPACESIZE + 4096 <= P + PRIM_RES_SIZE ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp ->
  rw_cells asegs m A_ALLOC [C8 (wz P); C8 (wz PRIM_RES_SIZE); CB 16 j1; C8 (wz S)] ->
  rw_cells asegs m A_SECONDARY [C8 (wz 4096)] ->
  rw_cells asegs m (mb + 16) [C8 (wz (needed n))] ->
  stk asegs m (SH mb) (SH mb + smapsize n / 8) ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' (wz (roundup (needed n) 4096)) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 (wz (sec_user mb + rounded8 n)) s7 s8 (wz (sec_user mb + usz n + 7)) s10 s11 t3' t4' t5' t6')
               F (wz 0x3238c) fc None m' (seg_rom asegs)
      /\ munch [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
                (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
                (bv_unsigned sp - 1024, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3230c) fc None m (seg_rom asegs)).
Proof.
  intros until j1. intros MI IC PC -> -> -> -> -> -> Hn HP M1k M2 M3 MP P1 P2 PS1 PS2 ST HCL LO CA CS HW SV.
  (nelimp (ablk_lin _ _ M1k) 4%nat; intros M1 M1b _ M1d).
  (nelimp (sec_facts n HP) 6%nat; intros F1 F2 F3 F4 F5 F6). (nelimp (usz_le_rounded8 n) 3%nat; intros U1 U2 U3). pose proof (rounded8_range n Hn) as R8.
  assert (RU : roundup (needed n) 4096 = smapsize n - 4096) by (unfold smapsize; lia).
  assert (RU2 : needed n <= roundup (needed n) 4096 <= needed n + 4095 /\ roundup (needed n) 4096 mod 4096 = 0).
  { unfold roundup. split; [Z.div_mod_to_equations; lia| apply Z_mod_mult]. }
  set (ru := roundup (needed n) 4096) in *.
  set (ue8 := sec_user mb + rounded8 n).
  pose proof (munch_refl [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256); (SH ue8, SH ue8 + (mb + smapsize n - ue8) / 8); (bv_unsigned sp - 1024, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold sec_alloc_beg, sec_user, SEC_HDR, SEC_RZ, KHIGHMEM_BEG, AIMG_HI, A_SECONDARY, A_ALLOC, KSPACESIZE, PRIM_RES_SIZE in *. idtac.
  unfold usz in *. change (683032 + 64) with 683096 in CS.
  pose proof (rt_SH_aligned_add mb 4096 ltac:(Z.div_mod_to_equations; lia)) as SH1. change (4096 / 8) with 512 in SH1.
  pose proof (rt_SH_aligned_add mb (6144 + rounded8 n) ltac:(Z.div_mod_to_equations; lia)) as SH2.
  pose proof (rt_SH_aligned_add mb (smapsize n) ltac:(Z.div_mod_to_equations; lia)) as SH3.
  pose proof (rt_SH_bounds mb ltac:(lia)) as SB. unfold KHIGHMEM_BEG, AIMG_HI in SB.
  assert (R88 : (6144 + rounded8 n) / 8 = 768 + rounded8 n / 8) by (Z.div_mod_to_equations; lia).
  assert (SZ2 : (mb + smapsize n - ue8) / 8 = smapsize n / 8 - 768 - rounded8 n / 8) by (subst ue8; Z.div_mod_to_equations; lia).
  assert (SZ2' : 2048 <= mb + smapsize n - ue8 /\ (mb + smapsize n - ue8) mod 8 = 0) by (subst ue8; unfold smapsize in *; Z.div_mod_to_equations; lia).
  destruct (vis_carve m _ _ (SH mb + 512) 256 SV ltac:(lia) ltac:(cbn; unfold smapsize; Z.div_mod_to_equations; lia)) as [sj1 SC1].
  destruct (vis_carve m _ _ (SH mb + (768 + rounded8 n / 8)) (Z.to_nat ((mb + smapsize n - ue8) / 8)) SV ltac:(Z.div_mod_to_equations; lia) ltac:(rewrite Z2Nat.id by lia; Z.div_mod_to_equations; lia)) as [sj2 SC2].
  replace (SH mb + 512) with (SH (mb + 4096)) in SC1 by lia.
  assert (SHU : SH ue8 = SH mb + (768 + rounded8 n / 8)) by (subst ue8; rewrite <- R88, <- SH2; f_equal; lia).
  rewrite <- SHU in SC2.
  clear SV.
  leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  replace (Z.land 4095 (mb + 4096)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2^12) with 4096; Z.div_mod_to_equations; lia).
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  replace (mb + 4096 - 4096) with mb by lia.
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite (land_m4096 (needed n + 4095)) by lia. replace ((needed n + 4095) / 4096 * 4096) with ru by (subst ru; unfold roundup; f_equal; f_equal; lia).
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  rewrite (land_m8 (mb + 6144 + n `max` 1 + 7)) by lia.
  replace ((mb + 6144 + n `max` 1 + 7) / 8 * 8) with ue8 by (subst ue8; unfold rounded8, roundup; Z.div_mod_to_equations; lia).
  lstep. lstep. lstep. (* [comment removed for export] *)
  replace (mb + 6144 - (mb + 4096)) with 2048 by lia.
  lstep. (* [comment removed for export] *)
  callxp ltac:(eapply poison_shadow_proof with (a := mb + 4096) (sz := 2048) (v := 250) (lo := lo);
    [ exact IC| exact PC| eassumption| exact ST| idtac; lia| unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity
    | Z.div_mod_to_equations; lia| reflexivity| lia
    | apply (ablk_app_range mb (mb + smapsize n)); [exact M1k| lia| lia| lia]| lia
    | intros; discriminate
    | change (2048 / 8) with 256; exact SC1 ])
    ltac:(unfold poison_shadow_post, APOISON_STACK; change (2048 / 8) with 256; clear SC1 HW ST).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI2 end. match goal with H : stk _ _ lo _ |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  replace (mb + 4096 - ue8 + ru) with (mb + smapsize n - ue8) by lia.
  assert (IC2 : icpt_cells m2) by (eapply icpt_cells_high; [exact MU| | exact IC]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_HI; lia).
  assert (PC2 : poison_cells m2) by (eapply poison_cells_high; [exact MU| | exact PC]; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_HI; lia).
  lstep. (* [comment removed for export] *)
  callxp ltac:(eapply poison_shadow_proof with (a := ue8) (sz := mb + smapsize n - ue8) (v := 250) (lo := lo);
    [ exact IC2| exact PC2| exact MI2| exact ST2| idtac; lia| unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity
    | subst ue8; Z.div_mod_to_equations; lia| lia| lia
    | apply (ablk_app_range mb (mb + smapsize n)); [exact M1k| subst ue8; lia| lia| subst ue8; lia]| lia
    | intros; discriminate
    | exact SC2 ])
    ltac:(unfold poison_shadow_post, APOISON_STACK; clear SC2 ST2).
  cbv beta delta [wz] in *.
  finish.
Qed.

(* [comment removed for export] *)
Lemma alloc_a4s_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n mb P S lo : Z) (j1 : list byte),
  mem_inv asegs m -> icpt_cells m -> poison_cells m ->
  s0 = wz 0 -> s1 = wz (usz n) -> s2 = wz (sec_alloc_beg mb) -> s4 = wz (sec_user mb) -> s6 = wz A_ALLOC ->
  s9 = wz (sec_user mb + usz n) ->
  0 <= n < 2^32 -> bprim n = false ->
  ablk mb (mb + smapsize n) -> mb mod 4096 = 0 -> mb + smapsize n <= alloc_ceiling ->   (* [comment removed for export] *)
  (mb + smapsize n <= P \/ P + PRIM_RES_SIZE <= mb) -> KHIGHMEM_BEG <= P -> P + PRIM_RES_SIZE <= alloc_ceiling -> P <= S -> S + KSPACESIZE + 4096 <= P + PRIM_RES_SIZE ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp ->
  rw_cells asegs m A_ALLOC [C8 (wz P); C8 (wz PRIM_RES_SIZE); CB 16 j1; C8 (wz S)] ->
  rw_cells asegs m A_SECONDARY [C8 (wz 4096)] ->
  rw_cells asegs m (mb + 16) [C8 (wz (needed n))] ->
  stk asegs m (SH mb) (SH mb + smapsize n / 8) ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' (wz (roundup (needed n) 4096)) s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 (wz (sec_user mb + rounded8 n)) s7 s8 (wz (sec_user mb + usz n + 7)) s10 s11 t3' t4' t5' t6')
               F (wz 0x3238c) fc None m' (seg_rom asegs)
      /\ munch [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
                (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
                (bv_unsigned sp - 1024, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x322b0) fc None m (seg_rom asegs)).
Proof.
  intros until j1. intros MI IC PC -> -> -> -> -> -> Hn HP M1 M2 M3 MP P1 P2 PS1 PS2 ST HCL LO CA CS HW SV.
  (nelimp (ablk_lin _ _ M1) 4%nat; intros M1a M1b _ M1d). unfold AIMG_HI in M1a.
  (nelimp (sec_facts n HP) 6%nat; intros F1 F2 F3 F4 F5 F6).
  pose proof ST as ST0. pose proof M3 as M30. pose proof HCL as HCL0. pose proof MP as MP0. pose proof PS2 as PS20. pose proof P2 as P20. pose proof P1 as P10.
  assert (E1 : sec_alloc_beg mb = mb + 4096) by reflexivity. assert (E2 : sec_user mb = mb + 6144) by (unfold sec_user, SEC_HDR, SEC_RZ; lia).
  assert (U1 : 1 <= usz n) by (unfold usz; lia).
  unfold KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, PRIM_RES_SIZE in Hn, M1, M2, M3, MP, P1, P2, PS1, PS2, HCL, LO. change (2 ^ 37) with 137438953472 in PS2.
  idtac. leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if2 BR. (* [comment removed for export] *)
  - eapply evt_cut; [eapply alloc_a4s_tail with (n := n) (mb := mb) (P := P) (S := S) (lo := lo) (j1 := j1)|]. all: try reflexivity; try eassumption.
    all: try (unfold PRIM_RES_SIZE, KSPACESIZE, KHIGHMEM_BEG, AIMG_HI; idtac; lia).
    cbv beta. intros ms' PO. apply evt_done. exact PO.
  - lstep. lstep. lstep. (* [comment removed for export] *)
    lstep; if_lia. (* [comment removed for export] *)
    eapply evt_cut; [eapply alloc_a4s_tail with (n := n) (mb := mb) (P := P) (S := S) (lo := lo) (j1 := j1); try reflexivity; try eassumption; unfold PRIM_RES_SIZE, KSPACESIZE, KHIGHMEM_BEG, AIMG_HI; idtac; lia|].
    cbv beta. intros ms' PO. apply evt_done. exact PO.
Qed.
End A4S.


End CeilWrap.
End RTW_m_a4s.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
Module RTW_m_at1s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a4 RTW_m_a4s OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section AT1S.
Hypothesis poison_shadow_proof : poison_shadow_spec.

(* [comment removed for export] *)
Lemma alloc_t1s_pre :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (n mb id b1 P S lo : Z) (j1 j8 ja : list byte),
  mem_inv asegs m -> icpt_cells m -> poison_cells m ->
  a0 = wz id -> s0 = wz 0 -> s1 = wz (usz n) -> s2 = wz (sec_alloc_beg mb) -> s4 = wz (sec_user mb) -> s5 = wz (sec_user mb + -16) -> s6 = wz A_ALLOC ->
  s8 = wz 0 -> s9 = wz (sec_user mb + usz n) ->
  0 <= n < 2^32 -> bprim n = false -> 0 <= id < 2^32 ->
  ablk mb (mb + smapsize n) -> mb mod 4096 = 0 -> mb + smapsize n <= alloc_ceiling ->   (* [comment removed for export] *)
  (mb + smapsize n <= P \/ P + PRIM_RES_SIZE <= mb) -> KHIGHMEM_BEG <= P -> P + PRIM_RES_SIZE <= alloc_ceiling -> P <= S -> S + KSPACESIZE + 4096 <= P + PRIM_RES_SIZE ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp ->
  rw_cells asegs m (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); CB 8 j8] ->
  rw_cells asegs m A_ALLOC [C8 (wz P); C8 (wz PRIM_RES_SIZE); CB 16 ja; C8 (wz S)] ->
  rw_cells asegs m A_SECONDARY [C8 (wz 4096)] ->
  rw_cells asegs m (mb + 16) [C8 (wz (needed n))] ->
  stk asegs m (SH mb) (SH mb + smapsize n / 8) ->
  evt asegs (fun ms' => exists (s0' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR (wz 0x323ac) sp gp tp t0' t1' t2' s0' s1 (wz (sec_user mb)) (wz (usz n / 8 * 8)) (wz 0) a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 (wz (usz n / 8 * 8)) s7 s8 (wz (sec_user mb + usz n + 7)) s10 s11 t3' t4' t5' t6')
               F (wz APOISON_SHADOW) fc None m' (seg_rom asegs)
      /\ munch [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
                (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
                (sec_user mb + -8, sec_user mb); (bv_unsigned sp - 1024, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x322a0) fc None m (seg_rom asegs)).
Proof.
  intros until ja. intros MI IC PC -> -> -> -> -> -> -> -> -> Hn HP Hid M1k M2 M3 MP P1 P2 PS1 PS2 ST HCL LO HDR CA CS HW SV.
  pose proof (ablk_lin _ _ M1k) as (M1 & M1b & _ & M1d).
  pose proof (sec_facts n HP) as (F1 & F2 & F3 & F4 & F5 & F6). pose proof (usz_le_rounded8 n) as (U1 & U2 & U3). pose proof (rounded8_range n Hn) as R8.
  assert (E2 : sec_user mb = mb + 6144) by (unfold sec_user, SEC_HDR, SEC_RZ; lia). assert (E1 : sec_alloc_beg mb = mb + 4096) by reflexivity.
  assert (SMN : rounded8 n + 8192 <= smapsize n) by (unfold smapsize, roundup; rewrite F6; Z.div_mod_to_equations; lia).
  assert (V1 : 1 <= usz n) by (unfold usz; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
                (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
                (sec_user mb + -8, sec_user mb); (bv_unsigned sp - 1024, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  unfold usz, KHIGHMEM_BEG, AIMG_HI, PRIM_RES_SIZE, KSPACESIZE in *. idtac.
  pose proof (rt_SH_mono 6287360 (sec_alloc_beg mb) ltac:(unfold sec_alloc_beg, SEC_HDR; lia)) as SB1. change (SH 6287360) with 0x800b7e00 in SB1.
  pose proof (rt_SH_mono 6287360 (sec_user mb + rounded8 n) ltac:(lia)) as SB2. change (SH 6287360) with 0x800b7e00 in SB2.
  assert (SV' : True -> stk asegs m (SH mb) (SH mb + smapsize n / 8)) by (intros _; exact SV). clear SV.   (* [comment removed for export] *)
  unfold A_ALLOC in CA. unfold A_SECONDARY, A_ALLOC in CS.
  pose proof (rt_SH_bounds (mb + smapsize n) ltac:(lia)) as SB3.
  assert (SHa : SH (sec_alloc_beg mb) = SH mb + 512) by (rewrite E1, rt_SH_aligned_add by (Z.div_mod_to_equations; lia); reflexivity).
  assert (SHe : SH (mb + smapsize n) = SH mb + smapsize n / 8) by (rewrite rt_SH_aligned_add by (Z.div_mod_to_equations; lia); reflexivity).
  assert (SHu : SH (sec_user mb + rounded8 n) = SH mb + (6144 + rounded8 n) / 8).
  { rewrite E2. replace (mb + 6144 + rounded8 n) with (mb + (6144 + rounded8 n)) by lia. rewrite rt_SH_aligned_add by (Z.div_mod_to_equations; lia). reflexivity. }
  assert (SZ2 : (mb + smapsize n - (sec_user mb + rounded8 n)) / 8 = smapsize n / 8 - (6144 + rounded8 n) / 8) by (rewrite E2; Z.div_mod_to_equations; lia).
  leaf_prep.
  (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  rewrite (Z.mod_small id), Z.lor_0_l by lia.
  lstep. (* [comment removed for export] *)
  match goal with H : mem_inv _ _ |- _ => rename H into MI0 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST0 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
  match goal with H : rw_cells _ m0 (sec_user mb + -16) _ |- _ => rename H into HDR0 end.
  assert (HDR0' : True -> rw_cells asegs m0 (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]) by (intros _; exact HDR0).
  pose proof (munch_refl [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
                (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
                (bv_unsigned sp - 1024, bv_unsigned sp)] m0) as MU2.
  pose proof (wmono_refl asegs m0) as WM2.
  assert (IC0 : icpt_cells m0) by (eapply icpt_cells_high; [exact MU| | exact IC]; unfold AIMG_HI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  assert (PC0 : poison_cells m0) by (eapply poison_cells_high; [exact MU| | exact PC]; unfold AIMG_HI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  assert (SV0 : stk asegs m0 (SH mb) (SH mb + smapsize n / 8)).
  { eapply stk_wmono_noseg; [exact (SV' I)| exact WM|]. pose proof (rt_SH_bounds mb ltac:(lia)). unfold AIMG_HI. lia. }
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply (alloc_a4s_spec poison_shadow_proof) with (n := n) (mb := mb) (P := P) (S := S) (lo := lo);
    [ exact MI0| exact IC0| exact PC0| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| unfold usz; reflexivity
    | exact Hn| exact HP| exact M1k| exact M2| idtac; lia
    | unfold PRIM_RES_SIZE; lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| unfold PRIM_RES_SIZE; idtac; lia| lia| unfold PRIM_RES_SIZE, KSPACESIZE; lia
    | exact ST0| idtac; lia| lia
    | exact CA| exact CS| exact HW| exact SV0 ]) ltac:(clear HDR0 HW).
  cbv beta delta [wz] in *. unfold usz in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  try clear HDR0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (HDR1 : rw_cells asegs mx (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (n `max` 1)); C8 (Z_to_bv 64 id)])
      by (eapply (rw_cells_transport asegs _ m0 mx); [exact (HDR0' I)| exact MU2| exact WM2| cbn; blia]) end.
  clear HDR0' MU2 WM2.
  (* [comment removed for export] *)
  lstep. lstep. fl. lstep. (* [comment removed for export] *)
  rewrite land_48m8 by lia.
  sepM. lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  finish.
Qed.

(* [comment removed for export] *)
Lemma alloc_t1s_post :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (n ub lo : Z) (g0 : byte),
  leafc st m -> mem_inv asegs m -> memtoshadow_cells m ->
  s1 = wz (usz n) -> s4 = wz ub -> s6 = wz (usz n / 8 * 8) ->
  0 <= n < 2^32 -> ablk ub (ub + usz n + 8) -> ub + usz n + 8 <= alloc_ceiling -> ub mod 8 = 0 ->   (* [comment removed for export] *)
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp ->
  (usz n mod 8 <> 0 -> rw_cells asegs m (SH (ub + usz n / 8 * 8)) [C1 g0]) ->
  evt asegs (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (wz 0x32440) fc None m' (seg_rom asegs)
      /\ munch [(SH (ub + usz n / 8 * 8), SH (ub + usz n / 8 * 8) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ (usz n mod 8 <> 0 -> rw_cells asegs m' (SH (ub + usz n / 8 * 8)) [C1 (zb (usz n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x323ac) fc None m (seg_rom asegs)).
Proof.
  intros until g0. intros LC MI MC -> -> -> Hn U1 U2 U8 ST HCL LO SHB.
  pose proof (munch_refl [(SH (ub + usz n / 8 * 8), SH (ub + usz n / 8 * 8) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (V1 : 1 <= usz n) by (unfold usz; lia).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold KHIGHMEM_BEG, AIMG_HI in *. idtac.
  destruct (Z.eq_dec (usz n mod 8) 0) as [R0|RNZ].
  - (* [comment removed for export] *)
    clear SHB. leaf_prep.
    lstep; if_lia.
    apply evt_done. do 18 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [assumption|].
    intros C. exfalso. exact (C R0).
  - specialize (SHB RNZ). leaf_prep.
    lstep; if_lia. (* [comment removed for export] *)
    callxp ltac:(eapply alloc_a5_spec with (st := st) (n := n) (ub := ub) (lo := lo) (g0 := g0);
      [ exact LC| exact MI| exact MC| reflexivity| reflexivity| reflexivity| exact Hn| exact RNZ| exact U1| idtac; lia| exact U8
      | exact ST| idtac; lia| lia| exact SHB ]) ltac:(clear SHB).
    cbv beta delta [wz] in *.
    apply evt_done. do 18 eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    intros _. assumption.
Qed.
End AT1S.


End CeilWrap.
End RTW_m_at1s.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memset.
Module RTW_m_at2s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a6s OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a7 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma alloc_t2s_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n mb id b1 lo : Z) (j1 j0 bj uj : list byte) (sj0 sj1 sj2 sj3 : word) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  let r := sec_alloc_beg mb in
  leafc st m -> RTWF st -> mem_inv asegs m -> fill_cells m -> tp = wz ATP ->
  s1 = wz (usz n) -> s2 = wz r -> s3 = wz (needed n) -> s4 = wz (r + rz_size n) -> s5 = wz (r + rz_size n + -16) ->
  0 <= n < 2^32 -> bprim n = false -> 0 <= id < 2^32 -> 0 <= b1 < 256 -> Z.land b1 115 = 17 ->
  ablk mb (mb + smapsize n) -> mb + smapsize n <= alloc_ceiling -> mb mod 4096 = 0 ->   (* [comment removed for export] *)
  (st_ctx st + 160 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_ctx st) -> st_ctx st + 160 <= alloc_ceiling -> (mb + smapsize n <= st_ctx st \/ st_ctx st + 160 <= mb) ->
  (st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st) -> (st_ctx st + 160 <= st_t st \/ st_t st + 4096 <= st_ctx st) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2] ->
  rw_cells asegs m (st_t st + 2904) [C8 sj3] ->
  rw_cells asegs m (r + rz_size n + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)] ->
  rw_cells asegs m r [CB 16 bj] ->
  rw_cells asegs m (r + rz_size n) [CB (Z.to_nat (usz n)) uj] ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (b1' : Z) (sj0' sj1' sj2' sj3' : word)
                               (ujr : list byte) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 128)) gp tp t0' t1' t2' v0 v1 (wz (r + rz_size n)) a1' a2' a3' a4' a5' a6' a7'
                    v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch [(r, r + 16); (r + rz_size n + -16, r + rz_size n); (r + rz_size n, r + rz_size n + usz n);
                (st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912);
                (bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 128)
      /\ rw_cells asegs m' (r + rz_size n + -16) [C1 (zb CHUNK_ALLOCATED); C1 (zb b1'); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]
      /\ Z.land b1' 127 = HDR_BYTE1_MALLOC /\ 0 <= b1' < 256
      /\ rw_cells asegs m' r [C8 (wz KALLOCBEG_MAGIC); C8 (wz (r + rz_size n + -16))]
      /\ rw_cells asegs m' (st_t st + 2800) [C8 sj0'; C8 sj1'; C8 sj2']
      /\ rw_cells asegs m' (st_t st + 2904) [C8 sj3']
      /\ rw_cells asegs m' (r + rz_size n)
           [CB (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX)) (repeat (zb MALLOC_FILL_BYTE) (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX)));
            CB (Z.to_nat (usz n - Z.min (usz n) MALLOC_FILL_MAX)) ujr])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x32440) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros r LC WF MI FC TP -> -> -> -> -> Hn HP Hid Hb1 Hb1' M1 M2 M3 X1 X2 X3 TC X4 ST HCL LO SPH FR TS1 TS2 HDR BH USR.
  (nelimp (ablk_lin _ _ M1) 4%nat; intros M1a M1b _ M1d). unfold AIMG_HI in M1a.
  (nelimp (sec_facts n HP) 6%nat; intros F1 F2 F3 F4 F5 F6). (nelimp (usz_le_rounded8 n) 3%nat; intros V1 V2 V3). pose proof (rounded8_range n Hn) as R8.
  assert (Er : r = mb + 4096) by reflexivity. clearbody r.
  assert (SMN : rounded8 n + 8192 <= smapsize n) by (unfold smapsize, roundup; rewrite F6; Z.div_mod_to_equations; lia).
  assert (U1 : 1 <= usz n) by (unfold usz; lia).
  assert (FL : 1 <= Z.min (usz n) MALLOC_FILL_MAX <= usz n /\ Z.min (usz n) MALLOC_FILL_MAX <= 4096) by (unfold usz, MALLOC_FILL_MAX in *; lia).
  set (fl := Z.min (usz n) MALLOC_FILL_MAX) in *.
  pose proof (t_range st WF) as TR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (BH' : True -> rw_cells asegs m r [CB 16 bj]) by (intros _; exact BH). clear BH. rename BH' into BH.  (* [comment removed for export] *)
  unfold KHIGHMEM_BEG, AIMG_HI in *. idtac. rewrite F2 in *.
  pose proof (munch_refl [(r, r + 16); ((r + 2048) + -16, (r + 2048)); ((r + 2048), (r + 2048) + usz n); (st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912);
                          (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (munch_refl [((r + 2048), (r + 2048) + usz n); (st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU'.
  pose proof (wmono_refl asegs m) as WM.
  assert (HWL : Forall (fun iv : Z * Z => (snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= st_ctx st + 152 \/ st_ctx st + 160 <= fst iv))
            [(r, r + 16); ((r + 2048) + -16, (r + 2048)); ((r + 2048), (r + 2048) + usz n); (st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)]).
  { olin_all. unfold AIMG_LO, AIMG_HI. unfold usz in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on X3 X4 F4 Er ALx OLx X2 HCL LO). }
  (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs m (r + 2048) [] (Z.to_nat (usz n)) uj [] [Z.to_nat fl; Z.to_nat (usz n - fl)]) in USR; [| cbn [sum_nat]; unfold usz in *; lia].
  cbn [mk_CB_cells app] in USR.
  apply (proj1 (rw_cells_app m (r + 2048) [CB (Z.to_nat fl) (firstn (Z.to_nat fl) uj)] _)) in USR as [USR1 USR2].
  cbn [cells_size Cells.csize Nat.add] in USR2. rewrite Nat.add_0_r, Z2Nat.id in USR2 by lia.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_a6s_spec with (lo := lo) (st := st) (n := n) (ub := r + 2048);
    [ exact LC| exact WF| exact MI| exact FC| exact TP| reflexivity| reflexivity| reflexivity| exact Hn| exact HP
    | exact ST| idtac; lia| lia| lia| exact FR| exact TS1| exact TS2 ]) ltac:(clear TS2 TS1 ST).
  cbv beta delta [wz] in *. fold fl.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply memset_spec; [rewrite !unsigned_lit by lia; exact USR1| exact MI1])
         ltac:(unfold memset_post; rewrite !unsigned_lit by (unfold MALLOC_FILL_BYTE; lia); clear USR1).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
  match goal with H : rw_cells _ _ (r + 2048) [CB _ (repeat _ _)] |- _ => rename H into FILL end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
  assert (BH9 : 16 < 2048 -> rw_cells asegs m9 r [CB 16 bj]).
  { intros _. eapply (rw_cells_transport asegs _ m m9); [exact (BH I)| exact MU'| exact WM| cbn; (lia_on M2 X2 X3 TC X4 HCL LO F1 V2 R8 Er SMN TR)]. }
  clear MU' BH.
  assert (LC9 : leafc st m9) by (eapply leafc_out; [exact MU| exact WM| exact HWL| exact LC]).
  match goal with H : stk _ _ lo _ |- _ => rename H into ST9 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp) (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FR9 end.
  match goal with H : rw_cells _ _ ((r + 2048) + -16) _ |- _ => rename H into HDR9 end.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_a7_spec with (st := st) (n := n) (r := r) (id := id) (b1 := b1) (lo := lo) (bj := bj);
    [ exact LC9| exact MI2| exact TP| reflexivity| reflexivity| rewrite F2; reflexivity| rewrite F2; reflexivity| exact Hn| exact Hid| exact Hb1| exact Hb1'
    | unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| Z.div_mod_to_equations; (lia_on M3 Er H H0 H19)| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| (lia_on X3 F6 Er SMN)
    | exact ST9| idtac; lia| lia| lia| exact FR9| rewrite F2; exact HDR9| rewrite F2; exact BH9 ]) ltac:(clear HDR9 ST9).
  cbv beta delta [wz] in *. rewrite F2 in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  apply evt_done. nexists 14%nat.
  match goal with H : Z.land ?b 127 = HDR_BYTE1_MALLOC |- _ => exists b end.
  nexists 4%nat. eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI3|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|].
  split; [match goal with H : 16 < 2048 -> ?X |- _ => exact (H ltac:(lia)) end|].
  split; [eassumption|]. split; [eassumption|].
  apply (proj2 (rw_cells_app _ (r + 2048) [CB _ _] [CB _ _])). split.
  - unfold MALLOC_FILL_BYTE, zb in *. change (190 mod 256) with 190 in FILL. exact FILL.
  - cbn [cells_size Cells.csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. eassumption.
Qed.


End CeilWrap.
End RTW_m_at2s.

(* [comment removed for export] *)
Module RTW_m_at3s.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 RTW_m_at1s RTW_m_at2s OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac c10_split_outside H := lazymatch type of H with _ /\ _ => let H1 := fresh "Ho" in destruct H as [H1 H]; c10_split_outside H | _ => idtac end.
Ltac c10_subfp_slia :=
  lazymatch goal with
  | Hx : (~ _) /\ _ |- (~ _) /\ _ =>
      c10_split_outside Hx;
      repeat match goal with |- _ /\ _ => split end;
      first [ exact I
            | let Cq := fresh "Cq" in intro Cq;
              match goal with Hi : ~ _ |- False => apply Hi; first [exact Cq | lia] end ]
  end.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.slia ::= first [ exact I | c10_subfp_slia | lia | split; [lia|exact I] ].
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition t3s_W (st : rtstate) (mb n SP : Z) : list (Z * Z) :=
  [(SH (sec_user mb + usz n / 8 * 8), SH (sec_user mb + usz n / 8 * 8) + 1);
   (sec_alloc_beg mb, sec_alloc_beg mb + 16); (sec_user mb + -16, sec_user mb); (sec_user mb, sec_user mb + usz n);
   (st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (SP - 32, SP)].

Section AT3S.
Hypothesis poison_shadow_proof : poison_shadow_spec.

Lemma alloc_t3s_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (n mb id b1 lo : Z) (g0 : byte) (j1 j0 bj uj : list byte) (sj0 sj1 sj2 sj3 : word) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  leafc st m -> RTWF st -> mem_inv asegs m -> memtoshadow_cells m -> fill_cells m -> tp = wz ATP ->
  s1 = wz (usz n) -> s2 = wz (sec_alloc_beg mb) -> s3 = wz (needed n) -> s4 = wz (sec_user mb) -> s5 = wz (sec_user mb + -16) ->
  s6 = wz (usz n / 8 * 8) ->
  0 <= n < 2^32 -> bprim n = false -> 0 <= id < 2^32 -> 0 <= b1 < 256 -> Z.land b1 115 = 17 ->
  ablk mb (mb + smapsize n) -> mb + smapsize n <= alloc_ceiling -> mb mod 4096 = 0 ->   (* [comment removed for export] *)
  (st_ctx st + 160 <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= st_ctx st) -> st_ctx st + 160 <= alloc_ceiling -> (mb + smapsize n <= st_ctx st \/ st_ctx st + 160 <= mb) ->
  (st_t st + 4096 <= mb \/ mb + smapsize n <= st_t st) -> (st_ctx st + 160 <= st_t st \/ st_t st + 4096 <= st_ctx st) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2] ->
  rw_cells asegs m (st_t st + 2904) [C8 sj3] ->
  rw_cells asegs m (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)] ->
  rw_cells asegs m (sec_alloc_beg mb) [CB 16 bj] ->
  rw_cells asegs m (sec_user mb) [CB (Z.to_nat (usz n)) uj] ->
  (usz n mod 8 <> 0 -> rw_cells asegs m (SH (sec_user mb + usz n / 8 * 8)) [C1 g0]) ->
  evt asegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (b1' : Z) (sj0' sj1' sj2' sj3' : word)
                               (ujr : list byte) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 128)) gp tp t0' t1' t2' v0 v1 (wz (sec_user mb)) a1' a2' a3' a4' a5' a6' a7'
                    v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6')
               F (ret_pc vra) fc None m' (seg_rom asegs)
      /\ munch (t3s_W st mb n (bv_unsigned sp)) m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp + 128)
      /\ rw_cells asegs m' (sec_user mb + -16) [C1 (zb CHUNK_ALLOCATED); C1 (zb b1'); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]
      /\ Z.land b1' 127 = HDR_BYTE1_MALLOC /\ 0 <= b1' < 256
      /\ rw_cells asegs m' (sec_alloc_beg mb) [C8 (wz KALLOCBEG_MAGIC); C8 (wz (sec_user mb + -16))]
      /\ rw_cells asegs m' (st_t st + 2800) [C8 sj0'; C8 sj1'; C8 sj2']
      /\ rw_cells asegs m' (st_t st + 2904) [C8 sj3']
      /\ rw_cells asegs m' (sec_user mb)
           [CB (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX)) (repeat (zb MALLOC_FILL_BYTE) (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX)));
            CB (Z.to_nat (usz n - Z.min (usz n) MALLOC_FILL_MAX)) ujr]
      /\ (usz n mod 8 <> 0 -> rw_cells asegs m' (SH (sec_user mb + usz n / 8 * 8)) [C1 (zb (usz n mod 8))]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x323ac) fc None m (seg_rom asegs)).
Proof.
  intros until v11. intros LC WF MI MC FC TP -> -> -> -> -> -> Hn HP Hid Hb1 Hb1' M1 M3 M2 X1 X2 X3 TC X4 ST HCL LO SPH FR TS1 TS2 HDR BH USR SHB.
  (nelimp (sec_facts n HP) 6%nat; intros F1 F2 F3 F4 F5 F6). (nelimp (usz_le_rounded8 n) 3%nat; intros U1 U2 U3). pose proof (rounded8_range n Hn) as R8.
  assert (E2 : sec_user mb = mb + 6144) by (unfold sec_user, SEC_HDR, SEC_RZ; lia). assert (E1 : sec_alloc_beg mb = mb + 4096) by reflexivity.
  assert (SMN : rounded8 n + 8192 <= smapsize n) by (unfold smapsize, roundup; rewrite F6; Z.div_mod_to_equations; lia).
  assert (V1 : 1 <= usz n) by (unfold usz; lia).
  pose proof (t_range st WF) as TR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  (nelimp (ablk_lin _ _ M1) 4%nat; intros M1a M1b _ M1d). unfold AIMG_HI in M1a.
  pose proof (rt_SH_mono 6287360 (sec_user mb + usz n / 8 * 8) ltac:(lia)) as SB1. change (SH 6287360) with 0x800b7e00 in SB1.
  pose proof (rt_SH_bounds (sec_user mb + usz n / 8 * 8) ltac:(idtac; lia)) as SB2.
  unfold KHIGHMEM_BEG, AIMG_HI in *. idtac.
  pose proof (munch_refl (t3s_W st mb n (bv_unsigned sp)) m) as MU. unfold t3s_W in MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  assert (TS1' : True -> rw_cells asegs m (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2]) by (intros _; exact TS1).
  assert (TS2' : True -> rw_cells asegs m (st_t st + 2904) [C8 sj3]) by (intros _; exact TS2).
  assert (HDR' : True -> rw_cells asegs m (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)]) by (intros _; exact HDR).
  assert (BH' : True -> rw_cells asegs m (sec_alloc_beg mb) [CB 16 bj]) by (intros _; exact BH).
  assert (USR' : True -> rw_cells asegs m (sec_user mb) [CB (Z.to_nat (usz n)) uj]) by (intros _; exact USR).
  assert (FR' : True -> rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11)) by (intros _; exact FR).
  clear TS1 TS2 HDR BH USR FR.
  pose proof (munch_refl [(SH (sec_user mb + usz n / 8 * 8), SH (sec_user mb + usz n / 8 * 8) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU1.
  leaf_prep.
  (* [comment removed for export] *)
  callxp ltac:(eapply alloc_t1s_post with (st := st) (n := n) (ub := sec_user mb) (lo := lo) (g0 := g0);
    [ exact LC| exact MI| exact MC| reflexivity| reflexivity| reflexivity| exact Hn| eapply ablk_sub; [exact M1| rewrite E2; lia| rewrite E2; unfold usz in *; lia]| idtac; lia| rewrite E2; Z.div_mod_to_equations; lia
    | exact ST| idtac; lia| lia| exact SHB ]) ltac:(clear ST).
  cbv beta delta [wz] in *.
  match goal with H : mem_inv _ _ |- _ => rename H into MI1 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST1 end.
  match goal with H : usz n mod 8 <> 0 -> rw_cells _ _ _ _ |- _ => rename H into SHB1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  assert (DJ : forall a k, (a + k <= 0x7fff7000 \/ 0x10007fff8000 <= a) -> a + k <= bv_unsigned sp - 16 -> 0 <= k ->   (* [comment removed for export] *)
            disjoint_from [(SH (sec_user mb + usz n / 8 * 8), SH (sec_user mb + usz n / 8 * 8) + 1); (bv_unsigned sp - 16, bv_unsigned sp)] a k).
  { intros a k Ha Hk Hk0. cbn. lia. }
  assert (TS1 : rw_cells asegs m5 (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2]) by (eapply (rw_cells_transport asegs _ m m5); [exact (TS1' I)| exact MU1| exact WM| apply DJ; cbn; (cut_on [M3 X2 F1 F4 U2 R8 SMN V1 TR M1 X3 TC X4 HCL LO] blia)]).
  assert (TS2 : rw_cells asegs m5 (st_t st + 2904) [C8 sj3]) by (eapply (rw_cells_transport asegs _ m m5); [exact (TS2' I)| exact MU1| exact WM| apply DJ; cbn; blia]).
  assert (HDR : rw_cells asegs m5 (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (usz n)); C8 (Z_to_bv 64 id)])
    by (eapply (rw_cells_transport asegs _ m m5); [exact (HDR' I)| exact MU1| exact WM| apply DJ; cbn; blia]).
  assert (BH : rw_cells asegs m5 (sec_alloc_beg mb) [CB 16 bj]) by (eapply (rw_cells_transport asegs _ m m5); [exact (BH' I)| exact MU1| exact WM| apply DJ; cbn; blia]).
  assert (USR : rw_cells asegs m5 (sec_user mb) [CB (Z.to_nat (usz n)) uj])
    by (eapply (rw_cells_transport asegs _ m m5); [exact (USR' I)| exact MU1| exact WM| apply DJ; cbn; rewrite ?Z2Nat.id by lia; blia]).
  assert (FR : rw_cells asegs m5 (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11)).
  { eapply (rw_cells_transport asegs _ m m5); [exact (FR' I)| exact MU1| exact WM|]. unfold alloc_frame. cbn. lia. }
  assert (LC5 : leafc st m5).
  { eapply leafc_high; [exact MU1| exact WM| | exact LC]. unfold AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; blia. }
  assert (FC5 : fill_cells m5).
  { eapply fill_cells_high; [exact MU1| | exact FC]. unfold AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
  clear TS1' TS2' HDR' BH' USR' FR' MU1.
  pose proof (munch_refl [(sec_alloc_beg mb, sec_alloc_beg mb + 16); (sec_alloc_beg mb + rz_size n + -16, sec_alloc_beg mb + rz_size n);
                          (sec_alloc_beg mb + rz_size n, sec_alloc_beg mb + rz_size n + usz n);
                          (st_t st + 2800, st_t st + 2824); (st_t st + 2904, st_t st + 2912); (bv_unsigned sp - 32, bv_unsigned sp)] m5) as MU2.
  pose proof (wmono_refl asegs m5) as WM2.
  (* [comment removed for export] *)
  sepM. callxp ltac:(eapply alloc_t2s_spec with (st := st) (n := n) (mb := mb) (id := id) (b1 := b1) (lo := lo) (bj := bj) (uj := uj);
    [ exact LC5| exact WF| exact MI1| exact FC5| exact TP
    | reflexivity| reflexivity| reflexivity| rewrite F2, E2; unfold wz; f_equal; lia| rewrite F2, E2; unfold wz; f_equal; lia
    | exact Hn| exact HP| exact Hid| exact Hb1| exact Hb1'
    | exact M1| idtac; lia| exact M2
    | exact X1| idtac; lia| lia| lia| lia
    | exact ST1| idtac; lia| lia| lia| exact FR| exact TS1| exact TS2
    | rewrite F2; replace (sec_alloc_beg mb + 2048 + -16) with (sec_user mb + -16) by lia; exact HDR
    | exact BH
    | rewrite F2; replace (sec_alloc_beg mb + 2048) with (sec_user mb) by lia; exact USR ]) ltac:(clear USR BH HDR TS2 TS1; clear ST1).
  cbv beta delta [wz] in *. rewrite F2 in *.
  replace (sec_alloc_beg mb + 2048 + -16) with (sec_user mb + -16) in * by lia.
  replace (sec_alloc_beg mb + 2048) with (sec_user mb) in * by lia.
  match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
  apply evt_done. nexists 14%nat.
  match goal with H : Z.land ?b 127 = HDR_BYTE1_MALLOC |- _ => exists b end.
  nexists 4%nat. eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  intros Hz. eapply (rw_cells_transport asegs _ m5); [exact (SHB1 Hz)| exact MU2| exact WM2| cbn; blia].
Qed.
End AT3S.


End CeilWrap.
End RTW_m_at3s.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_spz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Module RTW_m_atails.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_front OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memset OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a5 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a6 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_at1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_atail RTW_m_at1s RTW_m_at3s OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_spz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma sub_fp_app_l : forall W W2, sub_fp W (W ++ W2).
Proof.
  intros W W2 x. induction W as [|[lo hi] W IH]; cbn; [intros _; exact I|].
  intros [H1 H2]. split; [exact H1| apply IH; exact H2].
Qed.

Lemma rw_cells_recast' : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
Lemma CB1_C1 : forall m a j, rw_cells asegs m a [CB 1 j] -> exists b : byte, rw_cells asegs m a [C1 b].
Proof.
  intros m a j H. pose proof H as [[W _] _]. cbn in W. destruct W as [W _]. destruct j as [|b [|]]; cbn in W; try lia.
  exists b. eapply rw_cells_recast'; [exact H| cbn; split; exact I| reflexivity].
Qed.

(* [comment removed for export] *)
Definition atails_W1 (mb n SP : Z) : list (Z * Z) :=
  [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
   (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
   (sec_user mb + -8, sec_user mb); (SP - 1024, SP);
   (SH (sec_user mb), SH (sec_user mb) + usz n / 8 * 8 / 8)].
Definition atails_W (st : rtstate) (mb n SP : Z) : list (Z * Z) := atails_W1 mb n SP ++ t3s_W st mb n SP.

Definition tails_post (vra : word) (SP : Z) (gp tp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (mb n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  fun ms' mo' g' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR vra (wz (SP + 128)) gp tp t0' t1' t2' v0 v1 (wz (sec_user mb)) a1' a2' a3' a4' a5' a6' a7'
                 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 t3' t4' t5' t6') F (ret_pc vra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ g' = g
    /\ RTS (st_liveS st mb n) m' mo' g' /\ stk asegs m' lo (SP + 128)
    /\ cli_pres st (SP + 128) m m' /\ errno_same m m'
    /\ exists junk, rw_cells asegs m' (sec_user mb) [CB (Z.to_nat n) junk]
                    /\ Forall (fun b => b = zb MALLOC_FILL_BYTE) (firstn (Z.to_nat (Z.min n MALLOC_FILL_MAX)) junk).

Section ATAILS.
Hypothesis poison_shadow_proof : poison_shadow_spec.

Lemma alloc_tails_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost) (st : rtstate)
         (n mb id b1 lo : Z) (j1 j8 j0 : list byte) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : word),
  RTS st m mo g -> In (mb, n) (st_spend st) -> bprim n = false -> 0 <= n < 2^32 -> tp = wz ATP ->
  a0 = wz id -> s0 = wz 0 -> s1 = wz (usz n) -> s2 = wz (sec_alloc_beg mb) -> s3 = wz (needed n) -> s4 = wz (sec_user mb) ->
  s5 = wz (sec_user mb + -16) -> s6 = wz A_ALLOC -> s8 = wz 0 -> s9 = wz (sec_user mb + usz n) ->
  0 <= id < 2^32 -> 0 <= b1 < 256 -> Z.land b1 115 = 17 ->
  sec_win g mb n ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp + 128 <= 2^64 ->
  mem_inv asegs m ->
  rw_cells asegs m (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
  rw_cells asegs m (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); CB 8 j8] ->
  LSCPS asegs (tails_post vra (bv_unsigned sp) gp tp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 F fc st mb n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz 0x322a0) fc None m (seg_rom asegs)) mo g.
Proof.
  intros until v11. intros (HR & WF & HM & HG & HF & HSW) HSP HP Hn TP -> -> -> -> -> -> -> -> -> -> Hid Hb1 Hb1' WIN ST HCL LO SPH MI FR HDR. subst tp.
  (nelimp (sec_facts n HP) 6%nat; intros F1 F2 F3 F4 F5 F6). (nelimp (usz_le_rounded8 n) 3%nat; intros U1 U2 U3). pose proof (rounded8_range n Hn) as R8.
  assert (E2 : sec_user mb = mb + 6144) by (unfold sec_user, SEC_HDR, SEC_RZ; lia). assert (E1 : sec_alloc_beg mb = mb + 4096) by reflexivity.
  assert (SMN : rounded8 n + 8192 <= smapsize n) by (unfold smapsize, roundup; rewrite F6; Z.div_mod_to_equations; lia).
  assert (V1 : 1 <= usz n) by (unfold usz; lia). assert (UN : n <= usz n) by (unfold usz; lia).
  pose proof (spz_sec st WF mb n HSP) as HSEC.
  (nelimp (map_range st WF mb n HSEC) 4%nat; intros MR1 MR2 MR3 MR4).
  (nelimp (map_sh_range st WF mb n HSEC) 3%nat; intros MS1 MS2 MS3).
  pose proof (t_vs_map st WF mb n HSEC) as TM. pose proof (t_range st WF) as TR.
  pose proof (prim_vs_map st WF mb n HSEC) as PM. (nelimp (P_range st WF) 3%nat; intros Q1 Q2 _). pose proof (wb_P_S st (wf_base_ok st WF)) as [PS1 PS2].
  (nelim (wb_ctx_loose st (wf_base_ok st WF)) 5%nat; intros cb ck CL1 CL2 CL3).
  pose proof (loose_vs_map st WF mb n HSEC cb ck CL1) as CM. (nelimp (loose0_range st WF cb ck CL1) 4%nat; intros CR1 CR2 CR3 CR4).
  pose proof (wb_ctx_t st (wf_base_ok st WF)) as CT.
  olin_all.   (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (SHu : SH (sec_user mb) = SH mb + 768) by (rewrite E2, rt_SH_aligned_add by (Z.div_mod_to_equations; lia); reflexivity).
  assert (SHe : SH (mb + smapsize n) = SH mb + smapsize n / 8) by (rewrite rt_SH_aligned_add by (Z.div_mod_to_equations; lia); reflexivity).
  assert (SHq : SH (sec_user mb + usz n / 8 * 8) = SH (sec_user mb) + usz n / 8) by (rewrite rt_SH_aligned_add by (rewrite E2; Z.div_mod_to_equations; (lia_on F1 F4 R8 SMN UN MR4 TM CL2 CL3 CM CT H H0 H14)); f_equal; Z.div_mod_to_equations; (lia_on H H0)).
  assert (Q8 : usz n / 8 * 8 / 8 = usz n / 8) by (Z.div_mod_to_equations; (lia_on F1 R8 SMN TM CL2 CL3 CM CT SHq H H0)).
  assert (SHr : SH (sec_alloc_beg mb) = SH mb + 512) by (rewrite E1, rt_SH_aligned_add by (Z.div_mod_to_equations; lia); reflexivity).
  assert (SHt : SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8 = SH mb + smapsize n / 8).
  { rewrite E2. replace (mb + 6144 + rounded8 n) with (mb + (6144 + rounded8 n)) by lia. rewrite rt_SH_aligned_add by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; (lia_on F1 F3 F4 R8 SMN UN TM CL2 CL3 CM CT SHe SHr H H0 H4 H5 H9 H10 H34 H39). }
  pose proof (rt_SH_mono mb (sec_user mb + rounded8 n) ltac:(lia)) as SHv.
  unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. idtac.
  apply lscps_assume. intros NWX HO HB.
  (* [comment removed for export] *)
  pose proof (rtrep_artcells st m HR) as HA.
  pose proof (artcells_icpt m HA) as IC. pose proof (artcells_poison m HA) as PC.
  pose proof (rtrep_fill_cells st m HR HA) as FC. pose proof (rtrep_memtoshadow_cells st m HR HA) as MC.
  pose proof (leafc_of_RTREP st m HR) as LC. clear HA.
  destruct (rr_alloc st m HR) as ((ja1 & ja2 & ja3 & CA0) & (jb1 & jb2 & jb3 & CS0) & _).
  pose proof (rw_cells_take m A_ALLOC [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 ja1; W8 (st_spacebeg st)] _ CA0) as CA. clear CA0.
  pose proof (rw_cells_take m A_SECONDARY [W8 4096] _ CS0) as CS. clear CS0.
  (nelim (proj2 (proj2 (rr_ptrarr st m HR)) (mb, n) HSP) 3%nat; intros VM VS HW0). cbn [fst snd] in VM, VS, HW0.
  pose proof (rw_cells_take m (mb + Z.of_nat (cells_size [W8 mb; W8 (smapsize n)])) [W8 (needed n)] [W8 (sec_index st mb)]
                (rw_cells_drop m mb [W8 mb; W8 (smapsize n)] _ HW0)) as HW. cbn [cells_size Cells.csize Nat.add] in HW. change (Z.of_nat 16) with 16 in HW. clear HW0.
  destruct (vis_carve m _ _ (sec_alloc_beg mb) 16 VM ltac:(lia) ltac:(cbn; lia)) as [bj BH].
  destruct (vis_carve m _ _ (sec_user mb) (Z.to_nat (usz n)) VM ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [uj USR].
  destruct (vis_carve m _ _ (SH (sec_user mb)) (Z.to_nat (usz n / 8 * 8 / 8)) VS ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as [shz SHZ].
  destruct (vis_carve m _ _ (SH (sec_user mb + usz n / 8 * 8)) 1 VS ltac:(lia) ltac:(cbn; Z.div_mod_to_equations; (lia_on F1 F3 F4 U1 R8 SMN UN TM CL2 CL3 CM CT SHu SHq SHr SHt H H0 H4 H5 H34))) as [jg SHG0].
  destruct (CB1_C1 m _ jg SHG0) as [g0 SHG]. clear SHG0.
  destruct (rr_thread st m HR) as (TV & _).
  (nelim (vis_c8x3 m _ _ (st_t st + 2800) TV ltac:(lia) ltac:(lia)) 4%nat; intros sj0 sj1 sj2 TS1).
  destruct (vis_c8 m _ _ (st_t st + 2904) TV ltac:(lia) ltac:(lia)) as [sj3 TS2].
  (* [comment removed for export] *)
  assert (CONT : forall (rax t0x t1x t2x s0x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (m6 : word -> option byte) (mo6 : Model),
    RTMODEL st mo6 -> GWIN st m6 mo6 g -> FRONTR mo6 (g_res g) -> LOK asegs mo6 ->
    mem_inv asegs m6 -> munch (atails_W1 mb n (bv_unsigned sp)) m m6 -> wmono asegs m m6 -> stk asegs m6 lo (bv_unsigned sp) ->
    rw_cells asegs m6 (SH (sec_user mb)) [CB (Z.to_nat (usz n / 8 * 8 / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (usz n / 8 * 8 / 8)))] ->
    rw_cells asegs m6 (sec_user mb + -16) [CB 1 j1; C1 (zb b1); C2 (wz 0); C4 (wz (usz n)); C8 (wz id)] ->
    rw_cells asegs m6 (bv_unsigned sp) (alloc_frame j0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11) ->
    LSCPS asegs (tails_post vra (bv_unsigned sp) gp (wz ATP) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 F fc st mb n lo m g)
      (MS (mkR rax sp gp (wz ATP) t0x t1x t2x s0x (wz (usz n)) a0x a1x a2x a3x a4x a5x a6x a7x
               (wz (sec_alloc_beg mb)) (wz (needed n)) (wz (sec_user mb)) (wz (sec_user mb + -16)) (wz (usz n / 8 * 8)) s7 (wz 0) (wz (sec_user mb + usz n + 7)) s10 s11
               t3x t4x t5x t6x)
          F (wz 0x323ac) fc None m6 (seg_rom asegs)) mo6 g).
  { intros until mo6. intros HM6 HG6 HF6 HO6 MI6 MU6 WM6 ST6 SHZ6 HDR6 FR6.
    (* [comment removed for export] *)
    assert (DJ : forall a k, 0 <= k ->
              (a + k <= SH mb + 512 \/ SH mb + 768 + usz n / 8 <= a) -> (a + k <= SH (sec_user mb + rounded8 n) \/ SH mb + smapsize n / 8 <= a) ->
              (a + k <= sec_user mb + -8 \/ sec_user mb <= a) -> a + k <= bv_unsigned sp - 1024 ->
              disjoint_from (atails_W1 mb n (bv_unsigned sp)) a k).
    { intros a k Hk D1 D2 D3 D4. unfold atails_W1. cbn. (lia_on V1 SHu SHr SHt D1 D2 D3 D4). }
    pose proof (rt_SH_mono (sec_user mb + usz n / 8 * 8) (sec_user mb + rounded8 n) ltac:(Z.div_mod_to_equations; (lia_on F1 F4 U1 R8 SMN UN TM CL2 CL3 CM CT Q8 H H0 H29))) as SHM.
    assert (LC6 : leafc st m6).
    { eapply leafc_high; [exact MU6| exact WM6| | exact LC]. unfold atails_W1, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (cut_on [F1 U2 E2 SMN V1 MR2 MS1 MS3 CL2 CL3 OLx0 ALx SHu SHe SHq Q8 SHr SHt SHM F3 F4 R8 UN MR4 TM CM CT HCL LO CR3] (cut_on [U2 E2 SMN MS1 MS3 CL2 CL3 OLx0 ALx SHu SHe SHq SHr SHt SHM CM HCL LO CR3] (cut_on [U2 E2 SMN MS1 MS3 CL2 CL3 OLx0 SHu SHe SHq SHr SHt SHM CM ALx HCL LO CR3] blia))). }
    assert (MC6 : memtoshadow_cells m6).
    { eapply memtoshadow_cells_high; [exact MU6| | exact MC]. unfold atails_W1, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; blia. }
    assert (FC6 : fill_cells m6).
    { eapply fill_cells_high; [exact MU6| | exact FC]. unfold atails_W1, AIMG_HI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; blia. }
    assert (TS16 : rw_cells asegs m6 (st_t st + 2800) [C8 sj0; C8 sj1; C8 sj2]) by (eapply (rw_cells_transport asegs _ m m6); [exact TS1| exact MU6| exact WM6| apply DJ; cbn; (cut_on [U2 E2 SMN MS1 MS3 SHe SHt F4 TM HCL LO TR] (cut_on [F1 U2 E2 SMN V1 MR2 MS1 MS3 OLx SHu SHe SHq SHt SHM Q8 F4 R8 UN TM CL2 CL3 CM CT HCL LO TR CR3 ALx] blia))]).
    assert (TS26 : rw_cells asegs m6 (st_t st + 2904) [C8 sj3]) by (eapply (rw_cells_transport asegs _ m m6); [exact TS2| exact MU6| exact WM6| apply DJ; cbn; (cut_on [U2 E2 SMN MS1 MS3 SHe SHt F4 TM HCL LO TR] (cut_on [F1 U2 E2 SMN V1 MR2 MS1 MS3 OLx SHu SHe SHq SHt SHM Q8 F4 R8 UN TM CL2 CL3 CM CT HCL LO TR CR3 ALx] blia))]).
    assert (BH6 : rw_cells asegs m6 (sec_alloc_beg mb) [CB 16 bj]) by (eapply (rw_cells_transport asegs _ m m6); [exact BH| exact MU6| exact WM6| apply DJ; cbn; blia]).
    assert (USR6 : rw_cells asegs m6 (sec_user mb) [CB (Z.to_nat (usz n)) uj])
      by (eapply (rw_cells_transport asegs _ m m6); [exact USR| exact MU6| exact WM6| apply DJ; cbn; rewrite ?Z2Nat.id by lia; blia]).
    assert (SHG6 : usz n mod 8 <> 0 -> rw_cells asegs m6 (SH (sec_user mb + usz n / 8 * 8)) [C1 g0]).
    { intros Hz. eapply (rw_cells_transport asegs _ m m6); [exact SHG| exact MU6| exact WM6|].
      pose proof (rt_SH_mono (sec_user mb + usz n / 8 * 8 + 8) (sec_user mb + rounded8 n) ltac:(Z.div_mod_to_equations; (lia_on F1 U1 R8 SMN TM CL2 CL3 CM CT Q8 Hz H H0 H29))) as SHM'.
      rewrite rt_SH_aligned_add in SHM' by (rewrite E2; Z.div_mod_to_equations; (lia_on F1 R8 SMN MR4 TM CL2 CL3 CM CT Q8 Hz H0 H4 H5 H29)). change (8 / 8) with 1 in SHM'.
      apply DJ; cbn; blia. }
    pose proof (munch_weaken _ (atails_W st mb n (bv_unsigned sp)) m m6 (sub_fp_app_l _ _) MU6) as MU. clear MU6.
    unfold atails_W, atails_W1, t3s_W in MU. cbn [app] in MU.
    assert (SHZ6' : True -> rw_cells asegs m6 (SH (sec_user mb)) [CB (Z.to_nat (usz n / 8 * 8 / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (usz n / 8 * 8 / 8)))]) by (intros _; exact SHZ6).
    pose proof (munch_refl (t3s_W st mb n (bv_unsigned sp)) m6) as MU2. unfold t3s_W in MU2. pose proof (wmono_refl asegs m6) as WM2.
    eapply lscps_step_evt. cbv beta delta [wz] in *.
    sepM. sepM. callxp ltac:(eapply alloc_t3s_spec with (st := st) (n := n) (mb := mb) (id := id) (b1 := b1) (lo := lo) (g0 := g0) (bj := bj) (uj := uj);
      [ exact LC6| exact WF| exact MI6| exact MC6| exact FC6| reflexivity
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | exact Hn| exact HP| exact Hid| exact Hb1| exact Hb1'
      | exact MR1| idtac; lia| exact MR4
      | unfold KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG; lia| idtac; lia| (lia_on CL2 CL3 CM)| lia| lia
      | exact ST6| idtac; lia| lia| lia
      | exact FR6| exact TS16| exact TS26| exact HDR6| exact BH6| exact USR6| exact SHG6 ])
      ltac:(unfold t3s_W; clear USR6 BH6 TS26 TS16 HDR6; clear ST6).
    cbv beta delta [wz] in *. try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
    match goal with H : mem_inv _ _ |- _ => rename H into MI7 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
    match goal with H : rw_cells _ m7 (sec_user mb + -16) _ |- _ => rename H into HDRF end.
    match goal with H : rw_cells _ m7 (sec_alloc_beg mb) _ |- _ => rename H into BHF end.
    match goal with H : rw_cells _ m7 (sec_user mb) [CB _ _; CB _ _] |- _ => rename H into USRF end.
    match goal with H : usz n mod 8 <> 0 -> rw_cells _ m7 _ _ |- _ => rename H into SHGF end.
    match goal with H : Z.land ?b 127 = HDR_BYTE1_MALLOC |- _ => rename H into HB1F; rename b into b1f end.
    match goal with H : 0 <= b1f < 256 |- _ => rename H into HB1R end.
    match goal with H : stk _ m7 lo _ |- _ => rename H into STF end.
    match goal with H : wmono asegs m m7 |- _ => rename H into WM end.
    (* [comment removed for export] *)
    assert (SHZ7 : rw_cells asegs m7 (SH (sec_user mb)) [CB (Z.to_nat (usz n / 8 * 8 / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (usz n / 8 * 8 / 8)))]).
    { eapply (rw_cells_transport asegs _ m6 m7); [exact (SHZ6' I)| exact MU2| exact WM2|]. cbn. rewrite ?Z2Nat.id by lia. (lia_on HCL LO F1 F4 U1 U2 R8 E2 E1 SMN V1 MR2 MS1 MS3 OLx OLx0 ALx SHu SHe SHq Q8 SHt SHM). }
    clear SHZ6' MU2.
    apply evt_done. apply lscps_done.
    assert (HWz : Forall (spzc_ok st mb n (bv_unsigned sp + 128)) (atails_W st mb n (bv_unsigned sp))).
    { unfold atails_W, atails_W1, t3s_W, spzc_ok. unfold T_STATS, T_UNWINDING, CEIL.
      sepM. sepM. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on HCL LO U2 E2 SMN V1 SHu SHe SHq SHr SHt F4 E1). }
    unfold tails_post. nexists 15%nat. split; [reflexivity|]. split; [exact MI7|]. split; [reflexivity|].
    split.
    { apply RTS_intro.
      - eapply (RTREP_liveS' st WF mb n HSP _ m m7); [exact (spzc_spz _ _ _ _ _ HWz)| exact MU| exact WM| exact HR|].
        pose proof (spz_rtrep st WF mb n HSP _ (spzc_spz _ _ _ _ _ HWz) m m7 MU WM HR) as HR7.
        (nelim (proj2 (proj2 (rr_ptrarr st m7 HR7)) (mb, n) HSP) 3%nat; intros VM7 VS7 HW7). cbn [fst snd] in VM7, VS7, HW7.
        unfold R_block. split; [| split; [| split; [| split]]].
        + exists (zb b1f), (Z_to_bv 64 id). split.
          * unfold hdr_cells, b_chunk_beg, bm_state, hdr_state_live, size_hi, size_lo.
            replace (usz n / 2 ^ 32) with 0 by (symmetry; apply Z.div_small; unfold usz; lia). rewrite Z.mod_small by (unfold usz; lia).
            replace (sec_user mb - 16) with (sec_user mb + -16) by lia. exact HDRF.
          * unfold hdr_b1_ok. unfold zb. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small b1f) by lia. exact HB1F.
        + unfold R_bighdr, b_alloc_beg, b_chunk_beg. intros _. rewrite F2. replace (sec_user mb - 2048) with (sec_alloc_beg mb) by lia.
          replace (sec_user mb - 16) with (sec_user mb + -16) by lia. exact BHF.
        + unfold R_sechdr. intros _. unfold b_map_beg. replace (sec_user mb - SEC_RZ - SEC_HDR) with mb by (unfold SEC_RZ, SEC_HDR; lia).
          split; [exact VM7| split; [exact VS7| exact HW7]].
        + unfold b_hi, b_lo. rewrite HP, F5. unfold b_map_beg. replace (sec_user mb - SEC_RZ - SEC_HDR) with mb by (unfold SEC_RZ, SEC_HDR; lia). exact VM7.
        + unfold R_bshadow. rewrite HP. unfold shadow_enc.
          destruct (Z.eqb_spec (usz n mod 8) 0) as [Ez|Nz].
          * rewrite app_nil_r. change (repeat 0 (Z.to_nat (usz n / 8))) with (zrep 0 (usz n / 8)).
            apply CB_to_zcells_zrep; [lia|]. rewrite <- Q8. exact SHZ7.
          * rewrite zcells_app'. apply (proj2 (rw_cells_app _ _ _ _)). split.
            -- change (repeat 0 (Z.to_nat (usz n / 8))) with (zrep 0 (usz n / 8)). apply CB_to_zcells_zrep; [lia|]. rewrite <- Q8. exact SHZ7.
            -- rewrite zcells_size_Z. unfold zlen. rewrite repeat_length, Z2Nat.id by lia.
               cbn [zcells map]. rewrite <- SHq. exact (SHGF Nz).
      - apply RTWF_liveS'; [exact WF| exact HP| exact HSP].
      - apply RTMODEL_liveS'. exact HM6.
      - apply GWIN_liveS'. eapply GWIN_mem; [exact HG6| exact HO6| exact WM2].
      - exact HF6.
      - apply SWIN_liveS'. exact HSW. }
    split; [exact STF|].
    split; [eapply (cli_pres_spz st WF mb n HSP); [unfold CEIL; lia| exact MU| exact WM| exact HWz]|].
    split.
    { eapply errno_same_munch; [exact MU|]. unfold AERRNO, ATP.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (lia_on F1 U2 V1 MR2 MS1 OLx0 ALx SHr SHu SHq Q8 SHM E2 HCL LO E1 SMN OLx). }
    (* [comment removed for export] *)
    pose proof (rw_cells_merge asegs m7 (sec_user mb) [] [CB _ _; CB _ _] [] ltac:(rewrite app_nil_r; exact USRF)) as UM.
    cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add] in UM. rewrite app_nil_r, Nat.add_0_r in UM.
    replace (Z.to_nat (Z.min (usz n) MALLOC_FILL_MAX) + Z.to_nat (usz n - Z.min (usz n) MALLOC_FILL_MAX))%nat with (Z.to_nat (usz n)) in UM
      by (unfold MALLOC_FILL_MAX; (lia_on F1 U2 E2 SMN V1 UN MR2 OLx0 ALx)).
    apply (rw_cells_split_CB asegs m7 (sec_user mb) [] (Z.to_nat (usz n)) _ [] [Z.to_nat n; Z.to_nat (usz n - n)]) in UM; [| cbn; lia].
    cbn [mk_CB_cells app] in UM.
    lazymatch type of UM with rw_cells _ _ _ [CB _ ?l1; CB ?n2 ?l2] =>
      apply (proj1 (rw_cells_app m7 (sec_user mb) [CB (Z.to_nat n) l1] [CB n2 l2])) in UM as [UM _] end.
    eexists. split; [exact UM|].
    rewrite firstn_firstn. rewrite Nat.min_l by (unfold MALLOC_FILL_MAX; lia).
    apply fill_prefix. unfold MALLOC_FILL_MAX. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (munch_refl (atails_W1 mb n (bv_unsigned sp)) m) as MU. unfold atails_W1 in MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(SH (sec_alloc_beg mb), SH (sec_alloc_beg mb) + 256);
                (SH (sec_user mb + rounded8 n), SH (sec_user mb + rounded8 n) + (mb + smapsize n - (sec_user mb + rounded8 n)) / 8);
                (sec_user mb + -8, sec_user mb); (bv_unsigned sp - 1024, bv_unsigned sp)] m) as MUp.
  assert (SHZ' : True -> rw_cells asegs m (SH (sec_user mb)) [CB (Z.to_nat (usz n / 8 * 8 / 8)) shz]) by (intros _; exact SHZ). clear SHZ.
  eapply lscps_step_evt. cbv beta delta [wz] in *.
  sepM. sepM. callxp ltac:(eapply (alloc_t1s_pre poison_shadow_proof) with (n := n) (mb := mb) (id := id) (b1 := b1) (P := st_pbase st) (S := st_spacebeg st) (lo := lo);
    [ exact MI| exact IC| exact PC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | exact Hn| exact HP| exact Hid| exact MR1| exact MR4| idtac; lia
    | lia| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| exact PS1| exact PS2
    | exact ST| idtac; lia| lia
    | exact HDR| exact CA| exact CS| exact HW| exact VS ]) ltac:(clear SHG CS CA HDR; clear VS VM ST).
  cbv beta delta [wz] in *. try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  match goal with H : mem_inv _ _ |- _ => rename H into MI5 end.
  match goal with H : stk _ _ lo _ |- _ => rename H into ST5 end.
  match goal with H : rw_cells _ _ (sec_user mb + -16) _ |- _ => rename H into HDR5 end.
  match goal with H : rw_cells _ _ (bv_unsigned sp) (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FR5 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  assert (SHZ5 : rw_cells asegs m5 (SH (sec_user mb)) [CB (Z.to_nat (usz n / 8 * 8 / 8)) shz]).
  { eapply (rw_cells_transport asegs _ m m5); [exact (SHZ' I)| exact MUp| exact WM|]. cbn. rewrite ?Nat.add_0_r, ?Z2Nat.id by lia.
    pose proof (rt_SH_mono (sec_user mb + usz n / 8 * 8) (sec_user mb + rounded8 n) ltac:(Z.div_mod_to_equations; lia)) as SHM. lia. }
  clear SHZ' MUp.
  assert (IC5 : icpt_cells m5) by (eapply icpt_cells_high; [exact MU| | exact IC]; unfold AIMG_HI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  assert (PC5 : poison_cells m5) by (eapply poison_cells_high; [exact MU| | exact PC]; unfold AIMG_HI; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).
  assert (HG5 : GWIN st m5 mo g) by (eapply GWIN_mem; [exact HG| exact HO| exact WM]).
  (* [comment removed for export] *)
  sepM. sepM. callxp ltac:(eapply poison_shadow_proof with (a := sec_user mb) (sz := usz n / 8 * 8) (v := 0) (lo := lo);
    [ exact IC5| exact PC5| exact MI5| exact ST5| idtac; lia| unfold APOISON_STACK; lia| reflexivity| reflexivity| reflexivity
    | rewrite E2; Z.div_mod_to_equations; lia| apply Z_mod_mult| lia
    | apply (ablk_app_range mb (mb + smapsize n)); [exact MR1| lia| lia| lia]| lia
    | intros _; clear - Hn; unfold usz; Z.div_mod_to_equations; lia
    | exact SHZ5 ])
    ltac:(unfold poison_shadow_post, APOISON_STACK; clear SHZ5; clear ST5).
  cbv beta delta [wz] in *.
  replace (ret_pc (Z_to_bv 64 0x323ac)) with (Z_to_bv 64 0x323ac) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  match goal with H : mem_inv _ _ |- _ => rename H into MI6 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
  match goal with H : stk _ m6 lo _ |- _ => rename H into ST6 end.
  match goal with H : rw_cells _ m6 (SH (sec_user mb)) _ |- _ => rename H into SHZ6 end.
  match goal with H : rw_cells _ m6 (sec_user mb + -16) _ |- _ => rename H into HDR6 end.
  match goal with H : rw_cells _ m6 (bv_unsigned sp) (alloc_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _) |- _ => rename H into FR6 end.
  apply evt_done.
  apply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 mo HM ltac:(eapply GWIN_mem; [exact HG| exact HO| exact WM]) HF HO MI6 MU WM ST6 SHZ6 HDR6 FR6).
Qed.
End ATAILS.


End CeilWrap.
End RTW_m_atails.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_lib2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_tpz RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_a3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RTW_m_live.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_nn_specs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_nn_specs.RTW_m_aspec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RTW_m_spz.
Import RTW_m_atails.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_m_mallocN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_m_mallocN.RTW_m_alloc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstateP.RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma map_vs_depot_fp : forall st mb n a, RTWF st -> In (mb, n) (st_sec st) ->
  mb <= a < mb + smapsize n -> ~ in_ivs (depot_fp st) a.
Proof.
  intros st mb n a WF HSEC Ha nelH_; (nelim nelH_ 4%nat; intros lo hi Hin Hr).
  pose proof (map_range st WF mb n HSEC) as (G1 & _).
  unfold depot_fp, fp_depot_blocks in Hin. destruct Hin as [E|Hin].
  - injection E as E1 E2. subst lo hi. unfold A_STACKSTORE, A_DEPOT_MAP1, KHIGHMEM_BEG, AIMG_HI in *. blia.
  - pose proof (wb_pwdj st (wf_base_ok st WF)) as PW. rewrite rt_ranges_tail in PW. apply pwdj_app_r in PW.
    rewrite app_assoc in PW.
    pose proof (pwdj_app_disj _ _ (mb, mb + smapsize n) (lo, hi) PW
      ltac:(apply in_or_app; right; apply in_map_iff; exists (mb, n); split; [reflexivity| exact HSEC]) Hin) as D.
    cbn [fst snd] in D. lia.
Qed.

Section ASEC.
Hypothesis depot_put_proof : depot_put_specS.   (* [comment removed for export] *)
Hypothesis poison_shadow_proof : poison_shadow_spec.

Theorem alloc_sec_proof : alloc_sec_stmt.
Proof.
  unfold alloc_sec_stmt. intros until j0.
  intros RTS1 HTPX WF0 Hn HP TP M1 M2 M3 Esp Esec SC Et Eap Eqp Eqt Eqc Ereg Ecch SOBJ STR1 TRL TRR SPS1 SPS2 ROOM BO1 HDEP GM1 CP01 ES01 ST1 HCL LO SPS MI1 FRA PZ1 PZ2 WIN.
  (nelim RTS1 6%nat; intros HR1 WF1 HM1 HG1 HF1 HSW1). (nelim SC 4%nat; intros Esp0 Elb Elf Etrs).
  (nelimp (sec_facts n HP) 6%nat; intros F1 F2 F3 F4 F5 F6). (nelimp (usz_le_rounded8 n) 3%nat; intros U1 U2 U3). pose proof (rounded8_range n Hn) as R8.
  assert (E2 : sec_user mb = mb + 6144) by (unfold sec_user, SEC_HDR, SEC_RZ; lia). assert (E1 : sec_alloc_beg mb = mb + 4096) by reflexivity.
  assert (SMN : rounded8 n + 8192 <= smapsize n) by (unfold smapsize, roundup; rewrite F6; Z.div_mod_to_equations; lia).
  assert (V1 : 1 <= usz n) by (unfold usz; lia). assert (UN : n <= usz n) by (unfold usz; lia).
  assert (HSP : In (mb, n) (st_spend st1)) by (rewrite Esp; left; reflexivity).
  pose proof (spz_sec st1 WF1 mb n HSP) as HSEC.
  (nelimp (map_sh_range st1 WF1 mb n HSEC) 3%nat; intros MS1 MS2 MS3).
  pose proof (t_vs_map st1 WF1 mb n HSEC) as TM. rewrite Et in TM. pose proof (t_range st WF0) as TR.
  (nelim (wb_ctx_loose st1 (wf_base_ok st1 WF1)) 5%nat; intros cb ck CL1 CL2 CL3).
  pose proof (loose_vs_map st1 WF1 mb n HSEC cb ck CL1) as CM. (nelimp (loose0_range st1 WF1 cb ck CL1) 4%nat; intros CR1 CR2 CR3 CR4).
  pose proof (wb_ctx_t st1 (wf_base_ok st1 WF1)) as CT. rewrite Et in CT.
  (nelimp (map_range st1 WF1 mb n HSEC) 4%nat; intros MR1 MR2 MR3 MR4).
  olin_all.   (* [comment removed for export] *)
  pose proof (wb_sp0 st (wf_base_ok st WF0)) as SP0. unfold AALLOCATE_STACK in LO. unfold BST_SIZE in SPS2.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *. idtac.
  apply lscps_assume. intros NWX HO1 HB1.
  (* [comment removed for export] *)
  (nelim (proj2 (proj2 (rr_ptrarr st1 m1 HR1)) (mb, n) HSP) 3%nat; intros VM VS _). cbn [fst snd] in VM, VS.
  destruct (vis_carve m1 _ _ ((sec_alloc_beg mb + rz_size n) + -16) 16 VM ltac:(lia) ltac:(cbn; lia)) as [hj HDR0].
  destruct (rr_thread st1 m1 HR1) as (_ & (tj1 & tj2 & tj3 & tj4 & tj5 & TT) & _ & _ & TID & _).
  pose proof (rw_cells_merge asegs m1 (st_t st1) [C8 (wz (st_ctx st1))] _ [] ltac:(rewrite app_nil_r; exact TT)) as TT'.
  cbn [cells_size cells_bytes Cells.csize cbytes app Nat.add length] in TT'. clear TT. rewrite Et in TT'.
  pose proof (rw_cells_drop m1 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)] SOBJ) as SO2.
  cbn [cells_size Cells.csize Nat.add] in SO2. change (Z.of_nat 8) with 8 in SO2.
  apply c44_c8 in SO2; [| unfold TRACE_MAX_LEN in TRL; lia].
  pose proof (proj2 (rw_cells_app m1 S [C8 (Z_to_bv 64 (S + 16))] [C8 (Z_to_bv 64 (zlen tr))])
                (conj (rw_cells_take m1 S [C8 (Z_to_bv 64 (S + 16))] [C4 (Z_to_bv 64 (zlen tr)); C4 (Z_to_bv 64 0)] SOBJ) SO2)) as SO.
  clear SO2.
  eapply lscps_step_evt. cbv beta delta [wz] in *. unfold alloc_frame in FRA.
  lstep; if_lia. (* [comment removed for export] *)
  pose proof (munch_refl [((sec_alloc_beg mb + rz_size n) + -16, (sec_alloc_beg mb + rz_size n))] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  callxp ltac:(eapply alloc_a3_spec with (n := n) (r := sec_alloc_beg mb) (t := st_t st) (ctx := st_ctx st1) (S := S) (ntr := zlen tr);
    [ exact MI1| reflexivity| reflexivity| reflexivity| rewrite F2; reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | exact Hn| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| Z.div_mod_to_equations; (lia_on E1 MR4 H H0 H19)
    | unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; (lia_on TR)| unfold KHIGHMEM_BEG, AIMG_HI; lia| idtac; lia| (lia_on F6 E1 SMN TM)| (lia_on F6 E1 SMN CL2 CL3 CM)
    | idtac; lia| lia| unfold TRACE_MAX_LEN in TRL; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | exact HDR0| rewrite unsigned_lit by lia; exact FRA| exact TT'| exact TID| exact SO ]) ltac:(clear TID HDR0 PZ2 PZ1 VS VM).
  cbv beta delta [wz] in *. rewrite F2 in *.
  replace (sec_alloc_beg mb + 2048 + -16) with (sec_user mb + -16) in * by lia.
  replace (sec_alloc_beg mb + 2048) with (sec_user mb) in * by lia.
  match goal with H : mem_inv _ _ |- _ => rename H into MI3 end.
  match goal with H : rw_cells _ _ (sec_user mb + -16) _ |- _ => rename H into HDR3 end.
  match goal with H : Z.land ?b 115 = 17 |- _ => rename H into Hb1; rename b into b1 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
  assert (HW3 : Forall (spzc_ok st1 mb n (bv_unsigned sp)) [(sec_user mb + -16, sec_user mb)]).
  { constructor; [| constructor]. unfold spzc_ok. cbn [fst snd]. left. lia. }
  pose proof (spz_rtrep st1 WF1 mb n HSP _ (spzc_spz _ _ _ _ _ HW3) m1 m3 MU WM HR1) as HR3.
  assert (CP13 : cli_pres st1 (bv_unsigned sp) m1 m3).
  { eapply (cli_pres_spz st1 WF1 mb n HSP); [unfold CEIL; lia| exact MU| exact WM| exact HW3]. }
  assert (STR3 : cells_at asegs m3 (S + 16) (trace_cells tr)).
  { eapply (ro_cells_transport asegs _ m1 m3); [exact STR1| exact MU|]. cbn [disjoint_from]. rewrite trace_cells_size. lia. }
  match goal with H : stk _ m3 lo _ |- _ => rename H into ST3 end.
  match goal with H : rw_cells _ m3 (bv_unsigned sp - 128) _ |- _ => rename H into FR3 end.
  assert (HG3 : GWIN st1 m3 mo1 g1) by (eapply GWIN_mem; [exact HG1| exact HO1| exact WM]).
  assert (ES3 : errno_same m m3).
  { eapply errno_same_trans; [exact ES01|]. eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. unfold AERRNO, ATP. lia. }
  clear MU WM.
  lstep. (* [comment removed for export] *)
  apply evt_done.
  eapply lscps_bind.
  { pose proof depot_put_proof as DP. unfold depot_put_specS in DP. eapply DP with (lo := lo) (P := S + 16) (tr := tr) (st := st1); try reflexivity.
    - exact (RTS_intro _ _ _ _ HR3 WF1 HM1 HG3 HF1 HSW1).
    - exact TRL. - exact TRR.
    - exact STR3.
    - right. rewrite unsigned_lit by lia. lia.
    - idtac. lia.
    - unfold TRACE_MAX_LEN in TRL. lia.
    - exact TP.
    - rewrite Etrs. exact ROOM.
    - unfold budget_ok in BO1. unfold alloc_deposit in HDEP. pose proof (fp_nonneg n ltac:(lia)). pose proof (rp_nonneg n). pose proof (cl24_tax_nonneg n). lia.
    - rewrite unsigned_lit by lia. exact ST3. - idtac; lia. - rewrite unsigned_lit by lia. unfold ADEPOT_STACK. lia.
    - exact MI3. }
  cbv beta. intros ms2 mo2 g2 PO.
  (nelim PO 30%nat; intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 st2 -> MI4 id -> Hid SBD TP2 RTS2 ST4 CP2 RF2 GM2 BO2)
.
  rewrite unsigned_lit in ST4, CP2, RF2 by lia.
  replace (ret_pc (Z_to_bv 64 0x322a0)) with (Z_to_bv 64 0x322a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (nelim RTS2 6%nat; intros HR4 WF2 HM2 HG2 HF2 HSW2).
  destruct SBD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D25 & D26). (* [comment removed for export] *)
  assert (HSP2 : In (mb, n) (st_spend st2)) by (rewrite D23; exact HSP).
  assert (HSEC2 : In (mb, n) (st_sec st2)) by (rewrite D9; exact HSEC).
  (* [comment removed for export] *)
  apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP2) in FR3; [| left; cbn; lia].
  destruct (proj2 (proj2 (rr_ptrarr st2 m4 HR4)) (mb, n) HSP2) as (VM4 & _). cbn [fst snd] in VM4.
  lazymatch type of HDR3 with rw_cells _ _ _ ?cs =>
    assert (HDR4 : rw_cells asegs m4 (sec_user mb + -16) cs) end.
  { eapply (rw_cells_rt_frame _ _ _ _ _ _ _ _ _ RF2 HDR3 VM4); [lia| cbn; lia| lia|].
    intros a Ha. cbn in Ha. split; [lia|]. apply (map_vs_depot_fp st2 mb n a WF2 HSEC2). lia. }
  clear HDR3.
  assert (ES4 : errno_same m m4).
  { eapply errno_same_trans; [exact ES3|]. eapply errno_same_rt_frame; [exact RF2| unfold AERRNO, ATP; lia|].
    intros a Ha. apply (errno_notin_depot_fp st2 a WF2 Ha). }
  assert (GM02 : gmono g g2) by (eapply gmono_trans; [exact GM1| exact GM2]).
  assert (WIN2 : sec_win g2 mb n).
  { intros xw Hxw. pose proof (WIN xw Hxw) as Wx. apply in_winb_true in Wx as (wlo & whi & Win & Wr).
    apply in_winb_true. exists wlo, whi. split; [exact (GM2 _ Win)| exact Wr]. }
  (* [comment removed for export] *)
  eapply lscps_bind.
  { eapply (alloc_tails_spec poison_shadow_proof) with (st := st2) (n := n) (mb := mb) (id := id) (b1 := b1) (lo := lo);
    [ exact (RTS_intro _ _ _ _ HR4 WF2 HM2 HG2 HF2 HSW2)| exact HSP2| exact HP| exact Hn| exact TP
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
    | exact Hid| lia| exact Hb1
    | exact WIN2
    | rewrite unsigned_lit by lia; exact ST4| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
    | exact MI4
    | rewrite unsigned_lit by lia; exact FR3| exact HDR4 ]. }
  cbv beta. intros ms5 mo5 g5 PO.
  (nelim PO 23%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m5 -> MI5 -> RTS5 ST5 CP5 ES5 JK).
  rewrite unsigned_lit in ST5, CP5 by lia. rewrite unsigned_lit by lia.
  replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
  apply lscps_done.
  unfold alloc_post_blk, rt_post_std. nexists 15%nat. exists m5, (st_liveS st2 mb n). split; [reflexivity|]. split; [exact MI5|].
  exists (sec_user mb). split; [reflexivity|].
  (nelimp (st_liveS_same st2 mb n) 11%nat; intros L1 L2 L3 L4 L5 L6 _ L8 L9 L10 _).
  split; [exact RTS5|].
  split; [exact ST5|].
  split.
  { unfold cli_pres in *. rewrite D1, D15, D21 in CP5. rewrite Esp0, Elb, Elf in CP13, CP2, CP5.
    eapply cj_pres_trans; [exact CP01|]. eapply cj_pres_trans; [exact CP13|].
    eapply cj_pres_trans; [eapply cj_pres_weaken; [exact CP2| lia| auto| auto]|]. exact CP5. }
  split; [eapply errno_same_trans; [exact ES4| exact ES5]|].
  split; [exact GM02|].
  split; [rewrite L1, D1; exact Esp0|]. split; [rewrite L3, D15; exact Elf|].
  split.
  { split; [| split; [| split; [| split]]].
    - rewrite L5, D22. exact Eap.
    - rewrite L6, D23, Esp. cbn [remove_first]. rewrite (proj2 (ck_eqb_eq _ _) eq_refl). reflexivity.
    - rewrite L8, D24. exact Eqp.
    - rewrite L9, D25. exact Eqt.
    - rewrite L10, D26. exact Eqc. }
  split; [lia|].
  split.
  { unfold ablock_range, KHIGHMEM_BEG, AIMG_HI. idtac. split; [lia|]. split; [rewrite E2; Z.div_mod_to_equations; lia|]. split; [lia|]. unfold usz in *. lia. }
  split.
  { intros Hin. apply in_map_iff in Hin as ([A' n'] & EA & Hin). cbn in EA. subst A'.
    apply (liveS_fresh' st2 mb n WF2 HP HSP2 (sec_user mb) n'); [| reflexivity].
    unfold all_blocks. apply in_or_app. left. rewrite D21, Elb. exact Hin. }
  split.
  { intros Fr kk Hin. rewrite <- Elf, <- D15 in Hin.
    (nelimp (frame_range st2 WF2 Fr kk Hin) 4%nat; intros Hk X Y AL). change FS_FRAMES_OFF with 36864 in X.
    pose proof (sec_framefree st2 WF2 mb n HSEC2) as D. unfold framefree in D.
    assert (8 <= fsz kk) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia). unfold usz in *. (lia_on F1 F4 U2 E2 TM CL2 CL3 CM CT MR2 OLx0 ALx SP0 X Y AL D). }
  split; [rewrite L2, D21, Elb; reflexivity|].
  split; [rewrite L4, <- Etrs; exact TP2|].
  split.
  { unfold budget_ok in *. rewrite (rt_prov_liveS' st2 mb n ltac:(exact (proj1 (ws_entry st2 (wf_sec_ok st2 WF2) _ HSEC2)))). unfold alloc_deposit. pose proof (cl24_tax_nonneg n). lia. }
  split; [exact JK|].
  pose proof (st_liveS_same st2 mb n) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L22 & _ & _ & _ & _ & _ & L28). (* [comment removed for export] *)
  split; [rewrite L22, D4; exact Ereg| rewrite L28, D6; exact Ecch].
Qed.
End ASEC.


End CeilWrap.
