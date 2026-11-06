(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ALayout APrim ATacA ACells APrimLem F_prim_cid F_prim_popf.
Import ListNotations.
Open Scope Z_scope.

Section CALLOC.
  Context {HC : HasCeiling}.
  Variables (ra gp tp : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q CB : Z) (m0 : mem).

  Definition callocA_post (lo c : Z) (s0 s1 s2 s3 s4 : word) (s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x14 x15 x16 x17 x28 m',
      ms' = MS (mkR ra (wz (q - 48)) gp tp x5 x6 x7 (wz c) (wz (CB + 80 * c)) (wz INSTANCE) (wz CB) x12 (wz 8) x14 x15 x16 x17
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
               F_ (wz 0x37ea4) fc None m' (seg_rom asegs)
      /\ munch [(q - 48, q)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' (q - 48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs m' lo (q - 48).

  #[using="Type"] Lemma calloc_A : forall lo size c (t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    stk asegs m0 lo q -> alloc_ceiling <= lo -> lo <= q - 48 -> q <= 2^47 -> mem_inv asegs m0 ->
    1 <= size <= 65536 -> 0 <= CB < 2^47 ->
    c = (if size <=? 512 then (size + 31) / 32 else cid_code (Z.log2 size) size) -> 1 <= c <= 31 ->
    evt asegs (callocA_post lo c s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6)
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz INSTANCE) (wz CB) (wz size) (wz 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x37cf8) fc None m0 (seg_rom asegs)).
  Proof.
    intros lo size c t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ST CLO LO QH MI SZ HCB Hcid Hc.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (munch_refl [(q - 48, q)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    zstep. carve_frame 48%nat ST.
    do 6 zstep.
    zstep. zstep. zstep.
    replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
    zstep. if_cases K1; zify_cond K1.
    2: { exfalso. rewrite Z.mod_small in K1 by lia. rewrite lxor_ones64' in K1 by lia. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    2: { exfalso. revert K2. clear. intros K2. lia. }
    clear K1 K2.
    destruct (Z.leb_spec size 512) as [SM|BG].
    - eapply evt_cut; [eapply (cid_small _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ size CB); lia|].
      intros ms' (x5 & x6 & x7 & x12 & x14 & x15 & x16 & x17 & x28 & ->).
      rewrite <- Hcid.
      zstep. if_cases K3; zify_cond K3. { exfalso. lia. } clear K3.
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. lia. } clear K4.
      zstep. zstep. zstep.
      replace (q + -48) with (q - 48) in * by lia. replace (CB + c * 80) with (CB + 80 * c) by lia.
      apply evt_done. unfold callocA_post. eexists _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
    - pose proof (Z.log2_spec size ltac:(lia)) as LS.
      assert (L9 : 9 <= Z.log2 size <= 16).
      { split; [change 9 with (Z.log2 512); apply Z.log2_le_mono; lia| change 16 with (Z.log2 65536); apply Z.log2_le_mono; lia]. }
      replace (Z.succ (Z.log2 size)) with (Z.log2 size + 1) in LS by lia.
      eapply evt_cut; [eapply (cid_big _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ size CB _ _ (Z.log2 size)); [lia| exact L9| exact LS]|].
      intros ms' (x5 & x6 & x7 & x12 & x14 & x15 & x16 & x17 & x28 & ->).
      rewrite <- Hcid.
      zstep. if_cases K3; zify_cond K3. { exfalso. lia. } clear K3.
      zstep. zstep. if_cases K4; zify_cond K4. { exfalso. lia. } clear K4.
      zstep. zstep. zstep.
      replace (q + -48) with (q - 48) in * by lia. replace (CB + c * 80) with (CB + 80 * c) by lia.
      apply evt_done. unfold callocA_post. eexists _, _, _, _, _, _, _, _, _, _.
      split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  #[using="Type"] Lemma calloc_hit : forall lo c cnt csz calloc spacebeg v (maxc : word) (ws : list word)
      (x1 t0 t1 t2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0o s1o s2o s3o s4o : word),
    mem_inv asegs m0 -> 1 <= c <= 31 -> 1 <= cnt <= 16 -> 0 <= csz < 2^32 ->
    0 <= spacebeg -> spacebeg + 2^37 <= 2^47 -> 0 <= v < 2^32 ->
    CB mod 8 = 0 -> 0 < CB -> (CB + 2592 <= 0x10000 \/ 0x609000 <= CB) -> CB + 2592 <= lo -> alloc_ceiling <= lo -> lo <= q - 48 -> q <= 2^47 ->
    rw_cells asegs m0 (CB + 80 * c) [C4 (wz cnt); C4 maxc; C8 (wz csz)] ->
    u32arr asegs m0 (CB + 80 * c + 16) ws -> length ws = 16%nat -> nth_error ws (Z.to_nat (cnt - 1)) = Some (wz v) ->
    rw_cells asegs m0 (CB + 2576) [C8 (wz calloc)] ->
    rw_cells asegs m0 721592 [C8 (wz spacebeg)] ->
    rw_cells asegs m0 (q - 48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] -> stk asegs m0 lo (q - 48) ->
    evt asegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' m',
        ms' = MS (mkR ra (wz q) gp tp t0' t1' t2' s0o s1o (wz (spacebeg + c * 4294967296 + 16 * v)) a1' a2' a3' a4' a5' a6' a7'
                      s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                 F_ (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(CB + 80 * c, CB + 80 * c + 4); (CB + 2576, CB + 2584)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
        /\ rw_cells asegs m' (CB + 80 * c) [C4 (wz (cnt - 1)); C4 maxc; C8 (wz csz)]
        /\ u32arr asegs m' (CB + 80 * c + 16) ws
        /\ rw_cells asegs m' (CB + 2576) [C8 (wz (calloc + csz))]
        /\ rw_cells asegs m' 721592 [C8 (wz spacebeg)]
        /\ stk asegs m' lo q)
      (MS (mkR x1 (wz (q - 48)) gp tp t0 t1 t2 (wz c) (wz (CB + 80 * c)) (wz INSTANCE) (wz CB) (wz cnt) (wz 8) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x37eac) fc None m0 (seg_rom asegs)).
  Proof.
    intros until s4o. intros MI Hc Hcnt Hcsz SB0 SB1 Hv CB8 CBL CBI CBH CLO LO QH PC CH LEN NTH STC SBC FR ST.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    demod CB8.
    pose proof (munch_refl [(CB + 80 * c, CB + 80 * c + 4); (CB + 2576, CB + 2584)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    set (pcl := CB + 80 * c) in *. assert (Hpcl : pcl = CB + 80 * c) by reflexivity. clearbody pcl.
    zstep. zstep. zstep.
    zstep.
    zstep. zstep.
    zstep. zstep.
    assert (E4 : Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30 = 4 * (cnt - 1)).
    { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. rewrite Z.mod_small by lia.
      replace ((cnt + -1) * 2 ^ 32) with ((4 * (cnt - 1)) * 2 ^ 30) by lia. apply Z.div_mul. lia. }
    rewrite E4. clear E4.
    pose proof (u32arr_read asegs _ (pcl + 16) ws (cnt - 1) _ (wa (pcl + 16 + 4 * (cnt - 1))) CH NTH ltac:(lia) eq_refl) as HR.
    zstep.
    assert (ZX : zx32 (Z_to_bv 64 v) = Z_to_bv 64 v) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    rewrite ZX. clear ZX HR.
    assert (AMO : amo_aligned AD (Z_to_bv 64 (CB + 2576)) = true) by (apply amo_aligned_intro_d; [lia| rewrite CB0; clear; Z.div_mod_to_equations; lia]).
    amo_step_h AMO.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. if_cases K9; zify_cond K9. 2: { exfalso. revert K9. clear. intros; lia. } clear K9.
    do 6 zstep. zstep. replace (q - 48 + 48) with q by lia. zstep.
    release_frame FR ST q.
    rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (2 ^ 32) with 4294967296.
    replace (v * 16 + (c * 4294967296 + spacebeg)) with (spacebeg + c * 4294967296 + 16 * v) by lia.
    subst pcl. cbn [amo_val] in STC. rewrite ?lit_add_lit in STC.
    apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.
End CALLOC.
