(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep SysMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import PEnv LJ F_mm_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section MMD.
Variable E : penv.

Definition rar_map_entry : Z := 0x7413c.

Definition rar_map_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x28 x29 x30 x31 : word) (H : word -> bool) (beg size lo : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz beg) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range (swlo beg) (swhi beg size) (unhide_range beg (beg + size) H)
    /\ munch [(q - 368, q); (beg, beg + size); (swlo beg, swhi beg size)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' beg [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
    /\ stk asegs m' (swlo beg) (swhi beg size) /\ shvis H' m'
    /\ gmunch [(q - 368, q); (beg, beg + size)] m m'.

Definition rar_mapfod_entry : Z := 0x6c07c.

#[using="Type"] Lemma rar_mapfod_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo beg size : Z),
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> stk asegs m lo q ->
  0x10007fff8000 <= lo -> lo <= q - 368 -> q <= 2^47 ->
  a0 = wz beg -> a1 = wz size ->
  beg mod 4096 = 0 -> size mod 4096 = 0 -> 0x609000 <= beg -> 0 < size -> beg + size <= 2^47 -> app_mem beg size ->
  (beg + size <= lo \/ q <= beg) ->
  implA H (t_commit beg size)
        (rar_map_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H beg size lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz rar_mapfod_entry) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros MI C SV PE ST LO LOQ QHI -> -> AL SL IMG S0 TOP AM SEP. unfold rar_mapfod_entry. pe_split PE.
  assert (LZ : lenZ size = size). { rewrite lenZ_mmap_len by lia. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. nia. }
  assert (S47 : size < 2^47) by lia. rewrite <- LZ in TOP, AM, SEP.
  pose proof (munch_refl [(q - 368, q)] m) as MU.
  pose proof (gmunch_refl [(q - 368, q)] m) as GM.
  pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_commit _ _)).
  lz_go.
  do 3 zstep.
  carve_frame 96%nat ST.
  do 7 zstep.
  do 3 zstep.
  do 3 zstep.
  zstep.   zstep. if_true.
  do 2 zstep.   zstep. if_false.
  do 4 zstep.
  rewrite land_m4096 by lia. replace (size + 4095 - (size + 4095) mod 4096) with size by (Z.div_mod_to_equations; nia).
  zstep. if_true.
  zstep.
  rewrite land_m4096 by lia. replace (beg - beg mod 4096) with beg by lia.
  do 5 zstep.
  zstep.
  call (named_fd_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) lo);
    [assumption| pe_join | replace (q - 96) with (q + -96) by lia; exact ST | lia | lia | lia |].
  replace (q - 96) with (q + -96) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  do 6 zstep.
  zstep. zstep.
  node_commit.
  do 4 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg); [assumption| reflexivity| lia|].
  do 6 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg); [assumption| reflexivity| lia|].
  zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
  zstep. zstep.
  call inc_total_mmap_spec; [assumption| pe_join |].
  do 9 zstep. release_frame FR ST q.
  rewrite LZ in *. lz_ret. unfold rar_map_post. finish.
  - reflexivity.
  - eapply shvis_wmono; [exact SV0| exact WMa].
Qed.

Definition rar_map_post32 (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x28 x29 x30 x31 : word) (H : word -> bool) (beg size lo : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz beg) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range (swlo beg) (swhi beg size) (unhide_range beg (beg + size) H)
    /\ munch [(q - 400, q); (beg, beg + size); (swlo beg, swhi beg size)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' beg [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
    /\ stk asegs m' (swlo beg) (swhi beg size) /\ shvis H' m'
    /\ gmunch [(q - 400, q); (beg, beg + size)] m m'.

#[using="Type"] Lemma rar_map_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo beg size : Z),
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> stk asegs m lo q ->
  0x10007fff8000 <= lo -> lo <= q - 400 -> q <= 2^47 ->
  a1 = wz beg -> a2 = wz size ->
  beg mod 4096 = 0 -> size mod 4096 = 0 -> 0x609000 <= beg -> 0 < size -> beg + size <= 2^47 -> app_mem beg size ->
  (beg + size <= lo \/ q <= beg) ->
  implA H (t_commit beg size)
        (rar_map_post32 ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H beg size lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz rar_map_entry) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros MI C SV PE ST LO LOQ QHI -> -> AL SL IMG S0 TOP AM SEP. unfold rar_map_entry. pe_split PE.
  pose proof (munch_refl [(q - 400, q)] m) as MU.
  pose proof (gmunch_refl [(q - 400, q)] m) as GM.
  pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_commit _ _)).
  carve_frame 32%nat ST.
  lz_go. do 5 zstep.
  do 6 zstep.
  callA (rar_mapfod_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (q - 32) lo beg size);
    [ assumption | assumption | eapply shvis_wmono; [exact SV| exact WM] | pe_join
    | replace (q - 32) with (q + -32) by lia; exact ST | lia | lia | lia | reflexivity | reflexivity
    | lia | lia | lia | lia | lia | assumption | lia |].
  replace (q - 32) with (q + -32) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
  do 6 zstep. release_frame FR ST q.
  lz_ret. unfold rar_map_post32. finish.
  - reflexivity.
  - eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  - pe_join.
  - eapply gmunch_weaken; [| exact GM]. unfold sub_fp; cbn [outside]; intros; lia.
Qed.

Definition rar_mapordie_entry : Z := 0x74288.

#[using="Type"] Lemma rar_mapordie_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo beg size : Z),
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> stk asegs m lo q ->
  0x10007fff8000 <= lo -> lo <= q - 368 -> q <= 2^47 ->
  a1 = wz beg -> a2 = wz size ->
  beg mod 4096 = 0 -> size mod 4096 = 0 -> 0x609000 <= beg -> 0 < size -> beg + size <= 2^47 -> app_mem beg size ->
  (beg + size <= lo \/ q <= beg) ->
  implA H (t_commit beg size)
        (rar_map_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H beg size lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz rar_mapordie_entry) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros MI C SV PE ST LO LOQ QHI -> -> AL SL IMG S0 TOP AM SEP. unfold rar_mapordie_entry. pe_split PE.
  assert (LZ : lenZ size = size). { rewrite lenZ_mmap_len by lia. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. nia. }
  assert (S47 : size < 2^47) by lia. rewrite <- LZ in TOP, AM, SEP.
  pose proof (munch_refl [(q - 368, q)] m) as MU.
  pose proof (gmunch_refl [(q - 368, q)] m) as GM.
  pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_commit _ _)).
  lz_go. do 4 zstep.
  do 3 zstep.
  carve_frame 96%nat ST.
  do 7 zstep.
  do 3 zstep.
  do 3 zstep.
  zstep.   zstep. if_true.
  do 2 zstep.   zstep. if_false.
  do 4 zstep.
  rewrite land_m4096 by lia. replace (size + 4095 - (size + 4095) mod 4096) with size by (Z.div_mod_to_equations; nia).
  zstep. if_true.
  zstep.
  rewrite land_m4096 by lia. replace (beg - beg mod 4096) with beg by lia.
  do 5 zstep.
  zstep.
  call (named_fd_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 96) lo);
    [assumption| pe_join | replace (q - 96) with (q + -96) by lia; exact ST | lia | lia | lia |].
  replace (q - 96) with (q + -96) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  do 6 zstep.
  zstep. zstep.
  node_commit.
  do 4 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg); [assumption| reflexivity| lia|].
  do 6 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ beg); [assumption| reflexivity| lia|].
  zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
  zstep. zstep.
  call inc_total_mmap_spec; [assumption| pe_join |].
  do 9 zstep. release_frame FR ST q.
  rewrite LZ in *. lz_ret. unfold rar_map_post. finish.
  - reflexivity.
  - eapply shvis_wmono; [exact SV0| exact WMa].
Qed.
End MMD.
