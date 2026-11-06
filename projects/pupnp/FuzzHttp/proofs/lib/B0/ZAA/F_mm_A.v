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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import PEnv LJ.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section MM.
Context {HC : HasCeiling}.
Variable E : penv.

Definition iserror_entry : Z := 0x6a194.

#[using="Type"] Lemma iserror_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  mem_inv asegs m -> a0 = wz r -> 0 <= r <= 2^64 - 4096 ->
  evt asegs (fun ms' => exists a2' a3',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz iserror_entry) fc None m (seg_rom asegs)).
Proof.
  intros until r. intros MI -> R. unfold iserror_entry.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep.
  if_cases K; zify_cond K.
  - zstep. zstep. replace (18446744073709547520 <? r) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. finish.
  - exfalso. lia.
Qed.

Definition inc_total_mmap_entry : Z := 0x6607c.
Definition dec_total_mmap_entry : Z := 0x660c0.

#[using="Type"] Lemma inc_total_mmap_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv asegs m -> poison_env E m ->
  evt asegs (fun ms' => exists a1' a2',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m /\ poison_env E m)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz inc_total_mmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI ME. unfold inc_total_mmap_entry. pose proof ME as ME0. pe_split ME.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep.
  if_true. zstep. finish.
Qed.

#[using="Type"] Lemma dec_total_mmap_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv asegs m -> poison_env E m ->
  evt asegs (fun ms' => exists a0' a1',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m /\ poison_env E m)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz dec_total_mmap_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI ME. unfold dec_total_mmap_entry. pose proof ME as ME0. pe_split ME.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. zstep. if_true. zstep. finish.
Qed.

Definition named_fd_entry : Z := 0x6c580.

#[using="Type"] Lemma named_fd_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q lo : Z),
  mem_inv asegs m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 272 -> q <= 2^47 ->
  evt asegs (fun ms' => exists a2' m',
      ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz (-1)) a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 272, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ poison_env E m')
    (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz named_fd_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI ME ST LO LOQ QHI. unfold named_fd_entry. pe_split ME.
  pose proof (munch_refl [(q - 272, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 272%nat ST.
  Ltac named_fd_tail FR ST q :=
    do 10 zstep; release_frame FR ST q; finish;
    pe_join.
  do 10 zstep.
  zstep. if_cases K.
  -   named_fd_tail FR ST q.
  - do 6 zstep.   if_true. named_fd_tail FR ST q.
Qed.

Definition unmap_or_die_entry : Z := 0x6ba24.

Definition unmap_or_die_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x14 x15 x16 x28 x29 x30 x31 : word) (H : word -> bool) (addr len lo : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x10 x11 x12 x13 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range addr (addr + lenZ len) H
    /\ munch [(q - 48, q); (addr, addr + lenZ len)] m m' /\ wmono_but [(addr, addr + lenZ len)] m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'.

#[using="Type"] Lemma unmap_or_die_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo addr len : Z),
  mem_inv asegs m -> mclean H m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 48 -> q <= 2^47 ->
  a0 = wz addr -> a1 = wz len ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (addr + lenZ len <= lo \/ q <= addr) ->
  implA H (t_unmap addr len)
        (unmap_or_die_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 a4 a5 a6 x28 x29 x30 x31 H addr len lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz unmap_or_die_entry) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI C ME ST LO LOQ QHI -> -> AL IMG L0 TOP SEP. unfold unmap_or_die_entry. pe_split ME.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [(q - 48, q); (addr, addr + lenZ len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_unmap _ _)).
  carve_frame 48%nat ST.
  lz_go. do 5 zstep.
  zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  zstep. zstep. zstep.
  zstep.   zstep.
  node_unmap.
  do 6 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0); [assumption| reflexivity| lia|].
  zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. vm_compute in K2. lia. }
  zstep. zstep.
  call dec_total_mmap_spec; [assumption| pe_join |].
  do 6 zstep. release_frame FR ST q.
  lz_ret. unfold unmap_or_die_post. finish.
  - reflexivity.
  - eapply wmono_but_trans; [exact WM| apply wmono_but_of_wmono; exact WMu].
Qed.

Definition mmap_or_die_entry : Z := 0x6baa0.

Definition mmap_or_die_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x28 x29 x30 x31 : word) (H : word -> bool) (size lo : Z) (avoid : list (Z * Z)) (m : word -> option byte)
  : Z -> (word -> bool) -> machine_state -> Prop :=
  fun a H' ms' => exists x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz a) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range (swlo a) (swhi a size) (unhide_range a (a + size) H)
    /\ munch [(q - 320, q); (a, a + size); (swlo a, swhi a size)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ a mod 4096 = 0 /\ 0x609000 <= a /\ app_mem a size /\ anon_place a size
    /\ Forall (fun iv => a + size <= fst iv \/ snd iv <= a) avoid
    /\ rw_cells asegs m' a [CB (Z.to_nat size) (repeat (Z_to_bv 8 0) (Z.to_nat size))]
    /\ stk asegs m' (swlo a) (swhi a size) /\ shvis H' m'
    /\ gmunch [(q - 320, q); (a, a + size)] m m'.

#[using="Type"] Lemma mmap_or_die_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo size alo ahi : Z) (avoid : list (Z * Z)),
  mem_inv asegs m -> mclean H m -> shvis H m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 320 -> q <= 2^47 ->
  a0 = wz size -> size mod 4096 = 0 -> 0 < size < 2^47 ->
  In (alo, ahi) avoid -> alo <= lo -> q <= ahi ->
  implA H (t_anon size avoid)
        (mmap_or_die_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H size lo avoid m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz mmap_or_die_entry) fc None m (seg_rom asegs)).
Proof.
  intros until avoid. intros MI C SV ME ST LO LOQ QHI -> AL SZ AIN ALO AHI. unfold mmap_or_die_entry. pe_split ME.
  pose proof (lenZ_bound size ltac:(lia)) as LB.
  assert (LZ : lenZ size = size). { rewrite lenZ_mmap_len by lia. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. nia. }
  pose proof (munch_refl [(q - 320, q)] m) as MU. pose proof (wmono_refl asegs m) as WM. pose proof (gmunch_refl [(q - 320, q)] m) as GM.
  rewrite <- (ebind_ret_r (t_anon _ _)).
  carve_frame 48%nat ST.
  lz_go. do 5 zstep.
  do 4 zstep.
  zstep.
  zstep. if_true.
  do 3 zstep.   if_false.
  do 4 zstep.
  rewrite land_m4096 by lia. replace (size + 4095 - (size + 4095) mod 4096) with size by (Z.div_mod_to_equations; nia).
  do 5 zstep.
  zstep.
  call (named_fd_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 48) lo);
    [assumption| pe_join | replace (q - 48) with (q + -48) by lia; exact ST | lia | lia | lia |].
  replace (q - 48) with (q + -48) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  do 6 zstep.
  zstep. zstep.
  node_anon.
  do 4 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a); [assumption| reflexivity| lia|].
  do 6 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a); [assumption| reflexivity| lia|].
  zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
  zstep. zstep.
  call inc_total_mmap_spec; [assumption| pe_join |].
  do 7 zstep. release_frame FR ST q.
  rewrite LZ in *. lz_ret. unfold mmap_or_die_post. finish.
  - reflexivity.
  - eapply shvis_wmono; [exact SV0| exact WMa].
Qed.
End MM.
