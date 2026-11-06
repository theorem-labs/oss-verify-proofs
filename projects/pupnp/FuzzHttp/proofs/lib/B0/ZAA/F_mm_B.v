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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import PEnv LJ F_mm_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section MMB.
Variable E : penv.

Definition getpagesize_entry : Z := 0x6b0e0.

Definition getpagesize_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x11 x12 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz 4096) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 544, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ poison_env E m'.

#[using="Type"] Lemma getpagesize_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q lo : Z),
  mem_inv asegs m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 544 -> q <= 2^47 ->
  evt asegs (getpagesize_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 a3 a4 a5 a6 a7 x28 x29 x30 x31 lo m)
    (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz getpagesize_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI PE ST LO LOQ QHI. unfold getpagesize_entry. pe_split PE.
  pose proof (munch_refl [(q - 544, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep.
  carve_frame 544%nat ST.
  do 4 zstep.
  do 4 zstep.
  zstep. zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
  do 4 zstep.
  zstep.
  zstep. if_cases K1; zify_cond K1; [exfalso; clear -K1; vm_compute in K1; lia|].
  zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  do 3 zstep. if_cases K3; zify_cond K3; [exfalso; clear -K3; vm_compute in K3; lia|].
  zstep. zstep. if_cases K4; zify_cond K4; [| exfalso; clear -K4; vm_compute in K4; lia].
  do 3 zstep. zstep. if_false.
  do 8 zstep.
  zstep.
  do 5 zstep.
  zstep. replace (bv_eqb (pe_canary E) (pe_canary E)) with true by (symmetry; apply bv_eqb_refl). cbn [negb].
  do 5 zstep. release_frame FR ST q. unfold getpagesize_post. finish. pe_join.
Qed.

Definition imadvise_entry : Z := 0x6a1dc.

#[using="Type"] Lemma imadvise_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv asegs m -> poison_env E m -> bv_unsigned a2 <> 4 ->
  evt asegs (fun ms' => exists a3',
      ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) a1 a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m (seg_rom asegs)
      /\ munch [] m m /\ wmono asegs m m /\ mem_inv asegs m /\ poison_env E m)
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz imadvise_entry) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI PE NE4. unfold imadvise_entry. pose proof PE as PE0. pe_split PE.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep.   zstep. if_cases K4; zify_cond K4; [exfalso; rewrite ?unsigned_lit in K4 by lia; lia|].
  zstep. zstep. finish.
Qed.

Definition imadvise_dn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x11 x12 x14 x15 x16 x28 x29 x30 x31 : word) (H : word -> bool) (addr len : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists a3' m',
    ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (wz 0) x11 x12 a3' x14 x15 x16 (wz 233) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = hide_range addr (addr + lenZ len) H
    /\ munch [(addr, addr + lenZ len)] m m' /\ wmono_but [(addr, addr + lenZ len)] m m' /\ mem_inv asegs m' /\ poison_env E m'.

#[using="Type"] Lemma imadvise_dontneed_spec : forall (ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (addr len : Z),
  mem_inv asegs m -> mclean H m -> poison_env E m ->
  a0 = wz addr -> a1 = wz len -> a2 = wz 4 ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  implA H (t_madv addr len)
        (imadvise_dn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 a1 a2 a4 a5 a6 x28 x29 x30 x31 H addr len m)
        (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz imadvise_entry) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI C PE -> -> -> AL IMG L0 TOP. unfold imadvise_entry. pose proof PE as PE0. pe_split PE.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [(addr, addr + lenZ len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_madv _ _)).
  lz_go. zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep.   zstep. if_cases K4; zify_cond K4; [| exfalso; rewrite ?unsigned_lit in K4 by lia; lia].
  zstep.
  node_madv.
  zstep.   zstep.
  lz_ret. unfold imadvise_dn_post. finish.
  - reflexivity.
  - pe_join.
Qed.

Definition dontdump_entry : Z := 0x73678.

#[using="Type"] Lemma dontdump_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q lo : Z),
  mem_inv asegs m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 16 -> q <= 2^47 ->
  evt asegs (fun ms' => exists a2' a3' m',
      ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz 1) a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(q - 16, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo q /\ poison_env E m')
    (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (wz dontdump_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros MI PE ST LO LOQ QHI. unfold dontdump_entry. pe_split PE.
  pose proof (munch_refl [(q - 16, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  do 4 zstep.
  call imadvise_spec; [assumption| pe_join| rewrite unsigned_lit by lia; lia|].
  match goal with E0 : poison_env _ _ |- _ => rename E0 into ME end. pe_split ME.
  do 4 zstep. release_frame FR ST q. finish. pe_join.
Qed.

Definition mmap_named_entry : Z := 0x6b9b0.

Definition mmap_named_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x28 x29 x30 x31 : word) (H : word -> bool) (addr len lo : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz addr) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range addr (addr + lenZ len) H
    /\ munch [(q - 320, q); (addr, addr + lenZ len)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' addr [CB (Z.to_nat (lenZ len)) (repeat (Z_to_bv 8 0) (Z.to_nat (lenZ len)))].

#[using="Type"] Lemma mmap_named_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo addr len : Z),
  mem_inv asegs m -> mclean H m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 320 -> q <= 2^47 ->
  a0 = wz addr -> a1 = wz len -> a2 = wz PROT_RW -> a3 = wz MAPF_FIXED_NR ->
  addr mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (addr + lenZ len <= lo \/ q <= addr) -> addr + lenZ len <= 0x10007fff8000 ->
  implA H (t_remap addr len)
        (mmap_named_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H addr len lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz mmap_named_entry) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI C PE ST LO LOQ QHI -> -> -> -> AL IMG L0 TOP SEP SHR. unfold mmap_named_entry. pe_split PE.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [(q - 320, q); (addr, addr + lenZ len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_remap _ _)).
  carve_frame 48%nat ST.
  lz_go. do 5 zstep.
  do 3 zstep.
  do 3 zstep.
  zstep.
  call (named_fd_spec E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (q - 48) lo);
    [assumption| pe_join | replace (q - 48) with (q + -48) by lia; exact ST | lia | lia | lia |].
  replace (q - 48) with (q + -48) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  do 6 zstep.
  zstep. zstep.
  unfold t_remap. node_fixed.
  do 4 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ addr); [assumption| reflexivity| lia|].
  do 7 zstep. release_frame FR ST q. lz_ret. unfold mmap_named_post. finish. reflexivity. pe_join.
Qed.

Definition mmap_fixed_nr_entry : Z := 0x73e94.

Definition mmap_fixed_nr_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x28 x29 x30 x31 : word) (H : word -> bool) (addr len lo : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz 1) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range addr (addr + lenZ len) H
    /\ munch [(q - 368, q); (addr, addr + lenZ len)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' addr [CB (Z.to_nat (lenZ len)) (repeat (Z_to_bv 8 0) (Z.to_nat (lenZ len)))].

#[using="Type"] Lemma mmap_fixed_nr_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo addr len : Z),
  mem_inv asegs m -> mclean H m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 368 -> q <= 2^47 ->
  a0 = wz addr -> a1 = wz len ->
  addr mod 4096 = 0 -> len mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (addr + lenZ len <= lo \/ q <= addr) -> addr + lenZ len <= 0x10007fff8000 ->
  implA H (t_remap addr len)
        (mmap_fixed_nr_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H addr len lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz mmap_fixed_nr_entry) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI C PE ST LO LOQ QHI -> -> AL LL IMG L0 TOP SEP SHR. unfold mmap_fixed_nr_entry. pe_split PE.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  assert (LZ : lenZ len = len). { rewrite lenZ_mmap_len by lia. unfold mmap_len, page_round_up_Z, page_size. Z.div_mod_to_equations. nia. }
  pose proof (munch_refl [(q - 368, q); (addr, addr + lenZ len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_remap _ _)).
  carve_frame 48%nat ST.
  lz_go. do 6 zstep.
  do 6 zstep.
  zstep. if_true.
  do 2 zstep. zstep. if_false.
  do 4 zstep.
  rewrite land_m4096 by lia. replace (len + 4095 - (len + 4095) mod 4096) with len by (Z.div_mod_to_equations; nia).
  zstep. if_true.
  zstep.
  rewrite (Z.land_comm _ addr), land_m4096 by lia. replace (addr - addr mod 4096) with addr by lia.
  do 7 zstep.
  callA (mmap_named_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (q - 48) lo addr len);
    [assumption| assumption| pe_join| replace (q - 48) with (q + -48) by lia; exact ST| lia| lia| lia
    | reflexivity| reflexivity| reflexivity| reflexivity| lia| lia| lia| lia| lia| lia|].
  replace (q - 48) with (q + -48) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  do 5 zstep.
  call (iserror_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ addr); [assumption| reflexivity| lia|].
  zstep. zstep. if_true.
  zstep. zstep.
  call (inc_total_mmap_spec E); [assumption| pe_join|].
  match goal with E0 : poison_env _ _ |- _ => rename E0 into ME end. pe_split ME.
  zstep.   do 8 zstep. release_frame FR ST q.
  lz_ret. unfold mmap_fixed_nr_post. finish. reflexivity. pe_join.
Qed.

Definition mmap_fixed_super_entry : Z := 0x73fc4.

Definition mmap_fixed_super_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (x5 x6 x7 x28 x29 x30 x31 : word) (H : word -> bool) (addr len lo : Z) (m : word -> option byte)
  : unit -> (word -> bool) -> machine_state -> Prop :=
  fun _ H' ms' => exists x11 x12 x13 x14 x15 x16 x17 m',
    ms' = MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 (wz 1) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ H' = unhide_range addr (addr + lenZ len) H
    /\ munch [(q - 400, q); (addr, addr + lenZ len)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo q /\ poison_env E m'
    /\ rw_cells asegs m' addr [CB (Z.to_nat (lenZ len)) (repeat (Z_to_bv 8 0) (Z.to_nat (lenZ len)))].

#[using="Type"] Lemma mmap_fixed_super_spec : forall (ra gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H : word -> bool) (q lo addr len : Z),
  mem_inv asegs m -> mclean H m -> poison_env E m -> stk asegs m lo q -> 0x609000 <= lo -> lo <= q - 400 -> q <= 2^47 ->
  a0 = wz addr -> a1 = wz len ->
  addr mod 4096 = 0 -> len mod 4096 = 0 -> 0x609000 <= addr -> 0 < len < 2^47 -> addr + lenZ len <= 2^47 ->
  (addr + lenZ len <= lo \/ q <= addr) -> addr + lenZ len <= 0x10007fff8000 ->
  implA H (t_remap addr len)
        (mmap_fixed_super_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x5 x6 x7 x28 x29 x30 x31 H addr len lo m)
        (MS (mkR ra (wz q) gp tp x5 x6 x7 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz mmap_fixed_super_entry) fc None m (seg_rom asegs)).
Proof.
  intros until len. intros MI C PE ST LO LOQ QHI -> -> AL LL IMG L0 TOP SEP SHR. unfold mmap_fixed_super_entry. pe_split PE.
  pose proof (lenZ_bound len ltac:(lia)) as LB.
  pose proof (munch_refl [(q - 400, q); (addr, addr + lenZ len)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  rewrite <- (ebind_ret_r (t_remap _ _)).
  carve_frame 32%nat ST.
  lz_go. do 5 zstep.
  do 3 zstep.
  callA (mmap_fixed_nr_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H (q - 32) lo addr len);
    [assumption| assumption| pe_join| replace (q - 32) with (q + -32) by lia; exact ST| lia| lia| lia
    | reflexivity| reflexivity| lia| lia| lia| lia| lia| lia| lia|].
  replace (q - 32) with (q + -32) in * by lia.
  match goal with P : stk asegs _ lo _, E0 : poison_env _ _ |- _ => rename P into ST; rename E0 into ME end. pe_split ME.
  zstep. if_false.
  do 7 zstep.
  zstep. call imadvise_spec; [assumption| pe_join| |].
  {
    pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (pe_nohuge E))) as NR. change (bv_modulus 8) with 256 in NR.
    rewrite unsigned_lit by lia. lia. }
  match goal with E0 : poison_env _ _ |- _ => rename E0 into ME end. pe_split ME.
  do 7 zstep. release_frame FR ST q.
  lz_ret. unfold mmap_fixed_super_post. finish. reflexivity. pe_join.
Qed.

#[using="Type"] Lemma remu_lit : forall a b, 0 <= a < 2^64 -> 0 < b < 2^64 ->
  mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite unsigned_lit by lia. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_modu_unsigned. rewrite (unsigned_lit a), (unsigned_lit b) by lia. rewrite unsigned_lit; [reflexivity|].
  pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

End MMB.
