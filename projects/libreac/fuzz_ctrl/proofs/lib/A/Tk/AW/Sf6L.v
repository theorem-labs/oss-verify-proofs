(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/As/AllocWalkKit.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Tk/AW/SmLeaf.v, with its module paths, module names and numbers changed; 79 of its 105 lines of code are new or changed and 361 lines of the source are left out. *)
(* __asan_stack_free_6 (0x3dbf4, image A, fuzz_ctrl.asan libreac v1.9.0) with its shadow premise LOCALIZED:
   asan_stack_free_6_contract_L (lib/A/Prog/asan_stack_free_cF.v), which is the frozen asan_stack_free_6_contract
   with `shadow_rw m` replaced by `stk rsegs m (shadow_addr fr) (shadow_addr fr + fs_shadow_n 6 L)` -- the 512
   shadow bytes of the frame, the only shadow the run touches -- and without the post's `shadow_rw m'` conjunct.

   WHY IT EXISTS (rule 24: this is not a second proof of the function).  lib/A/Prog/asan_stack_freeF.v needs the
   walk to run on the restricted memory `MemNormP.normalize_P rsegs P m`, where P keeps only the four regions the
   footprint contract names (the image, [sp - 32, sp), [FS, FS + FS_SIZE), and the frame's 512 shadow bytes).
   That memory does NOT satisfy shadow_rw, which asks every shadow byte of the address space to be readable and
   writable, so Sf6.stack_free_6 cannot be the input of the route-1 lift; this form can.  Weakening a run's
   footprint is not possible after the fact (MemNormP.evtF_RNG_P_weaken_top asks every byte of P to be in RNG),
   so the walk is re-run with the weaker premise instead.

   The script below is Tk/AW/Sf6.v's stack_free_6 (blob of a working branch 81b7f401f87), with exactly
   these changes, and nothing else:
     - the premise `shadow_rw m` becomes the `stk` over [shadow_addr fr, shadow_addr fr + 512);
     - its two uses are replaced: `shadow_stk` (which turned shadow_rw into that stk) is dropped, and the frame's
       shadow window is taken straight from the new premise;
     - the in_shadow cover and the FakeStack/shadow apartness, which Sf6 read off the class-6 shadow region
       [shadow_addr (FS + 6328320), + 131072), are read off the frame's own window instead (shadow_range_in and
       app_shadow_apart at Fa, 512), from fs_place's app_mem cover;
     - the post's last conjunct, shadow_rw m', is gone with its proof (asan_stack_freeF.v re-establishes it on
       the full memory, where shadow_rw does hold, from munch / wmono and the 512 bytes written).
   The helper lemmas are Sf6's, used by path (Sf6.rw_rep_cells), not restated. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c asan_stack_free_c asan_stack_free_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Tac Image ZBridge Arr SysStep.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AK Require Import StepFast StoreFast LiaFix.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLeaf SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Sf6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_ul.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step_core segs R F pc fc rv m ro ::= step_core_fast segs R F pc fc rv m ro.
Local Ltac zsimp ::= zsimp_fast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_guard | solve_load_image ].

Theorem stack_free_6_L : asan_stack_free_6_contract_L.
Proof.
  unfold asan_stack_free_6_contract_L, asan_stack_free_contract_L, ASAN_STACK_FREE_6, ASAN_STACK_FREE_K. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS j.
  intros HJ EFR0 HL HL8 PL FLG0 FLW0 AC SHL0 MI0 ST0 LOK ROOM HLO HHI.
  apply ul_entry. rewrite mkR_ul.
  pose proof (m2s_of_asan m AC) as M2.
  destruct PL as (FS0 & FS4K & FSGT & FAPP & FSTK0).
  assert (STF : stk rsegs m FS (FS + FS_SIZE)) by exact FSTK0. clear FSTK0.
  assert (ST : stk rsegs m lo (bv_unsigned sp)) by exact ST0. clear ST0.
  assert (MI : mem_inv rsegs m) by exact MI0. clear MI0.
  assert (SHL : stk rsegs m (shadow_addr (bv_unsigned a0))
                  (shadow_addr (bv_unsigned a0) + fs_shadow_n 6 (bv_unsigned a1))) by exact SHL0. clear SHL0.
  change (fs_M 6) with 256 in HJ. change (fs_B 6) with 4096 in HL, FLW0.
  remember (FS + 6328320 + j * 4096) as Fa eqn:EFa.
  assert (EFR : fs_frame FS 6 j = Fa).
  { rewrite EFa. unfold fs_frame, fs_B.
    change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + j * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + j * (64 * 64)).
    lia. }
  remember (FS + 36352 + j) as FLG eqn:EFLG.
  assert (EFG : fs_flag FS 6 j = FLG).
  { rewrite EFLG. unfold fs_flag. change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 6) + j) with (FS + 4096 + 32768 - 512 + j).
    lia. }
  rewrite EFR in EFR0. rewrite EFG in FLG0, FLW0. rewrite EFR0 in FLW0.
  replace (Fa + 4096 - 8) with (Fa + 4088) in FLW0 by lia.
  rewrite <- (Z_to_bv_lit_self a0), EFR0.
  assert (FLW : ro_cells rsegs m (Fa + 4088) [C8 (Z_to_bv 64 FLG)]) by (apply ro8; exact FLW0). clear FLW0.
  unfold FS_SIZE, ASAN_GT in *.
  assert (FC : rw_cells rsegs m FLG [C1 (Z_to_bv 8 1)])
    by (apply (stk_rw m FS (FS + 11571200)); [exact STF| apply ro1; exact FLG0| lia| cbn; lia]).
  clear FLG0.
  assert (AFa : app_mem Fa) by (apply FAPP; lia).
  assert (AFL : app_mem FLG) by (apply FAPP; lia).
  (* the frame's own shadow window, from the localized premise *)
  replace (fs_shadow_n 6 (bv_unsigned a1)) with 512 in SHL by reflexivity.
  rewrite EFR0 in SHL.
  remember (shadow_addr Fa) as SA eqn:ESA'.
  rewrite <- ?ESA' in SHL.
  assert (FA8 : Fa mod 8 = 0) by (rewrite EFa; lia).
  assert (SHI : forall y, SA <= y < SA + 512 -> in_shadow y).
  { rewrite ESA'. apply shadow_range_in; [lia| exact FA8| lia|]. intros x Hx. apply FAPP. lia. }
  destruct (stk_junk m SA (SA + 512) SA 512 SHL ltac:(lia) ltac:(lia)) as (j3 & SHC).
  assert (SAL : 0x5fe000 <= SA).
  { pose proof (SHI SA ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  assert (SAU : SA + 512 <= 0x10007fff8000).
  { pose proof (SHI (SA + 511) ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  assert (DFS : FS + 11571200 <= SA \/ SA + 512 <= FS)
    by (apply (app_shadow_apart FS (FS + 11571200) SA 512); [intros x Hx; apply FAPP; lia| lia| exact SHI| lia]).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold HIGHMEM_BEG, APPMEM_END in HLO, HHI.
  clear SHL.
  pose proof (munch_refl [(FLG, FLG + 1); (SA, SA + 512); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST. do 2 zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (m2s_cells_munch m mx _ M2 MU ltac:(repeat constructor; cbn [fst]; lia)) as M2c end.
  zstep. call m2s_spec; [reflexivity| unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AFa; exact AFa
                        | exact M2c| assumption|].
  clear M2c.
  replace (Fa / 8 + 2147450880) with SA by (rewrite ESA'; reflexivity).
  do 3 zstep.
  do 63 (zstep; zstep; zstep; if_cases K; zify_cond K;
         [clear K| exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]]).
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]| clear K].
  do 2 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
  apply evt_done. unfold asan_stack_free_post_L. cbv zeta.
  do 15 eexists. exists mF.
  split; [cbv delta [mkR]; reflexivity|].
  rewrite EFR, EFG, <- ESA'. replace (fs_shadow_n 6 (bv_unsigned a1)) with 512 by reflexivity.
  assert (SHF : bytes_at rsegs mF SA (repeat (Z_to_bv 8 0xf5) (Z.to_nat 512))).
  { change (Z.to_nat 512) with (8 * 64)%nat. eapply Sf6.rw_rep_cells; [exact SHC|].
    first [ reflexivity | vm_compute; reflexivity
          | unfold le8; cbn; repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity ]. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [split; [exact FS0|]; split; [exact FS4K|]; split; [unfold ASAN_GT; lia|]; split; [exact FAPP| exact STF]|].
  split; [apply rw_c1_bytes; exact FC|].
  split; [exact SHF|].
  apply (asan_cells_kept [(FLG, FLG + 1); (SA, SA + 512); (bv_unsigned sp - 32, bv_unsigned sp)] m mF AC MU).
  cbn. try unfold RT_LO, RT_HI. lia.
Qed.
