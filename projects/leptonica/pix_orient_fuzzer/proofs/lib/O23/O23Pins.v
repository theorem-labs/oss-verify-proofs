(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded proofs of need_locks_img and s16_pins, made over the old launch input, replaced by leptonica/kernel_fuzzer's plain proofs, addresses mapped from this unit's LS16 layout and env_ok). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymDrive SymDriveX.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec Hoare AllocIface MemSplit RefLayout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocInv_auxv AllocBase AllocCalloc MallocAllocLayout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23Startup O23StartupDefs O23StartupFacts O23MainEntry O23Open O23Malloc65536 O23Main.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x143fb3) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem s16_pins : @O23Main.pins (@mallocng_alloc_layout LS16).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LS16] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x123c50 <= a)%Z -> (a + Z.of_nat n <= 0x144020)%Z -> (a + Z.of_nat n <= 0x123c7c \/ 0x123c80 <= a)%Z ->
              (a + Z.of_nat n <= 0x143d68 \/ 0x143f88 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 (inpA [a0s; path] envv) a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 (inpA [a0s; path] envv) a_draw tid (Z_to_bv 64 0x143fb3) = None).
      { apply (D_main_none sp0 (inpA [a0s; path] envv) a_draw tid 0x143fb3%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x143fb3%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x143fb3) + Z.of_nat 0)%Z with 0x143fb3%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x143fe0%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + destruct (me_lau _ _ _ _ _ _ ME) as [brk Hlau].
      apply (aux_env_intro (inpA [a0s; path] envv) a_mbase RPH (Z_to_bv 64 (Z.of_N Plain.M.init_pc)) sp0 brk a_draw M
               Hva Hve (me_vl _ _ _ _ _ _ ME) Hlau Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS16]. change (bv_unsigned (Z_to_bv 64 0x143fb0) + 8)%Z with 0x143fb8%Z.
        rewrite (LIBC 0x143fb8%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x112758)) with 0x112758%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
