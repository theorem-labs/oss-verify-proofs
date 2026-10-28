(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocInv_auxv AllocBase AllocCalloc AllocSure AllocCredit MallocAllocLayout.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23FuzzIface V23LeptBase V23LeptOc_iface V23LeptFuzz V23LeptOcW V23LeptUddT V23LeptUddW V23LeptP8Closed V23LeptRoomP8.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rdn_agree_on : forall segs (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (forall x : word, a <= u x < a + Z.of_nat n -> M' x = M x) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros segs M M' a n Ha Hn E. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply E. lia.
Qed.

#[export] Instance u16_lept_pins : @LeptPins (@mallocng_alloc_layout LU16) LLU16.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LLU16 fst snd inZs]; unfold inZ; cbn [fst snd].
  - intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LU16]. exact Ha.
  - intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU16] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x158463 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x158490 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LU16] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU16] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU16] in He. rewrite !u_Z2bv in He by lia. lia.
  - intros a [G1 G2]. cbn [IMG_LO IMG_HI LU16] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU16] in H. lia.
  - intros r H. exact H.
  - reflexivity.
  - intros z Hz. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros z Hz. lia.
  - split; [lia|]. split; [lia|]. intros z Hz. lia.
  - lia.
Qed.

#[export] Instance u16_pins16 : @V23Pins (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem u16_fuzz_call_open : forall (ACR : @AllocCredit (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16)) (STK RK : Z) (RB : Z -> Z -> Z -> Z),
  @pixOrientCorrect_contract (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16) (@acr_sure _ _ ACR) STK RK RB ->
  (STK + 64 <= LSTK)%Z -> (0 <= RK)%Z /\ (RK_deser + RK <= FUZZ_CALLS)%Z ->
  (forall w h cm, (1 <= w <= 20000)%Z -> (1 <= h <= 20000)%Z -> (0 <= RB w h cm)%Z /\ (RB_deser + RB w h cm <= 2 ^ 31 - 2 ^ 26)%Z) ->
  @fuzz_call_contract (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16) (@acr_sure _ _ ACR).
Proof.
  intros ACR STK RK RB HOC HS HK HB.
  exact (@lept_fuzz_call _ _ (@acr_sure _ _ ACR) u16_lept_pins u16_pins16 STK RK RB HOC HS HK HB).
Qed.

(* [comment removed for export] *)
Theorem u16_fuzz_call : forall ACR : @AllocCredit (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16),
  @fuzz_call_contract (@mallocng_alloc_layout LU16) (@mallocng_calloc_layout LU16) (@acr_sure _ _ ACR).
Proof.
  intros ACR.
  exact (u16_fuzz_call_open ACR (OC_STACK UDD_STACK) (RK_oc RK_udd) (RB_oc RB_udd)
           (@pixOrientCorrect_closed_W _ _ (@acr_sure _ _ ACR) u16_lept_pins u16_pins16)
           oc_stack_ok oc_rk_ok RB_oc_fits).
Qed.
