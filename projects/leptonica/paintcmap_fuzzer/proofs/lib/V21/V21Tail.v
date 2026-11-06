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
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21Kit.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21Drv1.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptBase.
Module V21LeptPinsA.
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
Import OSSVerify.leptonica.paintcmap_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptDefs.
Import V21Kit.
Import V21Drv1.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptBase.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V21Kit.V21MallocLayout.

Import V21Drv1.V21FuzzIface.

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

#[export] Instance u21_lept_pins : @LeptPins (@mallocng_alloc_layout LU21) LLU21.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LLU21 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LU21]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU21] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x524ab 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x524d8 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LU21] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU21] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU21] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LU21] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU21] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU21] in H. lia.
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

#[export] Instance u21_pins16 : @V21Pins (@mallocng_alloc_layout LU21) (@mallocng_calloc_layout LU21).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.
End V21LeptPinsA.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptStderr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptUb.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21CL7a.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21CL8a.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptCmapValid.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21CL9a.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptDeser.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptBox.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptCmap2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptPixCopyA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptPixCopy.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptSelCmap.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21LeptSelMasked.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21_code_136d4_14000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21_code_14000_15000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21_code_15000_16000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21_code_16000_17000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21_code_17000_18000.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
Module V21LeptFuzz.
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
Import OSSVerify.leptonica.paintcmap_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptArith2.
Import V21Drv1.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptStderr.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptUb.
Import V21CL7a.
Import V21CL8a.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptCmapValid.
Import V21CL9a.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptDeser.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptBox.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptCmap2.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptPixCopyA.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptPixCopy.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptSelCmap.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptSelMasked.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21_code_136d4_14000.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21_code_14000_15000.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21_code_15000_16000.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21_code_16000_17000.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21_code_17000_18000.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptRoomPC.
(* [comment removed for export] *)
(* [comment removed for export] *)








Import V21Drv1.V21FuzzIface.


Import V21CL7a.V21LeptErr.

Import V21CL8a.V21LeptPixHdr.


Import V21CL9a.V21LeptPixDestroy.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rebase.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure} {LL : LeptLayout} {PINS : @LeptPins AL LL}.

Definition rebase (C : lctx) (m : word -> option byte) (A : AS) : lctx :=
  LCTX (c_sp0 C) (c_argv C) (c_envp C) (c_top C) (c_vm C) m A.

Lemma Cok_rebase : forall C m A, Cok C -> Cok (rebase C m A).
Proof. intros C m A [T1 T2 T3 T4 T5]. constructor; cbn; assumption. Qed.

Lemma W_rebase : forall C A m md, W C A m md -> W (rebase C m A) A m md.
Proof.
  intros C A m md HW. destruct HW. constructor; cbn; try assumption.
  - intros a _ _ _ _ _. reflexivity.
  - intros q k L. exact L.
  - intros q k i _ _. reflexivity.
  - intros a D. right; right. exact D.
Qed.

Lemma W_unbase : forall C A1 m1 md1 A m md, W C A1 m1 md1 -> W (rebase C m1 A1) A m md -> W C A m md.
Proof.
  intros C A1 m1 md1 A m md W1 W2. destruct W1 as [I1 P1 E1 V1 WN1 CL1 H1 F1 K1 L1 D1]. destruct W2 as [I2 P2 E2 V2 WN2 CL2 H2 F2 K2 L2 D2].
  cbn in *. constructor; try assumption.
  - intros a N1 N2 N3 N4 N5. rewrite (F2 a N1 N2 N3 N4 N5). exact (F1 a N1 N2 N3 N4 N5).
  - intros q k L. exact (K2 q k (K1 q k L)).
  - intros q k i L Hi. rewrite (L2 q k i (K1 q k L) Hi). exact (L1 q k i L Hi).
  - intros a D. destruct (D1 a D) as [X|[X|X]]; [left; exact X | right; left; exact X |]. exact (D2 a X).
Qed.

(* [comment removed for export] *)
Lemma W_blk0 : forall C A m md (p k : Z) (x : word), Cok C -> W C A m md ->
  live (c_A0 C) (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= 2 ^ 64)%Z -> (p <= bv_unsigned x < p + k)%Z -> m x = c_m0 C x.
Proof.
  intros C A m md p k x CK HW L Hp Hpk Hx.
  pose proof (w_live0 _ _ _ _ HW (Z_to_bv 64 p) k (bv_unsigned x - p)%Z L ltac:(lia)) as E.
  replace (at_ (Z_to_bv 64 p) (bv_unsigned x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact E.
Qed.
End Rebase.

Section FuzzSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU21} {P16 : V21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Definition FZ3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_small : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13d48 : word) m rom) (mkst regs' ret (FZ3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FZ3. eexists. split.
    - zv F_13c44 D_13c44 (Z_to_bv 64 (s - 48)).
      stepST F_13c48 D_13c48 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13c4c D_13c4c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13c50 D_13c50 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13c54 D_13c54. sn F_13c58 D_13c58. stepb_tk F_13c5c D_13c5c ltac:(condZ).
      sn F_13d1c D_13d1c.
      stepLD8 F_13d20 D_13d20 ret. stepLD8 F_13d24 D_13d24 (getr regs 8). stepLD8 F_13d28 D_13d28 (getr regs 9).
      zv F_13d2c D_13d2c (Z_to_bv 64 s). stepret F_13d30 D_13d30 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_A : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    store_ok SEGS m (Z_to_bv 64 0x21ed0) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x13d48 : word) m rom)
                              (mkst regs' (0x172cc : word) (wbytes (FZ3 m s ret regs) (Z_to_bv 64 0x21ed0) (word_to_le_bytes 8 (Z_to_bv 64 0x13e38))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13d80 /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FZ3. eexists. split.
    - zv F_13c44 D_13c44 (Z_to_bv 64 (s - 48)).
      stepST F_13c48 D_13c48 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_13c4c D_13c4c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_13c50 D_13c50 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_13c54 D_13c54. sn F_13c58 D_13c58. stepb_ft F_13c5c D_13c5c ltac:(condZ).
      sn F_13c60 D_13c60. sn F_13c64 D_13c64. sn F_13c68 D_13c68. sn F_13c6c D_13c6c.
      stepb_tk F_13e54 D_13e54 ltac:(condZ).
      sn F_13e60 D_13e60.
      stepST F_13e64 D_13e64 (Z_to_bv 64 0x21ed0) (Z_to_bv 64 0x13e38) ltac:(store_ok_peel; exact SOKh).
      stepret F_13e68 D_13e68 (0x13d74 : word) ltac:(bveq).
      sn F_13c70 D_13c70. sn F_13c74 D_13c74. sn F_13c78 D_13c78. sn F_171c4 D_171c4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x13d80 : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret SOK R1 R2 R3 H2 H10. eexists. split.
    - stepST F_13c7c D_13c7c (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_13c80 D_13c80 ltac:(condZ).
      sn F_13d1c D_13d1c.
      stepLD8 F_13d20 D_13d20 ret. stepLD8 F_13d24 D_13d24 s0v. stepLD8 F_13d28 D_13d28 s1v.
      zv F_13d2c D_13d2c (Z_to_bv 64 s). stepret F_13d30 D_13d30 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x13d80 : word) m rom) (mkst regs' (0x14158 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13da0 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ getr regs' 10 = Z_to_bv 64 278 /\ getr regs' 11 = Z_to_bv 64 35 /\ getr regs' 12 = Z_to_bv 64 122 /\ getr regs' 13 = Z_to_bv 64 50
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof.
    intros regs m s pix Hs Hs64 Hp Hp64 SOK H2 H10. eexists. split.
    - stepST F_13c7c D_13c7c (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_13c80 D_13c80 ltac:(condZ).
      sn F_13c84 D_13c84. sn F_13c88 D_13c88. sn F_13c8c D_13c8c. sn F_13c90 D_13c90. sn F_13c94 D_13c94. sn F_13c98 D_13c98. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_C : forall regs m (s pix bx : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= bx < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 bx -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x13da0 : word) m rom) (mkst regs' (0x15124 : word) (wbytes m (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 bx))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13db4 /\ getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 9 = Z_to_bv 64 bx
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pix bx Hs Hs64 Hbx SOK H2 H10 H8. eexists. split.
    - sn F_13c9c D_13c9c.
      stepST F_13ca0 D_13ca0 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 bx) ltac:(sok_in SOK).
      sn F_13ca4 D_13ca4. sn F_13ca8 D_13ca8. sn F_13cac D_13cac. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_D : forall regs m (s pixd bx : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 9 = Z_to_bv 64 bx ->
    exists regs', msteps SEGS (mkst regs (0x13db4 : word) m rom) (mkst regs' (0x168ac : word) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13dd0 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 bx
      /\ getr regs' 12 = Z_to_bv 64 2 /\ getr regs' 13 = Z_to_bv 64 255 /\ getr regs' 14 = Z_to_bv 64 255 /\ getr regs' 15 = Z_to_bv 64 100
      /\ regs_agree (fun r => In r [1; 11; 12; 13; 14; 15]%list) regs regs'.
  Proof.
    intros regs m s pixd bx Hs Hs64 Hp SOK H2 H10 H9. eexists. split.
    - stepST F_13cb0 D_13cb0 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      sn F_13cb4 D_13cb4. sn F_13cb8 D_13cb8. sn F_13cbc D_13cbc. sn F_13cc0 D_13cc0. sn F_13cc4 D_13cc4. sn F_13cc8 D_13cc8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_E : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13dd0 : word) m rom) (mkst regs' (0x142d4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13dd8 /\ getr regs' 10 = Z_to_bv 64 (s - 40)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_13ccc D_13ccc (Z_to_bv 64 (s - 40)). sn F_13cd0 D_13cd0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_F : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13dd8 : word) m rom) (mkst regs' (0x149ac : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13de0 /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_13cd4 D_13cd4 (Z_to_bv 64 (s - 48)). sn F_13cd8 D_13cd8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_G : forall regs m (s pix : Z),
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x13de0 : word) m rom) (mkst regs' (0x15124 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13dec /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s pix H2 H8. eexists. split.
    - sn F_13cdc D_13cdc. sn F_13ce0 D_13ce0. sn F_13ce4 D_13ce4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_H : forall regs m (s pixd : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pixd ->
    exists regs', msteps SEGS (mkst regs (0x13dec : word) m rom) (mkst regs' (0x16da0 : word) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13e10 /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [1; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp SOK H2 H10. eexists. split.
    - stepST F_13ce8 D_13ce8 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      sn F_13cec D_13cec. sn F_13cf0 D_13cf0. sn F_13cf4 D_13cf4. sn F_13cf8 D_13cf8. sn F_13cfc D_13cfc. sn F_13d00 D_13d00. sn F_13d04 D_13d04.
      sn F_13d08 D_13d08. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_I : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13e10 : word) m rom) (mkst regs' (0x149ac : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13e18 /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_13d0c D_13d0c (Z_to_bv 64 (s - 48)). sn F_13d10 D_13d10. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_J : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13e18 : word) m rom) (mkst regs' (0x149ac : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x13e20 /\ getr regs' 10 = Z_to_bv 64 (s - 32)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_13d14 D_13d14 (Z_to_bv 64 (s - 32)). sn F_13d18 D_13d18. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_Z : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x13e20 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_13d1c D_13d1c.
      stepLD8 F_13d20 D_13d20 ret. stepLD8 F_13d24 D_13d24 s0v. stepLD8 F_13d28 D_13d28 s1v.
      zv F_13d2c D_13d2c (Z_to_bv 64 s). stepret F_13d30 D_13d30 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pixDestroy_null : forall regs m (s pp : Z) (ret : word),
    (32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= 2 ^ 64)%Z -> (pp mod 8 = 0)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pp ->
    exists regs', msteps SEGS (mkst regs (0x149ac : word) m rom)
      (mkst regs' ret (wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
                                  (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 11]%list) regs regs'.
  Proof.
    intros regs m s pp ret Hs Hpp Hpp64 ALpp Hret SOK Rpp H2 H1 H10. eexists. split.
    - zv F_148a8 D_148a8 (Z_to_bv 64 (s - 32)).
      stepST F_148ac D_148ac (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_148b0 D_148b0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_148b4 D_148b4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepb_ft F_148b8 D_148b8 ltac:(condZ).
      guard8 F_148bc D_148bc ALpp. stepb_ft F_148c0 D_148c0 ltac:(condZ). (* [comment removed for export] *)
      stepLD F_148c4 D_148c4 (Z_to_le_bytes 8 0) (Z_to_bv 64 0) ltac:(addr_norm; rewrite ?Z.add_0_r; repeat rdn_peel1; exact Rpp) ltac:(apply lez8; lia).
      stepb_tk F_148c8 D_148c8 ltac:(condZ).
      stepLD8 F_14970 D_14970 ret. stepLD8 F_14974 D_14974 (getr regs 8). stepLD8 F_14978 D_14978 (getr regs 9).
      zv F_1497c D_1497c (Z_to_bv 64 s). stepret F_14980 D_14980 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End FuzzSegs.

Section Phases.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU21} {P16 : V21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma pixDestroy_null_W : forall C A m md regs (s pp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 32 <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> (forall x : word, ~ (s - 32 <= u x < s)%Z -> m' x = m x) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x149ac : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp ret S CK HW H2 Hlo Hpp Hpphi ALpp H1 Hret H10 Rpp HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *.
  destruct (pixDestroy_null al_rom regs m s pp ret ltac:(lia) Hpp ltac:(lia) ALpp Hret (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) Rpp H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  apply (HK M1 r1 HW1).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM1.
  - intros x Hx. subst M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
Qed.

  Variables (C : lctx) (A A1 : AS) (m2 : word -> option byte) (md0 : Model) (vm1 : VmMaps).
  Variables (s : Z) (ret : word) (regs : bvmap 5 word) (S : TSet).
  Variables (pixs w h d cm datas : Z) (cv : cmapv).
  Variables (kR bR : Z).
  Let C1 := rebase C m2 A1.

  Hypothesis CK : Cok C.
  Hypothesis Hs16 : (s mod 16 = 0)%Z.
  Hypothesis Htop : c_top C = s.
  Hypothesis HA0 : c_A0 C = A.
  Hypothesis Hret : ret_ok ret.
  Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x32220.
  Hypothesis HW2 : W C A1 m2 (with_vmmaps vm1 md0).
  Hypothesis PXs : PIXat m2 pixs (hdv w h d cm datas).
  Hypothesis HOK : hdr_ok w h d.
  Hypothesis Hw : (1 <= w)%Z.
  Hypothesis Hh : (1 <= h)%Z.
  Hypothesis Lps : live A1 (Z_to_bv 64 pixs) = Some 64%Z.
  Hypothesis Lds : live A1 (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z.
  Hypothesis L0ps : live A (Z_to_bv 64 pixs) = None.
  Hypothesis L0ds : live A (Z_to_bv 64 datas) = None.
  Hypothesis NEsd : boxed (datas <> pixs).
  Hypothesis HCM : boxed (cm = 0%Z \/ ((1 <= cm)%Z /\ CMAPat m2 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                    live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
                    cm <> c_arr cv /\ cm <> pixs /\ c_arr cv <> pixs /\ datas <> cm /\ datas <> c_arr cv)).
  Hypothesis LEQ1 : forall q, q <> Z_to_bv 64 pixs -> q <> Z_to_bv 64 datas -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv)) -> live A1 q = live A q.
  Hypothesis R8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret).
  Hypothesis R16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)).
  Hypothesis R24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)).
  Hypothesis R32 : rdn SEGS m2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixs)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hrm : aroom A1 vm1 (kR - RK_deser) (bR - RB_deser).
  Hypothesis Hrk : (RK_paintcmap <= kR)%Z.
  Hypothesis Hrb : (RB_paintcmap <= bR)%Z.
  Hypothesis KF : forall A' m' vm' r', W C A' m' (with_vmmaps vm' md0) -> (forall q, live A' q = live A q) ->
    getr r' 10 = Z_to_bv 64 0 -> cs_kept regs r' -> aroom A' vm' (kR - RK_paintcmap) (bR - RB_paintcmap) -> realizes SEGS (mkCfg (mkst r' ret m' al_rom) (with_vmmaps vm' md0)) S.

  Lemma CK1 : Cok C1. Proof. exact (Cok_rebase C m2 A1 CK). Qed.

  (* [comment removed for export] *)
  Ltac nin_cs Hx := let H := fresh in pose proof Hx as H; unfold cs_rest in H; cbn in H; repeat (destruct H as [<-|H]; [notin_list|]); destruct H.

  (* [comment removed for export] *)
  Lemma later_cells : forall Ak mk mdk, W C1 Ak mk mdk -> FRM C1 (s - 32) m2 mk ->
    rdn SEGS mk (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS mk (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
    rdn SEGS mk (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
    rdn SEGS mk (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixs)).
  Proof.
    intros Ak mk mdk HW F. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
    rewrite !(FRM_rdn16 C1 (s - 32) m2 mk _ 8 CK1 F) by (cbn; lia). repeat split; assumption.
  Qed.

  Lemma later_pixs : forall Ak mk mdk, W C1 Ak mk mdk ->
    PIXat mk pixs (hdv w h d cm datas) /\ (cm <> 0%Z -> CMAPat mk cm cv).
  Proof.
    intros Ak mk mdk HW. pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof PXs as (Hp0 & Hp64 & _).
    destruct (blk_range C A1 m2 _ (Z_to_bv 64 pixs) 64 CK HW2 Lps ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
    split.
    - apply (PIXat_frame m2); [exact PXs|]. intros x Hx. exact (W_blk0 C1 Ak mk mdk pixs 64 x CK1 HW Lps ltac:(lia) ltac:(lia) Hx).
    - intros NZ. destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & _ & Lc & _)]; [exfalso; exact (NZ Z0)|]. pose proof CM as (Hc0 & Hc64 & _).
      apply (CMAPat_frame m2); [exact CM|]. intros x Hx. exact (W_blk0 C1 Ak mk mdk cm 24 x CK1 HW Lc ltac:(lia) ltac:(lia) Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma PH5 : forall A7 m9 vm7 r,
    W C1 A7 m9 (with_vmmaps vm7 md0) -> aroom A7 vm7 (kR - RK_paintcmap) (bR - RB_paintcmap) -> FRM C1 (s - 32) m2 m9 -> (forall q, live A7 q = live A1 q) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x13e18 : word) m9 al_rom) (with_vmmaps vm7 md0)) S.
  Proof.
    intros A7 m9 vm7 r HW9 Hrm7 F9 LQ7 Q2 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof PXs as (Hp0 & Hp64 & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data hdv] in Rds.
    destruct (blk_range C A1 m2 _ (Z_to_bv 64 datas) _ CK HW2 Lds ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    destruct (later_cells A7 m9 _ HW9 F9) as (C8 & C16 & C24 & C32). destruct (later_pixs A7 m9 _ HW9) as [PX9 CM9].
    pose proof (W_unbase C A1 m2 _ A7 m9 _ HW2 HW9) as HW9'.
    destruct (fz_J al_rom r m9 s ltac:(lia) ltac:(lia) Q2) as (r1 & RUN1 & P2 & P1 & P10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN1 |].
    assert (P4 : getr r1 4 = Z_to_bv 64 0x32220) by (rewrite (AG1 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
    apply (pixDestroy_W C A7 m9 _ r1 (s - 48) (s - 32) pixs cm (4 * c_nalloc cv) (4 * (wpl_of w d * h)) (hdv w h d cm datas) cv (Z_to_bv 64 0x13e20) S
             CK HW9' P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
             P1 ltac:(red; apply bv_eq; reflexivity) P4 ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) P10 ltac:(rewrite <- w2l_Z8 by lia; exact C32) PX9 eq_refl eq_refl eq_refl).
    - rewrite LQ7. exact Lps.
    - rewrite HA0. exact L0ps.
    - right. cbn [p_data hdv]. rewrite LQ7, HA0. pose proof (box_e _ NEsd) as NEsd'. split; [exact Lds|]. split; [exact L0ds|]. split; [lia|]. split; [lia|].
      intros NZ. destruct (box_e _ HCM) as [Z0 | X]; [exfalso; exact (NZ Z0) | lia].
    - cbn [p_cmap hdv]. destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & CMOK & Lc & La & L0c & L0a & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
      rewrite !LQ7, HA0. pose proof CMOK as (Hcd & Hna & _). split; [exact (CM9 ltac:(lia))|]. repeat (split; [assumption|]).
      rewrite Hna. destruct Hcd as [->|[->|[->| ->]]]; cbn; lia.
    - intros A8 m10 vm8 r2 HW10 CS10 PD POST R0 HRT10. rewrite with_vmmaps_twice in HW10 |- *.
      replace (Z_to_bv 64 0x13e20) with (0x13e20 : word) by (apply bv_eq; reflexivity).
      pose proof POST as [F10 L10].
      destruct (fz_Z al_rom r2 m10 s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret) as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
      { rewrite (FRM_rdn16 C (s - 32 + 8) m9 m10 (s - 8) 8 CK F10) by (cbn; lia). exact C8. }
      { rewrite (FRM_rdn16 C (s - 32 + 8) m9 m10 (s - 16) 8 CK F10) by (cbn; lia). exact C16. }
      { rewrite (FRM_rdn16 C (s - 32 + 8) m9 m10 (s - 24) 8 CK F10) by (cbn; lia). exact C24. }
      { csr. reflexivity. }
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact RUN3 |].
      apply (KF A8 m10 vm8 r3 HW10).
      + intros q. cbn [p_data p_cmap hdv] in PD. destruct PD as (D1 & D2 & D3 & D4).
        destruct (bv_eq_dec _ q (Z_to_bv 64 pixs)) as [->|N1]; [rewrite D1, L0ps; reflexivity|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 datas)) as [->|N2]; [rewrite (D2 ltac:(lia)), L0ds; reflexivity|].
        destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & CMOK & Lc & La & L0c & L0a & _)].
        * rewrite (D4 q N1 ltac:(intros _; exact N2) ltac:(intros X; exfalso; exact (X Z0))), LQ7.
          apply LEQ1; [exact N1 | exact N2 | intros X; exfalso; exact (X Z0)].
        * destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N3]; [rewrite (proj1 (D3 ltac:(lia))), L0c; reflexivity|].
          destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [rewrite (proj2 (D3 ltac:(lia))), L0a; reflexivity|].
          rewrite (D4 q N1 ltac:(intros _; exact N2) ltac:(intros _; split; [exact N3 | exact N4])), LQ7.
          apply LEQ1; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]].
      + exact V10.
      + apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 |].
        intros x Hx. rewrite (AG3 x), (cs_rest_of_kept _ _ CS10 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx).
      + room_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma FRM_win_write : forall mk (a : word) bs, FRM C1 (s - 32) m2 mk ->
    (c_top C - LSTK <= u a)%Z -> (u a + Z.of_nat (length bs) <= s - 32)%Z -> FRM C1 (s - 32) m2 (wbytes mk a bs).
  Proof.
    intros mk a bs F Hlo Hhi. pose proof CK as [T1 T2 T3 T4 T5]. laypins.
    eapply FRM_trans; [exact F|]. intros x _ _ _ _ N5. unfold scratch in N5. cbn in N5. apply wbytes_outside; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma PH4 : forall A5 A6 m8 vm6 r,
    W C1 A6 m8 (with_vmmaps vm6 md0) -> aroom A6 vm6 (kR - RK_paintcmap) (bR - RB_paintcmap) -> FRM C1 (s - 32) m2 m8 -> (forall q, live A5 q = live A1 q) ->
    ((getr r 10 = Z_to_bv 64 0 /\ forall q, live A6 q = live A5 q)
     \/ (exists pixd cd data, getr r 10 = Z_to_bv 64 pixd /\ pixt_new C1 A5 A6 m8 pixd w h d cd data cv)) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x13dec : word) m8 al_rom) (with_vmmaps vm6 md0)) S.
  Proof.
    intros A5 A6 m8 vm6 r HW8 Hrm6 F8 LQ5 RES Q2 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof CK1 as CK1'.
    destruct RES as [[A0 LQ6] | (pixd & cd & data & Hres & PT)].
    - (* [comment removed for export] *)
      destruct (fz_H al_rom r m8 s 0 ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C1 A6 m8 _ (s - 48) 48 CK1' HW8 ltac:(cbn; lia) ltac:(cbn; lia)) Q2 A0)
        as (r1 & RUN1 & P2 & P1 & P10 & P11 & AG1).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN1 |].
      set (M := wbytes m8 _ _).
      assert (HWM : W C1 A6 M (with_vmmaps vm6 md0)) by (subst M; apply (W_store_win C1 A6 m8 _ _ _ CK1' HW8); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (FM : FRM C1 (s - 32) m2 M) by (subst M; apply FRM_win_write; [exact F8 | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
      apply (pixSetSelectMaskedCmap_W C1 A6 M _ r1 (s - 48) 0 (Z_to_bv 64 0x13e10) S CK1' HWM P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 ltac:(left; reflexivity)).
      intros m9 r2 HW9 CS9 PM9.
      replace (Z_to_bv 64 0x13e10) with (0x13e10 : word) by (apply bv_eq; reflexivity).
      assert (F9 : FRM C1 (s - 32) m2 m9) by (eapply FRM_trans; [exact FM | eapply FRM_mono; [exact (proj1 PM9) | lia]]).
      assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      destruct (fz_I al_rom r2 m9 s ltac:(lia) ltac:(lia) Y2) as (r3 & RUN3 & X2 & X1 & X10 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN3 |].
      assert (R48 : rdn SEGS m9 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 0)).
      { rewrite (FRM_rdn16 C1 (s - 48) M m9 (s - 48) 8 CK1' (proj1 PM9)) by (cbn; lia). subst M. rewrite <- (w2b_Z 8 0) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
      apply (pixDestroy_null_W C1 A6 m9 _ r3 (s - 48) (s - 48) (Z_to_bv 64 0x13e18) S CK1' HW9 X2 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) X1 ltac:(red; apply bv_eq; reflexivity) X10 R48).
      intros m10 r4 HW10 CS10 PM10 OUT10.
      replace (Z_to_bv 64 0x13e18) with (0x13e18 : word) by (apply bv_eq; reflexivity).
      apply (PH5 A6 m10 vm6 r4 HW10 Hrm6).
      + eapply FRM_trans; [exact F9|]. eapply FRM_mono; [exact (proj1 PM10) | lia].
      + intros q. rewrite LQ6. apply LQ5.
      + csr. reflexivity.
      + intros x Hx. rewrite (cs_rest_of_kept _ _ CS10 x Hx), (AG3 x), (cs_rest_of_kept _ _ CS9 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx).
    - (* [comment removed for export] *)
      pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L5p & L5d & L1p & L1d & L6p & L6d & PXd & CMR).
      unfold C1, rebase in TOPp, TOPd, L1p, L1d. cbn [c_vm c_A0] in TOPp, TOPd, L1p, L1d.
      assert (NEw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia). apply box_i in NEpd.
      destruct (fz_H al_rom r m8 s pixd ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C1 A6 m8 _ (s - 48) 48 CK1' HW8 ltac:(cbn; lia) ltac:(cbn; lia)) Q2 Hres)
        as (r1 & RUN1 & P2 & P1 & P10 & P11 & AG1).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN1 |].
      set (M := wbytes m8 _ _).
      assert (HWM : W C1 A6 M (with_vmmaps vm6 md0)) by (subst M; apply (W_store_win C1 A6 m8 _ _ _ CK1' HW8); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (FM : FRM C1 (s - 32) m2 M) by (subst M; apply FRM_win_write; [exact F8 | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
      assert (OUTM : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M x = m8 x) by (intros x Hx; subst M; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (PXM : PIXat M pixd (hdv w h d cd data)) by (apply (PIXat_frame m8); [exact PXd | intros x Hx; apply OUTM; lia]).
      apply (pixSetSelectMaskedCmap_W C1 A6 M _ r1 (s - 48) pixd (Z_to_bv 64 0x13e10) S CK1' HWM P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 ltac:(right; exists (hdv w h d cd data); split; [exact PXM | exact L6p])).
      intros m9 r2 HW9 CS9 PM9.
      replace (Z_to_bv 64 0x13e10) with (0x13e10 : word) by (apply bv_eq; reflexivity).
      assert (F9 : FRM C1 (s - 32) m2 m9) by (eapply FRM_trans; [exact FM | eapply FRM_mono; [exact (proj1 PM9) | lia]]).
      assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      destruct (fz_I al_rom r2 m9 s ltac:(lia) ltac:(lia) Y2) as (r3 & RUN3 & X2 & X1 & X10 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN3 |].
      assert (R48 : rdn SEGS m9 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixd)).
      { rewrite (FRM_rdn16 C1 (s - 48) M m9 (s - 48) 8 CK1' (proj1 PM9)) by (cbn; lia). subst M. rewrite <- (w2b_Z 8 pixd) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
      assert (PX9 : PIXat m9 pixd (hdv w h d cd data)) by (apply (PIXat_frame M); [exact PXM | intros x Hx; exact (LIVK_at A6 M m9 pixd 64 x (proj2 PM9) L6p ltac:(lia) ltac:(lia) Hx)]).
      assert (X4 : getr r3 4 = Z_to_bv 64 0x32220) by (rewrite (AG3 4) by notin_list; rewrite (cs_rest_of_kept _ _ CS9 4) by (cbn; tauto); rewrite (AG1 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
      (* [comment removed for export] *)
      assert (FIN : forall (ad : Z) A7 m10 vm7 r4, aroom A7 vm7 (kR - RK_paintcmap) (bR - RB_paintcmap) -> W C1 A7 m10 (with_vmmaps vm7 (with_vmmaps vm6 md0)) -> cs_kept r3 r4 ->
                pixd_post A6 A7 pixd data cd ad -> POSTM C1 (c_A0 C1) (s - 48 + 8) m9 m10 ->
                (cd <> 0%Z -> live A5 (Z_to_bv 64 cd) = None /\ live A5 (Z_to_bv 64 ad) = None /\
                   forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> q <> Z_to_bv 64 cd -> q <> Z_to_bv 64 ad -> live A6 q = live A5 q) ->
                (cd = 0%Z -> forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A6 q = live A5 q) ->
                realizes SEGS (mkCfg (mkst r4 (Z_to_bv 64 0x13e18) m10 al_rom) (with_vmmaps vm7 (with_vmmaps vm6 md0))) S).
      { intros ad A7 m10 vm7 r4 Hrm7 HW10 CS10 PD PM10 CASE1 CASE0. rewrite with_vmmaps_twice in HW10 |- *.
        replace (Z_to_bv 64 0x13e18) with (0x13e18 : word) by (apply bv_eq; reflexivity).
        apply (PH5 A7 m10 vm7 r4 HW10 Hrm7).
        - eapply FRM_trans; [exact F9|]. eapply FRM_mono; [exact (proj1 PM10) | lia].
        - intros q. destruct PD as (D1 & D2 & D3 & D4).
          destruct (bv_eq_dec _ q (Z_to_bv 64 pixd)) as [->|N1]; [rewrite D1, <- LQ5, L5p; reflexivity|].
          destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|N2]; [rewrite (D2 ltac:(lia)), <- LQ5, L5d; reflexivity|].
          destruct (Z.eq_dec cd 0) as [Z0|NZ].
          + rewrite (D4 q N1 ltac:(intros _; exact N2) ltac:(intros X; exfalso; exact (X Z0))), <- LQ5. exact (CASE0 Z0 q N1 N2).
          + destruct (CASE1 NZ) as (L5c & L5a & LEQ6).
            destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [->|N3]; [rewrite (proj1 (D3 NZ)), <- LQ5, L5c; reflexivity|].
            destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [->|N4]; [rewrite (proj2 (D3 NZ)), <- LQ5, L5a; reflexivity|].
            rewrite (D4 q N1 ltac:(intros _; exact N2) ltac:(intros _; split; [exact N3 | exact N4])), <- LQ5. exact (LEQ6 q N1 N2 N3 N4).
        - csr. reflexivity.
        - intros x Hx. rewrite (cs_rest_of_kept _ _ CS10 x Hx), (AG3 x), (cs_rest_of_kept _ _ CS9 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx). }
      destruct CMR as [[CD0 LEQ6] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & L5c & L5a & L1c & L1a & L6c & L6a & CM8 & LEQ6)].
      + (* [comment removed for export] *)
        apply (pixDestroy_W C1 A6 m9 _ r3 (s - 48) (s - 48) pixd cd 0 (4 * (wpl_of w d * h)) (hdv w h d cd data) cmap0 (Z_to_bv 64 0x13e18) S
                 CK1' HW9 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia)
                 X1 ltac:(red; apply bv_eq; reflexivity) X4 ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) X10 R48 PX9 eq_refl eq_refl eq_refl L6p L1p).
        * right. cbn [p_data hdv c_arr cmap0]. pose proof (box_e _ NEpd). split; [exact L6d|]. split; [exact L1d|]. split; [lia|]. split; [lia|]. intros NZ. exfalso. exact (NZ CD0).
        * left. exact CD0.
        * intros A7 m10 vm7 r4 HW10 CS10 PD PM10 _ HRT10. cbn [p_data hdv c_arr cmap0] in PD.
          apply (FIN 0%Z A7 m10 vm7 r4 ltac:(room_tac) HW10 CS10 PD PM10); [intros NZ; exfalso; exact (NZ CD0) | intros _; exact LEQ6].
      + (* [comment removed for export] *)
        unfold C1, rebase in TOPcd, TOPad, L1c, L1a. cbn [c_vm c_A0] in TOPcd, TOPad, L1c, L1a.
        apply box_i in NEcdad. apply box_i in NEcdp. apply box_i in NEcdd. apply box_i in NEadp. apply box_i in NEadd.
        pose proof CMOKc as (Hcd & Hna & Hn & _).
        assert (Hna2 : (2 <= c_nalloc cv <= 256)%Z) by (rewrite Hna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia). clear Hcd.
        assert (CM9 : CMAPat m9 cd (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0)).
        { apply (CMAPat_frame M); [apply (CMAPat_frame m8); [exact CM8 | intros x Hx; apply OUTM; lia] |].
          intros x Hx. exact (LIVK_at A6 M m9 cd 24 x (proj2 PM9) L6c ltac:(lia) ltac:(lia) Hx). }
        apply (pixDestroy_W C1 A6 m9 _ r3 (s - 48) (s - 48) pixd cd (4 * c_nalloc cv) (4 * (wpl_of w d * h)) (hdv w h d cd data)
                 (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) (Z_to_bv 64 0x13e18) S
                 CK1' HW9 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia)
                 X1 ltac:(red; apply bv_eq; reflexivity) X4 ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) X10 R48 PX9 eq_refl eq_refl eq_refl L6p L1p).
        * right. cbn [p_data hdv c_arr]. pose proof (box_e _ NEpd). pose proof (box_e _ NEcdd). pose proof (box_e _ NEadd).
          split; [exact L6d|]. split; [exact L1d|]. split; [lia|]. split; [lia|]. intros _. split; lia.
        * right. cbn [c_arr]. pose proof (box_e _ NEcdad). pose proof (box_e _ NEcdp). pose proof (box_e _ NEadp).
          split; [exact CM9|]. split; [exact L6c|]. split; [exact L6a|]. split; [exact L1c|]. split; [exact L1a|].
          split; [lia|]. split; [lia|]. split; [lia|]. lia.
        * intros A7 m10 vm7 r4 HW10 CS10 PD PM10 _ HRT10. cbn [p_data hdv c_arr] in PD.
          apply (FIN ad A7 m10 vm7 r4 ltac:(room_tac) HW10 CS10 PD PM10); [| intros Z0; exfalso; lia].
          intros _. split; [exact L5c|]. split; [exact L5a|]. exact LEQ6.
  Qed.

  (* [comment removed for export] *)
  Definition pdfacts (A2 A3 : AS) (m : word -> option byte) (pixd cd data n' : Z) : Prop :=
    (4096 <= pixd)%Z /\ (pixd + 64 <= alloc_top (c_vm C))%Z /\ (4096 <= data)%Z /\ (data + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z /\ pixd <> data /\
    live A2 (Z_to_bv 64 pixd) = None /\ live A2 (Z_to_bv 64 data) = None /\ live A1 (Z_to_bv 64 pixd) = None /\ live A1 (Z_to_bv 64 data) = None /\
    live A3 (Z_to_bv 64 pixd) = Some 64%Z /\ live A3 (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z /\
    PIXat m pixd (hdv w h d cd data) /\
    ( (cd = 0%Z /\ forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A3 q = live A2 q)
      \/ (exists ad, cmap_ok cv /\ (4096 <= cd)%Z /\ (cd + 32 <= alloc_top (c_vm C))%Z /\ (4096 <= ad)%Z /\ (ad + 4 * c_nalloc cv <= alloc_top (c_vm C))%Z /\
           cd <> ad /\ cd <> pixd /\ cd <> data /\ ad <> pixd /\ ad <> data /\
           live A2 (Z_to_bv 64 cd) = None /\ live A2 (Z_to_bv 64 ad) = None /\ live A1 (Z_to_bv 64 cd) = None /\ live A1 (Z_to_bv 64 ad) = None /\
           live A3 (Z_to_bv 64 cd) = Some 24%Z /\ live A3 (Z_to_bv 64 ad) = Some (4 * c_nalloc cv)%Z /\
           (1 <= n' <= c_nalloc cv)%Z /\ CMAPat m cd (cset_n (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) n') /\
           (forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> q <> Z_to_bv 64 cd -> q <> Z_to_bv 64 ad -> live A3 q = live A2 q)) ).

  Lemma pdfacts_frame : forall A2 A3 m m' pixd cd data n', pdfacts A2 A3 m pixd cd data n' ->
    (forall (p k : Z) (x : word), live A3 (Z_to_bv 64 p) = Some k -> live A2 (Z_to_bv 64 p) = None -> (0 <= p)%Z -> (p + k <= 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> m' x = m x) ->
    pdfacts A2 A3 m' pixd cd data n'.
  Proof.
    intros A2 A3 m m' pixd cd data n' PD EQ. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    destruct PD as (Gp & TOPp & Gd & TOPd & NEpd & L2p & L2d & L1p & L1d & L3p & L3d & PX & CMR).
    do 11 (split; [assumption|]). split.
    - apply (PIXat_frame m); [exact PX|]. intros x Hx. exact (EQ pixd 64%Z x L3p L2p ltac:(lia) ltac:(lia) Hx).
    - destruct CMR as [L | (ad & X1 & Gcd & TOPcd & Gad & TOPad & X)]; [left; exact L | right; exists ad]. do 5 (split; [assumption|]).
      destruct X as (N1 & N2 & N3 & N4 & N5 & L2c & L2a & L1c & L1a & L3c & L3a & Hn' & CM & LEQ).
      do 12 (split; [assumption|]). split; [| exact LEQ].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. exact (EQ cd 24%Z x L3c L2c ltac:(lia) ltac:(lia) Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma PH3 : forall A2 A3 m6 vm3 r (bx pixd cd data n' : Z),
    W C1 A3 m6 (with_vmmaps vm3 md0) -> aroom A3 vm3 (kR - (RK_deser + RK_box + RK_pixcopy)) (bR - (RB_deser + RB_box + RB_pixcopy)) -> FRM C1 (s - 32) m2 m6 ->
    ((bx = 0%Z /\ forall q, live A2 q = live A1 q)
     \/ ((4096 <= bx)%Z /\ (bx + 32 <= alloc_top (c_vm C))%Z /\ live A2 (Z_to_bv 64 bx) = Some 20%Z /\ live A1 (Z_to_bv 64 bx) = None /\ BOXat m6 bx 278 35 122 50 1 /\
         forall q, q <> Z_to_bv 64 bx -> live A2 q = live A1 q)) ->
    rdn SEGS m6 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 bx) ->
    ((pixd = 0%Z /\ forall q, live A3 q = live A2 q) \/ pdfacts A2 A3 m6 pixd cd data n') ->
    rdn SEGS m6 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixd) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pixs -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x13dd0 : word) m6 al_rom) (with_vmmaps vm3 md0)) S.
  Proof.
    intros A2 A3 m6 vm3 r bx pixd cd data n' HW6 Hrm3 F6 HBX R40 HPD R48 Q2 Q8 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof CK1 as CK1'.
    (* [comment removed for export] *)
    assert (SUB23 : sub_live A2 A3).
    { intros q k Lq. destruct HPD as [[_ LQ] | PD]; [rewrite LQ; exact Lq|].
      destruct PD as (_ & _ & _ & _ & _ & L2p & L2d & _ & _ & _ & _ & _ & CMR).
      destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L2c & L2a & _ & _ & _ & _ & _ & _ & LEQ)].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
    destruct (fz_E al_rom r m6 s ltac:(lia) ltac:(lia) Q2) as (r1 & RUN1 & P2 & P1 & P10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN1 |].
    assert (P4 : getr r1 4 = Z_to_bv 64 0x32220) by (rewrite (AG1 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
    (* [comment removed for export] *)
    assert (NEXT : forall A4 m7 vm4 r2, aroom A4 vm4 (kR - (RK_deser + RK_box + RK_pixcopy)) (bR - (RB_deser + RB_box + RB_pixcopy)) -> W C1 A4 m7 (with_vmmaps vm4 (with_vmmaps vm3 md0)) -> cs_kept r1 r2 -> FRM C1 (s - 32) m6 m7 ->
              (forall q, live A4 q = if bv_eq_dec _ q (Z_to_bv 64 bx) then live A1 q else live A3 q) ->
              (forall (p k : Z) (x : word), live A3 (Z_to_bv 64 p) = Some k -> live A2 (Z_to_bv 64 p) = None -> (0 <= p)%Z -> (p + k <= 2 ^ 64)%Z -> (p <= u x < p + k)%Z -> m7 x = m6 x) ->
              rdn SEGS m7 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixd) ->
              realizes SEGS (mkCfg (mkst r2 (Z_to_bv 64 0x13dd8) m7 al_rom) (with_vmmaps vm4 (with_vmmaps vm3 md0))) S).
    2:{ destruct HBX as [[BX0 LQ2] | (Gb & TOPb & L2b & L1b & BX & LQ2)].
        - (* [comment removed for export] *)
          subst bx.
          apply (boxDestroy_null_W C1 A3 m6 _ r1 (s - 40) (Z_to_bv 64 0x13dd8) S HW6 ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) P1 ltac:(red; apply bv_eq; reflexivity) P10 R40).
          intros r2 CS2. rewrite <- (with_vmmaps_twice vm3 vm3 md0).
          apply (NEXT A3 m6 vm3 r2 Hrm3); [rewrite with_vmmaps_twice; exact HW6 | exact CS2 | apply FRM_refl | | intros; reflexivity | exact R48].
          intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 0)) as [->|NE]; [| reflexivity]. rewrite <- LQ2.
          destruct HPD as [[_ LQ] | PD]; [rewrite LQ; reflexivity|].
          destruct PD as (Gp & TOPp & Gd & TOPd & _ & _ & _ & _ & _ & _ & _ & _ & CMR).
          destruct CMR as [[_ LEQ] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LEQ)].
          + apply LEQ; apply zbv_ne2; lia.
          + pose proof CMOKc as (Hcd & Hna & _). assert (Hna2 : (2 <= c_nalloc cv)%Z) by (rewrite Hna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia). clear Hcd.
            apply LEQ; apply zbv_ne2; lia.
        - (* [comment removed for export] *)
          pose proof BX as (Hb1 & Hb64 & _).
          apply (boxDestroy_W C1 A3 m6 _ r1 (s - 48) (s - 40) bx (Z_to_bv 64 0x13dd8) S CK1' HW6 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
                   ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) P1 ltac:(red; apply bv_eq; reflexivity) P4 P10 R40 BX (SUB23 _ _ L2b) L1b).
          intros A4 m7 vm4 r2 HW7 CS7 L4b LEQ4 PM7 HRT7.
          apply (NEXT A4 _ vm4 r2 ltac:(room_tac) HW7 CS7).
          + eapply FRM_trans; [eapply FRM_mono; [exact (proj1 PM7) | lia] |]. intros x _ _ _ _ N5. unfold scratch in N5. cbn in N5.
            apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
          + intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 bx)) as [->|NE]; [rewrite L4b, L1b; reflexivity | exact (LEQ4 q NE)].
          + intros p k x L L2 G0 TP Hx. assert (NE : Z_to_bv 64 p <> Z_to_bv 64 bx) by (intros E; rewrite E in L2; congruence).
            assert (L4 : live A4 (Z_to_bv 64 p) = Some k) by (rewrite (LEQ4 _ NE); exact L).
            destruct (blk_range C1 A4 _ _ (Z_to_bv 64 p) k CK1' HW7 L4 ltac:(destruct (Z_lt_ge_dec 0 k); [lia|]; exfalso; pose proof (ai_live_hull A4 _ _ _ _ (w_inv _ _ _ _ HW7) L4); lia)) as [G4 TP4].
            rewrite u_Z2bv in G4, TP4 by lia. cbn in TP4.
            rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
            apply (LIVK_at A4 m6 m7 p k x (proj2 PM7)); [exact L4 | lia | lia | exact Hx].
          + rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
            rewrite (FRM_rdn16 C1 (s - 48) m6 m7 (s - 48) 8 CK1' (proj1 PM7)) by (cbn; lia). exact R48. }
    intros A4 m7 vm4 r2 Hrm4 HW7 CS7 F7 LQ4 EQ7 R48'. rewrite with_vmmaps_twice in HW7 |- *.
    replace (Z_to_bv 64 0x13dd8) with (0x13dd8 : word) by (apply bv_eq; reflexivity).
    assert (F7' : FRM C1 (s - 32) m2 m7) by (eapply FRM_trans; [exact F6 | exact F7]).
    assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    destruct (fz_F al_rom r2 m7 s ltac:(lia) ltac:(lia) Y2) as (r3 & RUN3 & X2 & X1 & X10 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN3 |].
    assert (X4 : getr r3 4 = Z_to_bv 64 0x32220) by (rewrite (AG3 4) by notin_list; csr; reflexivity).
    (* [comment removed for export] *)
    assert (LAST : forall A5 m8 vm5 r4, aroom A5 vm5 (kR - (RK_deser + RK_box + RK_pixcopy)) (bR - (RB_deser + RB_box + RB_pixcopy)) -> W C1 A5 m8 (with_vmmaps vm5 (with_vmmaps vm4 md0)) -> cs_kept r3 r4 -> FRM C1 (s - 32) m7 m8 ->
              (forall q, live A5 q = live A1 q) ->
              realizes SEGS (mkCfg (mkst r4 (Z_to_bv 64 0x13de0) m8 al_rom) (with_vmmaps vm5 (with_vmmaps vm4 md0))) S).
    { intros A5 m8 vm5 r4 Hrm5 HW8 CS8 F8 LQ5. rewrite with_vmmaps_twice in HW8 |- *.
      replace (Z_to_bv 64 0x13de0) with (0x13de0 : word) by (apply bv_eq; reflexivity).
      assert (F8' : FRM C1 (s - 32) m2 m8) by (eapply FRM_trans; [exact F7' | exact F8]).
      assert (Z8 : getr r4 8 = Z_to_bv 64 pixs) by (csr; reflexivity).
      destruct (fz_G al_rom r4 m8 s pixs ltac:(csr; reflexivity) Z8) as (r5 & RUN5 & V2 & V1 & V10 & V11 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact RUN5 |].
      destruct (later_pixs A5 m8 _ HW8) as [PX8 CM8].
      assert (V4 : getr r5 4 = Z_to_bv 64 0x32220) by (rewrite (AG5 4) by notin_list; csr; reflexivity).
      refine (pixCopy_W C1 A5 m8 _ r5 (s - 48) pixs w h d cm datas cv (Z_to_bv 64 0x13dec) S CK1' HW8 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) V1 ltac:(red; apply bv_eq; reflexivity) V4 V10 V11 PX8 HOK Hw Hh _ _ _
               (kR - (RK_deser + RK_box + RK_pixcopy)) (bR - (RB_deser + RB_box + RB_pixcopy)) _ _ _ _).
      - rewrite LQ5. exact Lps.
      - rewrite LQ5. exact Lds.
      - destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & CMOK & Lc & La & _)]; [left; exact Z0 | right]. rewrite !LQ5. split; [exact (CM8 ltac:(lia)) | split; [exact CMOK | split; [exact Lc | exact La]]].
      - room_tac.
      - room_consts; lia.
      - room_consts; lia.
      - unfold TK. intros A6 m9 vm6 r6 HW9 CS9 PM9 RES Hrm6. rewrite with_vmmaps_twice in HW9 |- *.
        replace (Z_to_bv 64 0x13dec) with (0x13dec : word) by (apply bv_eq; reflexivity).
        apply (PH4 A5 A6 m9 vm6 r6 HW9 ltac:(room_tac)).
        + eapply FRM_trans; [exact F8' | eapply FRM_mono; [exact (proj1 PM9) | lia]].
        + exact LQ5.
        + exact RES.
        + csr. reflexivity.
        + intros x Hx. rewrite (cs_rest_of_kept _ _ CS9 x Hx), (AG5 x), (cs_rest_of_kept _ _ CS8 x Hx), (AG3 x), (cs_rest_of_kept _ _ CS7 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx). }
    destruct HPD as [[PD0 LQ3] | PD].
    - (* [comment removed for export] *)
      subst pixd.
      apply (pixDestroy_null_W C1 A4 m7 _ r3 (s - 48) (s - 48) (Z_to_bv 64 0x13de0) S CK1' HW7 X2 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) X1 ltac:(red; apply bv_eq; reflexivity) X10 R48').
      intros m8 r4 HW8 CS8 PM8 OUT8. rewrite <- (with_vmmaps_twice vm4 vm4 md0).
      apply (LAST A4 m8 vm4 r4 Hrm4); [rewrite with_vmmaps_twice; exact HW8 | exact CS8 | eapply FRM_mono; [exact (proj1 PM8) | lia] |].
      intros q. rewrite LQ4. destruct (bv_eq_dec _ q (Z_to_bv 64 bx)) as [->|NE]; [reflexivity|]. rewrite LQ3.
      destruct HBX as [[-> LQ2] | (_ & _ & _ & _ & _ & LQ2)]; [apply LQ2 | exact (LQ2 q NE)].
    - pose proof (pdfacts_frame A2 A3 m6 m7 pixd cd data n' PD EQ7) as PD7.
      destruct PD7 as (Gp & TOPp & Gd & TOPd & NEpd & L2p & L2d & L1p & L1d & L3p & L3d & PX7 & CMR).
      assert (NEpb : Z_to_bv 64 pixd <> Z_to_bv 64 bx).
      { destruct HBX as [[-> _] | (_ & _ & L2b & _)]; [apply zbv_ne2; lia | intros E; rewrite E in L2p; congruence]. }
      assert (NEdb : Z_to_bv 64 data <> Z_to_bv 64 bx).
      { destruct HBX as [[-> _] | (_ & _ & L2b & _)]; [apply zbv_ne2; lia | intros E; rewrite E in L2d; congruence]. }
      assert (L4p : live A4 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite LQ4; destruct (bv_eq_dec _ _ _) as [E|_]; [exfalso; exact (NEpb E) | exact L3p]).
      assert (L4d : live A4 (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z) by (rewrite LQ4; destruct (bv_eq_dec _ _ _) as [E|_]; [exfalso; exact (NEdb E) | exact L3d]).
      assert (NEw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia). apply box_i in NEpd.
      (* [comment removed for export] *)
      assert (FIN : forall (ad : Z) A5 m8 vm5 r4, aroom A5 vm5 (kR - (RK_deser + RK_box + RK_pixcopy)) (bR - (RB_deser + RB_box + RB_pixcopy)) -> W C1 A5 m8 (with_vmmaps vm5 (with_vmmaps vm4 md0)) -> cs_kept r3 r4 ->
                pixd_post A4 A5 pixd data cd ad -> POSTM C1 (c_A0 C1) (s - 48 + 8) m7 m8 ->
                (cd <> 0%Z -> live A2 (Z_to_bv 64 cd) = None /\ live A2 (Z_to_bv 64 ad) = None /\ Z_to_bv 64 cd <> Z_to_bv 64 bx /\ Z_to_bv 64 ad <> Z_to_bv 64 bx /\
                   forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> q <> Z_to_bv 64 cd -> q <> Z_to_bv 64 ad -> live A3 q = live A2 q) ->
                (cd = 0%Z -> forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> live A3 q = live A2 q) ->
                realizes SEGS (mkCfg (mkst r4 (Z_to_bv 64 0x13de0) m8 al_rom) (with_vmmaps vm5 (with_vmmaps vm4 md0))) S).
      { intros ad A5 m8 vm5 r4 Hrm5 HW8 CS8 PDP PM8 CASE1 CASE0.
        apply (LAST A5 m8 vm5 r4 Hrm5 HW8 CS8); [eapply FRM_mono; [exact (proj1 PM8) | lia] |].
        intros q. destruct PDP as (D1 & D2 & D3 & D4).
        assert (BXq : q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 data -> (cd <> 0%Z -> q <> Z_to_bv 64 cd /\ q <> Z_to_bv 64 ad) -> live A5 q = live A1 q).
        { intros N1 N2 N34. rewrite (D4 q N1 ltac:(intros _; exact N2) N34), LQ4. destruct (bv_eq_dec _ q (Z_to_bv 64 bx)) as [->|NE]; [reflexivity|].
          destruct (Z.eq_dec cd 0) as [Z0|NZ].
          - rewrite (CASE0 Z0 q N1 N2). destruct HBX as [[-> LQ2] | (_ & _ & _ & _ & _ & LQ2)]; [apply LQ2 | exact (LQ2 q NE)].
          - destruct (CASE1 NZ) as (_ & _ & _ & _ & LEQ3). destruct (N34 NZ) as [N3 N4]. rewrite (LEQ3 q N1 N2 N3 N4).
            destruct HBX as [[-> LQ2] | (_ & _ & _ & _ & _ & LQ2)]; [apply LQ2 | exact (LQ2 q NE)]. }
        destruct (bv_eq_dec _ q (Z_to_bv 64 pixd)) as [->|N1]; [rewrite D1, L1p; reflexivity|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|N2]; [rewrite (D2 ltac:(lia)), L1d; reflexivity|].
        destruct (Z.eq_dec cd 0) as [Z0|NZ]; [apply BXq; [exact N1 | exact N2 | intros X; exfalso; exact (X Z0)] |].
        destruct (CASE1 NZ) as (L2c & L2a & NEcb & NEab & LEQ3).
        destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [->|N3].
        { rewrite (proj1 (D3 NZ)). destruct HBX as [[-> LQ2] | (_ & _ & _ & _ & _ & LQ2)]; [rewrite <- LQ2 | rewrite <- (LQ2 _ NEcb)]; symmetry; exact L2c. }
        destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [->|N4].
        { rewrite (proj2 (D3 NZ)). destruct HBX as [[-> LQ2] | (_ & _ & _ & _ & _ & LQ2)]; [rewrite <- LQ2 | rewrite <- (LQ2 _ NEab)]; symmetry; exact L2a. }
        apply BXq; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]]. }
      destruct CMR as [[CD0 LEQ3] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & L2c & L2a & L1c & L1a & L3c & L3a & Hn' & CM7 & LEQ3)].
      + (* [comment removed for export] *)
        apply (pixDestroy_W C1 A4 m7 _ r3 (s - 48) (s - 48) pixd cd 0 (4 * (wpl_of w d * h)) (hdv w h d cd data) cmap0 (Z_to_bv 64 0x13de0) S
                 CK1' HW7 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia)
                 X1 ltac:(red; apply bv_eq; reflexivity) X4 ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) X10 R48' PX7 eq_refl eq_refl eq_refl L4p L1p).
        * right. cbn [p_data hdv c_arr cmap0]. pose proof (box_e _ NEpd). split; [exact L4d|]. split; [exact L1d|]. split; [lia|]. split; [lia|]. intros NZ. exfalso. exact (NZ CD0).
        * left. exact CD0.
        * intros A5 m8 vm5 r4 HW8 CS8 PDP PM8 _ HRT8. cbn [p_data hdv c_arr cmap0] in PDP.
          apply (FIN 0%Z A5 m8 vm5 r4 ltac:(room_tac) HW8 CS8 PDP PM8); [intros NZ; exfalso; exact (NZ CD0) | intros _; exact LEQ3].
      + (* [comment removed for export] *)
        apply box_i in NEcdad. apply box_i in NEcdp. apply box_i in NEcdd. apply box_i in NEadp. apply box_i in NEadd.
        pose proof CMOKc as (Hcd & Hna & Hn & _).
        assert (Hna2 : (2 <= c_nalloc cv <= 256)%Z) by (rewrite Hna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia). clear Hcd.
        assert (NEcb : Z_to_bv 64 cd <> Z_to_bv 64 bx) by (destruct HBX as [[-> _] | (_ & _ & L2b & _)]; [apply zbv_ne2; lia | intros E; rewrite E in L2c; congruence]).
        assert (NEab : Z_to_bv 64 ad <> Z_to_bv 64 bx) by (destruct HBX as [[-> _] | (_ & _ & L2b & _)]; [apply zbv_ne2; lia | intros E; rewrite E in L2a; congruence]).
        assert (L4c : live A4 (Z_to_bv 64 cd) = Some 24%Z) by (rewrite LQ4; destruct (bv_eq_dec _ _ _) as [E|_]; [exfalso; exact (NEcb E) | exact L3c]).
        assert (L4a : live A4 (Z_to_bv 64 ad) = Some (4 * c_nalloc cv)%Z) by (rewrite LQ4; destruct (bv_eq_dec _ _ _) as [E|_]; [exfalso; exact (NEab E) | exact L3a]).
        apply (pixDestroy_W C1 A4 m7 _ r3 (s - 48) (s - 48) pixd cd (4 * c_nalloc cv) (4 * (wpl_of w d * h)) (hdv w h d cd data)
                 (cset_n (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) n') (Z_to_bv 64 0x13de0) S
                 CK1' HW7 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia)
                 X1 ltac:(red; apply bv_eq; reflexivity) X4 ltac:(apply sp_slot_al8; [exact Hs16 | reflexivity]) X10 R48' PX7 eq_refl eq_refl eq_refl L4p L1p).
        * right. cbn [p_data hdv c_arr cset_n]. pose proof (box_e _ NEpd). pose proof (box_e _ NEcdd). pose proof (box_e _ NEadd).
          split; [exact L4d|]. split; [exact L1d|]. split; [lia|]. split; [lia|]. intros _. split; lia.
        * right. cbn [c_arr cset_n]. pose proof (box_e _ NEcdad). pose proof (box_e _ NEcdp). pose proof (box_e _ NEadp).
          split; [exact CM7|]. split; [exact L4c|]. split; [exact L4a|]. split; [exact L1c|]. split; [exact L1a|].
          split; [lia|]. split; [lia|]. split; [lia|]. lia.
        * intros A5 m8 vm5 r4 HW8 CS8 PDP PM8 _ HRT8. cbn [p_data hdv c_arr cset_n] in PDP.
          apply (FIN ad A5 m8 vm5 r4 ltac:(room_tac) HW8 CS8 PDP PM8); [| intros Z0; exfalso; lia].
          intros _. split; [exact L2c|]. split; [exact L2a|]. split; [exact NEcb|]. split; [exact NEab|]. exact LEQ3.
  Qed.


  (* [comment removed for export] *)
  Lemma PH2 : forall A2 A3 m5 vm3 r (bx : Z),
    W C1 A3 m5 (with_vmmaps vm3 md0) -> aroom A3 vm3 (kR - (RK_deser + RK_box + RK_pixcopy)) (bR - (RB_deser + RB_box + RB_pixcopy)) -> FRM C1 (s - 32) m2 m5 ->
    ((bx = 0%Z /\ forall q, live A2 q = live A1 q)
     \/ ((4096 <= bx)%Z /\ (bx + 32 <= alloc_top (c_vm C))%Z /\ live A2 (Z_to_bv 64 bx) = Some 20%Z /\ live A1 (Z_to_bv 64 bx) = None /\ BOXat m5 bx 278 35 122 50 1 /\
         forall q, q <> Z_to_bv 64 bx -> live A2 q = live A1 q)) ->
    rdn SEGS m5 (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 bx) ->
    ((getr r 10 = Z_to_bv 64 0 /\ forall q, live A3 q = live A2 q)
     \/ (exists pixd cd data, getr r 10 = Z_to_bv 64 pixd /\ pixt_new C1 A2 A3 m5 pixd w h d cd data cv)) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pixs -> getr r 9 = Z_to_bv 64 bx -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x13db4 : word) m5 al_rom) (with_vmmaps vm3 md0)) S.
  Proof.
    intros A2 A3 m5 vm3 r bx HW5 Hrm3 F5 HBX R40 RES Q2 Q8 Q9 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof CK1 as CK1'.
    assert (Hbx : (0 <= bx < 2 ^ 64)%Z) by (destruct HBX as [[-> _] | (Gb & TOPb & _)]; lia).
    assert (SUB23 : sub_live A2 A3).
    { intros q k Lq. destruct RES as [[_ LQ] | (pixd & cd & data & _ & PT)]; [rewrite LQ; exact Lq|].
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & L2p & L2d & _ & _ & _ & _ & _ & CMR).
      destruct CMR as [[_ LEQ] | (ad & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L2c & L2a & _ & _ & _ & _ & _ & LEQ)].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence].
      - rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence | intros ->; congruence | intros ->; congruence]. }
    destruct RES as [[A0 LQ3] | (pixd & cd & data & Hres & PT)].
    - (* [comment removed for export] *)
      destruct (fz_D al_rom r m5 s 0 bx ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C1 A3 m5 _ (s - 48) 48 CK1' HW5 ltac:(cbn; lia) ltac:(cbn; lia)) Q2 A0 Q9)
        as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & AG1).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN1 |].
      set (M := wbytes m5 _ _).
      assert (HWM : W C1 A3 M (with_vmmaps vm3 md0)) by (subst M; apply (W_store_win C1 A3 m5 _ _ _ CK1' HW5); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (OUTM : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M x = m5 x) by (intros x Hx; subst M; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      apply (pixSetSelectCmap_null_W C1 A3 M _ r1 (s - 48) bx (Z_to_bv 64 0x13dd0) S CK1' HWM P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) P1 ltac:(red; apply bv_eq; reflexivity) P10).
      intros m6 r6 HW6 CS6 PM6.
      replace (Z_to_bv 64 0x13dd0) with (0x13dd0 : word) by (apply bv_eq; reflexivity).
      apply (PH3 A2 A3 m6 vm3 r6 bx 0 0 0 0 HW6 Hrm3).
      + eapply FRM_trans; [exact F5|]. eapply FRM_trans; [| eapply FRM_mono; [exact (proj1 PM6) | lia]].
        intros x _ _ _ _ N5. unfold scratch in N5. cbn in N5. apply OUTM. lia.
      + destruct HBX as [L | (Gb & TOPb & L2b & L1b & BX & LQ2)]; [left; exact L | right]. do 4 (split; [assumption|]). split; [| exact LQ2].
        apply (BOXat_frame m5); [exact BX|]. intros x Hx. rewrite (LIVK_at A3 M m6 bx 20 x (proj2 PM6) (SUB23 _ _ L2b) ltac:(lia) ltac:(lia) Hx). apply OUTM. lia.
      + rewrite (FRM_rdn16 C1 (s - 48) M m6 (s - 40) 8 CK1' (proj1 PM6)) by (cbn; lia). subst M. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R40.
      + left. split; [reflexivity | exact LQ3].
      + rewrite (FRM_rdn16 C1 (s - 48) M m6 (s - 48) 8 CK1' (proj1 PM6)) by (cbn; lia). subst M. rewrite <- (w2b_Z 8 0) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
      + csr. reflexivity.
      + csr. reflexivity.
      + intros x Hx. rewrite (cs_rest_of_kept _ _ CS6 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx).
    - (* [comment removed for export] *)
      pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L2p & L2d & L1p & L1d & L3p & L3d & PXd & CMR).
      unfold C1, rebase in TOPp, TOPd, L1p, L1d. cbn [c_vm c_A0] in TOPp, TOPd, L1p, L1d.
      assert (NEw : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
      destruct (fz_D al_rom r m5 s pixd bx ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C1 A3 m5 _ (s - 48) 48 CK1' HW5 ltac:(cbn; lia) ltac:(cbn; lia)) Q2 Hres Q9)
        as (r1 & RUN1 & P2 & P1 & P10 & P11 & P12 & P13 & P14 & P15 & AG1).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN1 |].
      set (M := wbytes m5 _ _).
      assert (HWM : W C1 A3 M (with_vmmaps vm3 md0)) by (subst M; apply (W_store_win C1 A3 m5 _ _ _ CK1' HW5); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (OUTM : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M x = m5 x) by (intros x Hx; subst M; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (PXM : PIXat M pixd (hdv w h d cd data)) by (apply (PIXat_frame m5); [exact PXd | intros x Hx; apply OUTM; lia]).
      (* [comment removed for export] *)
      assert (NEXT : forall (n' : Z) m6 r6, W C1 A3 m6 (with_vmmaps vm3 md0) -> cs_kept r1 r6 -> POSTM C1 A2 (s - 48) M m6 ->
                (bx <> 0%Z -> BOXat m6 bx 278 35 122 50 1) -> pdfacts A2 A3 m6 pixd cd data n' ->
                realizes SEGS (mkCfg (mkst r6 (Z_to_bv 64 0x13dd0) m6 al_rom) (with_vmmaps vm3 md0)) S).
      { intros n' m6 r6 HW6 CS6 PM6 BX6 PD6. replace (Z_to_bv 64 0x13dd0) with (0x13dd0 : word) by (apply bv_eq; reflexivity).
        apply (PH3 A2 A3 m6 vm3 r6 bx pixd cd data n' HW6 Hrm3).
        + eapply FRM_trans; [exact F5|]. eapply FRM_trans; [| eapply FRM_mono; [exact (proj1 PM6) | lia]].
          intros x _ _ _ _ N5. unfold scratch in N5. cbn in N5. apply OUTM. lia.
        + destruct HBX as [L | (Gb & TOPb & L2b & L1b & BX & LQ2)]; [left; exact L | right]. do 4 (split; [assumption|]). split; [apply BX6; lia | exact LQ2].
        + rewrite (FRM_rdn16 C1 (s - 48) M m6 (s - 40) 8 CK1' (proj1 PM6)) by (cbn; lia). subst M. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact R40.
        + right. exact PD6.
        + rewrite (FRM_rdn16 C1 (s - 48) M m6 (s - 48) 8 CK1' (proj1 PM6)) by (cbn; lia). subst M. rewrite <- (w2b_Z 8 pixd) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
        + csr. reflexivity.
        + csr. reflexivity.
        + intros x Hx. rewrite (cs_rest_of_kept _ _ CS6 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx). }
      destruct CMR as [[CD0 LEQ3] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & NEcdad & NEcdp & NEcdd & NEadp & NEadd & L2c & L2a & L1c & L1a & L3c & L3a & CM5 & LEQ3)].
      + (* [comment removed for export] *)
        assert (HBXs : bx = 0%Z \/ (BOXat M bx 278 35 122 50 1 /\ live A3 (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data /\
                                     (cd <> 0%Z -> Z_to_bv 64 bx <> Z_to_bv 64 cd /\ Z_to_bv 64 bx <> Z_to_bv 64 (c_arr cmap0)))).
        { destruct HBX as [[-> _] | (Gb & TOPb & L2b & L1b & BX & LQ2)]; [left; reflexivity | right].
          split; [apply (BOXat_frame m5); [exact BX | intros x Hx; apply OUTM; lia] |]. split; [exact (SUB23 _ _ L2b)|].
          split; [intros E; rewrite <- E in L2d; congruence|]. intros NZ. exfalso. exact (NZ CD0). }
        apply (pixSetSelectCmap_W C1 A2 A3 M _ r1 (s - 48) pixd bx w h d cd data cmap0 (Z_to_bv 64 0x13dd0) S CK1' HWM SUB23 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
                 ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14 P15 PXM HOK Hw Hh L3p L3d L2d L1d NEw
                 ltac:(left; exact CD0) HBXs).
        intros m6 r6 HW6 CS6 PM6 PX6 _ BX6.
        apply (NEXT 1%Z m6 r6 HW6 CS6 PM6 BX6).
        pose proof (box_e _ NEpd). do 11 (split; [assumption|]). split; [exact PX6|]. left. split; [exact CD0 | exact LEQ3].
      + (* [comment removed for export] *)
        unfold C1, rebase in TOPcd, TOPad, L1c, L1a. cbn [c_vm c_A0] in TOPcd, TOPad, L1c, L1a.
        pose proof CMOKc as (Hcd & Hna & Hn & _).
        assert (Hna2 : (2 <= c_nalloc cv <= 256)%Z) by (rewrite Hna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia). clear Hcd.
        assert (CMM : CMAPat M cd (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0)) by (apply (CMAPat_frame m5); [exact CM5 | intros x Hx; apply OUTM; lia]).
        pose proof (cmap_ok_copy cv ad CMOKc ltac:(lia)) as CMOK'.
        assert (NE1 : Z_to_bv 64 cd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
        assert (NE2 : Z_to_bv 64 cd <> Z_to_bv 64 ad) by (apply zbv_ne2; lia).
        assert (NE3 : Z_to_bv 64 pixd <> Z_to_bv 64 cd) by (apply zbv_ne2; lia).
        assert (NE4 : Z_to_bv 64 pixd <> Z_to_bv 64 ad) by (apply zbv_ne2; lia).
        apply box_i in NEcdad. apply box_i in NEcdp. apply box_i in NEcdd. apply box_i in NEadp. apply box_i in NEadd.
        assert (HCMs : cd = 0%Z \/ (CMAPat M cd (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) /\ cmap_ok (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) /\
                  live A3 (Z_to_bv 64 cd) = Some 24%Z /\ live A2 (Z_to_bv 64 cd) = None /\ live (c_A0 C1) (Z_to_bv 64 cd) = None /\
                  live A3 (Z_to_bv 64 (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0))) = Some (4 * c_nalloc (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0))%Z /\
                  live A2 (Z_to_bv 64 (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0))) = None /\
                  live (c_A0 C1) (Z_to_bv 64 (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0))) = None /\
                  Z_to_bv 64 cd <> Z_to_bv 64 data /\ Z_to_bv 64 cd <> Z_to_bv 64 (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0)) /\
                  Z_to_bv 64 pixd <> Z_to_bv 64 cd /\ Z_to_bv 64 pixd <> Z_to_bv 64 (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0)))).
        { right. cbn [c_arr c_nalloc c_A0 C1 rebase]. repeat (split; [assumption|]). exact NE4. }
        assert (HBXs : bx = 0%Z \/ (BOXat M bx 278 35 122 50 1 /\ live A3 (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data /\
                                     (cd <> 0%Z -> Z_to_bv 64 bx <> Z_to_bv 64 cd /\ Z_to_bv 64 bx <> Z_to_bv 64 (c_arr (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0))))).
        { destruct HBX as [[-> _] | (Gb & TOPb & L2b & L1b & BX & LQ2)]; [left; reflexivity | right]. cbn [c_arr].
          split; [apply (BOXat_frame m5); [exact BX | intros x Hx; apply OUTM; lia] |]. split; [exact (SUB23 _ _ L2b)|].
          split; [intros E; rewrite <- E in L2d; congruence|]. intros _.
          split; [intros E; rewrite <- E in L2c; congruence | intros E; rewrite <- E in L2a; congruence]. }
        apply (pixSetSelectCmap_W C1 A2 A3 M _ r1 (s - 48) pixd bx w h d cd data (CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) (Z_to_bv 64 0x13dd0) S
                 CK1' HWM SUB23 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
                 ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) P1 ltac:(red; apply bv_eq; reflexivity) P10 P11 P12 P13 P14 P15 PXM HOK Hw Hh L3p L3d L2d L1d NEw
                 HCMs HBXs).
        intros m6 r6 HW6 CS6 PM6 PX6 CM6 BX6.
        destruct (CM6 ltac:(lia)) as (n' & Hn' & CMn). cbn [c_nalloc] in Hn'.
        apply (NEXT n' m6 r6 HW6 CS6 PM6 BX6).
        pose proof (box_e _ NEpd). do 11 (split; [assumption|]). split; [exact PX6|]. right. exists ad.
        pose proof (box_e _ NEcdad). pose proof (box_e _ NEcdp). pose proof (box_e _ NEcdd). pose proof (box_e _ NEadp). pose proof (box_e _ NEadd).
        do 16 (split; [first [assumption | lia] |]). split; [exact Hn'|]. split; [exact CMn | exact LEQ3].
  Qed.

  (* [comment removed for export] *)
  Lemma PH1 : forall A2 m4 vm2 r (bx : Z),
    W C1 A2 m4 (with_vmmaps vm2 md0) -> aroom A2 vm2 (kR - (RK_deser + RK_box)) (bR - (RB_deser + RB_box)) -> FRM C1 (s - 32) m2 m4 ->
    ((bx = 0%Z /\ forall q, live A2 q = live A1 q)
     \/ ((4096 <= bx)%Z /\ (bx + 32 <= alloc_top (c_vm C))%Z /\ live A2 (Z_to_bv 64 bx) = Some 20%Z /\ live A1 (Z_to_bv 64 bx) = None /\ BOXat m4 bx 278 35 122 50 1 /\
         forall q, q <> Z_to_bv 64 bx -> live A2 q = live A1 q)) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pixs -> getr r 10 = Z_to_bv 64 bx -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x13da0 : word) m4 al_rom) (with_vmmaps vm2 md0)) S.
  Proof.
    intros A2 m4 vm2 r bx HW4 Hrm2 F4 HBX Q2 Q8 Q10 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof CK1 as CK1'.
    assert (Hbx : (0 <= bx < 2 ^ 64)%Z) by (destruct HBX as [[-> _] | (Gb & TOPb & _)]; lia).
    assert (SUB12 : sub_live A1 A2).
    { intros q k Lq. destruct HBX as [[_ LQ] | (_ & _ & _ & L1b & _ & LQ)]; [rewrite LQ; exact Lq|].
      rewrite LQ; [exact Lq|]. intros ->. congruence. }
    destruct (fz_C al_rom r m4 s pixs bx ltac:(lia) ltac:(lia) Hbx (W_sok_win C1 A2 m4 _ (s - 48) 48 CK1' HW4 ltac:(cbn; lia) ltac:(cbn; lia)) Q2 Q10 Q8)
      as (r1 & RUN1 & P2 & P1 & P8 & P9 & P10 & P11 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN1 |].
    set (M := wbytes m4 _ _).
    assert (HWM : W C1 A2 M (with_vmmaps vm2 md0)) by (subst M; apply (W_store_win C1 A2 m4 _ _ _ CK1' HW4); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    assert (FM : FRM C1 (s - 32) m2 M) by (subst M; apply FRM_win_write; [exact F4 | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
    assert (OUTM : forall x : word, ~ (s - 40 <= u x < s - 32)%Z -> M x = m4 x) by (intros x Hx; subst M; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
    destruct (later_pixs A2 M _ HWM) as [PXM CMM].
    assert (P4 : getr r1 4 = Z_to_bv 64 0x32220) by (rewrite (AG1 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
    refine (pixCopy_W C1 A2 M _ r1 (s - 48) pixs w h d cm datas cv (Z_to_bv 64 0x13db4) S CK1' HWM P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) P1 ltac:(red; apply bv_eq; reflexivity) P4 P10 P11 PXM HOK Hw Hh (SUB12 _ _ Lps) (SUB12 _ _ Lds) _
             (kR - (RK_deser + RK_box)) (bR - (RB_deser + RB_box)) _ _ _ _).
    - destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & CMOK & Lc & La & _)]; [left; exact Z0 | right].
      split; [exact (CMM ltac:(lia)) | split; [exact CMOK | split; [exact (SUB12 _ _ Lc) | exact (SUB12 _ _ La)]]].
    - room_tac.
    - room_consts; lia.
    - room_consts; lia.
    - unfold TK. intros A3 m5 vm3 r2 HW5 CS5 PM5 RES Hrm3. rewrite with_vmmaps_twice in HW5 |- *.
      replace (Z_to_bv 64 0x13db4) with (0x13db4 : word) by (apply bv_eq; reflexivity).
      apply (PH2 A2 A3 m5 vm3 r2 bx HW5 ltac:(room_tac)).
      + eapply FRM_trans; [exact FM | eapply FRM_mono; [exact (proj1 PM5) | lia]].
      + destruct HBX as [L | (Gb & TOPb & L2b & L1b & BX & LQ2)]; [left; exact L | right]. do 4 (split; [assumption|]). split; [| exact LQ2].
        apply (BOXat_frame M); [apply (BOXat_frame m4); [exact BX | intros x Hx; apply OUTM; lia] |].
        intros x Hx. exact (LIVK_at A2 M m5 bx 20 x (proj2 PM5) L2b ltac:(lia) ltac:(lia) Hx).
      + rewrite (FRM_rdn16 C1 (s - 48) M m5 (s - 40) 8 CK1' (proj1 PM5)) by (cbn; lia). subst M. rewrite <- (w2b_Z 8 bx) by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
      + exact RES.
      + csr. reflexivity.
      + csr. reflexivity.
      + csr. reflexivity.
      + intros x Hx. rewrite (cs_rest_of_kept _ _ CS5 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma PH0 : forall r,
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = Z_to_bv 64 0x13da0 -> getr r 8 = Z_to_bv 64 pixs ->
    getr r 10 = Z_to_bv 64 278 -> getr r 11 = Z_to_bv 64 35 -> getr r 12 = Z_to_bv 64 122 -> getr r 13 = Z_to_bv 64 50 ->
    (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x14158 : word) m2 al_rom) (with_vmmaps vm1 md0)) S.
  Proof.
    intros r Q2 Q1 Q8 Q10 Q11 Q12 Q13 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof CK1 as CK1'.
    assert (Q4 : getr r 4 = Z_to_bv 64 0x32220) by (rewrite (RR 4) by (cbn; tauto); exact H4).
    apply (boxCreate_W C1 A1 m2 _ r (s - 48) (Z_to_bv 64 0x13da0) S CK1' (W_rebase C A1 m2 _ HW2) Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Q13
             (kR - RK_deser) (bR - RB_deser) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A2 m4 vm2 r2 HW4 CS4 PM4 RES Hrm2. rewrite with_vmmaps_twice in HW4 |- *.
    replace (Z_to_bv 64 0x13da0) with (0x13da0 : word) by (apply bv_eq; reflexivity).
    assert (Hbx : exists bx, getr r2 10 = Z_to_bv 64 bx /\
              ((bx = 0%Z /\ forall q, live A2 q = live A1 q)
               \/ ((4096 <= bx)%Z /\ (bx + 32 <= alloc_top (c_vm C))%Z /\ live A2 (Z_to_bv 64 bx) = Some 20%Z /\ live A1 (Z_to_bv 64 bx) = None /\ BOXat m4 bx 278 35 122 50 1 /\
                   forall q, q <> Z_to_bv 64 bx -> live A2 q = live A1 q))).
    { destruct RES as [[A0 LQ] | (bx & A0 & BN)]; [exists 0%Z; split; [exact A0 | left; split; [reflexivity | exact LQ]] |].
      exists bx. split; [exact A0 | right]. destruct BN as (Gb & TOPb & _ & L1b & _ & L2b & LQ & BX). cbn [C1 rebase c_vm] in TOPb.
      repeat (split; [assumption|]). exact LQ. }
    destruct Hbx as (bx & A0 & HBX).
    apply (PH1 A2 m4 vm2 r2 bx HW4 ltac:(room_tac)); [eapply FRM_mono; [exact (proj1 PM4) | lia] | exact HBX | csr; reflexivity | csr; reflexivity | exact A0 |].
    intros x Hx. rewrite (cs_rest_of_kept _ _ CS4 x Hx). exact (RR x Hx).
  Qed.

End Phases.
End V21LeptFuzz.

Module V21LeptFuzzMain.
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
Import OSSVerify.leptonica.paintcmap_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptArith2.
Import V21Drv1.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptStderr.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptUb.
Import V21CL7a.
Import V21CL8a.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptCmapValid.
Import V21CL9a.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptDeser.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptBox.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptCmap2.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptPixCopyA.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptPixCopy.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptSelCmap.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptSelMasked.
Import V21LeptFuzz.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptRoomPC.
(* [comment removed for export] *)
(* [comment removed for export] *)








Import V21Drv1.V21FuzzIface.


Import V21CL7a.V21LeptErr.

Import V21CL8a.V21LeptPixHdr.


Import V21CL9a.V21LeptPixDestroy.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac nin_cs Hx := let H := fresh in pose proof Hx as H; unfold cs_rest in H; cbn in H; repeat (destruct H as [<-|H]; [notin_list|]); destruct H.

Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU21} {P16 : V21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_paintcmap <= FUZZ_CALLS)%Z /\ (forall size, (0 <= size)%Z -> (RB_paintcmap <= fuzz_margin size)%Z).
Proof. room_consts. unfold FUZZ_CALLS, fuzz_margin. split; [lia | intros; lia]. Qed.

Theorem lept_fuzz_call : @fuzz_call_contract AL CL ASR.
Proof.
  unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret H3 H4 Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm. pose proof (FZb size ltac:(lia)) as FZb'.
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in H4.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x13d48) with (0x13d48 : word) by (apply bv_eq; reflexivity).
  pose proof (u64_range (getr regs 2)) as Hs. pose proof (u64_range dptr) as Hdp. pose proof (u64_range sp0) as Hsp0r.
  set (s := u (getr regs 2)) in *.
  assert (H2 : getr regs 2 = Z_to_bv 64 s) by (subst s; rewrite zbv_self; reflexivity). clearbody s.
  set (dp := u dptr) in *.
  assert (Edp : dptr = Z_to_bv 64 dp) by (subst dp; rewrite zbv_self; reflexivity). clearbody dp. rewrite Edp in Ha0, Hlive, Hempty.
  set (C := LCTX sp0 argv envp s (m_vmmaps md) m A).
  assert (Etop : c_top C = s) by reflexivity. assert (Evm : c_vm C = m_vmmaps md) by reflexivity.
  assert (CK : Cok C) by (constructor; cbn; rewrite ?LSTK_val; lia).
  pose proof LSTK_val as LV.
  (* [comment removed for export] *)
  assert (SOK : store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    destruct (Hwin x ltac:(lia)) as (D & _). unfold wview. destruct (m x) eqn:E; [discriminate | exfalso; exact (D eq_refl)]. }
  assert (OUT3 : forall a : word, ~ (s - 24 <= u a < s)%Z -> FZ3 m s ret regs a = m a).
  { intros a Ha. unfold FZ3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (GR3 : mem_grows m (FZ3 m s ret regs)) by (unfold FZ3; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
  assert (BLK : forall q k i, live A q = Some k -> (0 <= i < k)%Z -> owned A (at_ q i) /\ ~ (s - 16384 <= u (at_ q i) < s)%Z).
  { intros q k i L Hi. pose proof (ai_live_hull A m (m_vmmaps md) q k Hinv L) as (Hk0 & _ & _ & OWN). pose proof (round16_ge k Hk0).
    destruct (OWN i ltac:(lia)) as (Ho & _). split; [exact Ho|]. intros R. exact (proj1 (proj2 (Hwin _ R)) Ho). }
  destruct (Z_lt_ge_dec size 3) as [SM|BG].
  { (* [comment removed for export] *)
    destruct (fz_small al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) Hret SOK H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q9 & AG1).
    eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
    rewrite <- (with_vmmaps_same md). apply (K A (FZ3 m s ret regs) (m_vmmaps md) r1).
    - apply (ai_frame A m _ _ Hinv).
      + intros a Ho _. apply OUT3. intros R. exact (proj1 (proj2 (Hwin a ltac:(lia))) Ho).
      + intros a _ Hx. exact (GR3 a Hx).
      + intros a _ Hx. destruct (Z_lt_ge_dec (u a) (s - 24)); [rewrite OUT3 in Hx by lia; exact Hx|].
        destruct (Z_lt_ge_dec (u a) s); [exact (proj1 (Hwin a ltac:(lia))) | rewrite OUT3 in Hx by lia; exact Hx].
    - intros q; reflexivity.
    - exact Q10.
    - apply cs_kept_intro; csr; reflexivity.
    - intros a _ _ _ _ NW. apply OUT3. lia.
    - intros q k i L Hi. apply OUT3. destruct (BLK q k i L Hi) as [_ X]. lia.
    - intros a Hx. right; right. exact (GR3 a Hx).
    - reflexivity. - reflexivity. - reflexivity. - reflexivity.
    - room_tac. }
  (* [comment removed for export] *)
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0x21ed0) 8 = true) by exact Hhdl.
  destruct (fz_A al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FZ3 m s ret regs) (Z_to_bv 64 0x21ed0) (word_to_le_bytes 8 (Z_to_bv 64 0x13e38))) in *.
  assert (OUT1 : forall a : word, ~ (s - 24 <= u a < s)%Z -> ~ (0x21ed0 <= u a < 0x21ed8)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LLU21] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 24)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0x21ed0); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 0x21ed8); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LLU21]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KF : forall A' mf vm' rr, W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> aroom A' vm' (kR - RK_paintcmap) (bR - RB_paintcmap) -> realizes SEGS (mkCfg (mkst rr ret mf al_rom) (with_vmmaps vm' md)) S).
  { intros A' mf vm' rr HWf LQ A0 CS HRf. apply (K A' mf vm' rr).
    - pose proof (w_inv _ _ _ _ HWf) as X. rewrite with_vmmaps_vmmaps in X. exact X.
    - exact LQ.
    - exact A0.
    - exact CS.
    - intros a N1 N2 N3 N4 N5. apply (w_frm _ _ _ _ HWf a); [exact N1 | exact N2 | exact N3 | unfold hcell; cbn; exact N4 | unfold scratch; cbn; rewrite LV; lia].
    - intros q k i Lq Hi. exact (w_live0 _ _ _ _ HWf q k i Lq Hi).
    - intros a Hx. exact (w_def _ _ _ _ HWf a Hx).
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V1. exact V1.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V2. exact V2.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V3. exact V3.
    - destruct (w_vm _ _ _ _ HWf) as (V1 & V2 & V3 & V4). rewrite with_vmmaps_vmmaps in V4. exact V4.
    - room_tac. }
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x32220) by (rewrite (AG1 4) by notin_list; exact H4).
  apply (pixDeserialize_W C A m1 md r1 (s - 48) dp pl (Z_to_bv 64 0x13d80) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia) ltac:(apply al16_mod4; exact Hal16)
           kR bR Hrm ltac:(room_consts; lia) ltac:(room_consts; lia)).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x13d80) with (0x13d80 : word) by (apply bv_eq; reflexivity).
  pose proof PM' as [F' L']. cbn [c_A0] in L'.
  assert (C1 : rdn SEGS m' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 8) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FZ3. rdn_solve. }
  assert (C2 : rdn SEGS m' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 16) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FZ3. rdn_solve. }
  assert (C3 : rdn SEGS m' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 48) m1 m' (s - 24) 8 CK F') by (rewrite ?Etop, ?LV; lia). subst m1. unfold FZ3. rdn_solve. }
  assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
  pose proof (W_sok_win C A' m' _ (s - 48) 48 CK HW' ltac:(rewrite Etop, LV; lia) ltac:(rewrite Etop; cbn; lia)) as SOK'.
  destruct RES as [[A0 LQ] | (pix & v & cv & A2p & PO & PF)].
  - (* [comment removed for export] *)
    destruct (fz_B0 al_rom r2 m' s ret (getr regs 8) (getr regs 9) ltac:(lia) ltac:(lia) Hret SOK' C1 C2 C3 Y2 A0) as (r3 & RUN3 & V2 & V1 & V10 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    assert (HWf : W C A' (wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm' md)).
    { apply (W_store_win C A' m' _ _ _ CK HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; rewrite ?LV; lia. }
    apply (KF A' _ vm' r3 HWf LQ V10 ltac:(apply cs_kept_intro; csr; reflexivity) ltac:(room_tac)).
  - (* [comment removed for export] *)
    pose proof PO as (PX & Rrc & Rtx & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ).
    pose proof PF as (Ev & HOK & Hw & Hh & CMOK).
    destruct v as [w h d spp wpl rc xres yres fmt spec text cm datas].
    cbn [p_w p_h p_d p_spp p_wpl p_rc p_xres p_yres p_fmt p_spec p_text p_cmap p_data] in PX, Rrc, Rtx, Hn4, Ld, LdA, Ld0, NEdp, RC, RQ, Ev, HOK, Hw, Hh, CMOK.
    injection Ev as E8 E7 E6 E5 E4 E3 E2 E1. subst spp wpl rc xres yres fmt spec text.
    change (PIXV w h d (spp_of d) (wpl_of w d) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z cm datas) with (hdv w h d cm datas) in PX.
    pose proof PX as (Hp0 & Hp64 & WF & _).
    destruct (blk_range C A' m' _ (Z_to_bv 64 pix) 64 CK HW' Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia. rewrite Evm in TOPp.
    pose proof (alloc_top_lt (m_vmmaps md)) as ATL. unfold two_pow_64 in ATL.
    destruct (fz_B1 al_rom r2 m' s pix ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 A2p) as (r3 & RUN3 & V2 & V1 & V8 & V10 & V11 & V12 & V13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
    set (m2 := wbytes m' (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))).
    assert (HW2 : W C A' m2 (with_vmmaps vm' md)).
    { subst m2. apply (W_store_win C A' m' _ _ _ CK HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; rewrite ?LV; lia. }
    assert (OUT2 : forall x : word, ~ (s - 32 <= u x < s - 24)%Z -> m2 x = m' x).
    { intros x Hx. subst m2. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PX2 : PIXat m2 pix (hdv w h d cm datas)) by (apply (PIXat_frame m'); [exact PX | intros x Hx; apply OUT2; lia]).
    assert (HCM : boxed (cm = 0%Z \/ ((1 <= cm)%Z /\ CMAPat m2 cm cv /\ cmap_ok cv /\ live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                    live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
                    cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ datas <> cm /\ datas <> c_arr cv))).
    { apply box_i. destruct RC as [Z0 | (Hc1 & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A' m' _ (Z_to_bv 64 cm) 24 CK HW' Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia. rewrite Evm in TOPc.
      split; [exact Hc1|]. split; [apply (CMAPat_frame m'); [exact CM | intros x Hx; apply OUT2; lia] |]. split; [exact (CMOK ltac:(lia))|].
      repeat (split; [assumption|]). exact N5. }
    assert (R8 : rdn SEGS m2 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
    { subst m2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact C1. }
    assert (R16 : rdn SEGS m2 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
    { subst m2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact C2. }
    assert (R24 : rdn SEGS m2 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
    { subst m2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact C3. }
    assert (R32 : rdn SEGS m2 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pix))).
    { subst m2. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
    apply (PH0 C A A' m2 md vm' s ret regs S pix w h d cm datas cv kR bR CK Hsp16 Etop eq_refl Hret H2 H4 HW2 PX2 HOK Hw Hh Lp Ld LpA LdA
             ltac:(apply box_i; exact NEdp) HCM RQ R8 R16 R24 R32 Hrm' ltac:(lia) ltac:(lia) KF r3 V2 V1 V8 V10 V11 V12 V13).
    intros x Hx. rewrite (AG3 x), (cs_rest_of_kept _ _ CS' x Hx), (AG1 x) by (nin_cs Hx). reflexivity.
Qed.
End Final.
End V21LeptFuzzMain.

Module V21LeptPinsI.
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
Import OSSVerify.leptonica.paintcmap_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptDefs.
Import V21Kit.
Import V21Drv1.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21LeptUb.
Import V21LeptFuzzMain.
Import V21LeptPinsA.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica.LeptRoom.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V21Kit.V21MallocLayout.

Import V21Drv1.V21FuzzIface.



Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Theorem u21_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LU21) (@mallocng_calloc_layout LU21),
  @fuzz_call_contract (@mallocng_alloc_layout LU21) (@mallocng_calloc_layout LU21) ASR.
Proof. intros ASR. exact (@lept_fuzz_call _ _ ASR u21_lept_pins u21_pins16). Qed.
End V21LeptPinsI.

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require V21Main.
Module V21Pins.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.paintcmap_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import V21Kit.
Import V21Drv1.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21Main.
(* [comment removed for export] *)
(* [comment removed for export] *)







Import V21Kit.V21MallocLayout. Import V21Kit.V21Startup. Import V21Kit.V21StartupDefs. Import V21Kit.V21StartupFacts.

Import V21Drv1.V21MainEntry. Import V21Drv1.V21Open. Import V21Drv1.V21Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x524ab) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem u21_pins : @V21Main.pins (@mallocng_alloc_layout LU21).
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout].
  - reflexivity.
  - reflexivity.
  - apply bv_eq. reflexivity.
  - apply bv_eq. reflexivity.
  - reflexivity.
  - intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LU21] in Hg.
    rewrite !u_small in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - intros a Hg. unfold mallocng_grantable in Hg. cbn [IMG_LO IMG_HI LU21] in Hg. exact Hg.
  - intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LU21] in He. rewrite !u_small in He by lia. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LU21] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LU21] in H. lia.
  - cbn. lia.
  - intros k Hk. exact Hk.
  - unfold mallocng_mmap_threshold. lia.
  - intros AMB sp0 a0s path envv tid regs0 mem0 Hvsp Hva Hve ME M (HEa & HEl & HEr).
    assert (Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z) by exact (proj1 Hvsp).
    assert (Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z) by exact (proj1 (proj2 Hvsp)).
    assert (Hal : (bv_unsigned sp0 mod 16 = 0)%Z) by exact (proj2 (proj2 Hvsp)).
    assert (LIBC : forall (a : Z) n, (0x32150 <= a)%Z -> (a + Z.of_nat n <= 0x52518)%Z -> (a + Z.of_nat n <= 0x3217c \/ 0x32180 <= a)%Z ->
              (a + Z.of_nat n <= 0x52260 \/ 0x52480 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LU21].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x524ab) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x524ab%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x524ab%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x524ab) + Z.of_nat 0)%Z with 0x524ab%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x524d8%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LU21]. change (bv_unsigned (Z_to_bv 64 0x524a8) + 8)%Z with 0x524b0%Z.
        rewrite (LIBC 0x524b0%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x20e88)) with 0x20e88%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End V21Pins.

From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver Require Spec.
Module V21Closed.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.paintcmap_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.CliDriver.Spec.
Import V21Kit.
Import V21Pins.
Import V21Drv1.
Import V21LeptPinsI.
Import OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21.V21Main.
(* [comment removed for export] *)







Import V21Kit.V21MallocLayout. Import V21Kit.V21Alloc. Import V21Kit.V21Sure.


Import V21Drv1.V21FuzzIface.

Import ListNotations.

Theorem u21_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Ubsan.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Ubsan.M.loaded_segments
      (init_config Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@V21Main.ref_realizes_spec_pins _ _ u21_sure V21Pins.u21_pins (u21_fuzz_call u21_sure)).
Qed.
End V21Closed.
