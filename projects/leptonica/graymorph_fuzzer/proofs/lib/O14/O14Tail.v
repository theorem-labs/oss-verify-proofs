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
From OSSVerify.leptonica.graymorph_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require MemSplit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptArith.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require GrayACELib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14Drv1.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptStderr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14CL7a.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptPixHdr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14CL8a.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptCmapValid.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptPixDestroy.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptDeser.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptCmap2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptPixCopyA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptPixCopy.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptGrayD_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptGrayA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptGrayDrv.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14_code_gmD_drv.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LeptRoom14.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LiaFast.
Module O14LeptFuzz.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.GrayACELib.
Import O14Drv1.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptStderr.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptBase.
Import O14CL7a.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixHdr.
Import O14CL8a.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptCmapValid.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixDestroy.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptDeser.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptCmap2.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixCopyA.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixCopy.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayD_iface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayA.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayDrv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14_code_gmD_drv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptRoom14.
(* [comment removed for export] *)








Import O14Drv1.O14FuzzIface.


Import O14CL7a.O14LeptErr.


Import O14CL8a.O14LeptCmap.



Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PixDestroyC.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
Lemma pixDestroy_fin_c : forall C A m md regs (s pp pix : Z) (ret s0v s1v : word) (S : TSet),
  Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 pp -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 8 = s0v -> getr regs' 9 = s1v ->
     (forall r, In r cs_rest -> getr regs' r = getr regs r) ->
     live A' (Z_to_bv 64 pix) = None -> (forall q, q <> Z_to_bv 64 pix -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15be4 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix ret s0v s1v S CK HW Hs16 Hlo Hpp Hpphi Hret H2 H8 H9 H4 R8 R16 R24 Lp L0p HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold ALLOC_STACK in Hlo.
  destruct (pxd_D al_rom regs m pix H8) as (r1 & RUN1 & Q10 & Q1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (Q2 : getr r1 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  replace (0x21ef4 : word) with (Z_to_bv 64 0x21ef4) by (apply bv_eq; reflexivity).
  apply (W_free16 C A m md r1 (Z_to_bv 64 pix) (Z_to_bv 64 0x15bec) 64 (s - 32) S CK HW Q10 Lp L0p Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 HWa CSa La LEQa PMa HRTa.
  replace (Z_to_bv 64 0x15bec) with (0x15bec : word) by (apply bv_eq; reflexivity).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 pp) by (csr; reflexivity).
  destruct (pxd_E al_rom r2 m1 s pp ret s0v s1v ltac:(lia) Hpp ltac:(lia) Hret) as (r3 & RUN3 & V2 & V1 & V8 & V9 & AG3).
  { apply (W_sok_win C A1 m1 _ pp 8 CK HWa); [lia | cbn; lia]. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16. }
  { rewrite (FRM_rdn16 C (s - 32) m m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24. }
  { exact E2. } { exact E9. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP : W C A1 (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm1 md) /\
               POSTM C (c_A0 C) (pp + 8) m (wbytes m1 (Z_to_bv 64 pp) (word_to_le_bytes 8 (Z_to_bv 64 0)))).
  { apply (WP_win C A1 (c_A0 C) m m1 _ _ _ (pp + 8) CK); [| exact (w_keep _ _ _ _ HWa) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    split; [exact HWa|]. apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa)|]. eapply POSTM_mono; [|exact PMa]. lia. }
  destruct WP as [HW3 PM3].
  apply (HK A1 _ vm1 r3); try assumption; try (solve [room_tac]).
  - intros r Hr. cbn [In cs_rest] in Hr.
    repeat (destruct Hr as [<-|Hr]; [csr; reflexivity|]). destruct Hr.
  - rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia.
  - intros a Ha. destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga & N2 & N3 & N4 & _).
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
    apply (proj1 PMa); try assumption; [intros [_ X]; lia | unfold scratch; lia].
Qed.


(* [comment removed for export] *)
Lemma pixDestroy_tail_c : forall C A m md regs (s pp pix cm karr : Z) (v : pixv) (cv : cmapv) (ret s0v s1v : word) (S : TSet),
  Cok C -> W C A m md ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 pp -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
  PIXat m pix v -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) ->
     getr regs' 2 = Z_to_bv 64 s -> getr regs' 8 = s0v -> getr regs' 9 = s1v ->
     (forall r, In r cs_rest -> getr regs' r = getr regs r) ->
     live A' (Z_to_bv 64 pix) = None ->
     (cm <> 0%Z -> live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 (c_arr cv)) = None) ->
     (forall q, q <> Z_to_bv 64 pix -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 (c_arr cv)) -> live A' q = live A q) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15bc0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr v cv ret s0v s1v S CK HW Hs16 Hlo Hpp Hpphi Hret H2 H8 H9 H4 R8 R16 R24 PX Ht Hc Lp L0p HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct HCM as [Hcm0 | (CM & Lcm & Larr & L0cm & L0arr & NE1 & NE2 & NE3 & Hk)].
  - (* [comment removed for export] *)
    rewrite Hcm0 in Hc.
    destruct (pxd_C0 al_rom regs m s pix v ltac:(lia) ltac:(lia) PX Ht Hc SOK ltac:(lia) H2 H8) as (r1 & RUN1 & Q2 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes m _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (Q9 : getr r1 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
    apply (pixDestroy_fin_c C A M1 md r1 s pp pix ret s0v s1v S CK HW1 Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret Q2 Q8 Q9 Q4);
      [subst M1; rdn_solve | subst M1; rdn_solve | subst M1; rdn_solve | exact Lp | exact L0p |].
    intros A' m' vm' regs' HW' X2 X8 X9 XR L' LEQ' PM' Rpp' CELL' RT'.
    apply (HK A' m' vm' regs' HW' X2 X8 X9); try assumption; try (solve [room_tac]).
    + intros r Hr. rewrite (XR r Hr). apply AG1. cbn [In cs_rest] in Hr.
      repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + intros X. exfalso. apply X. exact Hcm0.
    + intros q N1 _. apply LEQ'. exact N1.
    + eapply POSTM_trans; [exact PM1 | exact PM'].
    + intros a Ha. rewrite (CELL' a Ha). subst M1. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
  - (* [comment removed for export] *)
    pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF) as Rarr.
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    destruct (pxd_C1 al_rom regs m s pix cm v ltac:(lia) ltac:(lia) PX Ht Hc ltac:(lia) SOK ltac:(lia) H2 H8) as (r1 & RUN1 & Q2 & Q10 & Q1 & Q8 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes m _ _).
    assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1) by (subst M1; wp_win CK).
    destruct WP1 as [HW1 PM1].
    assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
    assert (CM1 : CMAPat M1 cm cv).
    { subst M1. apply (CMAPat_out m cm cv); [exact CM | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    apply (pixcmapDestroy_W C A M1 md r1 (s - 32) (s - 32) cm cv karr (Z_to_bv 64 0x15be0) S CK HW1 Q2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) Q1
             ltac:(red; apply bv_eq; reflexivity) Q4 Q10).
    { subst M1. rewrite <- (w2b_Z 8 cm) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
    { exact CM1. } { exact Lcm. } { exact Larr. } { exact L0cm. } { exact L0arr. } { exact NE1. }
    intros A1 m1 vm1 r2 HWa CSa La1 La2 LEQa PMa _ HRTa.
    replace (Z_to_bv 64 0x15be0) with (0x15be0 : word) by (apply bv_eq; reflexivity).
    assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (E8 : getr r2 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (E9 : getr r2 9 = Z_to_bv 64 pp) by (csr; reflexivity).
    assert (E4 : getr r2 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
    assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z).
    { rewrite (LEQa _ (zneq_w pix cm ltac:(lia) ltac:(lia) (not_eq_sym NE2)) (zneq_w pix (c_arr cv) ltac:(lia) ltac:(lia) (not_eq_sym NE3))). exact Lp. }
    (* [comment removed for export] *)
    assert (SOKp1 : store_ok SEGS m1 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
      exact (proj1 (proj2 (blk_byte C A1 m1 _ (Z_to_bv 64 pix) 64 x CK HWa Lp1 ltac:(rewrite u_Z2bv by lia; lia))) E). }
    pose proof (pxd_C2 al_rom r2 m1 pix ltac:(lia) ltac:(lia) SOKp1 E8) as RUN2.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN2 |].
    set (M2 := wbytes m1 _ _).
    assert (PMm1 : POSTM C (c_A0 C) (pp + 8) m m1).
    { eapply POSTM_trans; [exact PM1|]. apply (POSTM_sub C (c_A0 C) A1); [exact (w_keep _ _ _ _ HWa) | eapply POSTM_mono; [|exact PMa]; lia]. }
    assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) (pp + 8) m M2).
    { subst M2. apply (WP_blk C (c_A0 C) A1 m m1 _ (Z_to_bv 64 pix) _ 64); [exact CK | split; [exact HWa | exact PMm1] | exact Lp1 | exact L0p | exact L0p | exact (w_keep _ _ _ _ HWa) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
    destruct WP2 as [HW2 PM2].
    apply (pixDestroy_fin_c C A1 M2 _ r2 s pp pix ret s0v s1v S CK HW2 Hs16 ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret E2 E8 E9 E4).
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { subst M2. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
      rewrite (FRM_rdn16 C (s - 32 + 8) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
    { exact Lp1. }
    { exact L0p. }
    intros A' m' vm' regs' HW' X2 X8 X9 XR L' LEQ' PM' Rpp' CELL' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
    apply (HK A' m' vm' regs' HW' X2 X8 X9); try assumption; try (solve [room_tac]).
    + intros r Hr. rewrite (XR r Hr). rewrite (cs_rest_of_kept _ _ CSa r Hr). apply AG1. cbn [In cs_rest] in Hr.
      repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + intros _. split; [| ]. 
      * rewrite (LEQ' _ (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)). exact La1.
      * rewrite (LEQ' _ (zneq_w (c_arr cv) pix ltac:(lia) ltac:(lia) NE3)). exact La2.
    + intros q N1 N23. destruct (N23 ltac:(lia)) as [N2 N3]. rewrite (LEQ' q N1). apply LEQa; assumption.
    + eapply POSTM_trans; [exact PM2 | exact PM'].
    + intros a Ha. destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga & N2 & N3 & N4 & _).
      rewrite (CELL' a Ha). subst M2. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia).
      rewrite ((proj1 PMa) a); try assumption; [| intros [_ X]; lia | unfold scratch; lia].
      subst M1. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia.
Qed.

Theorem pixDestroy_cell_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x3be10 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (p_data v = 0%Z \/ (live A (Z_to_bv 64 (p_data v)) = Some R /\ live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ (0 < R)%Z /\
                      p_data v <> pix /\ (cm <> 0%Z -> p_data v <> cm /\ p_data v <> c_arr cv))) ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < pp)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x15b78 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pp pix cm karr R v cv ret S CK HW H2 Hs16 Hlo Hpp Hpphi H1 Hret H4 H10 Rpp PX Hrc Ht Hc Lp L0p HD HCM HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold ALLOC_STACK in Hlo.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (SOKp : store_ok SEGS m (Z_to_bv 64 pix) 64 = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m pix v x PX ltac:(lia) E). }
  destruct (pxd_A al_rom regs m s pp pix v ret ltac:(lia) Hpp ltac:(lia) ALp (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia))
              SOKp Rpp PX Hrc ltac:(lia) Gp H2 H1 H10) as (r1 & RUN1 & Q2 & Q8 & Q9 & Q10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M0 := wbytes (wbytes (wbytes m _ _) _ _) _ _).
  set (M1 := wbytes M0 _ _).
  assert (WP0 : W C A M0 md /\ POSTM C (c_A0 C) (pp + 8) m M0) by (subst M0; wp_win CK).
  assert (WP1 : W C A M1 md /\ POSTM C (c_A0 C) (pp + 8) m M1).
  { subst M1. apply (WP_blk C (c_A0 C) A m M0 md (Z_to_bv 64 pix) _ 64); [exact CK | exact WP0 | exact Lp | exact L0p | exact L0p | exact (w_keep _ _ _ _ HW) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
  destruct WP1 as [HW1 PM1]. clear WP0.
  assert (PX1 : PIXat M1 pix (set_rc v 0)).
  { subst M1. apply PIX_wr_rc; [|lia]. subst M0.
    repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
  assert (R8 : rdn SEGS M1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)) by (subst M1 M0; rdn_solve).
  assert (R16 : rdn SEGS M1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))) by (subst M1 M0; rdn_solve).
  assert (R24 : rdn SEGS M1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))) by (subst M1 M0; rdn_solve).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
  assert (HCM1 : cm = 0%Z \/ (CMAPat M1 cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)).
  { destruct HCM as [X|(CM & X)]; [left; exact X | right; split; [|exact X]].
    pose proof CM as (Hc0 & Hc64 & _). destruct X as (Lcm & _ & _ & _ & _ & NE2 & _).
    destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lcm Lp (zneq_w cm pix ltac:(lia) ltac:(lia) NE2)) as D.
    rewrite !u_Z2bv in D by lia. unfold round16 in D. change ((24 + 15) / 16)%Z with 2%Z in D. change ((64 + 15) / 16)%Z with 4%Z in D.
    subst M1 M0. repeat (apply CMAPat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact CM. }
  (* [comment removed for export] *)
  assert (TAIL : forall A1 m1 vm1 r2, W C A1 m1 (with_vmmaps vm1 md) ->
            getr r2 2 = Z_to_bv 64 (s - 32) -> getr r2 8 = Z_to_bv 64 pix -> getr r2 9 = Z_to_bv 64 pp -> getr r2 4 = Z_to_bv 64 0x3be10 ->
            (forall r, In r cs_rest -> getr r2 r = getr regs r) ->
            POSTM C (c_A0 C) (s - 32) M1 m1 -> PIXat m1 pix (set_rc v 0) ->
            live A1 (Z_to_bv 64 pix) = Some 64%Z ->
            (cm <> 0%Z -> live A1 (Z_to_bv 64 cm) = live A (Z_to_bv 64 cm) /\ live A1 (Z_to_bv 64 (c_arr cv)) = live A (Z_to_bv 64 (c_arr cv))) ->
            (p_data v <> 0%Z -> live A1 (Z_to_bv 64 (p_data v)) = None) ->
            (forall q, (p_data v <> 0%Z -> q <> Z_to_bv 64 (p_data v)) -> live A1 q = live A q) ->
            (cm <> 0%Z -> CMAPat m1 cm cv) ->
            roomtr A (m_vmmaps md) A1 vm1 0 0 -> (forall a : word, (s <= u a < pp)%Z -> m1 a = M1 a) ->
            realizes SEGS (mkCfg (mkst r2 (0x15bc0 : word) m1 al_rom) (with_vmmaps vm1 md)) S).
  { intros A1 m1 vm1 r2 HWa E2 E8 E9 E4 ER PMa PXa Lp1 Lcm1 LD1 LEQa CMa RTa CELLa.
    apply (pixDestroy_tail_c C A1 m1 _ r2 s pp pix cm karr (set_rc v 0) cv ret (getr regs 8) (getr regs 9) S CK HWa Hs16
             ltac:(unfold ALLOC_STACK; lia) Hpp Hpphi Hret E2 E8 E9 E4).
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). exact R8.
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact R16.
    - rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact R24.
    - exact PXa.
    - cbn. exact Ht.
    - cbn. exact Hc.
    - exact Lp1.
    - exact L0p.
    - destruct HCM1 as [X|(CM & Lcm & Larr & X)]; [left; exact X | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A M1 md _ _ CK HW1 Lcm ltac:(lia)) as [G _]. rewrite u_Z2bv in G by lia.
      assert (NC : cm <> 0%Z) by lia.
      destruct (Lcm1 NC) as [E1 E2']. rewrite E1, E2'.
      split; [exact (CMa NC) | split; [exact Lcm | split; [exact Larr | exact X]]].
    - intros A' m' vm' regs' HW' X2 X8 X9 XR L' Lcm' LEQ' PM' Rpp' CELL' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
      apply (HK A' m' vm' regs' HW').
      + apply cs_kept_of_rest; [rewrite X2, H2; reflexivity | exact X8 | exact X9 |].
        intros r Hr. rewrite (XR r Hr). exact (ER r Hr).
      + split; [exact L'|]. split; [|split].
        * intros ND. destruct HD as [X|(LR & LR0 & HR & NEdp & NEdc)]; [exfalso; exact (ND X)|].
          rewrite (LEQ' (Z_to_bv 64 (p_data v))); [exact (LD1 ND) | apply zneq_w; lia |].
          intros NC. destruct (NEdc NC) as [N2 N3].
          destruct HCM as [X|(CM & _ & _ & _ & _ & _)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
          split; apply zneq_w; lia.
        * intros NC. exact (Lcm' NC).
        * intros q N1 N2 N3. rewrite (LEQ' q N1 N3). apply LEQa. exact N2.
      + eapply POSTM_trans; [eapply POSTM_mono; [|exact PM1]; lia|]. eapply POSTM_trans; [eapply POSTM_mono; [|exact PMa]; lia | exact PM'].
      + exact Rpp'.
      + intros a Ha. rewrite (CELL' a Ha), (CELLa a Ha). subst M1 M0.
        destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga & _).
        rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity.
      + room_tac. }
  assert (ER1 : forall r, In r cs_rest -> getr r1 r = getr regs r).
  { intros r Hr. apply AG1. cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr. }
  destruct HD as [D0 | (LR & LR0 & HR & NEdp & NEdc)].
  - (* [comment removed for export] *)
    rewrite D0 in Q10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (pxd_B0 al_rom r1 M1 Q10) |].
    rewrite <- (with_vmmaps_same md). rewrite <- (with_vmmaps_same md) in HW1.
    apply (TAIL A M1 (m_vmmaps md) r1 HW1 Q2 Q8 Q9 Q4 ER1).
    + apply POSTM_refl.
    + exact PX1.
    + exact Lp.
    + intros _. split; reflexivity.
    + intros ND. exfalso. exact (ND D0).
    + intros q _. reflexivity.
    + intros NC. destruct HCM1 as [X|(CM & _)]; [exfalso; exact (NC X) | exact CM].
    + room_tac.
    + intros a _. reflexivity.
  - (* [comment removed for export] *)
    rename R into Rn.
    destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) Rn CK HW LR HR) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    destruct (pxd_B1 al_rom r1 M1 (p_data v) ltac:(lia) ltac:(lia) (W_pmm_free C A M1 md HW1) Q10) as (r2 & RUN2 & P10 & P1 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (P4 : getr r2 4 = Z_to_bv 64 0x3be10) by (csr; reflexivity).
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x21ef4 : word) with (Z_to_bv 64 0x21ef4) by (apply bv_eq; reflexivity).
    apply (W_free16 C A M1 md r2 (Z_to_bv 64 (p_data v)) (Z_to_bv 64 0x15bc0) Rn (s - 32) S CK HW1 P10 LR LR0 P1
             ltac:(red; apply bv_eq; reflexivity) P4 P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r3 HWa CSa La LEQa PMa HRTa.
    replace (Z_to_bv 64 0x15bc0) with (0x15bc0 : word) by (apply bv_eq; reflexivity).
    assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 (p_data v)) by (apply zneq_w; lia).
    assert (Lp1 : live A1 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (LEQa _ NEpd); exact Lp).
    apply (TAIL A1 m1 vm1 r3 HWa).
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + intros r Hr. rewrite (cs_rest_of_kept _ _ CSa r Hr). rewrite (AG2 r). exact (ER1 r Hr).
      cbn [In cs_rest] in Hr. repeat (destruct Hr as [<-|Hr]; [notin_lit|]). destruct Hr.
    + apply (POSTM_sub C (c_A0 C) A1); [exact (W_sub0 _ _ _ _ HWa) | exact PMa].
    + apply (PIXat_frame M1); [exact PX1|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 pix) 64%Z (u x - pix)%Z Lp1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
    + exact Lp1.
    + intros NC. destruct (NEdc NC) as [N2 N3].
      destruct HCM as [X|(CM & _)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof (cf_arr _ CWF).
      split; apply LEQa; apply zneq_w; lia.
    + intros _. exact La.
    + intros q Hq. apply LEQa. apply Hq. lia.
    + intros NC. destruct HCM1 as [X|(CM & Lcm & X)]; [exfalso; exact (NC X)|]. pose proof CM as (Hc0 & Hc64 & CWF & _).
      destruct (NEdc NC) as [N2 N3].
      assert (Lcm1 : live A1 (Z_to_bv 64 cm) = Some 24%Z) by (rewrite (LEQa _ (zneq_w cm (p_data v) ltac:(lia) ltac:(lia) (not_eq_sym N2))); exact Lcm).
      apply (CMAPat_frame M1); [exact CM|]. intros x Hx. pose proof (proj2 PMa (Z_to_bv 64 cm) 24%Z (u x - cm)%Z Lcm1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (cm + (u x - cm))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E.
    + room_tac.
    + intros a Ha. destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga & N2 & N3 & N4 & _).
      apply (proj1 PMa); try assumption; [intros [_ X]; lia | unfold scratch; lia].
Qed.

End PixDestroyC.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzSegs.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rnd1_spec (pcR ra1 : word) : Prop :=
  forall rom regs m (s pixs : Z), (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 8 = Z_to_bv 64 pixs ->
    exists regs', msteps SEGS (mkst regs pcR m rom) (mkst regs' (0x16424 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = ra1 /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
Definition rnd2_spec (ra1 ra2 : word) (drv : Z) : Prop :=
  forall rom regs m (s a0v : Z), (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 a0v ->
    exists regs', msteps SEGS (mkst regs ra1 m rom) (mkst regs' (Z_to_bv 64 drv) (wbytes m (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 a0v))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = ra2 /\ getr regs' 10 = Z_to_bv 64 a0v /\ getr regs' 11 = Z_to_bv 64 3 /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 11; 12]%list) regs regs'.
Definition rnd3_spec (ra2 ra3 : word) : Prop :=
  forall rom regs m (s a0v : Z), (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= a0v < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 a0v ->
    exists regs', msteps SEGS (mkst regs ra2 m rom) (mkst regs' (0x15b78 : word) (wbytes m (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 a0v))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = ra3 /\ getr regs' 10 = Z_to_bv 64 (s - 40)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Definition rnd4_spec (ra3 ra4 : word) : Prop :=
  forall rom regs m (s : Z), (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs ra3 m rom) (mkst regs' (0x15b78 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = ra4 /\ getr regs' 10 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.

Section Segs.
Variable rom : word -> option byte.

  Definition FZ3 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma fz_small : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= sz < 3)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x15244 : word) m rom) (mkst regs' ret (FZ3 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz Hret SOK H2 H1 H10 H11. unfold FZ3. eexists. split.
    - zv F_15148 D_15148 (Z_to_bv 64 (s - 48)).
      stepST F_1514c D_1514c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15150 D_15150 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15154 D_15154 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_15158 D_15158. sn F_1515c D_1515c. stepb_tk F_15160 D_15160 ltac:(condZ).
      sn F_15254 D_15254.
      stepLD8 F_15258 D_15258 ret. stepLD8 F_1525c D_1525c (getr regs 8). stepLD8 F_15260 D_15260 (getr regs 9).
      zv F_15264 D_15264 (Z_to_bv 64 s). stepret F_15268 D_15268 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_A : forall regs m (s sz : Z) (dptr ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (3 <= sz < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    store_ok SEGS m (Z_to_bv 64 0x2bab8) 8 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = dptr -> getr regs 11 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x15244 : word) m rom)
                              (mkst regs' (0x1f9c4 : word) (wbytes (FZ3 m s ret regs) (Z_to_bv 64 0x2bab8) (word_to_le_bytes 8 (Z_to_bv 64 0x15368))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x1527c /\ getr regs' 10 = dptr /\ getr regs' 11 = Z_to_bv 64 sz
      /\ getr regs' 8 = Z_to_bv 64 sz /\ getr regs' 9 = dptr
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s sz dptr ret Hs Hs64 Hsz SOK SOKh H2 H1 H10 H11. unfold FZ3. eexists. split.
    - zv F_15148 D_15148 (Z_to_bv 64 (s - 48)).
      stepST F_1514c D_1514c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_15150 D_15150 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_15154 D_15154 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      sn F_15158 D_15158. sn F_1515c D_1515c. stepb_ft F_15160 D_15160 ltac:(condZ).
      sn F_15164 D_15164. sn F_15168 D_15168. sn F_1516c D_1516c. sn F_15170 D_15170.
      stepb_tk F_1538c D_1538c ltac:(condZ).
      sn F_15398 D_15398.
      stepST F_1539c D_1539c (Z_to_bv 64 0x2bab8) (Z_to_bv 64 0x15368) ltac:(store_ok_peel; exact SOKh).
      stepret F_153a0 D_153a0 (0x15270 : word) ltac:(bveq).
      sn F_15174 D_15174. sn F_15178 D_15178. sn F_1517c D_1517c. sn F_1f8c4 D_1f8c4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B0 : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x1527c : word) m rom) (mkst regs' ret (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret SOK R1 R2 R3 H2 H10. eexists. split.
    - stepST F_15180 D_15180 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_15184 D_15184 ltac:(condZ).
      sn F_15254 D_15254.
      stepLD8 F_15258 D_15258 ret. stepLD8 F_1525c D_1525c s0v. stepLD8 F_15260 D_15260 s1v.
      zv F_15264 D_15264 (Z_to_bv 64 s). stepret F_15268 D_15268 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_B1 : forall regs m (s pix : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pix)%Z -> (pix < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    exists regs', msteps SEGS (mkst regs (0x1527c : word) m rom) (mkst regs' (0x15288 : word) (wbytes m (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 pix))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [8]%list) regs regs'.
  Proof.
    intros regs m s pix Hs Hs64 Hp Hp64 SOK H2 H10. eexists. split.
    - stepST F_15180 D_15180 (Z_to_bv 64 (s - 32)) (Z_to_bv 64 pix) ltac:(sok_in SOK).
      stepb_ft F_15184 D_15184 ltac:(condZ).
      zv F_15188 D_15188 (Z_to_bv 64 pix). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_J : forall regs m (s : Z),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x15348 : word) m rom) (mkst regs' (0x15b78 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 1 = Z_to_bv 64 0x15350 /\ getr regs' 10 = Z_to_bv 64 (s - 32)
      /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2. eexists. split.
    - zv F_1524c D_1524c (Z_to_bv 64 (s - 32)). sn F_15250 D_15250. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma fz_Z : forall regs m (s : Z) (ret s0v s1v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs', msteps SEGS (mkst regs (0x15350 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v Hs Hs64 Hret R1 R2 R3 H2. eexists. split.
    - sn F_15254 D_15254.
      stepLD8 F_15258 D_15258 ret. stepLD8 F_1525c D_1525c s0v. stepLD8 F_15260 D_15260 s1v.
      zv F_15264 D_15264 (Z_to_bv 64 s). stepret F_15268 D_15268 ret ltac:(bveq). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

(* [comment removed for export] *)
Lemma rc_1 : rnd1_spec (0x15288 : word) (0x15294 : word).
Proof.
  unfold rnd1_spec. intros rom regs m s pixs Hs Hs64 H2 H8. eexists. split.
  - sn F_1518c D_1518c. zv F_15190 D_15190 (Z_to_bv 64 pixs). sn F_15194 D_15194. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma rc_2 : rnd2_spec (0x15294 : word) (0x152a4 : word) PC_pixCloseGray3.
Proof.
  unfold rnd2_spec, PC_pixCloseGray3. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x21128) with (0x21128 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_15198 D_15198 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_1519c D_1519c. sn F_151a0 D_151a0. sn F_151a4 D_151a4. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma rc_3 : rnd3_spec (0x152a4 : word) (0x152b0 : word).
Proof.
  unfold rnd3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10. eexists. split.
  - stepST F_151a8 D_151a8 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_151ac D_151ac (Z_to_bv 64 (s - 40)). sn F_151b0 D_151b0. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma rc_4 : rnd4_spec (0x152b0 : word) (0x152b8 : word).
Proof.
  unfold rnd4_spec. intros rom regs m s Hs Hs64 H2. eexists. split.
  - zv F_151b4 D_151b4 (Z_to_bv 64 (s - 48)). sn F_151b8 D_151b8. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma rd_1 : rnd1_spec (0x152b8 : word) (0x152c4 : word).
Proof.
  unfold rnd1_spec. intros rom regs m s pixs Hs Hs64 H2 H8. eexists. split.
  - sn F_151bc D_151bc. zv F_151c0 D_151c0 (Z_to_bv 64 pixs). sn F_151c4 D_151c4. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma rd_2 : rnd2_spec (0x152c4 : word) (0x152d4 : word) PC_pixDilateGray3.
Proof.
  unfold rnd2_spec, PC_pixDilateGray3. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x20660) with (0x20660 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_151c8 D_151c8 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_151cc D_151cc. sn F_151d0 D_151d0. sn F_151d4 D_151d4. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma rd_3 : rnd3_spec (0x152d4 : word) (0x152e0 : word).
Proof.
  unfold rnd3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10. eexists. split.
  - stepST F_151d8 D_151d8 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_151dc D_151dc (Z_to_bv 64 (s - 40)). sn F_151e0 D_151e0. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma rd_4 : rnd4_spec (0x152e0 : word) (0x152e8 : word).
Proof.
  unfold rnd4_spec. intros rom regs m s Hs Hs64 H2. eexists. split.
  - zv F_151e4 D_151e4 (Z_to_bv 64 (s - 48)). sn F_151e8 D_151e8. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma re_1 : rnd1_spec (0x152e8 : word) (0x152f4 : word).
Proof.
  unfold rnd1_spec. intros rom regs m s pixs Hs Hs64 H2 H8. eexists. split.
  - sn F_151ec D_151ec. zv F_151f0 D_151f0 (Z_to_bv 64 pixs). sn F_151f4 D_151f4. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma re_2 : rnd2_spec (0x152f4 : word) (0x15304 : word) PC_pixErodeGray3.
Proof.
  unfold rnd2_spec, PC_pixErodeGray3. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x1fe10) with (0x1fe10 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_151f8 D_151f8 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_151fc D_151fc. sn F_15200 D_15200. sn F_15204 D_15204. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma re_3 : rnd3_spec (0x15304 : word) (0x15310 : word).
Proof.
  unfold rnd3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10. eexists. split.
  - stepST F_15208 D_15208 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_1520c D_1520c (Z_to_bv 64 (s - 40)). sn F_15210 D_15210. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma re_4 : rnd4_spec (0x15310 : word) (0x15318 : word).
Proof.
  unfold rnd4_spec. intros rom regs m s Hs Hs64 H2. eexists. split.
  - zv F_15214 D_15214 (Z_to_bv 64 (s - 48)). sn F_15218 D_15218. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

Lemma ro_1 : rnd1_spec (0x15318 : word) (0x15324 : word).
Proof.
  unfold rnd1_spec. intros rom regs m s pixs Hs Hs64 H2 H8. eexists. split.
  - sn F_1521c D_1521c. zv F_15220 D_15220 (Z_to_bv 64 pixs). sn F_15224 D_15224. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma ro_2 : rnd2_spec (0x15324 : word) (0x15334 : word) PC_pixOpenGray3.
Proof.
  unfold rnd2_spec, PC_pixOpenGray3. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10.
  replace (Z_to_bv 64 0x20eb0) with (0x20eb0 : word) by (apply bv_eq; reflexivity).
  eexists. split.
  - stepST F_15228 D_15228 (Z_to_bv 64 (s - 40)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    sn F_1522c D_1522c. sn F_15230 D_15230. sn F_15234 D_15234. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma ro_3 : rnd3_spec (0x15334 : word) (0x15340 : word).
Proof.
  unfold rnd3_spec. intros rom regs m s a0v Hs Hs64 Ha SOK H2 H10. eexists. split.
  - stepST F_15238 D_15238 (Z_to_bv 64 (s - 48)) (Z_to_bv 64 a0v) ltac:(sok_in SOK).
    zv F_1523c D_1523c (Z_to_bv 64 (s - 40)). sn F_15240 D_15240. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.
Lemma ro_4 : rnd4_spec (0x15340 : word) (0x15348 : word).
Proof.
  unfold rnd4_spec. intros rom regs m s Hs Hs64 H2. eexists. split.
  - zv F_15244 D_15244 (Z_to_bv 64 (s - 48)). sn F_15248 D_15248. apply mst_refl.
  - repeat split; gres; pin; try reflexivity; try (apply bv_eq; reflexivity). solve_regs_agree.
Qed.

End FuzzSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Phases.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

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
  Hypothesis H4 : getr regs 4 = Z_to_bv 64 0x3be10.
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
  Hypothesis Hrm : aroom A1 vm1 (kR - RK_deser) (bR - RB_deser).
  Hypothesis Hrk : (RK_graymorph <= kR)%Z.
  Hypothesis Hrb : (RB_graymorph <= bR)%Z.
  (* [comment removed for export] *)
  Hypothesis KF : forall A' m' vm' r', W C A' m' (with_vmmaps vm' md0) -> (forall q, live A' q = live A q) ->
    getr r' 10 = Z_to_bv 64 0 -> cs_kept regs r' -> aroom A' vm' (kR - RK_graymorph) (bR - RB_graymorph) -> realizes SEGS (mkCfg (mkst r' ret m' al_rom) (with_vmmaps vm' md0)) S.

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
    W C1 A7 m9 (with_vmmaps vm7 md0) -> aroom A7 vm7 (kR - RK_graymorph) (bR - RB_graymorph) -> FRM C1 (s - 32) m2 m9 -> (forall q, live A7 q = live A1 q) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x15348 : word) m9 al_rom) (with_vmmaps vm7 md0)) S.
  Proof.
    intros A7 m9 vm7 r HW9 Hrm7 F9 LQ7 Q2 RR.
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof PXs as (Hp0 & Hp64 & WFs & _). pose proof (wf_data _ WFs) as Rds. cbn [p_data hdv] in Rds.
    destruct (blk_range C A1 m2 _ (Z_to_bv 64 datas) _ CK HW2 Lds ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
    destruct (later_cells A7 m9 _ HW9 F9) as (C8 & C16 & C24 & C32). destruct (later_pixs A7 m9 _ HW9) as [PX9 CM9].
    pose proof (W_unbase C A1 m2 _ A7 m9 _ HW2 HW9) as HW9'.
    destruct (fz_J al_rom r m9 s ltac:(lia) ltac:(lia) Q2) as (r1 & RUN1 & P2 & P1 & P10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact RUN1 |].
    assert (P4 : getr r1 4 = Z_to_bv 64 0x3be10) by (rewrite (AG1 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
    apply (pixDestroy_W C A7 m9 _ r1 (s - 48) (s - 32) pixs cm (4 * c_nalloc cv) (4 * (wpl_of w d * h)) (hdv w h d cm datas) cv (Z_to_bv 64 0x15350) S
             CK HW9' P2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
             P1 ltac:(red; apply bv_eq; reflexivity) P4 P10 ltac:(rewrite <- w2l_Z8 by lia; exact C32) PX9 eq_refl eq_refl eq_refl).
    - rewrite LQ7. exact Lps.
    - rewrite HA0. exact L0ps.
    - right. cbn [p_data hdv]. rewrite LQ7, HA0. pose proof (box_e _ NEsd) as NEsd'. split; [exact Lds|]. split; [exact L0ds|]. split; [lia|]. split; [lia|].
      intros NZ. destruct (box_e _ HCM) as [Z0 | X]; [exfalso; exact (NZ Z0) | lia].
    - cbn [p_cmap hdv]. destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & CMOK & Lc & La & L0c & L0a & N1 & N2 & N3 & N4 & N5)]; [left; exact Z0 | right].
      rewrite !LQ7, HA0. pose proof CMOK as (Hcd & Hna & _). split; [exact (CM9 ltac:(lia))|]. repeat (split; [assumption|]).
      rewrite Hna. destruct Hcd as [->|[->|[->| ->]]]; cbn; lia.
    - intros A8 m10 vm8 r2 HW10 CS10 PD POST R0 HRT10. rewrite with_vmmaps_twice in HW10 |- *.
      replace (Z_to_bv 64 0x15350) with (0x15350 : word) by (apply bv_eq; reflexivity).
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
  (* [comment removed for export] *)
  Section Round.
  Variables (pcR ra1 ra2 ra3 ra4 : word) (drv RKd RBd : Z).
  Hypothesis S1 : rnd1_spec pcR ra1.
  Hypothesis S2 : rnd2_spec ra1 ra2 drv.
  Hypothesis S3 : rnd3_spec ra2 ra3.
  Hypothesis S4 : rnd4_spec ra3 ra4.
  Hypothesis RO1 : ret_ok ra1.
  Hypothesis RO2 : ret_ok ra2.
  Hypothesis RO3 : ret_ok ra3.
  Hypothesis RO4 : ret_ok ra4.
  Hypothesis DRV : gray3_contract drv RKd RBd.
  Hypothesis DRVn : gray3_null_contract drv.
  Hypothesis HRKd : (0 <= RKd)%Z.
  Hypothesis HRBd : (0 <= RBd)%Z.
  Variables (kk bb : Z).
  Hypothesis Hkk : (RK_pixcopy + RKd <= kk)%Z.
  Hypothesis Hbb : (RB_pixcopy14 + RBd <= bb)%Z.
  (* [comment removed for export] *)
  Hypothesis NEXT : forall A9 m9 vm9 r9, W C1 A9 m9 (with_vmmaps vm9 md0) -> aroom A9 vm9 (kk - RK_pixcopy - RKd) (bb - RB_pixcopy14 - RBd) ->
       FRM C1 (s - 32) m2 m9 -> (forall q, live A9 q = live A1 q) -> getr r9 2 = Z_to_bv 64 (s - 48) -> getr r9 8 = Z_to_bv 64 pixs ->
       (forall x, In x cs_rest -> getr r9 x = getr regs x) ->
       realizes SEGS (mkCfg (mkst r9 ra4 m9 al_rom) (with_vmmaps vm9 md0)) S.

  (* [comment removed for export] *)
  Lemma rnd_end : forall A3 m3 vm3 r3 (res : Z),
    W C1 A3 m3 (with_vmmaps vm3 md0) -> aroom A3 vm3 (kk - RK_pixcopy - RKd) (bb - RB_pixcopy14 - RBd) -> FRM C1 (s - 32) m2 m3 ->
    rdn SEGS m3 (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 res) ->
    ( (res = 0%Z /\ forall q, live A3 q = live A1 q)
      \/ (exists datar, d = 8%Z /\ pix_own C1 A1 A3 m3 res w h 8 datar /\ forall q, q <> Z_to_bv 64 res -> q <> Z_to_bv 64 datar -> live A3 q = live A1 q) ) ->
    getr r3 2 = Z_to_bv 64 (s - 48) -> getr r3 8 = Z_to_bv 64 pixs -> (forall x, In x cs_rest -> getr r3 x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r3 ra3 m3 al_rom) (with_vmmaps vm3 md0)) S.
  Proof.
    intros A3 m3 vm3 r3 res HW3 Hrm3 F3 Rres RES Q2 Q8 RR.
    assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof CK1 as CK1'.
    destruct (S4 al_rom r3 m3 s ltac:(lia) ltac:(lia) Q2) as (r4 & RUN4 & E2 & E1 & E10 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    destruct RES as [[R0 LQ3] | (datar & Ed & OWN & LEQ3)].
    - subst res.
      apply (pixDestroy_null_W C1 A3 m3 _ r4 (s - 48) (s - 48) ra4 S CK1' HW3 E2 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) E1 RO4 E10 Rres).
      intros m4 r5 HW4 CS5 PM4 OUT4.
      apply (NEXT A3 m4 vm3 r5 HW4 Hrm3).
      + eapply FRM_trans; [exact F3 | eapply FRM_mono; [exact (proj1 PM4) | lia]].
      + exact LQ3.
      + csr. reflexivity.
      + csr. reflexivity.
      + intros x Hx. rewrite (cs_rest_of_kept _ _ CS5 x Hx), (AG4 x) by (nin_cs Hx). exact (RR x Hx).
    - pose proof OWN as (Gr & TOPr & ALr & Gdr & TOPdr & ALdr & NEr & LAr & LAdr & L0r & L0dr & L3r & L3dr & PXr).
      assert (HOK8 : hdr_ok w h 8) by (rewrite <- Ed; exact HOK).
      pose proof (raster_pos w h 8 HOK8 Hw Hh) as Rpos.
      assert (E4 : getr r4 4 = Z_to_bv 64 0x3be10) by (rewrite (AG4 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
      apply (pixDestroy_keep_W C1 A3 m3 _ r4 (s - 48) (s - 48) res (4 * (wpl_of w 8 * h)) (hdv w h 8 0 datar) ra4 S CK1' HW3 E2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia) E1 RO4 E4 E10 Rres PXr
               eq_refl eq_refl eq_refl L3r L0r L3dr L0dr Rpos ltac:(cbn; lia)).
      intros A4 m4 vm4 r5 HW4 CS5 L4r L4dr LEQ4 PM4 R4 OUT4 RT4. cbn [p_data hdv] in L4dr, LEQ4. rewrite with_vmmaps_twice in HW4 |- *.
      apply (NEXT A4 m4 vm4 r5 HW4).
      + rewrite with_vmmaps_vmmaps in RT4. pose proof (RT4 _ _ Hrm3 ltac:(lia) ltac:(lia)) as X. rewrite !Z.sub_0_r in X. exact X.
      + eapply FRM_trans; [exact F3 | eapply FRM_mono; [exact (proj1 PM4) | lia]].
      + intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 res)) as [->|N1]; [rewrite L4r, LAr; reflexivity|].
        destruct (bv_eq_dec _ q (Z_to_bv 64 datar)) as [->|N2]; [rewrite L4dr, LAdr; reflexivity|].
        rewrite (LEQ4 q N1 N2). exact (LEQ3 q N1 N2).
      + csr. reflexivity.
      + csr. reflexivity.
      + intros x Hx. rewrite (cs_rest_of_kept _ _ CS5 x Hx), (AG4 x) by (nin_cs Hx). exact (RR x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma round_W : forall Ak mk vmk r,
    W C1 Ak mk (with_vmmaps vmk md0) -> aroom Ak vmk kk bb -> FRM C1 (s - 32) m2 mk -> (forall q, live Ak q = live A1 q) ->
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pixs -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r pcR mk al_rom) (with_vmmaps vmk md0)) S.
  Proof.
    intros Ak mk vmk r HWk Hrmk Fk LQk Q2 Q8 RR.
    assert (KP : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z) by (clear; room_consts; lia).
    pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. rewrite Htop in *.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof CK1 as CK1'.
    destruct (later_pixs Ak mk _ HWk) as [PXk CMk].
    (* [comment removed for export] *)
    destruct (S1 al_rom r mk s pixs ltac:(lia) ltac:(lia) Q2 Q8) as (r1 & RUN1 & E2 & E1 & E10 & E11 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |].
    assert (E4 : getr r1 4 = Z_to_bv 64 0x3be10) by (rewrite (AG1 4) by notin_list; rewrite (RR 4) by (cbn; tauto); exact H4).
    rewrite <- (with_vmmaps_vmmaps vmk md0) in Hrmk.
    refine (pixCopy_W C1 Ak mk _ r1 (s - 48) pixs w h d cm datas cv ra1 S CK1' HWk E2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(cbn; unfold LSF; lia) ltac:(cbn; lia) E1 RO1 E4 E10 E11 PXk HOK Hw Hh _ _ _ kk bb Hrmk ltac:(lia) ltac:(lia) _).
    { rewrite LQk. exact Lps. }
    { rewrite LQk. exact Lds. }
    { destruct (box_e _ HCM) as [Z0 | (Hc1 & CM & CMOK & Lc & La & _)]; [left; exact Z0 | right]. rewrite !LQk. split; [exact (CMk ltac:(lia)) | split; [exact CMOK | split; [exact Lc | exact La]]]. }
    unfold TK. intros A' m' vm' r2 HW' CS2 PM' RES Hrm'. rewrite with_vmmaps_twice in HW' |- *.
    assert (F' : FRM C1 (s - 32) m2 m') by (eapply FRM_trans; [exact Fk | eapply FRM_mono; [exact (proj1 PM') | lia]]).
    assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Y8 : getr r2 8 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (RR2 : forall x, In x cs_rest -> getr r2 x = getr regs x).
    { intros x Hx. rewrite (cs_rest_of_kept _ _ CS2 x Hx), (AG1 x) by (nin_cs Hx). exact (RR x Hx). }
    pose proof (W_sok_win C1 A' m' _ (s - 48) 48 CK1' HW' ltac:(cbn; lia) ltac:(cbn; lia)) as SOK'.
    destruct RES as [[R0 LQ'] | (copy & cd & data & R0 & PT)].
    - (* [comment removed for export] *)
      destruct (S2 al_rom r2 m' s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 R0) as (r3 & RUN3 & G2 & G1 & G10 & G11 & G12 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
      set (M := wbytes m' (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      assert (HWM : W C1 A' M (with_vmmaps vm' md0)) by (subst M; apply (W_store_win C1 A' m' _ _ _ CK1' HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (FM : FRM C1 (s - 32) m2 M) by (subst M; apply FRM_win_write; [exact F' | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
      assert (R40 : rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 0)).
      { subst M. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
      apply (DRVn C1 A' M _ r3 (s - 48)%Z ra2 S CK1' HWM G2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(cbn; unfold GM3_STACK, G3H_STACK, LSF; lia) ltac:(cbn; lia) G1 RO2 G10).
      intros m'' r4 HW'' CS4 PM'' A0.
      assert (F'' : FRM C1 (s - 32) m2 m'') by (eapply FRM_trans; [exact FM | eapply FRM_mono; [exact (proj1 PM'') | lia]]).
      assert (I2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      pose proof (W_sok_win C1 A' m'' _ (s - 48) 48 CK1' HW'' ltac:(cbn; lia) ltac:(cbn; lia)) as SOK''.
      destruct (S3 al_rom r4 m'' s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) SOK'' I2 A0) as (r5 & RUN5 & J2 & J1 & J10 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW'')) | exact (mp_lazy _ (w_pure _ _ _ _ HW'')) | exact RUN5 |].
      set (M' := wbytes m'' (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      assert (HWM' : W C1 A' M' (with_vmmaps vm' md0)) by (subst M'; apply (W_store_win C1 A' m'' _ _ _ CK1' HW''); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (FM' : FRM C1 (s - 32) m2 M') by (subst M'; apply FRM_win_write; [exact F'' | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
      assert (R40' : rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 0)).
      { subst M'. rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
        rewrite (FRM_rdn16 C1 (s - 48) M m'' (s - 40) 8 CK1' (proj1 PM'')) by (cbn; lia). exact R40. }
      assert (R48' : rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 0)).
      { subst M'. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
      apply (pixDestroy_null_W C1 A' M' _ r5 (s - 48) (s - 40) ra3 S CK1' HWM' J2 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) J1 RO3 J10 R40').
      intros m3 r6 HW3 CS6 PM3 OUT3.
      apply (rnd_end A' m3 vm' r6 0%Z HW3).
      + apply (aroom_mono A' vm' (kk - RK_pixcopy) (bb - RB_pixcopy14)); [exact Hrm' | lia | lia].
      + eapply FRM_trans; [exact FM' | eapply FRM_mono; [exact (proj1 PM3) | lia]].
      + apply (cell_out M' m3 (s - 48)); [intros x Hx; apply OUT3; lia | lia | lia | exact R48'].
      + left. split; [reflexivity|]. intros q. rewrite LQ'. apply LQk.
      + csr. reflexivity.
      + csr. reflexivity.
      + intros x Hx. rewrite (cs_rest_of_kept _ _ CS6 x Hx), (AG5 x), (cs_rest_of_kept _ _ CS4 x Hx), (AG3 x) by (nin_cs Hx). exact (RR2 x Hx).
    - (* [comment removed for export] *)
      pose proof PT as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Lkp & Lkd & L1p & L1d & L'p & L'd & PXd & CMR).
      cbn [C1 rebase c_vm c_A0] in TOPp, TOPd, L1p, L1d.
      set (n := (4 * (wpl_of w d * h))%Z) in *.
      assert (Hn0 : (0 < n)%Z) by (subst n; assert (1 * 1 <= wpl_of w d * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
      destruct (S2 al_rom r2 m' s copy ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 R0) as (r3 & RUN3 & G2 & G1 & G10 & G11 & G12 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN3 |].
      set (M := wbytes m' (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (Z_to_bv 64 copy))).
      assert (HWM : W C1 A' M (with_vmmaps vm' md0)) by (subst M; apply (W_store_win C1 A' m' _ _ _ CK1' HW'); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
      assert (FM : FRM C1 (s - 32) m2 M) by (subst M; apply FRM_win_write; [exact F' | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
      assert (OUTM : forall x : word, ~ (s - 40 <= u x < s - 32)%Z -> M x = m' x).
      { intros x Hx. subst M. apply (wbytes_out_Z _ (s - 40) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
      assert (R40 : rdn SEGS M (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 copy)).
      { subst M. rewrite <- (w2b_Z 8 copy) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
      assert (PXM : PIXat M copy (hdv w h d cd data)) by (apply (PIXat_frame m'); [exact PXd | intros x Hx; apply OUTM; lia]).
      assert (G4 : getr r3 4 = Z_to_bv 64 TP14) by (rewrite (AG3 4) by notin_list; rewrite (RR2 4) by (cbn; tauto); exact H4).
      rewrite <- (with_vmmaps_vmmaps vm' md0) in Hrm'.
      apply (DRV C1 A' M _ r3 (s - 48)%Z copy w h d cd data ra2 S CK1' HWM G2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(cbn; unfold GM3_STACK, G3H_STACK, LSF; lia) ltac:(cbn; lia) G1 RO2 G4 G10 G11 G12 PXM HOK Hw Hh L'p L'd
               (kk - RK_pixcopy)%Z (bb - RB_pixcopy14)%Z Hrm' ltac:(lia) ltac:(lia)).
      intros A'' m'' vm'' r4 HW'' CS4 PM'' RES'' Hrm''. rewrite with_vmmaps_twice in HW'' |- *.
      assert (F'' : FRM C1 (s - 32) m2 m'') by (eapply FRM_trans; [exact FM | eapply FRM_mono; [exact (proj1 PM'') | lia]]).
      assert (I2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      assert (RR4 : forall x, In x cs_rest -> getr r4 x = getr regs x).
      { intros x Hx. rewrite (cs_rest_of_kept _ _ CS4 x Hx), (AG3 x) by (nin_cs Hx). exact (RR2 x Hx). }
      pose proof (W_sok_win C1 A'' m'' _ (s - 48) 48 CK1' HW'' ltac:(cbn; lia) ltac:(cbn; lia)) as SOK''.
      assert (PX'' : PIXat m'' copy (hdv w h d cd data)).
      { apply (PIXat_frame M); [exact PXM|]. intros x Hx. exact (LIVK_at A' M m'' copy 64 x (proj2 PM'') L'p ltac:(lia) ltac:(lia) Hx). }
      assert (R40'' : rdn SEGS m'' (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 copy)).
      { rewrite (FRM_rdn16 C1 (s - 48) M m'' (s - 40) 8 CK1' (proj1 PM'')) by (cbn; lia). exact R40. }
      assert (LA1p : live A1 (Z_to_bv 64 copy) = None) by (rewrite <- LQk; exact Lkp).
      assert (LA1d : live A1 (Z_to_bv 64 data) = None) by (rewrite <- LQk; exact Lkd).
      assert (NEw : Z_to_bv 64 copy <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
      destruct RES'' as [[A0 LQ''] | (Ed & Ecd & pixr & datar & A0 & FRr)].
      + (* [comment removed for export] *)
        destruct (S3 al_rom r4 m'' s 0%Z ltac:(lia) ltac:(lia) ltac:(lia) SOK'' I2 A0) as (r5 & RUN5 & J2 & J1 & J10 & AG5).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW'')) | exact (mp_lazy _ (w_pure _ _ _ _ HW'')) | exact RUN5 |].
        set (M' := wbytes m'' (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
        assert (HWM' : W C1 A'' M' (with_vmmaps vm'' md0)) by (subst M'; apply (W_store_win C1 A'' m'' _ _ _ CK1' HW''); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
        assert (FM' : FRM C1 (s - 32) m2 M') by (subst M'; apply FRM_win_write; [exact F'' | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
        assert (OUTM' : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M' x = m'' x).
        { intros x Hx. subst M'. apply (wbytes_out_Z _ (s - 48) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
        assert (R40' : rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 copy)).
        { apply (cell_out m'' M' (s - 40)); [intros x Hx; apply OUTM'; lia | lia | lia | exact R40'']. }
        assert (R48' : rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 0)).
        { subst M'. rewrite <- (w2b_Z 8 0) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
        assert (PXM' : PIXat M' copy (hdv w h d cd data)) by (apply (PIXat_frame m''); [exact PX'' | intros x Hx; apply OUTM'; lia]).
        assert (J4 : getr r5 4 = Z_to_bv 64 0x3be10) by (rewrite (AG5 4) by notin_list; rewrite (RR4 4) by (cbn; tauto); exact H4).
        assert (Hrm3 : forall A3 vm3, roomtr A'' (m_vmmaps (with_vmmaps vm'' md0)) A3 vm3 0 0 -> aroom A3 vm3 (kk - RK_pixcopy - RKd) (bb - RB_pixcopy14 - RBd)).
        { intros A3 vm3 RT. rewrite with_vmmaps_vmmaps in RT. pose proof (RT _ _ Hrm'' ltac:(lia) ltac:(lia)) as X. rewrite !Z.sub_0_r in X. exact X. }
        destruct CMR as [[Ecd LEQc] | (ad & CMOKc & Gcd & TOPcd & Gad & TOPad & N1 & N2 & N3 & N4 & N5 & Lkcd & Lkad & L1cd & L1ad & L'cd & L'ad & CMd & LEQc)].
        * (* [comment removed for export] *)
          subst cd.
          apply (pixDestroy_cell_W C1 A'' M' _ r5 (s - 48) (s - 40) copy 0 0 n (hdv w h d 0 data) cv ra3 S CK1' HWM' J2
                   ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia) J1 RO3 J4 J10 R40' PXM' eq_refl eq_refl eq_refl).
          { rewrite LQ''. exact L'p. }
          { exact L1p. }
          { right. cbn [p_data hdv]. rewrite LQ''. split; [exact L'd|]. split; [exact L1d|]. split; [exact Hn0|]. split; [lia|]. intros X. exfalso. apply X. reflexivity. }
          { left. reflexivity. }
          intros A3 m3 vm3 r6 HW3 CS6 PD PM3 R0' CELL3 RT3. rewrite with_vmmaps_twice in HW3 |- *.
          cbn [p_data p_cmap hdv] in PD. destruct PD as (D1 & D2 & D3 & D4).
          apply (rnd_end A3 m3 vm3 r6 0%Z HW3 (Hrm3 A3 vm3 RT3)).
          -- eapply FRM_trans; [exact FM' | eapply FRM_mono; [exact (proj1 PM3) | lia]].
          -- apply (cell_out M' m3 (s - 48)); [intros x Hx; apply CELL3; lia | lia | lia | exact R48'].
          -- left. split; [reflexivity|]. intros q.
             destruct (bv_eq_dec _ q (Z_to_bv 64 copy)) as [->|Q1]; [rewrite D1, LA1p; reflexivity|].
             destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|Q2']; [rewrite (D2 ltac:(lia)), LA1d; reflexivity|].
             rewrite (D4 q Q1 ltac:(intros _; exact Q2') ltac:(intros X; exfalso; apply X; reflexivity)), LQ'', (LEQc q Q1 Q2'). apply LQk.
          -- csr. reflexivity.
          -- csr. reflexivity.
          -- intros x Hx. rewrite (cs_rest_of_kept _ _ CS6 x Hx), (AG5 x) by (nin_cs Hx). exact (RR4 x Hx).
        * (* [comment removed for export] *)
          set (cvd := CMAPV ad (c_d cv) (c_nalloc cv) (c_n cv) 0) in *.
          cbn [C1 rebase c_vm c_A0] in TOPcd, TOPad, L1cd, L1ad.
          assert (Hna2 : (0 < 4 * c_nalloc cv)%Z) by (pose proof CMOKc as (Hcd & Hna & _); rewrite Hna; destruct Hcd as [->|[->|[->| ->]]]; cbn; lia).
          assert (CMM' : CMAPat M' cd cvd).
          { apply (CMAPat_frame m''); [| intros x Hx; apply OUTM'; lia].
            apply (CMAPat_frame M); [| intros x Hx; exact (LIVK_at A' M m'' cd 24 x (proj2 PM'') L'cd ltac:(lia) ltac:(lia) Hx)].
            apply (CMAPat_frame m'); [exact CMd | intros x Hx; apply OUTM; lia]. }
          assert (LA1cd : live A1 (Z_to_bv 64 cd) = None) by (rewrite <- LQk; exact Lkcd).
          assert (LA1ad : live A1 (Z_to_bv 64 ad) = None) by (rewrite <- LQk; exact Lkad).
          apply (pixDestroy_cell_W C1 A'' M' _ r5 (s - 48) (s - 40) copy cd (4 * c_nalloc cv) n (hdv w h d cd data) cvd ra3 S CK1' HWM' J2
                   ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia) J1 RO3 J4 J10 R40' PXM' eq_refl eq_refl eq_refl).
          { rewrite LQ''. exact L'p. }
          { exact L1p. }
          { right. cbn [p_data hdv c_arr cvd]. rewrite LQ''. split; [exact L'd|]. split; [exact L1d|]. split; [exact Hn0|]. split; [lia|]. intros _. split; lia. }
          { right. cbn [c_arr cvd]. rewrite !LQ''. split; [exact CMM'|]. repeat (split; [first [assumption | lia]|]). exact Hna2. }
          intros A3 m3 vm3 r6 HW3 CS6 PD PM3 R0' CELL3 RT3. rewrite with_vmmaps_twice in HW3 |- *.
          cbn [p_data p_cmap hdv c_arr cvd] in PD. destruct PD as (D1 & D2 & D3 & D4).
          apply (rnd_end A3 m3 vm3 r6 0%Z HW3 (Hrm3 A3 vm3 RT3)).
          -- eapply FRM_trans; [exact FM' | eapply FRM_mono; [exact (proj1 PM3) | lia]].
          -- apply (cell_out M' m3 (s - 48)); [intros x Hx; apply CELL3; lia | lia | lia | exact R48'].
          -- left. split; [reflexivity|]. intros q.
             destruct (bv_eq_dec _ q (Z_to_bv 64 copy)) as [->|Q1]; [rewrite D1, LA1p; reflexivity|].
             destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|Q2']; [rewrite (D2 ltac:(lia)), LA1d; reflexivity|].
             destruct (bv_eq_dec _ q (Z_to_bv 64 cd)) as [->|Q3]; [rewrite (proj1 (D3 ltac:(lia))), LA1cd; reflexivity|].
             destruct (bv_eq_dec _ q (Z_to_bv 64 ad)) as [->|Q4]; [rewrite (proj2 (D3 ltac:(lia))), LA1ad; reflexivity|].
             rewrite (D4 q Q1 ltac:(intros _; exact Q2') ltac:(intros _; split; [exact Q3 | exact Q4])), LQ'', (LEQc q Q1 Q2' Q3 Q4). apply LQk.
          -- csr. reflexivity.
          -- csr. reflexivity.
          -- intros x Hx. rewrite (cs_rest_of_kept _ _ CS6 x Hx), (AG5 x) by (nin_cs Hx). exact (RR4 x Hx).
      + (* [comment removed for export] *)
        subst cd. destruct CMR as [[_ LEQc] | (ad & _ & B & _)]; [| exfalso; lia].
        pose proof (pix_fresh_own _ _ _ _ _ _ _ _ _ FRr) as OWNr. pose proof (pix_fresh_leq _ _ _ _ _ _ _ _ _ FRr) as LEQr.
        pose proof (pix_fresh_sub _ _ _ _ _ _ _ _ _ FRr) as SUBr.
        pose proof OWNr as (Gr & TOPr & ALr & Gdr & TOPdr & ALdr & NEr & L'r & L'dr & L1r & L1dr & L''r & L''dr & PXr).
        cbn [C1 rebase c_vm c_A0] in TOPr, TOPdr.
        destruct (S3 al_rom r4 m'' s pixr ltac:(lia) ltac:(lia) ltac:(lia) SOK'' I2 A0) as (r5 & RUN5 & J2 & J1 & J10 & AG5).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW'')) | exact (mp_lazy _ (w_pure _ _ _ _ HW'')) | exact RUN5 |].
        set (M' := wbytes m'' (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (Z_to_bv 64 pixr))).
        assert (HWM' : W C1 A'' M' (with_vmmaps vm'' md0)) by (subst M'; apply (W_store_win C1 A'' m'' _ _ _ CK1' HW''); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
        assert (FM' : FRM C1 (s - 32) m2 M') by (subst M'; apply FRM_win_write; [exact F'' | rewrite u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]).
        assert (OUTM' : forall x : word, ~ (s - 48 <= u x < s - 40)%Z -> M' x = m'' x).
        { intros x Hx. subst M'. apply (wbytes_out_Z _ (s - 48) 8); [rewrite length_N_to_le_bytes; reflexivity | lia | lia | lia]. }
        assert (R40' : rdn SEGS M' (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 copy)).
        { apply (cell_out m'' M' (s - 40)); [intros x Hx; apply OUTM'; lia | lia | lia | exact R40'']. }
        assert (R48' : rdn SEGS M' (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 pixr)).
        { subst M'. rewrite <- (w2b_Z 8 pixr) by lia. apply (rdn_wbytes_hit8 SEGS). rewrite u_Z2bv by lia. lia. }
        assert (PXM' : PIXat M' copy (hdv w h d 0 data)) by (apply (PIXat_frame m''); [exact PX'' | intros x Hx; apply OUTM'; lia]).
        assert (J4 : getr r5 4 = Z_to_bv 64 0x3be10) by (rewrite (AG5 4) by notin_list; rewrite (RR4 4) by (cbn; tauto); exact H4).
        apply (pixDestroy_keep_W C1 A'' M' _ r5 (s - 48) (s - 40) copy n (hdv w h d 0 data) ra3 S CK1' HWM' J2
                 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(cbn; unfold ALLOC_STACK; lia) ltac:(lia) ltac:(cbn; lia) J1 RO3 J4 J10 R40' PXM'
                 eq_refl eq_refl eq_refl (SUBr _ _ L'p) L1p (SUBr _ _ L'd) L1d Hn0 ltac:(cbn; lia)).
        intros A3 m3 vm3 r6 HW3 CS6 L3p L3d LEQ3 PM3 R0' OUT3 RT3. cbn [p_data hdv] in L3d, LEQ3. rewrite with_vmmaps_twice in HW3 |- *.
        assert (SUB1' : sub_live A1 A').
        { intros q k Lq. rewrite <- LQk in Lq. rewrite LEQc; [exact Lq | intros ->; congruence | intros ->; congruence]. }
        assert (Nrp : Z_to_bv 64 pixr <> Z_to_bv 64 copy) by (exact (live_ne A' _ _ _ L'r L'p)).
        assert (Nrd : Z_to_bv 64 pixr <> Z_to_bv 64 data) by (exact (live_ne A' _ _ _ L'r L'd)).
        assert (Ndrp : Z_to_bv 64 datar <> Z_to_bv 64 copy) by (exact (live_ne A' _ _ _ L'dr L'p)).
        assert (Ndrd : Z_to_bv 64 datar <> Z_to_bv 64 data) by (exact (live_ne A' _ _ _ L'dr L'd)).
        apply (rnd_end A3 m3 vm3 r6 pixr HW3).
        -- rewrite with_vmmaps_vmmaps in RT3. pose proof (RT3 _ _ Hrm'' ltac:(lia) ltac:(lia)) as X. rewrite !Z.sub_0_r in X. exact X.
        -- eapply FRM_trans; [exact FM' | eapply FRM_mono; [exact (proj1 PM3) | lia]].
        -- apply (cell_out M' m3 (s - 48)); [intros x Hx; apply OUT3; lia | lia | lia | exact R48'].
        -- right. exists datar. split; [exact Ed|]. split.
           ++ apply (pix_own_keep C1 A1 A'' A3 M' m3); [| apply LEQ3; assumption | apply LEQ3; assumption | exact (proj2 PM3)].
              apply pix_own_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite u_Z2bv by lia; cbn; lia].
              exact (pix_own_base C1 A1 A' A'' m'' _ _ _ _ _ OWNr SUB1').
           ++ intros q Q1 Q2'.
              destruct (bv_eq_dec _ q (Z_to_bv 64 copy)) as [->|Q3]; [rewrite L3p, LA1p; reflexivity|].
              destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|Q4]; [rewrite L3d, LA1d; reflexivity|].
              rewrite (LEQ3 q Q3 Q4), (LEQr q Q1 Q2'), (LEQc q Q3 Q4). apply LQk.
        -- csr. reflexivity.
        -- csr. reflexivity.
        -- intros x Hx. rewrite (cs_rest_of_kept _ _ CS6 x Hx), (AG5 x) by (nin_cs Hx). exact (RR4 x Hx).
  Qed.
  End Round.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rinv (kk bb : Z) (pc : word) : Prop :=
    forall Ak mk vmk r, W C1 Ak mk (with_vmmaps vmk md0) -> aroom Ak vmk kk bb -> FRM C1 (s - 32) m2 mk -> (forall q, live Ak q = live A1 q) ->
      getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pixs -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
      realizes SEGS (mkCfg (mkst r pc mk al_rom) (with_vmmaps vmk md0)) S.

  Hypothesis D_close : gray3_contract PC_pixCloseGray3 RK_gm4 RB_gm4.
  Hypothesis D_dilate : gray3_contract PC_pixDilateGray3 RK_gm3 RB_gm3.
  Hypothesis D_erode : gray3_contract PC_pixErodeGray3 RK_gm3 RB_gm3.
  Hypothesis D_open : gray3_contract PC_pixOpenGray3 RK_gm4 RB_gm4.
  Hypothesis N_close : gray3_null_contract PC_pixCloseGray3.
  Hypothesis N_dilate : gray3_null_contract PC_pixDilateGray3.
  Hypothesis N_erode : gray3_null_contract PC_pixErodeGray3.
  Hypothesis N_open : gray3_null_contract PC_pixOpenGray3.

  Lemma room_nn : (0 <= RK_pixcopy)%Z /\ (0 <= RB_pixcopy14)%Z /\ (0 <= RK_gm3)%Z /\ (0 <= RB_gm3)%Z /\ (0 <= RK_gm4)%Z /\ (0 <= RB_gm4)%Z /\
                  (0 <= RK_deser)%Z /\ (0 <= RB_deser)%Z.
  Proof. clear. room_consts. lia. Qed.

  Lemma R5 : rinv (kR - RK_graymorph) (bR - RB_graymorph) (0x15348 : word).
  Proof. intros Ak mk vmk r HWk Hrmk Fk LQk Q2 _ RR. exact (PH5 Ak mk vmk r HWk Hrmk Fk LQk Q2 RR). Qed.

  Ltac rok := red; apply bv_eq; reflexivity.

  Lemma R4 : rinv (kR - RK_graymorph + (RK_pixcopy + RK_gm4))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4))%Z (0x15318 : word).
  Proof.
    pose proof room_nn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
    assert (NX : rinv ((kR - RK_graymorph + (RK_pixcopy + RK_gm4)) - RK_pixcopy - RK_gm4)%Z ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4)) - RB_pixcopy14 - RB_gm4)%Z (0x15348 : word)).
    { replace ((kR - RK_graymorph + (RK_pixcopy + RK_gm4)) - RK_pixcopy - RK_gm4)%Z with (kR - RK_graymorph)%Z by lia. replace ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4)) - RB_pixcopy14 - RB_gm4)%Z with (bR - RB_graymorph)%Z by lia. exact R5. }
    exact (round_W (0x15318 : word) (0x15324 : word) (0x15334 : word) (0x15340 : word) (0x15348 : word) PC_pixOpenGray3 RK_gm4 RB_gm4
             ro_1 ro_2 ro_3 ro_4 ltac:(rok) ltac:(rok) ltac:(rok) ltac:(rok) D_open N_open N5 N6 (kR - RK_graymorph + (RK_pixcopy + RK_gm4))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4))%Z ltac:(lia) ltac:(lia) NX).
  Qed.

  Lemma R3 : rinv (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3))%Z (0x152e8 : word).
  Proof.
    pose proof room_nn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
    assert (NX : rinv ((kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3)) - RK_pixcopy - RK_gm3)%Z ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3)) - RB_pixcopy14 - RB_gm3)%Z (0x15318 : word)).
    { replace ((kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3)) - RK_pixcopy - RK_gm3)%Z with (kR - RK_graymorph + (RK_pixcopy + RK_gm4))%Z by lia. replace ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3)) - RB_pixcopy14 - RB_gm3)%Z with (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4))%Z by lia. exact R4. }
    exact (round_W (0x152e8 : word) (0x152f4 : word) (0x15304 : word) (0x15310 : word) (0x15318 : word) PC_pixErodeGray3 RK_gm3 RB_gm3
             re_1 re_2 re_3 re_4 ltac:(rok) ltac:(rok) ltac:(rok) ltac:(rok) D_erode N_erode N3 N4 (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3))%Z ltac:(lia) ltac:(lia) NX).
  Qed.

  Lemma R2 : rinv (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3))%Z (0x152b8 : word).
  Proof.
    pose proof room_nn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
    assert (NX : rinv ((kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3)) - RK_pixcopy - RK_gm3)%Z ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3)) - RB_pixcopy14 - RB_gm3)%Z (0x152e8 : word)).
    { replace ((kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3)) - RK_pixcopy - RK_gm3)%Z with (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3))%Z by lia. replace ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3)) - RB_pixcopy14 - RB_gm3)%Z with (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3))%Z by lia. exact R3. }
    exact (round_W (0x152b8 : word) (0x152c4 : word) (0x152d4 : word) (0x152e0 : word) (0x152e8 : word) PC_pixDilateGray3 RK_gm3 RB_gm3
             rd_1 rd_2 rd_3 rd_4 ltac:(rok) ltac:(rok) ltac:(rok) ltac:(rok) D_dilate N_dilate N3 N4 (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3))%Z ltac:(lia) ltac:(lia) NX).
  Qed.

  Lemma R1 : rinv (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm4))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm4))%Z (0x15288 : word).
  Proof.
    pose proof room_nn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
    assert (NX : rinv ((kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm4)) - RK_pixcopy - RK_gm4)%Z ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm4)) - RB_pixcopy14 - RB_gm4)%Z (0x152b8 : word)).
    { replace ((kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm4)) - RK_pixcopy - RK_gm4)%Z with (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3))%Z by lia. replace ((bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm4)) - RB_pixcopy14 - RB_gm4)%Z with (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3))%Z by lia. exact R2. }
    exact (round_W (0x15288 : word) (0x15294 : word) (0x152a4 : word) (0x152b0 : word) (0x152b8 : word) PC_pixCloseGray3 RK_gm4 RB_gm4
             rc_1 rc_2 rc_3 rc_4 ltac:(rok) ltac:(rok) ltac:(rok) ltac:(rok) D_close N_close N5 N6 (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm4))%Z (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm4))%Z ltac:(lia) ltac:(lia) NX).
  Qed.

  Lemma R1' : rinv (kR - RK_deser) (bR - RB_deser) (0x15288 : word).
  Proof.
    pose proof room_nn as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).
    replace (kR - RK_deser)%Z with (kR - RK_graymorph + (RK_pixcopy + RK_gm4) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm3) + (RK_pixcopy + RK_gm4))%Z by (unfold RK_graymorph; lia).
    replace (bR - RB_deser)%Z with (bR - RB_graymorph + (RB_pixcopy14 + RB_gm4) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm3) + (RB_pixcopy14 + RB_gm4))%Z by (unfold RB_graymorph; lia).
    exact R1.
  Qed.

  (* [comment removed for export] *)
  Lemma PH0 : forall r,
    getr r 2 = Z_to_bv 64 (s - 48) -> getr r 8 = Z_to_bv 64 pixs -> (forall x, In x cs_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (mkst r (0x15288 : word) m2 al_rom) (with_vmmaps vm1 md0)) S.
  Proof.
    intros r Q2 Q8 RR.
    apply (R1' A1 m2 vm1 r (W_rebase C A1 m2 _ HW2) Hrm (FRM_refl _ _ _) ltac:(intros q; reflexivity) Q2 Q8 RR).
  Qed.

End Phases.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O14LeptFuzz.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptGrayDrvI.
Module O14LeptFuzzMain.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptArith.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptArith2.
Import O14Drv1.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptStderr.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptBase.
Import O14CL7a.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixHdr.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptCmapValid.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixDestroy.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptDeser.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptCmap2.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixCopyA.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptPixCopy.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayD_iface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayA.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayDrv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptGrayDrvI.
Import O14LeptFuzz.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptRoom14.
(* [comment removed for export] *)








Import O14Drv1.O14FuzzIface.


Import O14CL7a.O14LeptErr.


Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac nin_cs Hx := let H := fresh in pose proof Hx as H; unfold cs_rest in H; cbn in H; repeat (destruct H as [<-|H]; [notin_list|]); destruct H.

Section Final.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma fuzz_covers : (RK_graymorph <= FUZZ_CALLS)%Z /\ (forall size, (0 <= size)%Z -> (RB_graymorph <= fuzz_margin size)%Z).
Proof. split; [rewrite RK_graymorph_val; unfold FUZZ_CALLS; lia | intros size _; unfold fuzz_margin; exact RB_graymorph_le]. Qed.

Theorem lept_fuzz_call : (forall fx : FPState, @pixAddBorderGeneral_contract fx AL CL ASR) -> (forall fx : FPState, @pixRemoveBorderGeneral_contract fx AL CL ASR) ->
  (forall fx : FPState, @pixRemoveBorderGeneral_null_contract fx AL CL ASR) -> @fuzz_call_contract AL CL ASR.
Proof.
  intros ABG0 RBG0 RBGn0. unfold fuzz_call_contract.
  intros fx A m md regs dptr size pl ret sp0 argv envp S Hinv Hpure Henv Ha0 Ha1 Hsz Hsz26 Hlive Hpl Hempty Hal16 Hra Hret H3 H4 Hsp16 Htop Hsp0 Hsp0hi Hisw Hwin Hsev Hpmm Hhdl Hgot kR bR Hrm Hrk Hrb K.
  pose proof (ABG0 fx) as ABG. pose proof (RBG0 fx) as RBG. pose proof (RBGn0 fx) as RBGn. clear ABG0 RBG0 RBGn0.
  pose proof fuzz_calls_nonneg as FZc. pose proof fuzz_covers as [FZk FZb].
  pose proof (fuzz_margin_bound size ltac:(lia)) as FZm. pose proof (FZb size ltac:(lia)) as FZb'.
  rewrite p16_segs in Hhdl, K |- *. rewrite p16_tp in H4.
  unfold LEPT_STACK, A_LEPT_SEV, A_LEPT_PMM, A_LEPT_HANDLER, A_GOT_LO, A_GOT_HI, PC_FUZZ in *.
  pose proof (alloc_top_win_vals _ Hisw) as ATW. unfold sp_window_hi in Hsp0hi.
  replace (Z_to_bv 64 0x15244) with (0x15244 : word) by (apply bv_eq; reflexivity).
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
  assert (SOKh : store_ok SEGS m (Z_to_bv 64 0x2bab8) 8 = true) by exact Hhdl.
  destruct (fz_A al_rom regs m s size (Z_to_bv 64 dp) ret ltac:(lia) ltac:(lia) ltac:(lia) SOK SOKh H2 Hra Ha0 Ha1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q8 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ Hpure) | exact (mp_lazy _ Hpure) | exact RUN1 |].
  set (m1 := wbytes (FZ3 m s ret regs) (Z_to_bv 64 0x2bab8) (word_to_le_bytes 8 (Z_to_bv 64 0x15368))) in *.
  assert (OUT1 : forall a : word, ~ (s - 24 <= u a < s)%Z -> ~ (0x2bab8 <= u a < 0x2bac0)%Z -> m1 a = m a).
  { intros a H1' H2'. subst m1. rewrite wbytes_outside; [apply OUT3; exact H1' | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
  assert (GR1 : mem_grows m m1) by (subst m1; eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
  assert (HW1 : W C A m1 md).
  { apply (W_entry C md m1 CK eq_refl Hinv Hpure Henv).
    - intros a Hw. unfold win in Hw; cbn in Hw. destruct (Hwin a ltac:(lia)) as (D & NO & _). split; [exact D | exact NO].
    - intros a Hc. cbn [inZs ll_clr LL16] in Hc. unfold inZ in Hc. cbn [fst snd] in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; [apply Hgot; lia | apply Hsev; lia | apply Hpmm; lia].
    - intros a NE. destruct (Z_lt_ge_dec (u a) (s - 24)); [| destruct (Z_lt_ge_dec (u a) s); [left; unfold win; cbn; lia|]].
      all: destruct (Z_lt_ge_dec (u a) 0x2bab8); [exfalso; apply NE; apply OUT1; lia|].
      all: destruct (Z_lt_ge_dec (u a) 0x2bac0); [right; unfold hcell; cbn; lia | exfalso; apply NE; apply OUT1; lia].
    - exact GR1.
    - rewrite p16_segs. subst m1. cbn [ll_hcell ll_devnull LL16]. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (Ldp : live A (Z_to_bv 64 dp) = Some size) by (apply Hlive; lia).
  destruct (blk_range C A m1 md (Z_to_bv 64 dp) size CK HW1 Ldp ltac:(lia)) as [Gdp Tdp]. rewrite u_Z2bv in Gdp, Tdp by lia. rewrite Evm in Tdp.
  assert (PLD : payload C dp pl).
  { split; [cbn; rewrite <- Hsz; exact Ldp|]. split; [intros i Hi; cbn; apply Hpl; lia|]. split; [lia | rewrite <- Hsz; lia]. }
  (* [comment removed for export] *)
  assert (KF : forall A' mf vm' rr, W C A' mf (with_vmmaps vm' md) -> (forall q, live A' q = live A q) -> getr rr 10 = Z_to_bv 64 0 ->
               cs_kept regs rr -> aroom A' vm' (kR - RK_graymorph) (bR - RB_graymorph) -> realizes SEGS (mkCfg (mkst rr ret mf al_rom) (with_vmmaps vm' md)) S).
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
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (rewrite (AG1 4) by notin_list; exact H4).
  apply (pixDeserialize_W C A m1 md r1 (s - 48) dp pl (Z_to_bv 64 0x1527c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hsp16; reflexivity)
           ltac:(rewrite Etop; unfold LSF; rewrite LV; lia) ltac:(rewrite Etop; lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10
           ltac:(rewrite Q11, Hsz; reflexivity) PLD ltac:(rewrite <- Hsz; lia)
           kR bR Hrm ltac:(room_consts; lia) ltac:(room_consts; lia)).
  unfold DK. intros A' m' vm' r2 HW' CS' PM' RES Hrm'.
  replace (Z_to_bv 64 0x1527c) with (0x1527c : word) by (apply bv_eq; reflexivity).
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
    destruct (fz_B1 al_rom r2 m' s pix ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK' Y2 A2p) as (r3 & RUN3 & V2 & V8 & AG3).
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
             ltac:(apply box_i; exact NEdp) HCM RQ R8 R16 R24 R32 Hrm' ltac:(lia) ltac:(lia) KF
             (pixCloseGray3_W ABG RBG RBGn) (pixDilateGray3_W ABG RBG RBGn) (pixErodeGray3_W ABG RBG RBGn) (pixOpenGray3_W ABG RBG RBGn)
             pixCloseGray3_null_W pixDilateGray3_null_W pixErodeGray3_null_W pixOpenGray3_null_W r3 V2 V8).
    intros x Hx. rewrite (AG3 x), (cs_rest_of_kept _ _ CS' x Hx), (AG1 x) by (nin_cs Hx). reflexivity.
Qed.
End Final.
End O14LeptFuzzMain.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocLayout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_auxv.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14Kit.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptRop.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14LeptGrayBorderW.
Module O14LeptPinsI.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LeptDefs.
Import O14Kit.
Import O14Drv1.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14LeptBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocSure.
(* [comment removed for export] *)







Import O14Kit.O14MallocLayout.

Import O14Drv1.O14FuzzIface.



Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma rdn_agree_on : forall segs (M M' : word -> option byte) (a : Z) (n : nat),
  0 <= a < 2 ^ 64 -> a + Z.of_nat n <= 2 ^ 64 -> (forall x : word, a <= u x < a + Z.of_nat n -> M' x = M x) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros segs M M' a n Ha Hn E. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply E. lia.
Qed.

#[export] Instance s16_lept_pins : @LeptPins (@mallocng_alloc_layout LS16) LL16.
Proof.
  constructor; cbn [al_segs al_rom al_malloc_pc al_free_pc al_gp al_globals al_grantable al_errno_slot al_in_ro al_in_rw
                    al_image_hi al_ret_ok al_mmap_threshold al_env mallocng_alloc_layout
                    ll_ro ll_clr ll_lg ll_errno ll_ag ll_img ll_hcell ll_devnull LL16 fst snd inZs]; unfold inZ; cbn [fst snd].
  - (* [comment removed for export] *) intros sp0 argv envp M a (_ & _ & RO & _) Ha. rewrite <- (WalksLib.zbv_self a). apply RO. cbn [IMG_LO RW_LO LS16]. exact Ha.
  - (* [comment removed for export] *) intros sp0 argv envp M M' (NL & PS & RO & AUX & GOT) E. pose proof (u64_range sp0) as Rsp.
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16] in *.
    split; [| split; [| split; [| split]]].
    + rewrite (rdn_agree_on _ M M' 0x5c09b 1); [exact NL | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + rewrite (rdn_agree_on _ M M' 0x5c0c8 8); [exact PS | lia | cbn; lia |]. intros x Hx. apply E. right; right; left. cbn in Hx. lia.
    + intros a Ha. rewrite E; [exact (RO a Ha) | left; rewrite u_Z2bv by lia; lia].
    + apply (aux_env_frame sp0 argv envp M M' AUX). intros a Ha. unfold aux_addr in Ha. cbn [A_LIBC LS16] in Ha. rewrite u_Z2bv in Ha by lia.
      apply E. destruct Ha as [Ha|Ha]; [right; right; left; lia | right; right; right; exact Ha].
    + intros a Ha. rewrite u_Z2bv in Ha by lia. rewrite E; [apply GOT; rewrite u_Z2bv by lia; exact Ha | right; left; left; rewrite u_Z2bv by lia; lia].
  - (* [comment removed for export] *) intros a Hg. unfold mallocng_globals in Hg. cbn [A_LOCK A_MALLOC_REPLACED LS16] in Hg. rewrite !u_Z2bv in Hg by lia. unfold CTX_SIZE in Hg. lia.
  - (* [comment removed for export] *) intros a He. unfold mallocng_errno_slot in He. cbn [A_ERRNO LS16] in He. rewrite !u_Z2bv in He by lia. lia.
  - (* [comment removed for export] *) intros a [G1 G2]. cbn [IMG_LO IMG_HI LS16] in G2. lia.
  - intros a H. unfold mallocng_in_ro in H. cbn [IMG_LO RW_LO LS16] in H. lia.
  - intros a H. unfold mallocng_in_rw in H. cbn [RW_LO IMG_HI LS16] in H. lia.
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

#[export] Instance s16_pins16 : @O14Pins (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16).
Proof. constructor; cbn; try reflexivity; apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Theorem s16_fuzz_call : forall ASR : @AllocSure (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16),
  @fuzz_call_contract (@mallocng_alloc_layout LS16) (@mallocng_calloc_layout LS16) ASR.
Proof.
  intros ASR.
  apply (@O14LeptFuzzMain.lept_fuzz_call _ _ ASR s16_lept_pins s16_pins16); intros fx.
  - exact (@O14LeptGrayBorderW.pixAddBorderGeneral_W fx _ _ ASR s16_lept_pins s16_pins16
             (@O14LeptRop.pixRasterop_uni_closed fx _ _ ASR s16_lept_pins s16_pins16) (@O14LeptRop.pixRasterop_src_W fx _ _ ASR s16_lept_pins s16_pins16)).
  - exact (@O14LeptGrayBorderW.pixRemoveBorderGeneral_W fx _ _ ASR s16_lept_pins s16_pins16
             (@O14LeptRop.pixRasterop_src_W fx _ _ ASR s16_lept_pins s16_pins16)).
  - exact (@O14LeptGrayBorderW.pixRemoveBorderGeneral_null_W fx _ _ ASR s16_lept_pins s16_pins16).
Qed.
End O14LeptPinsI.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require RefLayout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14Main.
Module O14Pins.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MemSplit.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_auxv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import O14Kit.
Import O14Drv1.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14Main.
(* [comment removed for export] *)







Import O14Kit.O14MallocLayout. Import O14Kit.O14Startup. Import O14Kit.O14StartupDefs. Import O14Kit.O14StartupFacts.

Import O14Drv1.O14MainEntry. Import O14Drv1.O14Open. Import O14Drv1.O14Malloc65536.

Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

Abbreviation RSEGS := Plain.M.loaded_segments.

Lemma need_locks_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x5c09b) 1 = Some [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Theorem s16_pins : @O14Main.pins (@mallocng_alloc_layout LS16).
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
    assert (LIBC : forall (a : Z) n, (0x3bd40 <= a)%Z -> (a + Z.of_nat n <= 0x5c108)%Z -> (a + Z.of_nat n <= 0x3bd6c \/ 0x3bd70 <= a)%Z ->
              (a + Z.of_nat n <= 0x5be50 \/ 0x5c070 <= a)%Z ->
              rdn RSEGS M (Z_to_bv 64 a) n = rdn RSEGS (D_main sp0 [a0s; path] envv a_hwcap a_draw tid) (Z_to_bv 64 a) n).
    { intros a n H1 H2 H3 H4. apply rdn_agree. intros j Hj. rewrite u_small by lia.
      rewrite HEl by (rewrite u_small by lia; lia).
      apply (main_entry_mem_data sp0 [a0s; path] envv tid regs0 mem0 ME). rewrite u_small, stack_max_size_val by lia. lia. }
    unfold mallocng_env. cbn [ml_segs A_NEED_LOCKS A_PAGE_SIZE A_LIBC A_GOT_SSP IMG_LO RW_LO LS16].
    split; [| split; [| split; [| split]]].
    + assert (NL : D_main sp0 [a0s; path] envv a_hwcap a_draw tid (Z_to_bv 64 0x5c09b) = None).
      { apply (D_main_none sp0 [a0s; path] envv a_hwcap a_draw tid 0x5c09b%Z Hva Hlo Hhi). vm_compute. reflexivity. }
      rewrite (LIBC 0x5c09b%Z 1%nat) by (cbn; lia). rewrite <- need_locks_img. apply rdn_agree.
      intros j Hj. destruct j as [|j]; [| exfalso; lia].
      replace (bv_unsigned (Z_to_bv 64 0x5c09b) + Z.of_nat 0)%Z with 0x5c09b%Z by (rewrite u_small by lia; reflexivity).
      rewrite NL. reflexivity.
    + rewrite (LIBC 0x5c0c8%Z 8%nat) by (cbn; lia). rewrite (D_main_pagesize sp0 [a0s; path] envv tid Hva). reflexivity.
    + intros a Ha. apply HEr. left. rewrite u_small by lia. lia.
    + apply (aux_env_intro RPH sp0 [a0s; path] envv a_uid a_hwcap a_draw M Hva Hve Hlo Hhi Hal).
      * intros a Ha. rewrite HEa by exact Ha.
        rewrite (main_entry_mem_above sp0 [a0s; path] envv tid regs0 mem0 ME a Ha). apply wrap_above_sp. exact Ha.
      * cbn [ml_segs A_LIBC LS16]. change (bv_unsigned (Z_to_bv 64 0x5c098) + 8)%Z with 0x5c0a0%Z.
        rewrite (LIBC 0x5c0a0%Z 8%nat) by (cbn; lia). rewrite n_to_le_8_spec.
        rewrite (D_main_auxvp sp0 a0s path envv tid Hvsp), (auxvp_eq sp0 a0s path envv). reflexivity.
    + intros a Ha. change (bv_unsigned (Z_to_bv 64 0x2aa70)) with 0x2aa70%Z in Ha. apply HEr. right. rewrite u_small by lia. lia.
Qed.
End O14Pins.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Spec.
Module O14Closed.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.Spec.
Import O14Kit.
Import O14Pins.
Import O14Drv1.
Import O14LeptPinsI.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14.O14Main.
(* [comment removed for export] *)







Import O14Kit.O14MallocLayout. Import O14Kit.O14Alloc. Import O14Kit.O14Sure.


Import O14Drv1.O14FuzzIface.

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem s16_realizes :
  forall sp brk mbase draw lim (inp : ProcInput),
    valid_sp sp -> valid_brk Plain.M.loaded_segments brk -> (2 ^ 34 <= lim)%Z ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    realizes Plain.M.loaded_segments
      (init_config Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs sp brk mbase draw lim inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  exact (@O14Main.ref_realizes_spec_pins _ _ s16_sure O14Pins.s16_pins (s16_fuzz_call s16_sure)).
Qed.
End O14Closed.
