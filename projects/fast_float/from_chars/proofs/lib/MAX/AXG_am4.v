(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMeta.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocLemmasRing OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfFrame OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ MngRepr MngHeap MngImage MngWb MngWk MngGeoX MngLt MngSurgery MngExc MngNtfPre MngNtfC MngNtfM MngNtfS MngGM MngCtx2.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngMW0 MngMW1.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_eez.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXG_am1 AXG_am3.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRepr OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngImage OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWb OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGeoX OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngLt OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngSurgery OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngExc OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfPre OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfC OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngNtfS OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngGM OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngCtx2 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngHeap.MngMWP OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW0 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngMW1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt10z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt100z OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am1 OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXG_am3.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Section AM4.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition amo_mem (m : word -> option byte) (pa ac tl sec : Z) : word -> option byte :=
  am_ep_mem
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (0 + 614144)) (word_to_le_bytes 8 (wa (ac + -1))))
      (wa (0 + 614176)) (word_to_le_bytes 8 (wa (pa + 4096)))) (wa (tl + 8)) (word_to_le_bytes 8 (wa pa)))
      (wa (0 + 614168)) (word_to_le_bytes 8 (wa pa))) (wa (pa + 0)) (word_to_le_bytes 8 (wa sec)))
      (wa (pa + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 614128)) (word_to_le_bytes 8 (wa (pa + 64))))
      (wa (0 + 614136)) (word_to_le_bytes 8 (wa 100)))
    (pa + 24).

(* [comment removed for export] *)
Definition amo0_mem (m : word -> option byte) (pa ac sec : Z) : word -> option byte :=
  am_ep_mem
    (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (wa (0 + 614144)) (word_to_le_bytes 8 (wa (ac + -1))))
      (wa (0 + 614176)) (word_to_le_bytes 8 (wa (pa + 4096)))) (wa (0 + 614160)) (word_to_le_bytes 8 (wa pa)))
      (wa (0 + 614168)) (word_to_le_bytes 8 (wa pa))) (wa (pa + 0)) (word_to_le_bytes 8 (wa sec)))
      (wa (pa + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 614128)) (word_to_le_bytes 8 (wa (pa + 64))))
      (wa (0 + 614136)) (word_to_le_bytes 8 (wa 100)))
    (pa + 24).

#[using="Type"] Theorem seg_amo : forall R0 m rom sp0 can ra s0 s1 s2 s3 s4 pa ac tl sec,
  am_frame R0 m sp0 can ra s0 s1 s2 s3 s4 -> getr R0 9 = wa pa -> mt10_pre R0 m pa ac tl sec -> tl <> 0 ->
  pa + 4096 <= sp0 - 1024 -> (pa + 4096 <= 0x10000 \/ 0x97000 <= pa) -> tl + 16 <= sp0 - 1024 -> (tl + 16 <= 0x10000 \/ 0x97000 <= tl) ->
  (ra = 0x524e8 \/ ra = 0x5210c) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (pa + 24 + d)) k = true) ->
  exists R', msteps SEGS (mkst R0 (wa 0x51ec0) m rom) (mkst R' (wa ra) (amo_mem m pa ac tl sec) rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1 /\ getr R' 10 = wa (pa + 24) /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\
    (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R0 m rom sp0 can ra s0 s1 s2 s3 s4 pa ac tl sec F R9 P Htl Hpa Himg Htl1 Htl2 Hra W16.
  pose proof P as P'. destruct P' as [_ _ Rp Rac Rtl Rsec Ap _ _ _ _ _ _ _ _ _ _].
  destruct (mt10_ptl R0 m rom pa ac tl sec P) as (R1 & Hms1 & A9 & A10 & A11 & A12 & A19 & Ak).
  { cbn [OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_mt10.RES_ptl fst snd]. repeat (first [apply Forall_nil | apply Forall_cons]). apply sc_br_z. rewrite br_eq_z.
    cbn [zeval edenot]. rewrite (zatom R0 (VALS_mt10 pa ac tl sec) 34 tl eq_refl eq_refl) by lia. change (0 mod 2^64) with 0.
    apply Z.eqb_neq. rewrite Z.mod_small by lia. exact Htl. }
  set (m1 := mt10_mem_ptl m R0 pa ac tl sec) in *.
  assert (KK : forall k, In k [1; 2; 3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. apply Ak. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'. }
  pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F) as Rsp.
  assert (F1 : am_frame R1 m1 sp0 can ra s0 s1 s2 s3 s4).
  { apply (am_frame_mem R1 m); [| intros x Hx; unfold m1, mt10_mem_ptl; rewrite !MngWb.wbytes_out by side; reflexivity
                               | intros x Hx; unfold m1, mt10_mem_ptl; rewrite !MngWb.wbytes_out by side; reflexivity].
    apply (am_frame_regs R0 R1 m sp0 can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R1 R0 _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R1 R0 _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + rewrite A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)). }
  assert (W16' : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m1 (wa (pa + 24 + 0 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m1); [unfold m1, mt10_mem_ptl; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
    replace (pa + 24 + 0 + d) with (pa + 24 + d) by ring. exact (W16 d k Hd Hk). }
  destruct (seg_ame R1 m1 rom sp0 can ra s0 s1 s2 s3 s4 (pa + 24) F1 A10 ltac:(lia) ltac:(clear - Ap; apply Z.mod_divide in Ap; [destruct Ap as (k0 & ->); replace (k0 * 4096 + 24) with ((k0 * 512 + 3) * 8) by ring; apply Z.mod_mul; lia | lia])
              W16' ltac:(lia) ltac:(lia) Hra) as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & K2).
  exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  do 8 (split; [assumption|]).
  intros k Hk'. rewrite (K2 k Hk'). apply KK. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'.
Qed.

#[using="Type"] Theorem seg_amo0 : forall R0 m rom sp0 can ra s0 s1 s2 s3 s4 pa ac sec,
  am_frame R0 m sp0 can ra s0 s1 s2 s3 s4 -> getr R0 9 = wa pa -> mt100_pre R0 m pa ac sec ->
  pa + 4096 <= sp0 - 1024 -> (pa + 4096 <= 0x10000 \/ 0x97000 <= pa) -> (ra = 0x524e8 \/ ra = 0x5210c) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (pa + 24 + d)) k = true) ->
  exists R', msteps SEGS (mkst R0 (wa 0x51ec0) m rom) (mkst R' (wa ra) (amo0_mem m pa ac sec) rom) /\
    getr R' 1 = wa ra /\ getr R' 2 = wa sp0 /\ getr R' 8 = wa s0 /\ getr R' 9 = wa s1 /\ getr R' 10 = wa (pa + 24) /\
    getr R' 18 = wa s2 /\ getr R' 19 = wa s3 /\ getr R' 20 = wa s4 /\
    (forall k, In k [3; 4; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros R0 m rom sp0 can ra s0 s1 s2 s3 s4 pa ac sec F R9 P Hpa Himg Hra W16.
  pose proof P as P'. destruct P' as [_ _ Rp Rac Rsec Ap _ _ _ _ _ _].
  destruct (mt100_pt00 R0 m rom pa ac sec P ltac:(constructor)) as (R1 & Hms1 & A9 & A10 & A11 & A12 & A19 & Ak).
  set (m1 := mt100_mem_pt00 m R0 pa ac sec) in *.
  assert (KK : forall k, In k [1; 2; 3; 4; 18; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (Z_to_bv 5 (Z.of_nat k)) = getr R0 (Z_to_bv 5 (Z.of_nat k))).
  { intros k Hk'. apply Ak. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'. }
  pose proof (mf_Rsp _ _ _ _ _ _ _ _ _ _ F) as Rsp.
  assert (F1 : am_frame R1 m1 sp0 can ra s0 s1 s2 s3 s4).
  { apply (am_frame_mem R1 m); [| intros x Hx; unfold m1, mt100_mem_pt00; rewrite !MngWb.wbytes_out by side; reflexivity
                               | intros x Hx; unfold m1, mt100_mem_pt00; rewrite !MngWb.wbytes_out by side; reflexivity].
    apply (am_frame_regs R0 R1 m sp0 can ra s0 s1 s2 s3 s4 F).
    + exact (kp_lit R1 R0 _ KK 2%nat (Z_to_bv 5 2) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + exact (kp_lit R1 R0 _ KK 18%nat (Z_to_bv 5 18) ltac:(cbn [In]; memb) ltac:(apply bv_eq; reflexivity)).
    + rewrite A19. exact (eq_sym (mf_R19 _ _ _ _ _ _ _ _ _ _ F)). }
  assert (W16' : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m1 (wa (pa + 24 + 0 + d)) k = true).
  { intros d k Hd Hk. apply (store_ok_mono SEGS k m m1); [unfold m1, mt100_mem_pt00; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|].
    replace (pa + 24 + 0 + d) with (pa + 24 + d) by ring. exact (W16 d k Hd Hk). }
  destruct (seg_ame R1 m1 rom sp0 can ra s0 s1 s2 s3 s4 (pa + 24) F1 A10 ltac:(lia) ltac:(clear - Ap; apply Z.mod_divide in Ap; [destruct Ap as (k0 & ->); replace (k0 * 4096 + 24) with ((k0 * 512 + 3) * 8) by ring; apply Z.mod_mul; lia | lia])
              W16' ltac:(lia) ltac:(lia) Hra) as (R2 & Hms2 & C1 & C2 & C8 & C9 & C10 & C18 & C19 & C20 & K2).
  exists R2. split; [exact (msteps_trans SEGS _ _ _ Hms1 Hms2)|].
  do 8 (split; [assumption|]).
  intros k Hk'. rewrite (K2 k Hk'). apply KK. clear - Hk'. cbn [In] in *. repeat (destruct Hk' as [<-|Hk']; [memb|]); destruct Hk'.
Qed.
End AM4.
