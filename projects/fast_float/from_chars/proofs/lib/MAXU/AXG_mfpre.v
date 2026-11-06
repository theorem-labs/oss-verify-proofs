(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3 SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngWb.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits AxMalloc AXF_efmem AXF_maz AXF_mb0z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXF_efbz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_mfmem AXF_mcz.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxMalloc OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efmem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_maz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mb0z OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_efbz.AXF_mtz OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXG_mfmem OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_mcz.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record mfp_pre (regs : bvmap 5 word) (m : word -> option byte) (n G avail idx ctr : Z) : Prop := {
  mp_R10 : getr regs 10 = wa n ; mp_Rn : 1 <= n <= 131051 ;
  mp_Rsp : 2^20 + 1024 <= bv_unsigned (getr regs 2) <= 2^47 ; mp_Asp : bv_unsigned (getr regs 2) mod 16 = 0 ;
  mp_STK : stk_ok SEGS m (getr regs 2) 1024 ;
  mp_RG : 1 <= G <= 2^63-1 ; mp_AG : G mod 8 = 0 ; mp_Gstk : G + 40 <= bv_unsigned (getr regs 2) - 1024 ;
  mp_GIMG : G + 40 <= 0x10000 \/ 0x99000 <= G ;
  mp_Rav : 1 <= avail <= 2^32-1 ; mp_Ridx : idx = ctz32 avail ; mp_Rctr : 0 <= ctr <= 2^32-1 ;
  mp_Mnl : rdn SEGS m (wa 0x97c23) 1 = Some (word_to_le_bytes 1 (wa 0)) ;
  mp_Mact : rdn SEGS m (wa (8 * size_to_class n + 621800)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  mp_Mtab : forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes))) ;
  mp_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  mp_Mdb : forall j, 0 <= j < 32 -> rdn SEGS m (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn))) ;
  mp_Mctr : rdn SEGS m (wa 621732) 4 = Some (word_to_le_bytes 4 (wa ctr)) ;
  mp_Mlock : rdn SEGS m (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  mp_W : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 24 + d)) k = true
}.

Definition mfp_mem (m : word -> option byte) (regs : bvmap 5 word) (G avail : Z) : word -> option byte :=
  mb0_mem (ma_mem m regs) G avail.

Definition callee_regs' : list nat := [1;2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%nat.

Lemma size_to_class_small : forall n, 1 <= n <= 156 -> Z.shiftr (n + 3) 4 = size_to_class n.
Proof.
  intros n Hn. unfold size_to_class, class_of_units, IB. replace (n + 4 - 1) with (n + 3) by ring.
  replace (Z.shiftr (n + 3) 4 <? 10) with true; [reflexivity|]. symmetry. apply Z.ltb_lt.
  rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. apply Z.div_lt_upper_bound; lia.
Qed.

Section MFP.
Context {fx : FPState}.

#[using="Type"] Theorem mfp_arm : forall regs m rom n G avail idx ctr, mfp_pre regs m n G avail idx ctr ->
  exists R, msteps SEGS (mkst regs (wa 0x530c8) m rom) (mkst R (wa 0x5494c) (mfp_mem m regs G avail) rom)
         /\ getr R 10 = wa G /\ getr R 11 = wa idx /\ getr R 12 = wa n /\ getr R 13 = wa (bv_swrap 32 ctr)
         /\ (forall k, In k callee_regs' -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n G avail idx ctr P.
  destruct P as [R10 Rn Rsp Asp STK RG AG Gstk GIMG Rav Ridx Rctr Mnl Mact Mtab Mav Mdb Mctr Mlock W].
  set (sp := bv_unsigned (getr regs 2)) in *.
  pose proof (u64_range (getr regs 2)) as Rsp64.
  (* [comment removed for export] *)
  assert (Rsp' : 2^20 <= sp <= 2^47) by lia.
  assert (A : exists R1, msteps SEGS (mkst regs (wa 0x530c8) m rom) (mkst R1 (wa 0x53f2c) (ma_mem m regs) rom) /\ ma_regs R1 regs n (size_to_class n)).
  { destruct (Z_le_gt_dec n 156) as [Hs|Hm].
    - destruct (ma_arm regs m rom n R10 ltac:(lia) Rsp' Asp STK) as (R1 & M1 & Q). exists R1. split; [exact M1|].
      rewrite <- (size_to_class_small n) by lia. exact Q.
    - exact (mam_arm regs m rom n R10 ltac:(lia) Rsp' Asp STK Mtab Mdb). }
  destruct A as (R1 & M1 & (Q8 & Q9 & Q19 & Q20 & Q2 & K1)).
  set (m1 := ma_mem m regs) in *.
  assert (SP1 : bv_unsigned (getr R1 2) = sp - 48) by (rewrite Q2; apply u_vaddi''; lia).
  (* [comment removed for export] *)
  assert (M1out : forall a k, 0 <= a -> a + Z.of_nat k <= sp - 48 -> rdn SEGS m1 (wa a) k = rdn SEGS m (wa a) k).
  { intros a k Ha Hk. apply rdn_frame'; [lia | lia |]. intros x Hx. apply ma_mem_out; [exact Rsp' | lia | lia]. }
  assert (M1hi : forall a k, sp <= a -> a + Z.of_nat k <= 2^64 -> rdn SEGS m1 (wa a) k = rdn SEGS m (wa a) k).
  { intros a k Ha Hk. apply rdn_frame'; [lia | lia |]. intros x Hx. apply ma_mem_out; [exact Rsp' | lia | lia]. }
  (* [comment removed for export] *)
  destruct (lowbit_pow avail ltac:(lia)) as (LP & Rj).
  assert (SC : 0 <= size_to_class n <= 47) by (pose proof (size_to_class_range n ltac:(unfold MMAP_THRESHOLD; lia)) as [A _]; lia).
  assert (P2 : mb0_pre R1 m1 n (size_to_class n) G avail idx).
  { constructor.
    - exact Q8.
    - exact Q9.
    - exact Q19.
    - exact Q20.
    - lia.
    - lia.
    - exact RG.
    - exact AG.
    - lia.
    - rewrite Ridx. lia.
    - rewrite M1out by (cbn; lia). exact Mnl.
    - rewrite M1out by (cbn; lia). exact Mact.
    - rewrite M1out by (cbn; lia). exact Mav.
    - rewrite db_mach_ok by lia. pose proof (db_table_ok (ctz32 avail) Rj) as (D1 & _). exact D1.
    - rewrite db_mach_ok by lia. pose proof (db_table_ok (ctz32 avail) Rj) as (D1 & D2).
      rewrite M1out by (cbn; lia). rewrite Z.add_comm, Mdb by lia. rewrite D2, Ridx. reflexivity.
    - intros d k Hd Hk. apply (store_ok_mono SEGS k m); [apply ma_mem_grows|]. apply W; assumption. }
  destruct (mb0_fast R1 m1 rom n _ G avail idx P2 ltac:(lia)) as (R2 & M2 & (S8 & S9 & S18 & S19 & S20 & K2)).
  set (m2 := mb0_mem m1 G avail) in *.
  assert (M2out : forall a k, 0 <= a -> a + Z.of_nat k <= 2^64 -> (a + Z.of_nat k <= G + 24 \/ G + 28 <= a) ->
                    rdn SEGS m2 (wa a) k = rdn SEGS m1 (wa a) k).
  { intros a k Ha Hk D. apply rdn_frame'; [lia | lia |]. intros x Hx. apply mb0_mem_out; [lia | lia | lia]. }
  assert (SP2 : getr R2 2 = getr R1 2) by exact (K2 2%nat ltac:(cbn; tauto)).
  (* [comment removed for export] *)
  assert (P3 : mt_pre R2 m2 n G idx ctr (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)).
  { constructor.
    - exact S8.
    - exact S9.
    - exact S18.
    - exact S19.
    - rewrite SP2, SP1. lia.
    - rewrite SP2, SP1. clear - Asp. Z.div_mod_to_equations. lia.
    - lia.
    - exact RG.
    - rewrite Ridx. lia.
    - exact Rctr.
    - rewrite M2out by (cbn; lia). rewrite M1out by (cbn; lia). exact Mctr.
    - rewrite M2out by (cbn; lia). rewrite M1out by (cbn; lia). exact Mlock.
    - rewrite SP2, SP1. rewrite M2out by (cbn; lia). replace (sp - 48 + 40) with (sp + - 8) by ring.
      exact (ma_rdn_save m regs Rsp' 8 (fun R => getr R 1) ltac:(cbn; tauto)).
    - rewrite SP2, SP1. rewrite M2out by (cbn; lia). replace (sp - 48 + 32) with (sp + - 16) by ring.
      exact (ma_rdn_save m regs Rsp' 16 (fun R => getr R 8) ltac:(cbn; tauto)).
    - rewrite SP2, SP1. rewrite M2out by (cbn; lia). replace (sp - 48 + 24) with (sp + - 24) by ring.
      exact (ma_rdn_save m regs Rsp' 24 (fun R => getr R 9) ltac:(cbn; tauto)).
    - rewrite SP2, SP1. rewrite M2out by (cbn; lia). replace (sp - 48 + 16) with (sp + - 32) by ring.
      exact (ma_rdn_save m regs Rsp' 32 (fun R => getr R 18) ltac:(cbn; tauto)).
    - rewrite SP2, SP1. rewrite M2out by (cbn; lia). replace (sp - 48 + 8) with (sp + - 40) by ring.
      exact (ma_rdn_save m regs Rsp' 40 (fun R => getr R 19) ltac:(cbn; tauto)).
    - rewrite SP2, SP1. rewrite M2out by (cbn; lia). replace (sp - 48 + 0) with (sp + - 48) by ring.
      exact (ma_rdn_save m regs Rsp' 48 (fun R => getr R 20) ltac:(cbn; tauto)). }
  destruct (mt_arm R2 m2 rom n G idx ctr _ _ _ _ _ _ P3) as (R3 & M3 & (T10 & T11 & T12 & T13 & T1 & T8 & T9 & T18 & T19 & T20 & T2 & K3)).
  exists R3. split; [exact (msteps_trans SEGS _ _ _ M1 (msteps_trans SEGS _ _ _ M2 M3))|].
  split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T13|].
  intros k Hk. cbn [callee_regs' In] in Hk.
  destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]].
  - exact T1.
  - transitivity (v_addi (getr R2 2) 48); [exact T2|]. rewrite SP2, Q2. change (getr regs (Z_to_bv 5 (Z.of_nat 2))) with (getr regs 2).
    apply bv_eq. rewrite u_vaddi''; rewrite ?u_vaddi''; lia.
  - rewrite (K3 3%nat ltac:(cbn; tauto)), (K2 3%nat ltac:(cbn; tauto)), (K1 3%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 4%nat ltac:(cbn; tauto)), (K2 4%nat ltac:(cbn; tauto)), (K1 4%nat ltac:(cbn; tauto)). reflexivity.
  - exact T8.
  - exact T9.
  - exact T18.
  - exact T19.
  - exact T20.
  - rewrite (K3 21%nat ltac:(cbn; tauto)), (K2 21%nat ltac:(cbn; tauto)), (K1 21%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 22%nat ltac:(cbn; tauto)), (K2 22%nat ltac:(cbn; tauto)), (K1 22%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 23%nat ltac:(cbn; tauto)), (K2 23%nat ltac:(cbn; tauto)), (K1 23%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 24%nat ltac:(cbn; tauto)), (K2 24%nat ltac:(cbn; tauto)), (K1 24%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 25%nat ltac:(cbn; tauto)), (K2 25%nat ltac:(cbn; tauto)), (K1 25%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 26%nat ltac:(cbn; tauto)), (K2 26%nat ltac:(cbn; tauto)), (K1 26%nat ltac:(cbn; tauto)). reflexivity.
  - rewrite (K3 27%nat ltac:(cbn; tauto)), (K2 27%nat ltac:(cbn; tauto)), (K1 27%nat ltac:(cbn; tauto)). reflexivity.
Qed.

End MFP.
