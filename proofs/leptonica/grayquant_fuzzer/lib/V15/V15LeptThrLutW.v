(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop KernelW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15ThrLut V15LeptThrLut.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ThrLutW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem thr_lut_hop_W : forall (fx : FPState) C A Ar M md regs (s w h datad datat qtab : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (c_top C - LSTK + 4608 <= s)%Z -> (s <= c_top C)%Z ->
  hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datat) = Some (4 * (wpl_of w 8 * h))%Z -> live A (Z_to_bv 64 qtab) = Some 1024%Z ->
  Z_to_bv 64 datad <> Z_to_bv 64 qtab -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datat < 2 ^ 64)%Z -> (0 <= qtab < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -208) -> getr regs 11 = Z_to_bv 64 h ->
  getr regs 18 = Z_to_bv 64 datad -> getr regs 9 = Z_to_bv 64 datat -> getr regs 19 = Z_to_bv 64 (wpl_of w 8) -> getr regs 14 = Z_to_bv 64 (wpl_of w 8) ->
  rdn SEGS M (Z_to_bv 64 (s + -128)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS M (Z_to_bv 64 (s + -124)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS M (Z_to_bv 64 (s + -120)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> regs_agree (fun r => In r [5; 6; 7; 8; 10; 11; 12; 13; 15; 16; 17; 20; 22; 28; 29; 30; 31]%bv) regs regs' ->
      (forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 8 * h))%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 0x1ddf8) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x1dcb0) M al_rom) md) S.
Proof.
  intros fx C A Ar M md regs s w h datad datat qtab S CK HW SUB Hlo Hhi HOK Hw1 Hh1 Ld Ld0 Ld00 Lt Lq NEdq Rd Rt Rq H2 H11 H18 H9 H19 H14 Kh Kw Kq HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr.
  assert (Hw4 : (w <= 4 * wpl_of w 8 /\ wpl_of w 8 <= 5000)%Z).
  { unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)) as MB. lia. }
  set (wpl := wpl_of w 8) in *. set (n := (4 * (wpl * h))%Z) in *.
  assert (Hn0 : (0 < n)%Z) by (assert (1 * 1 <= wpl * h)%Z by (apply Z.mul_le_mono_nonneg; lia); unfold n; lia).
  destruct (blk_range C A M md (Z_to_bv 64 datad) n CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A M md (Z_to_bv 64 datat) n CK HW Lt Hn0) as [Gt TOPt]. rewrite u_Z2bv in Gt, TOPt by lia.
  destruct (blk_range C A M md (Z_to_bv 64 qtab) 1024 CK HW Lq ltac:(lia)) as [Gq TOPq]. rewrite u_Z2bv in Gq, TOPq by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lt) as (_ & ALt & _). rewrite u_Z2bv in ALt by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lq) as (_ & ALq & _). rewrite u_Z2bv in ALq by lia.
  pose proof (blk_apart C A M md _ _ n 1024 CK HW Ld Lq NEdq ltac:(lia) ltac:(lia)) as APdq. rewrite !u_Z2bv in APdq by lia.
  assert (GEO : lut_geom (s - 208) datad datat qtab w h wpl wpl).
  { unfold lut_geom. fold n. pose proof (mod16_mod4 _ ALd). pose proof (mod16_mod4 _ ALt). pose proof (mod16_mod4 _ ALq). repeat split; first [assumption | lia]. }
  assert (GDJ : lut_disj (s - 208) datad qtab h wpl) by (unfold lut_disj; fold n; split; lia).
  assert (RO : regions_ok SEGS M [RD datad h wpl; RS datat h wpl]).
  { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; unfold RD, RS; cbn [fst snd]; fold n; (repeat split; try lia).
    - exact (blk_sok C A M md datad n CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A M md datat n CK HW Lt ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KC : kcs (s - 208) qtab w h M).
  { unfold kcs. replace (s - 208 + 80)%Z with (s + -128)%Z by lia. replace (s - 208 + 84)%Z with (s + -124)%Z by lia. replace (s - 208 + 88)%Z with (s + -120)%Z by lia.
    repeat split; assumption. }
  assert (QK : qtab_ok qtab M).
  { intros k Hk. pose proof (blk_sok C A M md qtab 1024 CK HW Lq ltac:(lia) ltac:(lia) ltac:(lia)) as SQ.
    exact (reg_read SEGS M M qtab _ (qtab + 4 * k) 4 wr_readable_img (mem_grows_refl _) SQ ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)). }
  destruct (lut_run al_rom (s - 208) datad datat qtab w h wpl wpl GEO GDJ M regs RO KC QK ltac:(rewrite H2; f_equal; lia) H9 H11 H14 H18 H19)
    as (regs' & M' & RUN & RI & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct (rinv_WP C A Ar M md M' s [RD datad h wpl] CK HW SUB Hhi RI) as [HW' PM'].
  { intros r [<- | []]. right. exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. unfold RD. cbn [fst snd]. fold n. repeat split; first [assumption | lia]. }
  apply (HK regs' M' HW' PM' AG).
  intros x Hx. apply (proj2 RI). intros r [<- | []]. unfold RD, inreg. cbn [fst snd]. fold n. exact Hx.
Qed.
End ThrLutW.
