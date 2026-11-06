(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun Bo0_code_8f368_90368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5DivLeafSpecsAB0 L5BResize16P.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5ARZ16.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5ARZ16P.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Definition U (R : bvmap 5 word) (k : nat) : Z := bv_unsigned (getr R (reg k)).
Lemma UR R k : 0 <= U R k < 2 ^ 64. Proof. unfold U. apply BL.bvu_range. Qed.
Lemma U_of R k z : getr R (reg k) = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> U R k = z.
Proof. intros H Hz. unfold U. rewrite H. apply L5.unsigned_lit. exact Hz. Qed.
Lemma U_to R k : getr R (reg k) = Z_to_bv 64 (U R k). Proof. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.

Lemma statics_vis LB FF LK cr A M model :
  ri_inv HI LB FF LK cr A M (vml_of model) ->
  let MV := mrestrict (ahid A model) M in
  L5.img_clear MV 860160 884736 /\ L5.u64_at RSEGS MV (0 + 911160) 2147450880 /\ L5.u32_at RSEGS MV (0 + 911168) 1.
Proof.
  intros HH. pose proof (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (aly_segs L C LY) in ST.
  pose proof (statics_facts L C M LY ST) as (IMGC & CSB & CUAR & _).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (_ & _ & VIMG & _).
  split. apply img_clear_mrestrict. exact IMGC.
  split. apply (proj2 (u64_at_vis _ M _ _ (VIMG (0 + 911160) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CSB.
  apply (proj2 (u32_at_vis _ M _ _ (VIMG (0 + 911168) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact CUAR.
Qed.

Lemma resize_limbs_short ws n : (n <= length ws)%nat -> resize_limbs ws n = firstn n ws.
Proof. intros H. unfold resize_limbs. replace (n - length ws)%nat with 0%nat by lia. cbn. rewrite app_nil_r. reflexivity. Qed.
Lemma resize_limbs_long ws n : (length ws <= n)%nat -> resize_limbs ws n = ws ++ repeat 0 (n - length ws).
Proof. intros H. unfold resize_limbs. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma resize_limbs_length ws n : length (resize_limbs ws n) = n.
Proof. unfold resize_limbs. rewrite length_app, length_firstn, repeat_length. lia. Qed.
Lemma in_firstn {A} (x : A) : forall (l : list A) n, In x (firstn n l) -> In x l.
Proof. induction l as [|y l IH]; intros [|n] Hx; cbn in Hx; try tauto. destruct Hx as [Hx|Hx]. left; exact Hx. right. exact (IH n Hx). Qed.
Lemma resize_limbs_range ws n : Forall (fun w => 0 <= w < 2 ^ 64) ws -> Forall (fun w => 0 <= w < 2 ^ 64) (resize_limbs ws n).
Proof.
  intros H. unfold resize_limbs. apply Forall_app. split.
  - rewrite Forall_forall in H |- *. intros x Hx. apply H. exact (in_firstn x ws n Hx).
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x. lia.
Qed.

(* [comment removed for export] *)
Lemma dyn_tail fx4 R4 M4 model4 K LB4 FF LK4 cr4 A4 (o spq r : Z) (n len : nat) (fb4 p cap F fl : Z) (R : bvmap 5 word) :
  let FF' := (F, 1, spq - 128 + 32) :: FF in let H4 := ahid A4 model4 in let MV4 := mrestrict H4 M4 in
  ri_inv HI LB4 FF' LK4 cr4 A4 M4 (vml_of model4) -> amodel_ok A4 model4 -> K [] ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 (spq + 16) -> spq mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M4 (spq + 16) (RESIZE_SCR + 16) -> Z.of_nat n <= 2 ^ 23 ->
  getr R4 (reg 2) = Z_to_bv 64 (spq - 128) -> getr R4 (reg 8) = Z_to_bv 64 (spq + 16) -> getr R4 (reg 9) = Z_to_bv 64 (spq - 128) -> getr R4 (reg 18) = Z_to_bv 64 F ->
  getr R4 (reg 19) = Z_to_bv 64 (Z.of_nat n) -> getr R4 (reg 20) = Z_to_bv 64 o -> getr R4 (reg 21) = Z_to_bv 64 (o + 8) -> getr R4 (reg 22) = Z_to_bv 64 (F / 8 + SB) ->
  getr R4 (reg 23) = Z_to_bv 64 F -> getr R4 (reg 24) = Z_to_bv 64 SB -> getr R4 (reg 25) = Z_to_bv 64 (Z.of_nat len) -> getr R4 (reg 26) = Z_to_bv 64 ((o + 8) / 8 + SB) ->
  getr R4 (reg 3) = getr R (reg 3) -> getr R4 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R4 (reg 27) = getr R (reg 27) ->
  L5.u64_at RSEGS MV4 (spq + 8) (U R 1) -> L5.u64_at RSEGS MV4 spq (U R 8) -> L5.u64_at RSEGS MV4 (spq - 8) (U R 9) -> L5.u64_at RSEGS MV4 (spq - 16) (U R 18) ->
  L5.u64_at RSEGS MV4 (spq - 24) (U R 19) -> L5.u64_at RSEGS MV4 (spq - 32) (U R 20) -> L5.u64_at RSEGS MV4 (spq - 40) (U R 21) -> L5.u64_at RSEGS MV4 (spq - 48) (U R 22) ->
  L5.u64_at RSEGS MV4 (spq - 56) (U R 23) -> L5.u64_at RSEGS MV4 (spq - 64) (U R 24) -> L5.u64_at RSEGS MV4 (spq - 72) (U R 25) -> L5.u64_at RSEGS MV4 (spq - 80) (U R 26) ->
  L5.u64_at RSEGS MV4 (spq - 112) 0 ->
  (4096 <= F /\ F + 128 <= 2 ^ 47 /\ 0x634000 <= F /\ F + 128 <= ahl_ceil ar) -> (F / 8) * 8 = F -> ar_fs ar <= F -> F + 128 <= ar_fs ar + FS_BYTES ->
  (0x7fff7000 + 17592186048512 <= F \/ F + 128 <= 0x7fff7000) -> L5.defined M4 (F / 8 + SB) 16 -> L5.u64_at RSEGS MV4 (F + 120) fl ->
  ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB4 FF' 0 0 fl -> (F + 128 <= fl \/ fl + 1 <= F) -> (0x7fff7000 + 17592186048512 <= fl \/ fl + 1 <= 0x7fff7000) ->
  (o + 32 <= F \/ F + 128 <= o) -> (o + 32 <= fl \/ fl + 1 <= o) -> (o / 8 + SB + 4 <= F / 8 + SB \/ F / 8 + SB + 16 <= o / 8 + SB) ->
  aobj FF o 32 -> L5.u8_at RSEGS M4 o fb4 -> Z.testbit fb4 0 = true -> 0 <= fb4 < 256 -> L5.u64_at RSEGS M4 (o + 16) cap -> L5.u64_at RSEGS M4 (o + 24) p -> shadow_zero M4 o 4 ->
  In (p, 8 * cap) LB4 -> (len < n)%nat -> Z.of_nat n <= cap -> cap <= 2 ^ 27 ->
  (forall (fx7 : FPState) R7 M7 model7 LK7, regs_preserved R R7 ->
      L5.u8_at RSEGS M7 o fb4 -> L5.u64_at RSEGS M7 (o + 8) (Z.of_nat n) -> L5.u64_at RSEGS M7 (o + 16) cap -> L5.u64_at RSEGS M7 (o + 24) p ->
      (forall a v, p <= a -> a + 8 <= p + 8 * Z.of_nat len -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M7 a v) ->
      (forall i, Z.of_nat len <= i < Z.of_nat n -> L5.u64_at RSEGS M7 (p + 8 * i) 0) ->
      ek L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) [(o, 32); (p + 8 * Z.of_nat len, 8 * (Z.of_nat n - Z.of_nat len))] M4 M7 -> dk L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) M4 M7 ->
      L5.defined M7 ((spq + 16) - (RESIZE_SCR + 16)) (RESIZE_SCR + 16) ->
      model_rt model4 model7 -> amodel_ok A4 model7 -> incl LK7 LK4 -> ri_inv HI LB4 FF LK7 cr4 A4 M7 (vml_of model7) ->
      srealizes RSEGS SCFG (cfg (fx:=fx7) R7 r M7 model7) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x8fdd4 M4 model4) K.
Proof.
  intros FF' H4 MV4 HH4 AM4 HK G1 RA G2 A32 G4 ASTK4 Hn Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q3 Q4 Q27
         C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 C96 C128 FR F8 FS1 FS2 FBIG FSHD FLC FLP FLNC FFL FLBIG OF OFL OSHF
         AOB O0 B0 Hfb O16 O24 SZ INB LTN NC CAP KONT.
  pose proof ASTK4 as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  assert (SPR : 0 <= (spq + 16) < 2 ^ 64 /\ 140735332487296 <= (spq + 16) <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  pose proof (statics_vis LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4). fold H4 MV4 in IMGC4, CSB4, CUAR4.
  assert (AOB' : aobj FF' o 32). { apply aobj_cons. exact AOB. }
  pose proof (aobj_facts L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 o 32 0 0 HH4 AOB' ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF4 & OVIS4 & OVSH4 & OCL4 & OCLSH4). change (32 / 8) with 4 in OVSH4, OCLSH4. fold H4 in OVIS4, OVSH4.
  pose proof (fl_range L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 _ fl HH4 FLP) as FLR.
  pose proof (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) (p, 8 * cap) INB) as ((P0 & P1 & P2 & P3 & P4 & P5) & PDEF & PSH & _). cbn [fst snd] in *.
  rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in P1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in P5.
  assert (LEN : 0 <= Z.of_nat len < Z.of_nat n) by (clear - LTN; lia).
  (* [comment removed for export] *)
  assert (XO4 : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS MV4 a v).
  { intros a v Ha Hc. apply (proj2 (u64_at_vis H4 M4 a v ltac:(eapply avis_sub; [exact OVIS4 | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))). exact Hc. }
  assert (OB4 : L5.u8_at RSEGS MV4 o fb4). { apply (proj2 (u8_at_vis H4 M4 o fb4 ltac:(eapply avis_sub; [exact OVIS4 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact O0. }
  assert (OZ4 : L5KA.zeros_at MV4 (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H4 M4 _ 4 OVSH4)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OW4 : L5.writable RSEGS MV4 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H4 M4 o 32 OVIS4)). exact ODEF4. clear - OR; lia. clear - OR; lia. }
  assert (W128 : L5.writable RSEGS MV4 (spq - 128) 144).
  { apply (proj2 (writable_vis H4 M4 (spq - 128) 144 (VIS4 (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M4 (spq + 16)). exact ASTK4. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (WB4 & WF4 & _).
  assert (VF4 : avis H4 F 128). { apply (VFS4 F 128 FS1 FS2). }
  assert (FDEF4 : L5.defined MV4 F 128). { apply (proj2 (defined_vis H4 M4 F 128 VF4)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))))). }
  assert (FW4 : L5.writable RSEGS MV4 F 128). { apply (L5C.writable_of_defined RSEGS). exact FDEF4. clear - FR; lia. clear - FR; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (F32 : F mod 32 = 0).
  { pose proof (proj1 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))) as X. cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 1) with 128 in X. clear - X. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VSH4 : avis H4 (F / 8 + SB) 16).
  { apply VFSSH4. intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FSHW4 : L5.writable RSEGS MV4 (F / 8 + SB) 16).
  { apply (proj2 (writable_vis H4 M4 _ 16 VSH4 ltac:(clear - FR F8; unfold SB; lia) ltac:(clear - FR F8; unfold SB; lia))). apply (L5C.writable_of_defined RSEGS). exact FSHD.
    clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
  pose proof (fl_writable L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 _ fl HH4 FLP) as [FLD4 FLW4].
  pose proof (fl_vis L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 fl HH4 FLP) as FLV4. fold H4 in FLV4.
  assert (FLW4v : L5.writable RSEGS MV4 fl 1). { apply (proj2 (writable_vis H4 M4 fl 1 FLV4 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW4. }
  assert (SF : spq - 128 + 144 <= F \/ F + 128 <= spq - 128) by (clear - FR SLO; lia).
  assert (SFL : spq - 128 + 144 <= fl \/ fl + 1 <= spq - 128) by (clear - FLR SLO; lia).
  assert (SO : spq - 128 + 144 <= o \/ o + 32 <= spq - 128) by (clear - OR SLO; lia).
  (* [comment removed for export] *)
  assert (PRNG : 4096 <= p <= 140737488355328) by (clear - P0 P3 P5; lia).   (* [comment removed for export] *)
  pose proof (rz16Cd_conc fx4 R4 MV4 (fun j : nat => match j with 2%nat => spq | 33%nat => o | 34%nat => Z.of_nat n | 35%nat => Z.of_nat len | 36%nat => fb4 | 37%nat => p | 40%nat => F | 41%nat => fl
                | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R4 1 | 48%nat => U R 24
                | 49%nat => U R 18 | 50%nat => U R 21 | 51%nat => U R 22 | 52%nat => U R 23 | 53%nat => U R 25 | 54%nat => U R 26 | _ => 0 end)) as P.
  cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (apply XO4; [clear; lia | sc]) ]).
  destruct P as (fx5 & R5 & M5v & MG5 & CdFR & CdFZ & (CdMS & CdKS & CdR1 & CdR10 & CdR11 & CdR12 & CdR13 & CdQ_V33nat & CdQ_V2nat & CdQ_V2nat_1 & CdQ_V2nat_2 & CdQ_V2nat_3 & CdQ_V2nat_4 & CdQ_V2nat_5 & CdQ_V2nat_6 & CdQ_V2nat_7 & CdQ_V2nat_8 & CdQ_V2nat_9 & CdQ_V2nat_10 & CdQ_V2nat_11 & CdQ_V2nat_12)).
  apply (apiece L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 fx4 fx5 R4 0x8fdd4 R5 0x5e7f0 M5v (fun a => spq - 128 <= a < (spq + 16) \/ o + 8 <= a < o + 16) K HH4 AM4 CdMS MG5).
  { intros a Ha Hna. apply CdFZ. exact Ha. clear - Hna; lia. clear - Hna; lia. }
  { intros a Ha [Wa|Wa]. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
    split. apply (obj_client L ar LB4 FF' 0 0 o 32 a AOB'). clear - Wa; lia. clear - Wa OR; lia. }
  intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
  assert (ASTK5 : astk ar M5 (spq + 16) (RESIZE_SCR + 16)). { eapply astk_grows. exact ASTK4. exact MGM5. }
  (* [comment removed for export] *)
  pose proof (aio_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (aly_segs L C LY), (aly_memset L C LY), (aly_scr_mem L C LY) in MS.
  assert (U2 : bv_unsigned (getr R5 2%bv) = spq - 128). { rewrite r2, (CdKS 2%nat) by inl. rewrite Q2. apply L5.unsigned_lit. clear - SPR; lia. }
  set (dst := p + 8 * Z.of_nat len). set (cnt := 8 * (Z.of_nat n - Z.of_nat len)).
  assert (DSTR : p <= dst /\ dst + cnt <= p + 8 * cap /\ 0 < cnt <= 2 ^ 27 /\ dst + cnt <= 2 ^ 47) by (subst dst cnt; clear - LEN CAP NC P5 Hn; lia).
  eapply (MS fx5 R5 M5 model5 LB4 FF' LK4 cr4 A4 dst 0 cnt K); clear MS.
  { split. exact HH5. split. exact (proj1 AM5). split. exact (proj2 AM5).
    split. rewrite r10, CdR10. f_equal. subst dst; clear; lia. split. rewrite r12, CdR12. f_equal. subst cnt; clear; lia. split. clear - DSTR; lia.
    split. rewrite r4. rk. split. rewrite r1, CdR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
    split. { rewrite U2. replace (spq - 128) with (spq + 16 - 144) by (clear; lia). apply (astack_ok_of_astk L ar C LY M4 M5 (spq + 16) (RESIZE_SCR + 16) 144 2560 ASTK4 MGM5). clear; lia. clear; lia.
             unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
             clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { (* [comment removed for export] *)
             intros a Ha. destruct PSH as [PZ PP].
             assert (G : 0 <= a / 8 - p / 8 < 8 * cap / 8).
             { clear - Ha DSTR P2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
             left. unfold byte_at, S. rewrite FRM5. unfold shadow_zero, byte_at, S in PZ. replace (a / 8 + SB) with (p / 8 + SB + (a / 8 - p / 8)) by (clear; lia). apply PZ. exact G.
             clear - G P0 P5 CAP; unfold SB. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             clear - G P0 P5 CAP OR OBIG SLO SPT; unfold SB. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    split. { intros i Hi. rewrite U2. apply (block_client L ar LB4 FF' _ _ p (8 * cap)). exact INB. clear - Hi DSTR; lia. }
    split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M5 dst cnt). eapply L5.defined_grows. exact MGM5.
             intros j Hj. replace (dst + j) with (p + (dst + j - p)) by (clear; lia). apply PDEF. clear - Hj DSTR; lia. clear - DSTR P0; lia. clear - DSTR; lia. exact Hi. exact Hm. }
    split. exact HK. apply (app_rng_block L ar C HI HIok LB4 FF' LK4 cr4 A4 M5 _ p (8 * cap) dst cnt HH5 INB). all: clear - DSTR; lia. }
  { rewrite r11. exact CdR11. }
  (* [comment removed for export] *)
  intros R6 M6 model6 mR10 RP6 ZB PRES6 SDEF6 RT6 MI6 HH6. rewrite U2 in PRES6, SDEF6. rewrite r1, CdR1.
  assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM5). }
  assert (ASTK6 : astk ar M6 (spq + 16) (RESIZE_SCR + 16)).
  { apply (astk_after_eq L ar C HI HIok LB4 FF' LK4 cr4 A4 M5 M5 M6 _ (spq + 16) _ (spq - 128) 2560 HH5 ASTK5 (mem_grows_refl M5)).
    intros a Ha Hs Hns. apply PRES6. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs DSTR P4; lia. exact SDEF6.
    unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
  pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
  pose proof (statics_vis LB4 FF' LK4 cr4 A4 M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
  set (H6 := ahid A4 model6) in *. set (MV6 := mrestrict H6 M6) in *.
  (* [comment removed for export] *)
  set (RNG := fun a => spq - 128 <= a < (spq + 16) \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16 \/ o <= a < o + 32).   (* [comment removed for export] *)
  assert (RCL : forall a, RNG a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB4 FF' (spq - 128) 2560 a /\ ~ (dst <= a < dst + cnt)).
  { intros a [Ra|[Ra|[Ra|Ra]]].
    - split. clear - Ra SPR; lia. split. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. clear - Ra DSTR P4 SLO; lia.
    - split. clear - Ra FR; lia. split. apply (fframe_client L ar LB4 FF' _ _ F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ra; lia.
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ INB)))))) (F, 1, spq - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as X.
      cbn [fst snd ff_addr ff_class] in X. change (ff_bytes 1) with 128 in X. clear - Ra X DSTR; lia.
    - split. clear - Ra FR F8; unfold SB in *; lia. split. apply (fframe_shadow_client L ar LB4 FF' _ _ F 1 (spq - 128 + 32)). left; reflexivity.
      change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Ra F8; unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      clear - Ra FR F8 FBIG DSTR P5 P0; unfold SB in *; lia.
    - split. clear - Ra OR; lia. split. apply (obj_client L ar LB4 FF' _ _ o 32 a AOB'). exact Ra.
      destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ INB)))))) g ltac:(apply in_or_app; left; right; exact Hg)) as X.
      cbn [fst snd] in X. clear - Ra X X1 X2 DSTR; lia. }
  assert (AG56 : forall a, RNG a -> MV6 (Z_to_bv 64 a) = M5v (Z_to_bv 64 a)).
  { intros a Ra. destruct (RCL a Ra) as (Ha & Ca & Na). apply aclientw_client in Ca.
    assert (V6 : H6 (Z_to_bv 64 a) = false).
    { destruct Ra as [Ra|[Ra|[Ra|Ra]]].
      - replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS6 (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (F + (a - F)) by (clear; lia). apply (VFS6 F 128 FS1 FS2). clear - Ra; lia.
      - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH6 (F / 8 + SB) 16). 2: clear - Ra; lia.
        intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        pose proof (aobj_facts L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M6 model6 o 32 0 0 HH6 AOB' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS6 & _).
        replace a with (o + (a - o)) by (clear; lia). apply (OVIS6 (a - o)). clear - Ra; lia. }
    assert (V4 : H4 (Z_to_bv 64 a) = false).
    { destruct Ra as [Ra|[Ra|[Ra|Ra]]].
      - replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS4 (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
      - replace a with (F + (a - F)) by (clear; lia). apply VF4. clear - Ra; lia.
      - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VSH4 (a - (F / 8 + SB))). clear - Ra; lia.
      - replace a with (o + (a - o)) by (clear; lia). apply (OVIS4 (a - o)). clear - Ra; lia. }
    unfold MV6. rewrite (mrestrict_visible H6 M6) by exact V6. rewrite (PRES6 a Ha Ca Na). apply EQ5. exact V4. }
  assert (XC6 : forall a v, (spq - 128 <= a <= spq + 8 \/ (F <= a <= F + 16 \/ F + 32 <= a <= F + 112) \/ o <= a <= o + 24) -> L5.u64_at RSEGS M5v a v -> L5.u64_at RSEGS MV6 a v).
  { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AG56. unfold RNG. clear - Ha Hj; lia. clear - Ha SPR FR OR; lia. clear - Ha SPR FR OR; lia. }
  assert (W128f : L5.writable RSEGS MV6 (spq - 128) 144).
  { apply (proj2 (writable_vis H6 M6 (spq - 128) 144 (VIS6 (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M6 (spq + 16)). exact ASTK6. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB6 & WF6 & _).
  assert (VF6 : avis H6 F 128). { apply (VFS6 F 128 FS1 FS2). }
  assert (FDEF6 : L5.defined MV6 F 128). { apply (proj2 (defined_vis H6 M6 F 128 VF6)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF6 _ (or_introl eq_refl))))))). }
  assert (FW6 : L5.writable RSEGS MV6 F 128). { apply (L5C.writable_of_defined RSEGS). exact FDEF6. clear - FR; lia. clear - FR; lia. }
  pose proof (aobj_facts L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M6 model6 o 32 0 0 HH6 AOB' ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF6 & OVIS6 & OVSH6 & _).
  change (32 / 8) with 4 in OVSH6. fold H6 in OVIS6, OVSH6.
  assert (AG46 : forall a, ((F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> MV6 (Z_to_bv 64 a) = MV4 (Z_to_bv 64 a)).
  { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra FR F8 OR; unfold SB in *; lia).
    assert (NF : ~ (spq - 128 <= a < spq - 128 + 144) /\ ~ (o + 8 <= a < o + 8 + 8)).
    { clear - Ra FR F8 OR OBIG SLO SPT OF OSHF. unfold SB in *. lia. }
    destruct Ra as [Ra|[Ra|Ra]].
    - rewrite AG56. apply CdFZ. exact Ha. exact (proj1 NF). exact (proj2 NF). unfold RNG; clear - Ra; lia.
    - rewrite AG56. apply CdFZ. exact Ha. exact (proj1 NF). exact (proj2 NF). unfold RNG; clear - Ra; lia.
    - unfold MV6. rewrite (mrestrict_visible H6 M6). 2:{ replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH6 (a - (o / 8 + SB))). clear - Ra; lia. }
      rewrite (PRES6 a Ha). 3:{ clear - Ra OR OBIG DSTR P5 P0; unfold SB in *; lia. }
      2:{ apply (aclient_narrow L ar LB4 FF' 0 0). replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH4. clear - Ra; lia. clear - Ra OR SLO SPT; unfold SB in *; lia. }
      rewrite (EQ5 (Z_to_bv 64 a)). 2:{ replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH4 (a - (o / 8 + SB))). clear - Ra; lia. }
      apply CdFZ. exact Ha. exact (proj1 NF). exact (proj2 NF). }
  assert (FSHW6 : L5.writable RSEGS MV6 (F / 8 + SB) 16).
  { eapply (L5C.writable_agree RSEGS MV4 MV6). 4: exact FSHW4. intros j Hj. apply AG46. clear - Hj; lia. clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
  pose proof (fl_writable L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M6 _ fl HH6 FLP) as [FLD6 FLW6].
  pose proof (fl_vis L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M6 model6 fl HH6 FLP) as FLV6. fold H6 in FLV6.
  assert (FLW6v : L5.writable RSEGS MV6 fl 1). { apply (proj2 (writable_vis H6 M6 fl 1 FLV6 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW6. }
  assert (FLC6 : L5.u64_at RSEGS MV6 (F + 120) fl).   (* [comment removed for export] *)
  { assert (FLCm : cell_is RSEGS M4 (F + ff_bytes 1 - 8) 8 fl).
    { change (ff_bytes 1) with 128. replace (F + 128 - 8) with (F + 120) by (clear; lia).
      apply (proj1 (u64_at_vis H4 M4 (F + 120) fl ltac:(eapply avis_sub; [exact VF4 | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact FLC. }
    pose proof (proj2 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model6 F 1 _ _ fl HH4 HH6 (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) FLCm)) as X.
    change (ff_bytes 1) with 128 in X. replace (F + 128 - 8) with (F + 120) in X by (clear; lia). exact X. }
  assert (OW6 : L5.writable RSEGS MV6 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H6 M6 o 32 OVIS6)). exact ODEF6. clear - OR; lia. clear - OR; lia. }
  assert (OZ6 : L5KA.zeros_at MV6 (o / 8 + SB) 4). { eapply L5KA.zeros_at_agree1. 2: exact OZ4. intros j Hj. apply AG46. clear - Hj; lia. }
  (* [comment removed for export] *)
  assert (RS6 : forall k, In k [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R6 (reg k) = getr R4 (reg k)).
  { intros k Hk. rewrite (cs_of_preserved R5 R6 k RP6). apply CdKS. revert Hk; apply (L5K.incl_b _ KS_rz16Cd); vm_compute; reflexivity.
    revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
  pose proof (rz16E_conc fx5 R6 MV6 (fun j : nat => match j with 2%nat => spq | 33%nat => o | 34%nat => Z.of_nat n | 35%nat => Z.of_nat len | 40%nat => F | 41%nat => fl
                | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R6 1 | 48%nat => U R 24
                | 49%nat => U R 18 | 50%nat => U R 21 | 51%nat => U R 22 | 52%nat => U R 23 | 53%nat => U R 25 | 54%nat => U R 26 | _ => 0 end)) as P.
  cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc | (rewrite RS6 by inl; sc) | (apply XC6; [clear; lia | sc]) ]).
  destruct P as (fx7 & R7 & M7v & MG7 & EFR & EFZ & (EMS & EKS & ER1 & ER2 & ER8 & ER9 & ER10 & ER18 & ER19 & ER20 & ER21 & ER22 & ER23 & ER24 & ER25 & ER26 & EB_V41nat & EB_V40nat & EB_V40nat_1 & EB_V40nat_2 & EB_V40nat_3 & EB_V40nat_4 & EB_V40nat_5 & EB_V40nat_6 & EB_V40nat_7 & EB_V40nat_8 & EB_V40nat_9 & EB_V40nat_10 & EB_V40nat_11 & EB_V40nat_12 & EB_V40nat_13 & EB_V40nat_14 & EB_V40nat_15 & EQ_V40nat & EDF)).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  pose proof (ret_to fx7 R7 M7v 0x8ff64 W_8ff64 r F_8ff64 eq_refl D_8ff64 ltac:(rewrite ER1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
  pose proof (msteps_trans _ _ _ _ EMS RET) as MS8. clear EMS RET.
  set (W7 := fun a => (spq - 128 <= a < (spq + 16) \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16) \/ a = fl).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (apiece_retire L ar C HI LY HIok LB4 FF LK4 cr4 A4 M6 model6 fx5 fx7 R6 0x8fe9c R7 r M7v W7 F 1 (spq - 128 + 32) fl K HH6 (conj Hh6 MI6)).
  { change (ff_bytes 1) with 128. replace (F + 128 - 8) with (F + 120) by (clear; lia).
    apply (proj1 (u64_at_vis H6 M6 (F + 120) fl ltac:(eapply avis_sub; [exact VF6 | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact FLC6. }
  { exact FLNC. }
  { exact FLV6. }
  { clear - FLR; lia. }
  { exact MS8. }
  { exact MG7. }
  { intros a Ha Hna. apply EFZ. exact Ha. all: clear - Hna; subst W7; cbn beta in Hna; unfold SB in *; lia. }
  { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [Wa|Wa]. 2: left; exact Wa. right.
    apply (aclient_narrow L ar LB4 FF' (spq - 128) 2560). exact (proj1 (proj2 (RCL a ltac:(unfold RNG; clear - Wa; tauto)))). clear; lia. }
  { intros a. subst W7; cbn beta. repeat match goal with X : _ |- _ => clear X end.
    destruct (rng_dec a (spq - 128) (spq + 16)); [left; tauto|]. destruct (rng_dec a F (F + 24)); [left; tauto|]. destruct (rng_dec a (F + 32) (F + 120)); [left; tauto|].
    destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 16)); [left; tauto|]. destruct (Z.eq_dec a fl); [tauto|]. right; tauto. }
  { exact EB_V41nat. }
  intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
  assert (ASTK7 : astk ar M7 (spq + 16) (RESIZE_SCR + 16)). { eapply astk_grows. exact ASTK6. exact MGM7. }
  (* [comment removed for export] *)
  assert (FM128 : F mod 128 = 0).
  { pose proof (proj1 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))) as X. cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 1) with 128 in X. exact X. }
  assert (FAPP : app_mem F 128). { unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - FR FBIG; lia. }
  assert (FAP : fframes_apart F 128 (FF ++ LK4)).
  { pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))))) as X. unfold FF' in X. cbn [ff_addr ff_class fst snd ff_remove] in X. rewrite Z.eqb_refl in X.
    change (ff_bytes 1) with 128 in X. exact X. }
  assert (FBLK : forall b, In b LB4 -> F + 128 <= fst b \/ fst b + snd b <= F).
  { intros b Hb. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 b Hb)))))) (F, 1, spq - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as X.
    cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 1) with 128 in X. clear - X; lia. }
  assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) a).
  { intros a Ha' Hc.
    destruct (sm_apart L ar C HI LY HIok LB4 FF LK4 cr4 A4 M4 _ F 1 _ fl (spq + 16) (RESIZE_SCR + 16) a 1 HH4 SPT ltac:(left; reflexivity) ltac:(clear - FR; lia)
                ltac:(change (ff_bytes 1) with 128; exact (proj2 (proj2 (proj2 FR)))) ltac:(change (ff_bytes 1) with 128; exact FAPP) ltac:(change (ff_bytes 1) with 128; exact FM128)
                ltac:(change (ff_bytes 1) with 128; exact FAP) ltac:(change (ff_bytes 1) with 128; exact FBLK) FLNC
                ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (X1 & X2 & X3).
    change (ff_bytes 1) with 128 in X1, X2. change (128 / 8) with 16 in X2. unfold S in Ha'. rewrite (proj1 FQ15) in Ha'. clear - Ha' X1 X2. unfold SB in *. lia. }
  assert (E47 : ek L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) [(o + 8, 8); (dst, cnt)] M4 M7).
  { eapply ek_trans. { apply (ek_piece L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) _ M4 M5 _ FRM5). intros a Ha Hc Ho [X|X].
      destruct (aclient_cases L ar C HI LY HIok LB4 FF LK4 cr4 A4 M7 _ (spq + 16) (RESIZE_SCR + 16) a HH7 SPT Hc) as [Y|Y].
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
      apply (Ho (o + 8, 8)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]; clear - X; lia. }
    eapply ek_trans. { apply (ek_mem L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) (spq - 128) 2560 (fun a => dst <= a < dst + cnt) _ M5 M6).
      intros a Ha Hc Hn'. apply PRES6. exact Ha. apply aclient_cons. exact Hc. exact Hn'.
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
      intros a _ Ho X. apply (Ho (dst, cnt)). right; left; reflexivity. exact X. }
    apply (ek_piece L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) _ M6 M7 _ FRM7). intros a Ha Hc Ho. subst W7; cbn beta. intros [[X|[X|X]]|X].
    - destruct (aclient_cases L ar C HI LY HIok LB4 FF LK4 cr4 A4 M7 _ (spq + 16) (RESIZE_SCR + 16) a HH7 SPT Hc) as [Y|Y].
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
    - apply (NCF a). left. clear - X; lia. exact Hc.
    - apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc.
    - subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc. }
  assert (D47 : dk L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) M4 M7).
  { eapply dk_trans. apply dk_grows. exact MGM5.
    eapply dk_trans. { apply (dk_mem L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) (spq - 128) 2560 (fun a => dst <= a < dst + cnt) M5 M6).
      intros a Ha Hc Hn'. apply PRES6. exact Ha. apply aclient_cons. exact Hc. exact Hn'. exact SDEF6.
      intros a Ha. destruct (ZB (a - dst) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (dst + (a - dst)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
      intros a; destruct (rng_dec a dst (dst + cnt)) as [X|X]; [left; exact X | right; exact X].
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
    apply dk_grows. exact MGM7. }
  assert (XV7 : forall a v, avis H6 a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M7v a v -> L5.u64_at RSEGS M7 a v).
  { intros a v Va Ha H8 Hc. apply (proj1 (u64_at_vis H6 M7 a v Va Ha H8)). unfold H6. rewrite VIS7. exact Hc. }
  apply (KONT fx7 R7 M7 model7 LK4).
  - apply preserved_by_index. intros k Hk. cbn in Hk.
    destruct Hk as [<-|Hk]. { rewrite ER2. rewrite <- r2, G2. reflexivity. }
    destruct Hk as [<-|Hk]. { rewrite (EKS 3%nat) by inl. rewrite (cs_of_preserved R5 R6 3 RP6) by inl. rewrite (CdKS 3%nat) by inl. exact Q3. }
    destruct Hk as [<-|Hk]. { rewrite (EKS 4%nat) by inl. rewrite (cs_of_preserved R5 R6 4 RP6) by inl. rewrite (CdKS 4%nat) by inl. rewrite Q4, <- r4, G4. reflexivity. }
    repeat (destruct Hk as [<-|Hk]; [first [rewrite ER8 | rewrite ER9 | rewrite ER18 | rewrite ER19 | rewrite ER20 | rewrite ER21 | rewrite ER22 | rewrite ER23
                                           | rewrite ER24 | rewrite ER25 | rewrite ER26
                                           | (rewrite (EKS 27%nat) by inl; rewrite (cs_of_preserved R5 R6 27 RP6) by inl; rewrite (CdKS 27%nat) by inl; exact Q27)];
                                     try (symmetry; apply U_to) |]). destruct Hk.
  - (* [comment removed for export] *) eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia.
    intros j Hj. apply E47. split. clear - Hj OR; lia. split. apply (obj_client L ar LB4 FF _ _ o 32 j AOB). clear - Hj; lia.
    intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Hj; lia.
    destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ INB)))))) g ltac:(apply in_or_app; left; right; exact Hg)) as X.
    cbn [fst snd] in X. clear - Hj X X1 X2 DSTR; lia.
  - (* [comment removed for export] *) apply (XV7 (o + 8) (Z.of_nat n) ltac:(eapply avis_sub; [exact OVIS6 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia)).
    eapply L5C.u64_at_agree. 4: exact CdQ_V33nat. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. rewrite <- AG56. 2: unfold RNG; clear - Hj; lia.
    apply EFZ. clear - Hj OR; lia. all: clear - Hj OR OBIG SLO SPT OF OFL FR F8; unfold SB in *; lia.
  - eapply L5C.u64_at_agree. 4: exact O16. 2: clear - OR; lia. 2: clear - OR; lia.
    intros j Hj. apply E47. split. clear - Hj OR; lia. split. apply (obj_client L ar LB4 FF _ _ o 32 j AOB). clear - Hj; lia.
    intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Hj; lia.
    destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ INB)))))) g ltac:(apply in_or_app; left; right; exact Hg)) as X.
    cbn [fst snd] in X. clear - Hj X X1 X2 DSTR; lia.
  - eapply L5C.u64_at_agree. 4: exact O24. 2: clear - OR; lia. 2: clear - OR; lia.
    intros j Hj. apply E47. split. clear - Hj OR; lia. split. apply (obj_client L ar LB4 FF _ _ o 32 j AOB). clear - Hj; lia.
    intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Hj; lia.
    destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ INB)))))) g ltac:(apply in_or_app; left; right; exact Hg)) as X.
    cbn [fst snd] in X. clear - Hj X X1 X2 DSTR; lia.
  - (* [comment removed for export] *) intros a v Ha Ha8 Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha P0; lia. 2: clear - Ha8 DSTR; lia.
    intros j Hj. apply E47. split. clear - Hj Ha Ha8 P0 DSTR; lia. split. apply (block_client L ar LB4 FF _ _ p (8 * cap)). exact INB. clear - Hj Ha Ha8 DSTR; lia.
    intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd].
    destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 _ INB)))))) g ltac:(apply in_or_app; left; right; exact Hg)) as X.
    cbn [fst snd] in X. clear - Hj X X1 X2 Ha Ha8 DSTR; lia. subst dst; clear - Hj Ha Ha8; lia.
  - (* [comment removed for export] *) intros i Hi.
    assert (VP : avis H6 (p + 8 * i) 8). { apply (VBLK6 p (8 * cap) (p + 8 * i) 8 INB). clear - Hi LEN; lia. clear - Hi NC; lia. }
    apply (XV7 (p + 8 * i) 0 VP ltac:(clear - Hi LEN P0; lia) ltac:(clear - Hi NC P5; lia)).
    apply u64_of_zeros_at. 2: clear - Hi LEN P0; lia. 2: clear - Hi NC P5; lia.
    intros j Hj. rewrite <- VIS7. unfold mrestrict. fold H6. rewrite (VP j Hj). rewrite FRM7.
    + destruct (ZB (p + 8 * i + j - dst) ltac:(subst dst cnt; clear - Hi Hj; lia)) as (v & Ev & Bv). unfold byte_at in Bv.
      replace (dst + (p + 8 * i + j - dst)) with (p + 8 * i + j) in Bv by (clear; lia). rewrite Bv. rewrite Ev. reflexivity.
    + clear - Hi Hj LEN NC P0 P5; lia.
    + subst W7; cbn beta. pose proof FBLK as FB'. specialize (FB' _ INB). cbn [fst snd] in FB'. clear - Hi Hj LEN NC P0 P4 P5 FB' FLNC SLO SPT FR F8 INB FLP.
      intros [[X|[X|X]]|X]. lia. lia. unfold SB in X. lia.
      apply FLNC. subst fl. apply aclient_cons. apply (block_client L ar LB4 FF 0 0 p (8 * cap)). exact INB. lia.
  - eapply ek_W. exact E47. intros a Ho rr [<-|[<-|[]]] X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng in X |- *; cbn [fst snd] in X |- *; clear - X; lia.
    apply (Ho (p + 8 * Z.of_nat len, 8 * (Z.of_nat n - Z.of_nat len))). right; left; reflexivity. exact X.
  - exact D47.
  - eapply astk_defined. exact ASTK7. clear; lia. clear; lia.
  - eapply L5LZ.model_rt_trans. exact RT5. eapply L5LZ.model_rt_trans. exact RT6. exact RT7.
  - exact AM7.
  - apply incl_refl.
  - exact HH7.
Qed.

Lemma ret_tail fx4 R4 M4 model4 K LB4 FF LK4 cr4 A4 (o spq r : Z) (n len : nat) (fb4 p cap F fl : Z) (R : bvmap 5 word) :
  let FF' := (F, 1, spq - 128 + 32) :: FF in let H4 := ahid A4 model4 in let MV4 := mrestrict H4 M4 in
  ri_inv HI LB4 FF' LK4 cr4 A4 M4 (vml_of model4) -> amodel_ok A4 model4 -> K [] ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 (spq + 16) -> spq mod 32 = 0 -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M4 (spq + 16) (RESIZE_SCR + 16) -> Z.of_nat n <= 2 ^ 23 ->
  getr R4 (reg 2) = Z_to_bv 64 (spq - 128) -> getr R4 (reg 8) = Z_to_bv 64 (spq + 16) -> getr R4 (reg 9) = Z_to_bv 64 (spq - 128) -> getr R4 (reg 18) = Z_to_bv 64 F ->
  getr R4 (reg 19) = Z_to_bv 64 (Z.of_nat n) -> getr R4 (reg 20) = Z_to_bv 64 o -> getr R4 (reg 21) = Z_to_bv 64 (o + 8) -> getr R4 (reg 22) = Z_to_bv 64 (F / 8 + SB) ->
  getr R4 (reg 23) = Z_to_bv 64 F -> getr R4 (reg 24) = Z_to_bv 64 SB -> getr R4 (reg 25) = Z_to_bv 64 (Z.of_nat len) -> getr R4 (reg 26) = Z_to_bv 64 ((o + 8) / 8 + SB) ->
  getr R4 (reg 3) = getr R (reg 3) -> getr R4 (reg 4) = Z_to_bv 64 (hl_tp L) -> getr R4 (reg 27) = getr R (reg 27) ->
  L5.u64_at RSEGS MV4 (spq + 8) (U R 1) -> L5.u64_at RSEGS MV4 spq (U R 8) -> L5.u64_at RSEGS MV4 (spq - 8) (U R 9) -> L5.u64_at RSEGS MV4 (spq - 16) (U R 18) ->
  L5.u64_at RSEGS MV4 (spq - 24) (U R 19) -> L5.u64_at RSEGS MV4 (spq - 32) (U R 20) -> L5.u64_at RSEGS MV4 (spq - 40) (U R 21) -> L5.u64_at RSEGS MV4 (spq - 48) (U R 22) ->
  L5.u64_at RSEGS MV4 (spq - 56) (U R 23) -> L5.u64_at RSEGS MV4 (spq - 64) (U R 24) -> L5.u64_at RSEGS MV4 (spq - 72) (U R 25) -> L5.u64_at RSEGS MV4 (spq - 80) (U R 26) ->
  L5.u64_at RSEGS MV4 (spq - 112) 0 ->
  (4096 <= F /\ F + 128 <= 2 ^ 47 /\ 0x634000 <= F /\ F + 128 <= ahl_ceil ar) -> (F / 8) * 8 = F -> ar_fs ar <= F -> F + 128 <= ar_fs ar + FS_BYTES ->
  (0x7fff7000 + 17592186048512 <= F \/ F + 128 <= 0x7fff7000) -> L5.defined M4 (F / 8 + SB) 16 -> L5.u64_at RSEGS MV4 (F + 120) fl ->
  ar_fs ar <= fl < ar_fs ar + FS_BYTES -> ~ aclient L ar LB4 FF' 0 0 fl -> (F + 128 <= fl \/ fl + 1 <= F) -> (0x7fff7000 + 17592186048512 <= fl \/ fl + 1 <= 0x7fff7000) ->
  (o + 32 <= F \/ F + 128 <= o) -> (o + 32 <= fl \/ fl + 1 <= o) -> (o / 8 + SB + 4 <= F / 8 + SB \/ F / 8 + SB + 16 <= o / 8 + SB) ->
  aobj FF o 32 -> L5.u8_at RSEGS M4 o fb4 -> 0 <= fb4 < 256 -> L5.u64_at RSEGS M4 (o + 16) cap -> L5.u64_at RSEGS M4 (o + 24) p -> shadow_zero M4 o 4 ->
  Z.of_nat len <= 2 ^ 27 -> ((n <= len)%nat \/ (Z.testbit fb4 0 = false /\ (len < n)%nat /\ (n <= 2)%nat)) ->
  (forall (fx7 : FPState) R7 M7 model7 LK7, regs_preserved R R7 ->
      L5.u8_at RSEGS M7 o fb4 -> L5.u64_at RSEGS M7 (o + 8) (Z.of_nat n) ->
      (forall a v, o + 16 <= a -> a + 8 <= o + 32 -> ((n <= len)%nat \/ a + 8 <= o + 16 + 8 * Z.of_nat len) -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M7 a v) ->
      (forall i, (len < n)%nat -> Z.of_nat len <= i < 2 -> L5.u64_at RSEGS M7 (o + 16 + 8 * i) 0) ->
      ek L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] M4 M7 -> dk L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) M4 M7 ->
      L5.defined M7 ((spq + 16) - (RESIZE_SCR + 16)) (RESIZE_SCR + 16) ->
      model_rt model4 model7 -> amodel_ok A4 model7 -> incl LK7 LK4 -> ri_inv HI LB4 FF LK7 cr4 A4 M7 (vml_of model7) ->
      srealizes RSEGS SCFG (cfg (fx:=fx7) R7 r M7 model7) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x8fdd4 M4 model4) K.
Proof.
  intros FF' H4 MV4 HH4 AM4 HK G1 RA G2 A32 G4 ASTK4 Hn Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q3 Q4 Q27
         C8 C16 C24 C32 C40 C48 C56 C64 C72 C80 C88 C96 C128 FR F8 FS1 FS2 FBIG FSHD FLC FLP FLNC FFL FLBIG OF OFL OSHF
         AOB O0 Hfb O16 O24 SZ LEN2 MODE KONT.
  pose proof ASTK4 as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  assert (SPR : 0 <= (spq + 16) < 2 ^ 64 /\ 140735332487296 <= (spq + 16) <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  pose proof (statics_vis LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4). fold H4 MV4 in IMGC4, CSB4, CUAR4.
  assert (AOB' : aobj FF' o 32). { apply aobj_cons. exact AOB. }
  pose proof (aobj_facts L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 o 32 0 0 HH4 AOB' ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF4 & OVIS4 & OVSH4 & OCL4 & OCLSH4). change (32 / 8) with 4 in OVSH4, OCLSH4. fold H4 in OVIS4, OVSH4.
  pose proof (fl_range L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 _ fl HH4 FLP) as FLR.
  (* [comment removed for export] *)
  assert (XO4 : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS MV4 a v).
  { intros a v Ha Hc. apply (proj2 (u64_at_vis H4 M4 a v ltac:(eapply avis_sub; [exact OVIS4 | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))). exact Hc. }
  assert (OB4 : L5.u8_at RSEGS MV4 o fb4). { apply (proj2 (u8_at_vis H4 M4 o fb4 ltac:(eapply avis_sub; [exact OVIS4 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). exact O0. }
  assert (OZ4 : L5KA.zeros_at MV4 (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H4 M4 _ 4 OVSH4)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (OW4 : L5.writable RSEGS MV4 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H4 M4 o 32 OVIS4)). exact ODEF4. clear - OR; lia. clear - OR; lia. }
  assert (W128 : L5.writable RSEGS MV4 (spq - 128) 144).
  { apply (proj2 (writable_vis H4 M4 (spq - 128) 144 (VIS4 (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M4 (spq + 16)). exact ASTK4. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as (WB4 & WF4 & _).
  assert (VF4 : avis H4 F 128). { apply (VFS4 F 128 FS1 FS2). }
  assert (FDEF4 : L5.defined MV4 F 128). { apply (proj2 (defined_vis H4 M4 F 128 VF4)). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))))). }
  assert (FW4 : L5.writable RSEGS MV4 F 128). { apply (L5C.writable_of_defined RSEGS). exact FDEF4. clear - FR; lia. clear - FR; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (F32 : F mod 32 = 0).
  { pose proof (proj1 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))) as X. cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 1) with 128 in X. clear - X. lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (VSH4 : avis H4 (F / 8 + SB) 16).
  { apply VFSSH4. intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (FSHW4 : L5.writable RSEGS MV4 (F / 8 + SB) 16).
  { apply (proj2 (writable_vis H4 M4 _ 16 VSH4 ltac:(clear - FR F8; unfold SB; lia) ltac:(clear - FR F8; unfold SB; lia))). apply (L5C.writable_of_defined RSEGS). exact FSHD.
    clear - FR F8; unfold SB; lia. clear - FR F8; unfold SB; lia. }
  pose proof (fl_writable L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 _ fl HH4 FLP) as [FLD4 FLW4].
  pose proof (fl_vis L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 fl HH4 FLP) as FLV4. fold H4 in FLV4.
  assert (FLW4v : L5.writable RSEGS MV4 fl 1). { apply (proj2 (writable_vis H4 M4 fl 1 FLV4 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW4. }
  assert (SF : spq - 128 + 144 <= F \/ F + 128 <= spq - 128) by (clear - FR SLO; lia).
  assert (SFL : spq - 128 + 144 <= fl \/ fl + 1 <= spq - 128) by (clear - FLR SLO; lia).
  assert (SO : spq - 128 + 144 <= o \/ o + 32 <= spq - 128) by (clear - OR SLO; lia).
  (* [comment removed for export] *)
  set (VC := fun j : nat => match j with 2%nat => spq | 33%nat => o | 34%nat => Z.of_nat n | 35%nat => Z.of_nat len | 36%nat => fb4 | 37%nat => p | 40%nat => F | 41%nat => fl
                | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R4 1 | 48%nat => U R 24
                | 49%nat => U R 18 | 50%nat => U R 21 | 51%nat => U R 22 | 52%nat => U R 23 | 53%nat => U R 25 | 54%nat => U R 26 | _ => 0 end).
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (RUN : exists fx7 R7 M7v, mem_grows MV4 M7v
            /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (spq - 128 <= i < spq - 128 + 144) -> ~ (F + 0 <= i < F + 0 + 24) -> ~ (F + 32 <= i < F + 32 + 88) -> ~ (F / 8 + SB <= i < F / 8 + SB + 16) -> ~ (fl + 0 <= i < fl + 0 + 1)
                  -> ~ (o + 8 <= i < o + 8 + 24) -> M7v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx4 R4 0x8fdd4 MV4) (st fx7 R7 r M7v)
            /\ (forall k, In k cs_all -> getr R7 (reg k) = getr R (reg k))
            /\ L5.u8_at RSEGS M7v fl 0 /\ L5.u64_at RSEGS M7v (o + 8) (Z.of_nat n)
            /\ (forall i, 0 <= i < 2 ^ 64 -> o + 16 <= i < o + 32 -> ((n <= len)%nat \/ i < o + 16 + 8 * Z.of_nat len) -> M7v (Z_to_bv 64 i) = MV4 (Z_to_bv 64 i))
            /\ (forall i, (len < n)%nat -> Z.of_nat len <= i < 2 -> L5.u64_at RSEGS M7v (o + 16 + 8 * i) 0)).
  { assert (RPF : forall R7 (KS : list nat), (forall x, In x KS -> getr R7 (reg x) = getr R4 (reg x)) -> incl [3; 4; 27]%nat KS ->
              getr R7 (reg 2) = Z_to_bv 64 (spq + 16) -> getr R7 (reg 8) = Z_to_bv 64 (U R 8) -> getr R7 (reg 9) = Z_to_bv 64 (U R 9) ->
              getr R7 (reg 18) = Z_to_bv 64 (U R 18) -> getr R7 (reg 19) = Z_to_bv 64 (U R 19) -> getr R7 (reg 20) = Z_to_bv 64 (U R 20) ->
              getr R7 (reg 21) = Z_to_bv 64 (U R 21) -> getr R7 (reg 22) = Z_to_bv 64 (U R 22) -> getr R7 (reg 23) = Z_to_bv 64 (U R 23) ->
              getr R7 (reg 24) = Z_to_bv 64 (U R 24) -> getr R7 (reg 25) = Z_to_bv 64 (U R 25) -> getr R7 (reg 26) = Z_to_bv 64 (U R 26) ->
              forall k, In k cs_all -> getr R7 (reg k) = getr R (reg k)).
    { intros R7 KS HKS HKI E2 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 k Hk. cbn in Hk.
      destruct Hk as [<-|Hk]. { rewrite E2. rewrite <- r2, G2. reflexivity. }
      destruct Hk as [<-|Hk]. { rewrite (HKS 3%nat (HKI 3%nat (or_introl eq_refl))). exact Q3. }
      destruct Hk as [<-|Hk]. { rewrite (HKS 4%nat (HKI 4%nat (or_intror (or_introl eq_refl)))). rewrite Q4, <- r4, G4. reflexivity. }
      repeat (destruct Hk as [<-|Hk]; [first [rewrite E8 | rewrite E9 | rewrite E18 | rewrite E19 | rewrite E20 | rewrite E21 | rewrite E22 | rewrite E23 | rewrite E24 | rewrite E25 | rewrite E26
                                             | (rewrite (HKS 27%nat (HKI 27%nat (or_intror (or_intror (or_introl eq_refl))))); exact Q27)]; try (symmetry; apply U_to) |]). destruct Hk. }
    destruct MODE as [GE|(B0 & LT & N2)].
    - pose proof (rz16Cge_conc fx4 R4 MV4 VC) as P. cbn beta iota delta [VC] in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx7 & R7 & M7v & MG7 & CgeFR & CgeFZ & (CgeMS & CgeKS & CgeR1 & CgeR2 & CgeR8 & CgeR9 & CgeR10 & CgeR18 & CgeR19 & CgeR20 & CgeR21 & CgeR22 & CgeR23 & CgeR24 & CgeR25 & CgeR26 & CgeB_V41nat & CgeB_V40nat & CgeB_V40nat_1 & CgeB_V40nat_2 & CgeB_V40nat_3 & CgeB_V40nat_4 & CgeB_V40nat_5 & CgeB_V40nat_6 & CgeB_V40nat_7 & CgeB_V40nat_8 & CgeB_V40nat_9 & CgeB_V40nat_10 & CgeB_V40nat_11 & CgeB_V40nat_12 & CgeB_V40nat_13 & CgeB_V40nat_14 & CgeB_V40nat_15 & CgeQ_V40nat & CgeQ_V33nat & CgeDF)).
      exists fx7, R7, M7v. split. exact MG7. split. { intros i Hi X1 X2 X2' X3 X4 X5. apply CgeFZ. exact Hi. exact X1. exact X2. exact X2'. exact X3. exact X4. clear - X5; lia. }
      split. { eapply msteps_trans. exact CgeMS. apply (ret_to fx7 R7 M7v 0x8ff64 W_8ff64 r F_8ff64 eq_refl D_8ff64). rewrite CgeR1, UR1; reflexivity. exact (proj1 RA). exact (proj2 RA). }
      split. { apply (RPF R7 KS_rz16Cge CgeKS). refine (L5K.incl_b _ _ _); vm_compute; reflexivity. all: assumption. }
      split. exact CgeB_V41nat. split. exact CgeQ_V33nat. split. { intros i Hi Ho _. apply CgeFZ. exact Hi. all: clear - Ho OR SLO SPT OF OFL OSHF FR F8 OBIG FBIG; unfold SB in *; lia. }
      intros i LT' _. exfalso. clear - GE LT'; lia.
    - destruct len as [|[|len]]. 3: exfalso; clear - LT N2; lia.
      + pose proof (rz16Ci0_conc fx4 R4 MV4 VC) as P. cbn beta iota delta [VC] in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx7 & R7 & M7v & MG7 & Ci0FR & Ci0FZ & (Ci0MS & Ci0KS & Ci0R1 & Ci0R2 & Ci0R8 & Ci0R9 & Ci0R10 & Ci0R11 & Ci0R12 & Ci0R13 & Ci0R18 & Ci0R19 & Ci0R20 & Ci0R21 & Ci0R22 & Ci0R23 & Ci0R24 & Ci0R25 & Ci0R26 & Ci0B_V41nat & Ci0B_V40nat & Ci0B_V40nat_1 & Ci0B_V40nat_2 & Ci0B_V40nat_3 & Ci0B_V40nat_4 & Ci0B_V40nat_5 & Ci0B_V40nat_6 & Ci0B_V40nat_7 & Ci0B_V40nat_8 & Ci0B_V40nat_9 & Ci0B_V40nat_10 & Ci0B_V40nat_11 & Ci0B_V40nat_12 & Ci0B_V40nat_13 & Ci0B_V40nat_14 & Ci0B_V40nat_15 & Ci0Q_V40nat & Ci0Q_V33nat & Ci0Q_V33nat_1 & Ci0Q_V33nat_2 & Ci0DF)).
        exists fx7, R7, M7v. split. exact MG7. split. { intros i Hi X1 X2 X2' X3 X4 X5. apply Ci0FZ. exact Hi. exact X1. exact X2. exact X2'. exact X3. exact X4. clear - X5; lia. }
        split. { eapply msteps_trans. exact Ci0MS. apply (ret_to fx7 R7 M7v 0x8ff64 W_8ff64 r F_8ff64 eq_refl D_8ff64). rewrite Ci0R1, UR1; reflexivity. exact (proj1 RA). exact (proj2 RA). }
        split. { apply (RPF R7 KS_rz16Ci0 Ci0KS). refine (L5K.incl_b _ _ _); vm_compute; reflexivity. all: assumption. }
        split. exact Ci0B_V41nat. split. exact Ci0Q_V33nat_2. split. { intros i Hi Ho [X|X]; exfalso; [clear - X LT; lia | clear - X Ho; lia]. }
        intros i _ Hi. assert (X : i = 0 \/ i = 1) by (clear - Hi; lia). destruct X as [-> | ->]. replace (o + 16 + 8 * 0) with (o + 16) by (clear; lia). exact Ci0Q_V33nat_1.
        replace (o + 16 + 8 * 1) with (o + 24) by (clear; lia). exact Ci0Q_V33nat.
      + pose proof (rz16Ci1_conc fx4 R4 MV4 VC) as P. cbn beta iota delta [VC] in P.
        assert (N2' : n = 2%nat) by (clear - LT N2; lia). rewrite N2' in Q19.
        feed P ltac:(first [apply UR | apply U_to | sc | (rewrite N2'; sc)]).
        destruct P as (fx7 & R7 & M7v & MG7 & Ci1FR & Ci1FZ & (Ci1MS & Ci1KS & Ci1R1 & Ci1R2 & Ci1R8 & Ci1R9 & Ci1R10 & Ci1R11 & Ci1R12 & Ci1R13 & Ci1R18 & Ci1R19 & Ci1R20 & Ci1R21 & Ci1R22 & Ci1R23 & Ci1R24 & Ci1R25 & Ci1R26 & Ci1B_V41nat & Ci1B_V40nat & Ci1B_V40nat_1 & Ci1B_V40nat_2 & Ci1B_V40nat_3 & Ci1B_V40nat_4 & Ci1B_V40nat_5 & Ci1B_V40nat_6 & Ci1B_V40nat_7 & Ci1B_V40nat_8 & Ci1B_V40nat_9 & Ci1B_V40nat_10 & Ci1B_V40nat_11 & Ci1B_V40nat_12 & Ci1B_V40nat_13 & Ci1B_V40nat_14 & Ci1B_V40nat_15 & Ci1Q_V40nat & Ci1Q_V33nat & Ci1Q_V33nat_1 & Ci1DF)).
        exists fx7, R7, M7v. split. exact MG7. split. { intros i Hi X1 X2 X2' X3 X4 X5. apply Ci1FZ. exact Hi. exact X1. exact X2. exact X2'. exact X3. exact X4. clear - X5; lia. clear - X5; lia. }
        split. { eapply msteps_trans. exact Ci1MS. apply (ret_to fx7 R7 M7v 0x8ff64 W_8ff64 r F_8ff64 eq_refl D_8ff64). rewrite Ci1R1, UR1; reflexivity. exact (proj1 RA). exact (proj2 RA). }
        split. { apply (RPF R7 KS_rz16Ci1 Ci1KS). refine (L5K.incl_b _ _ _); vm_compute; reflexivity. all: assumption. }
        split. exact Ci1B_V41nat. split. { rewrite N2'. exact Ci1Q_V33nat_1. } split. { intros i Hi Ho X. apply Ci1FZ. exact Hi. all: clear - Ho OR SLO SPT OF OFL OSHF FR F8 OBIG FBIG X LT; unfold SB in *; lia. }
        intros i _ Hi. assert (X : i = 1) by (clear - Hi; lia). subst i. replace (o + 16 + 8 * 1) with (o + 24) by (clear; lia). exact Ci1Q_V33nat. }
  destruct RUN as (fx7 & R7 & M7v & MG7 & XFZ & MS8 & RP7 & XFL & XO8 & XKEEP & XZERO).
  set (W7 := fun a => (spq - 128 <= a < (spq + 16) \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16) \/ a = fl \/ (o + 8 <= a < o + 32 /\ ~ (o + 16 <= a /\ ((n <= len)%nat \/ a < o + 16 + 8 * Z.of_nat len)))).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  apply (apiece_retire L ar C HI LY HIok LB4 FF LK4 cr4 A4 M4 model4 fx4 fx7 R4 0x8fdd4 R7 r M7v W7 F 1 (spq - 128 + 32) fl K HH4 AM4).
  { change (ff_bytes 1) with 128. replace (F + 128 - 8) with (F + 120) by (clear; lia).
    apply (proj1 (u64_at_vis H4 M4 (F + 120) fl ltac:(eapply avis_sub; [exact VF4 | clear; lia | clear; lia]) ltac:(clear - FR; lia) ltac:(clear - FR; lia))). exact FLC. }
  { exact FLNC. }
  { exact FLV4. }
  { clear - FLR; lia. }
  { exact MS8. }
  { exact MG7. }
  { intros a Ha Hna. subst W7; cbn beta in Hna. destruct (rng_dec a (o + 16) (o + 32)) as [I|I].
    - destruct (Nat.le_gt_cases n len) as [GE|LT]. apply XKEEP. exact Ha. exact I. left; exact GE.
      destruct (Z_lt_le_dec a (o + 16 + 8 * Z.of_nat len)) as [J|J]. apply XKEEP. exact Ha. exact I. right; exact J.
      exfalso. apply Hna. right; right. split. clear - I; lia. intros [_ [X|X]]. clear - X LT; lia. clear - X J; lia.
    - apply XFZ. exact Ha. all: clear - Hna I; unfold SB in *; first [lia | intros X; apply Hna; right; right; split; [clear - X; lia | intros [Y _]; clear - X Y I; lia]]. }
  { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [Wa|[Wa|[Wa _]]]. 2: left; exact Wa.
    - right. destruct Wa as [X|[X|X]]. apply stack_client. clear - X SLO SHI SPT; lia. clear; lia.
      apply (fframe_client L ar LB4 FF' _ _ F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - X; lia.
      apply (fframe_shadow_client L ar LB4 FF' _ _ F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. rewrite (proj1 FQ15). clear - X; unfold SB in *; lia.
    - right. apply (obj_client L ar LB4 FF' 0 0 o 32 a AOB'). clear - Wa; lia. }
  { intros a. subst W7; cbn beta. repeat match goal with X : _ |- _ => clear X end.
    destruct (rng_dec a (spq - 128) (spq + 16)) as [A1|A1]; [left; tauto|]. destruct (rng_dec a F (F + 24)) as [A2|A2]; [left; tauto|]. destruct (rng_dec a (F + 32) (F + 120)) as [A2'|A2']; [left; tauto|].
    destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 16)) as [A3|A3]; [left; tauto|]. destruct (Z.eq_dec a fl) as [A4|A4]; [tauto|].
    destruct (rng_dec a (o + 8) (o + 32)) as [A5|A5]. 2:{ right. intros [[X|[X|X]]|[X|[X _]]]; tauto. }
    destruct (Z_lt_le_dec a (o + 16)) as [A6|A6]. { left; right; right; split; [exact A5 | intros [X _]; lia]. }
    destruct (Nat.le_gt_cases n len) as [A7|A7]. { right. intros [[X|[X|X]]|[X|[Y X]]]; tauto. }
    destruct (Z_lt_le_dec a (o + 16 + 8 * Z.of_nat len)) as [A8|A8]. { right. intros [[X|[X|X]]|[X|[Y X]]]; tauto. }
    left; right; right. split. exact A5. intros [_ [X|X]]; lia. }
  { exact XFL. }
  intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
  assert (ASTK7 : astk ar M7 (spq + 16) (RESIZE_SCR + 16)). { eapply astk_grows. exact ASTK4. exact MGM7. }
  assert (FM128 : F mod 128 = 0).
  { pose proof (proj1 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))) as X. cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 1) with 128 in X. exact X. }
  assert (FAPP : app_mem F 128). { unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI. clear - FR FBIG; lia. }
  assert (FAP : fframes_apart F 128 (FF ++ LK4)).
  { pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (WF4 _ (or_introl eq_refl))))))) as X. unfold FF' in X. cbn [ff_addr ff_class fst snd ff_remove] in X. rewrite Z.eqb_refl in X.
    change (ff_bytes 1) with 128 in X. exact X. }
  assert (FBLK : forall b, In b LB4 -> F + 128 <= fst b \/ fst b + snd b <= F).
  { intros b Hb. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB4 b Hb)))))) (F, 1, spq - 128 + 32) ltac:(apply in_or_app; left; left; reflexivity)) as X.
    cbn [ff_addr ff_class fst snd] in X. change (ff_bytes 1) with 128 in X. clear - X; lia. }
  assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) a).
  { intros a Ha' Hc.
    destruct (sm_apart L ar C HI LY HIok LB4 FF LK4 cr4 A4 M4 _ F 1 _ fl (spq + 16) (RESIZE_SCR + 16) a 1 HH4 SPT ltac:(left; reflexivity) ltac:(clear - FR; lia)
                ltac:(change (ff_bytes 1) with 128; exact (proj2 (proj2 (proj2 FR)))) ltac:(change (ff_bytes 1) with 128; exact FAPP) ltac:(change (ff_bytes 1) with 128; exact FM128)
                ltac:(change (ff_bytes 1) with 128; exact FAP) ltac:(change (ff_bytes 1) with 128; exact FBLK) FLNC
                ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (X1 & X2 & X3).
    change (ff_bytes 1) with 128 in X1, X2. change (128 / 8) with 16 in X2. unfold S in Ha'. rewrite (proj1 FQ15) in Ha'. clear - Ha' X1 X2. unfold SB in *. lia. }
  assert (XV7 : forall a v, avis H4 a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M7v a v -> L5.u64_at RSEGS M7 a v).
  { intros a v Va Ha H8 Hc. apply (proj1 (u64_at_vis H4 M7 a v Va Ha H8)). unfold H4. rewrite VIS7. exact Hc. }
  apply (KONT fx7 R7 M7 model7 LK4).
  - apply preserved_by_index. exact RP7.
  - eapply L5C.u8_at_agree. 4: exact O0. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply FRM7. clear - Hj OR; lia.
    subst W7; cbn beta. clear - Hj OR SLO SPT OF OFL OSHF FR F8 OBIG FBIG. unfold SB in *. intros [[X|[X|X]]|[X|[X _]]]; lia.
  - apply (XV7 (o + 8) (Z.of_nat n) ltac:(eapply avis_sub; [exact OVIS4 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia)). exact XO8.
  - intros a v Ha Ha8 Hm Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Ha8 OR; lia.
    intros j Hj. rewrite <- (mrestrict_visible H4 M4 (Z_to_bv 64 j)). 2:{ replace j with (o + (j - o)) by (clear; lia). apply (OVIS4 (j - o)). clear - Ha Ha8 Hj; lia. }
    rewrite <- XKEEP. 2: clear - Hj Ha Ha8 OR; lia. 2: clear - Hj Ha Ha8; lia. 2:{ destruct Hm as [Hm|Hm]. left; exact Hm. right; clear - Hm Hj; lia. }
    rewrite <- VIS7. symmetry. apply mrestrict_visible. replace j with (o + (j - o)) by (clear; lia). apply (OVIS4 (j - o)). clear - Ha Ha8 Hj; lia.
  - intros i LT Hi. apply (XV7 (o + 16 + 8 * i) 0 ltac:(eapply avis_sub; [exact OVIS4 | clear - Hi; lia | clear - Hi; lia]) ltac:(clear - OR Hi; lia) ltac:(clear - OR Hi; lia)). apply XZERO. exact LT. exact Hi.
  - apply (ek_piece L ar LB4 FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] M4 M7 _ FRM7). intros a Ha Hc Ho. subst W7; cbn beta. intros [[X|[X|X]]|[X|[X _]]].
    + destruct (aclient_cases L ar C HI LY HIok LB4 FF LK4 cr4 A4 M7 _ (spq + 16) (RESIZE_SCR + 16) a HH7 SPT Hc) as [Y|Y].
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
    + apply (NCF a). left. clear - X; lia. exact Hc.
    + apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc.
    + subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
    + apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia.
  - eapply dk_grows. exact MGM7.
  - eapply astk_defined. exact ASTK7. clear; lia. clear; lia.
  - exact RT7.
  - exact AM7.
  - apply incl_refl.
  - exact HH7.
Qed.

(* [comment removed for export] *)
Theorem resize_ok_at16 : reserve_spec L ar HI -> L5DLA.resize_spec_at 16 L ar HI.
Proof.
  intros RSV fx R M model K LB FF LK cr A o sp r n b ws HH AM HK G10 G11 Hn CAP CR G1 RA G2 A32 G4 STK ROOM RS OB OL AOB SZ INB KONT.
  assert (Esp : exists spq, sp = spq + 16) by (exists (sp - 16); clear; lia). destruct Esp as [spq ->].
  assert (A32q : spq mod 32 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  clear A32. rename A32q into A32.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  assert (SPR : 0 <= (spq + 16) < 2 ^ 64 /\ 140735332487296 <= (spq + 16) <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA16 : (spq - 128) mod 16 = 0 /\ (spq - 128) mod 32 = 0).
  { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 (spq + 16) (RESIZE_SCR + 16) HH AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  assert (LENB : (len <= 2)%nat \/ exists cap q, sto = L5.BDyn cap q /\ Z.of_nat len <= cap <= 2 ^ 27).
  { destruct sto as [v0 v1|cap q]. left. exact (proj1 (proj2 (proj2 (proj2 OST)))). right. exists cap, q. split. reflexivity. clear - OST. decompose [and] OST. lia. }
  assert (LEN : 0 <= Z.of_nat len <= 2 ^ 27) by (clear - LENB; destruct LENB as [X|(c & q & _ & X)]; lia).
  assert (W128 : L5.writable RSEGS MV (spq - 128) 144).
  { apply (proj2 (writable_vis H M (spq - 128) 144 (VIS (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M (spq + 16)). exact STK. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
  (* [comment removed for export] *)
  pose proof (rz16A_conc fx R MV (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => Z.of_nat n | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(first [apply UR | apply U_to | sc]).
  destruct P as (fx1 & R1 & M1v & MG1 & AFR & AFZ & (AMS & AKS & AR1 & AR2 & AR8 & AR9 & AR10 & AR11 & AR12 & AR19 & AR20 & AR24 & AQ_V2nat & AQ_V2nat_1 & AQ_V2nat_2 & AQ_V2nat_3 & AQ_V2nat_4 & AQ_V2nat_5 & AQ_V2nat_6 & AQ_V2nat_7 & AQ_V2nat_8 & AQ_V2nat_9 & AQ_V2nat_10 & AQ_V2nat_11 & AQ_V2nat_12)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R RESIZE R1 SM1 M1v (fun a => spq - 128 <= a < (spq + 16)) K HH AM AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = spq - 128). { rewrite r2, AR2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, (AKS 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, AR1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. replace (spq - 128) with (spq + 16 - 144) by (clear; lia). apply (astack_ok_of_astk L ar C LY M M1 (spq + 16) (RESIZE_SCR + 16) 144 512 STK MGM1). clear; lia. clear; lia. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
    first [exact (proj1 SA16) | (replace (spq + 16 - 144) with (spq - 128) by (clear; lia); exact (proj1 SA16))].
  - clear - ROOM. unfold ffr in ROOM. unfold ff_room. lia.
  - intros f Hf. rewrite U2. specialize (RS f Hf). clear - RS. lia.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, AR1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 1 (spq - 128 + 32) fl HH2 ltac:(left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 (spq + 16) (RESIZE_SCR + 16)).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ (spq + 16) _ (spq - 128) 512 HH STK MGM1 PRES2). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
      unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _ & _ & VFSSH2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    set (FF' := (F, 1, spq - 128 + 32) :: FF) in *.
    pose proof (aobj_facts L ar C HI LY HIok LB FF' LK2 cr A M2 model2 o 32 0 0 HH2 (aobj_cons FF _ o 32 AOB) ltac:(clear; lia) ltac:(reflexivity))
      as (_ & _ & ODEF2 & OVIS2 & OVSH2 & _). change (32 / 8) with 4 in OVSH2. fold H2 in OVIS2, OVSH2.
    assert (AG2 : forall a, (spq - 128 <= a < (spq + 16) \/ o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> MV2 (Z_to_bv 64 a) = (if (spq - 128 <=? a) then M1v (Z_to_bv 64 a) else M (Z_to_bv 64 a))).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      unfold MV2. rewrite (mrestrict_visible H2 M2).
      2:{ destruct Ra as [Ra|[Ra|Ra]]. replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS2 (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia. }
      rewrite (proj1 PRES2 a Ha).
      2:{ destruct Ra as [Ra|[Ra|Ra]]. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia. apply (obj_client L ar LB FF _ _ o 32 a AOB). exact Ra.
          apply (aclient_narrow L ar LB FF (spq + 16) (RESIZE_SCR + 16)). replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ra; lia.
          clear - Ra OR SLO SPT; unfold SB in *; lia. }
      destruct (Z.leb_spec (spq - 128) a) as [Hs|Hs].
      - rewrite <- VIS1. symmetry. apply mrestrict_visible. replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS (spq - 128) 144). clear - SLO; lia. clear - SPR; lia.
        clear - Ra Hs OR SLO SPT OBIG; unfold SB in *; lia.
      - apply FRM1. exact Ha. clear - Hs; lia. }
    assert (XC2 : forall a v, spq - 128 <= a <= spq + 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia. intros j Hj. rewrite AG2. 2: clear - Ha Hj; lia.
      destruct (Z.leb_spec (spq - 128) j) as [Hs|Hs]. reflexivity. exfalso; clear - Ha Hj Hs; lia. }
    assert (XO2 : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Ha OR; lia. intros j Hj. rewrite AG2. 2: clear - Ha Hj; lia.
      destruct (Z.leb_spec (spq - 128) j) as [Hs|Hs]. exfalso; clear - Ha Hj Hs OR SLO SPT; lia. reflexivity. }
    assert (OZ2 : L5KA.zeros_at MV2 (o / 8 + SB) 4).
    { intros i Hi. rewrite AG2. 2: clear - Hi; lia. destruct (Z.leb_spec (spq - 128) (o / 8 + SB + i)) as [Hs|Hs]. exfalso; clear - Hi Hs OR OBIG SLO SPT; unfold SB in *; lia.
      unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
    assert (OW2 : L5.writable RSEGS MV2 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
    assert (W128b : L5.writable RSEGS MV2 (spq - 128) 144).
    { apply (proj2 (writable_vis H2 M2 (spq - 128) 144 (VIS2 (spq - 128) 144 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M2 (spq + 16)). exact ASTK2. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. clear; lia. clear; lia. clear; lia. }
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl (spq + 16) (RESIZE_SCR + 16) o 32 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC OCL ltac:(clear; lia)) as (OF & OFSH & OFL).
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl (spq + 16) 0 (spq - 128) 144 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 1) with 128 in OF, SF. change (ff_bytes 1 / 8) with 16 in OFSH, SFSH.
    assert (OSHF : o / 8 + SB + 4 <= F / 8 + SB \/ F / 8 + SB + 16 <= o / 8 + SB) by (clear - OF F8 OR; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    (* [comment removed for export] *)
    assert (RS2 : forall k, In k [18; 21; 22; 23; 25; 26; 27]%nat -> getr R2 (reg k) = getr R (reg k)).
    { intros k Hk. rewrite (cs_of_preserved R1 R2 k RP2). apply AKS. revert Hk; apply (L5K.incl_b _ KS_rz16A); vm_compute; reflexivity.
      revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
    Local Ltac rwB RS := rewrite ?(RS 18%nat), ?(RS 21%nat), ?(RS 22%nat), ?(RS 23%nat), ?(RS 25%nat), ?(RS 26%nat), ?(RS 27%nat) by inl.
    pose proof (rz16B_conc fx1 R2 MV2 (fun j => match j with 2%nat => spq | 33%nat => o | 34%nat => Z.of_nat n | 35%nat => Z.of_nat len | 40%nat => F | 41%nat => fl
                  | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R2 1 | 48%nat => U R 24 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XC2; [clear; lia | unfold U; rwB RS2; sc]) | (apply XO2; [clear; lia | sc]) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & BFR & BFZ & (BMS & BKS & BR1 & BR10 & BR11 & BR12 & BR13 & BR14 & BR15 & BR18 & BR21 & BR22 & BR23 & BR25 & BR26 & BQ_V2nat & BB_V40nat & BB_V40nat_1 & BB_V40nat_2 & BB_V40nat_3 & BB_V40nat_4 & BB_V40nat_5 & BB_V40nat_6 & BB_V40nat_7 & BB_V40nat_8 & BB_V40nat_9 & BB_V40nat_10 & BB_V40nat_11 & BQ_V40nat & BQ_V40nat_1 & BQ_V40nat_2 & BQ_V2nat_1 & BQ_V2nat_2 & BQ_V2nat_3 & BQ_V2nat_4 & BQ_V2nat_5 & BQ_V2nat_6 & BQ_V2nat_7 & BQ_V2nat_8 & BQ_V2nat_9 & BQ_V2nat_10 & BQ_V2nat_11 & BQ_V2nat_12 & BQ_V2nat_13 & BDF)).
    rewrite (RS2 18%nat) in BQ_V2nat_4 by inl. rewrite (RS2 21%nat) in BQ_V2nat_7 by inl. rewrite (RS2 22%nat) in BQ_V2nat_8 by inl.
    rewrite (RS2 23%nat) in BQ_V2nat_9 by inl. rewrite (RS2 25%nat) in BQ_V2nat_11 by inl. rewrite (RS2 26%nat) in BQ_V2nat_12 by inl.
    apply (apiece L ar C HI LY HIok LB FF' LK2 cr A M2 model2 fx1 fx3 R2 0x8fd14 R3 RESERVE M3v
             (fun a => spq - 128 <= a < (spq + 16) \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16) K HH2 (conj Hh2 MI2) BMS MG3).
    { intros a Ha Hna. apply BFZ. exact Ha. all: clear - Hna; unfold SB in Hna; lia. }
    { intros a Ha [Wa|[Wa|Wa]].
      - split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia.
      - split. apply (fframe_client L ar LB FF' 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB FF' 0 0 F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. 
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 (spq + 16) (RESIZE_SCR + 16)). { eapply astk_grows. exact ASTK2. exact MGM3. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as WF2.
    assert (ND2 : NoDup (map ff_addr (FF' ++ LK2))). { clear - WF2. decompose [and] WF2. assumption. }
    (* [comment removed for export] *)
    assert (E03o : forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra OR; unfold SB in *; lia).
      rewrite FRM3. 2: exact Ha. 2:{ clear - Ra OR OBIG SLO SPT OF OSHF OFSH FBIG F8 FR; unfold SB in *; lia. }
      rewrite (proj1 PRES2 a Ha). 2:{ destruct Ra as [Ra|Ra]. apply (obj_client L ar LB FF _ _ o 32 a AOB). exact Ra.
          apply (aclient_narrow L ar LB FF (spq + 16) (RESIZE_SCR + 16)). replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ra; lia.
          clear - Ra OR SLO SPT; unfold SB in *; lia. }
      apply FRM1. exact Ha. clear - Ra OR SLO SPT OBIG; unfold SB in *; lia. }
    (* [comment removed for export] *)
    apply (RSV fx3 R3 M3 model3 K LB FF' LK2 cr A o (Z.of_nat n) (spq - 128) 0x8fdd4 (L5.BO fb len sto) HH3 AM3 HK).
    + rewrite r10. exact BR10.
    + rewrite r11. exact BR11.
    + clear - Hn; lia.
    + exact CAP.
    + cbn [L5.bo_dyn L5.bo_fb]. intros D G3. apply CR. clear - G3; lia. exact D.
    + rewrite r1. exact BR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. rk.
    + exact (proj2 SA16).
    + rewrite r4. rk.
    + replace (spq - 128) with (spq + 16 - 144) by (clear; lia). apply (astk_sub ar M3 M3 (spq + 16) (RESIZE_SCR + 16) 144 RESERVE_SCR ASTK3 (mem_grows_refl M3)). clear; lia. unfold RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
      unfold RESIZE_SCR; clear; lia. first [exact (proj1 SA16) | (replace (spq + 16 - 144) with (spq - 128) by (clear; lia); exact (proj1 SA16))].
    + apply (ffr_push FF LK LK2 (F, 1, spq - 128 + 32) 4 3 ROOM LKI2 ND2). clear; lia. clear; lia.
    + apply (ffrs_push FF (spq + 16)). exact RS. clear; lia. clear; lia.
    + eapply (L5C.big_at_agree RSEGS M M3). intros j Hj. apply E03o. left; clear - Hj; lia. clear - OR; lia. clear - OR; lia. exact OB.
    + apply aobj_cons. exact AOB.
    + intros j Hj. unfold byte_at, S. rewrite E03o. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj. right; clear - Hj; lia.
    + (* [comment removed for export] *)
      cbn [L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_cap].
      intros fx4 R4 M4 model4 gr LB4 cr4 LK4 A4 [RP4 POST] RT4 IA4 AM4 LKI4 HH4.
      (* [comment removed for export] *)
      assert (COMMON : forall (W4 : list L5.range), ahpres L ar LB FF' (spq - 128) RESERVE_SCR W4 M3 M4 ->
                (forall a, L5.outside [(o, 32)] a -> L5.outside W4 a) ->
                astk ar M4 (spq + 16) (RESIZE_SCR + 16)
                /\ (forall a, spq - 128 <= a < (spq + 16) \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16 \/ o / 8 + SB <= a < o / 8 + SB + 4 ->
                      mrestrict (ahid A4 model4) M4 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a))
                /\ L5.defined M4 (F / 8 + SB) 16
                /\ ek L ar LB FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] M M4 /\ dk L ar LB FF (spq + 16) (RESIZE_SCR + 16) M M4).
      { intros W4 PRES4 HW4.
        assert (ASTK4 : astk ar M4 (spq + 16) (RESIZE_SCR + 16)).
        { apply (astk_after L ar C HI HIok LB FF' LK2 cr A M3 M3 M4 _ (spq + 16) _ (spq - 128) RESERVE_SCR W4 HH3 ASTK3 (mem_grows_refl M3) PRES4).
          unfold RESIZE_SCR; clear; lia. clear; lia. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
        pose proof (vis_pack L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 HH4) as (_ & VIS4 & _ & VFS4 & _ & _ & VFSSH4 & _).
        pose proof (aobj_facts L ar C HI LY HIok LB4 FF' LK4 cr4 A4 M4 model4 o 32 0 0 HH4 (aobj_cons FF _ o 32 AOB) ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS4 & OVSH4 & _).
        change (32 / 8) with 4 in OVSH4.
        assert (CL : forall a, spq - 128 <= a < (spq + 16) \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16 \/ o / 8 + SB <= a < o / 8 + SB + 4 ->
                     0 <= a < 2 ^ 64 /\ aclient L ar LB FF' (spq - 128) RESERVE_SCR a /\ L5.outside [(o, 32)] a).
        { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR FR F8 OR; unfold SB in *; lia). split. exact Ha. split.
          - destruct Ra as [Ra|[Ra|[Ra|Ra]]].
            + apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
            + apply (fframe_client L ar LB FF' _ _ F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ra; lia.
            + apply (fframe_shadow_client L ar LB FF' _ _ F 1 (spq - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S.
              rewrite (proj1 FQ15) || idtac. clear - Ra F8. unfold SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
            + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
              apply (aclient_narrow L ar LB FF' 0 0). apply aclient_cons. replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). eapply aclient_00. apply OCLSH. clear - Ra; lia.
              clear - Ra OR SLO SPT; unfold SB, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in *; lia.
          - intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd]. clear - Ra OR OBIG SLO SPT OF OFSH FBIG F8 FR; unfold SB in *; lia. }
        split. exact ASTK4.
        split. { intros a Ra. destruct (CL a Ra) as (Ha & Ca & Oa). rewrite (mrestrict_visible (ahid A4 model4) M4).
          2:{ destruct Ra as [Ra|[Ra|[Ra|Ra]]].
              replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS4 (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
              replace a with (F + (a - F)) by (clear; lia). apply (VFS4 F 128 FS1 FS2). clear - Ra; lia.
              replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH4 (F / 8 + SB) 16). 2: clear - Ra; lia.
              intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
              Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
              replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH4 (a - (o / 8 + SB))). clear - Ra; lia. }
          rewrite (proj1 PRES4 a). 2:{ split. exact Ha. split. exact Ca. apply HW4. exact Oa. }
          apply EQ3. destruct Ra as [Ra|[Ra|[Ra|Ra]]].
          replace a with ((spq - 128) + (a - (spq - 128))) by (clear; lia). apply (VIS2 (spq - 128) 144). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          replace a with (F + (a - F)) by (clear; lia). apply (VF (a - F)). clear - Ra; lia.
          replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VSH (a - (F / 8 + SB))). clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia. }
        split. { intros i Hi. destruct (CL (F / 8 + SB + i) ltac:(clear - Hi; lia)) as (Ha & Ca & Oa). apply (proj2 (proj2 PRES4)). exact Ha. exact Ca.
          rewrite (EQ3 (Z_to_bv 64 (F / 8 + SB + i))). 2:{ apply (VSH i). exact Hi. } apply MG3. eapply (L5KA.zeros_at_defined MV2 _ 16 FSHZ). exact Hi. }
        assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF (spq + 16) (RESIZE_SCR + 16) a).
        { intros a Ha'. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) (RESIZE_SCR + 16) F 128 a HH SPT).
          clear - FR; lia. exact FCEIL. exact FAPP. exact (proj2 FQ15). clear; lia. reflexivity.
          eapply fframes_apart_incl. exact FAPART. intros g Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha'. }
        split.
        - eapply ek_trans. { apply (ek_piece L ar LB FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] M M1 _ FRM1). intros a Ha Hc _ X.
            destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) (RESIZE_SCR + 16) a HH SPT Hc) as [Y|Y].
            unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia. }
          eapply ek_trans. { apply (ek_rt L ar LB FF [] (spq + 16) (RESIZE_SCR + 16) (spq - 128) 512 [(o, 32)] M1 M2 PRES2). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
          eapply ek_trans. { apply (ek_piece L ar LB FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] M2 M3 _ FRM3). intros a Ha Hc _ [X|[X|X]].
            + destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) (RESIZE_SCR + 16) a HH SPT Hc) as [Y|Y].
              unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia.
            + apply (NCF a). left. clear - X; lia. exact Hc.
            + apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc. }
          apply (ek_callee L ar LB [] FF [(F, 1, spq - 128 + 32)] (spq + 16) (RESIZE_SCR + 16) (spq - 128) RESERVE_SCR [(o, 32)] W4 M3 M4 PRES4).
          unfold RESIZE_SCR; clear; lia. clear; lia. intros a _ Ho. apply HW4. exact Ho.
        - eapply dk_trans. apply dk_grows. exact MGM1.
          eapply dk_trans. apply (dk_rt L ar LB FF [] (spq + 16) (RESIZE_SCR + 16) (spq - 128) 512 M1 M2 PRES2). unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
          eapply dk_trans. apply dk_grows. exact MGM3.
          apply (dk_callee L ar LB [] FF [(F, 1, spq - 128 + 32)] (spq + 16) (RESIZE_SCR + 16) (spq - 128) RESERVE_SCR W4 M3 M4 PRES4). unfold RESIZE_SCR; clear; lia. clear; lia. }
      assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
      assert (R4_2 : getr R4 (reg 2) = Z_to_bv 64 (spq - 128)). { rk. }
      assert (R4_8 : getr R4 (reg 8) = Z_to_bv 64 (spq + 16)). { rk. }
      assert (R4_9 : getr R4 (reg 9) = Z_to_bv 64 (spq - 128)). { rk. }
      assert (R4_18 : getr R4 (reg 18) = Z_to_bv 64 F). { rk. }
      assert (R4_19 : getr R4 (reg 19) = Z_to_bv 64 (Z.of_nat n)). { rk. }
      assert (R4_20 : getr R4 (reg 20) = Z_to_bv 64 o). { rk. }
      assert (R4_21 : getr R4 (reg 21) = Z_to_bv 64 (o + 8)). { rk. }
      assert (R4_22 : getr R4 (reg 22) = Z_to_bv 64 (F / 8 + SB)). { rk. }
      assert (R4_23 : getr R4 (reg 23) = Z_to_bv 64 F). { rk. }
      assert (R4_24 : getr R4 (reg 24) = Z_to_bv 64 SB). { rk. }
      assert (R4_25 : getr R4 (reg 25) = Z_to_bv 64 (Z.of_nat len)). { rk. }
      assert (R4_26 : getr R4 (reg 26) = Z_to_bv 64 ((o + 8) / 8 + SB)). { rk. }
      assert (R4_3 : getr R4 (reg 3) = getr R (reg 3)). { rewrite (cs_of_preserved R3 R4 3 RP4) by inl. rk. }
      assert (R4_4 : getr R4 (reg 4) = Z_to_bv 64 (hl_tp L)). { rk. }
      assert (R4_27 : getr R4 (reg 27) = getr R (reg 27)). { rewrite (cs_of_preserved R3 R4 27 RP4) by inl. rewrite (BKS 27%nat) by inl. apply RS2. inl. }
      destruct gr as [|q' cap'].
      * (* [comment removed for export] *)
        destruct POST as (DN & -> & -> & OB4 & PRES4).
        destruct (COMMON [] PRES4 ltac:(intros a _ rr [])) as (ASTK4 & AG34 & FSHD4 & E04 & D04). clear COMMON.
        set (H4 := ahid A4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
        pose proof OB4 as (O0' & _ & O8' & OST').
        assert (XC4 : forall a v, spq - 128 <= a <= spq + 8 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV4 a v).
        { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia. intros j Hj. apply AG34. clear - Ha Hj; lia. }
        assert (FLC4 : L5.u64_at RSEGS MV4 (F + 120) fl).   (* [comment removed for export] *)
        { pose proof (proj2 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model4 F 1 _ _ fl HH2 HH4 (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) FLC)) as X.
          change (ff_bytes 1) with 128 in X. replace (F + 128 - 8) with (F + 120) in X by (clear; lia). exact X. }
        assert (C1624 : exists c16 c24, L5.u64_at RSEGS M4 (o + 16) c16 /\ L5.u64_at RSEGS M4 (o + 24) c24).
        { destruct sto as [v0 v1|cap q]; cbn [L5.bo_fb L5.bo_len L5.bo_st] in OST'. destruct OST' as (_ & X16 & X24 & _). exists v0, v1. split; assumption.
          destruct OST' as (_ & X16 & X24 & _). exists cap, q. split; assumption. }
        destruct C1624 as (c16 & c24 & O16' & O24').
        assert (SZ4 : shadow_zero M4 o 4).
        { intros j Hj. unfold byte_at, S. rewrite E04. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj.
          split. clear - Hj OR; unfold SB; lia. split. apply OCLSH. exact Hj. intros rr [<-|[]]; unfold L5.in_rng; cbn [fst snd]. clear - Hj OR OBIG; unfold SB in *; lia. }
        cbn [L5.bo_fb L5.bo_len] in O0', O8'.
        assert (RT: forall MODE : (n <= len)%nat \/ (Z.testbit fb 0 = false /\ (len < n)%nat /\ (n <= 2)%nat),
          (forall (fx7 : FPState) R7 M7 model7 LK7, regs_preserved R R7 ->
            L5.u8_at RSEGS M7 o fb -> L5.u64_at RSEGS M7 (o + 8) (Z.of_nat n) ->
            (forall a v, o + 16 <= a -> a + 8 <= o + 32 -> ((n <= len)%nat \/ a + 8 <= o + 16 + 8 * Z.of_nat len) -> L5.u64_at RSEGS M4 a v -> L5.u64_at RSEGS M7 a v) ->
            (forall i, (len < n)%nat -> Z.of_nat len <= i < 2 -> L5.u64_at RSEGS M7 (o + 16 + 8 * i) 0) ->
            ek L ar LB FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] M4 M7 -> dk L ar LB FF (spq + 16) (RESIZE_SCR + 16) M4 M7 -> L5.defined M7 ((spq + 16) - (RESIZE_SCR + 16)) (RESIZE_SCR + 16) ->
            model_rt model4 model7 -> amodel_ok A4 model7 -> incl LK7 LK4 -> ri_inv HI LB FF LK7 cr A4 M7 (vml_of model7) ->
            srealizes RSEGS SCFG (cfg (fx:=fx7) R7 r M7 model7) K) ->
          srealizes RSEGS SCFG (cfg (fx:=fx4) R4 0x8fdd4 M4 model4) K).
        { intros MODE KT. apply (ret_tail fx4 R4 M4 model4 K LB FF LK4 cr A4 o spq r n len fb c24 c16 F fl R HH4 AM4 HK G1 RA G2 A32 G4 ASTK4 Hn
                       R4_2 R4_8 R4_9 R4_18 R4_19 R4_20 R4_21 R4_22 R4_23 R4_24 R4_25 R4_26 R4_3 R4_4 R4_27).
          all: try (apply XC4; [clear; lia | first [exact BQ_V2nat_1 | exact BQ_V2nat_2 | exact BQ_V2nat_3 | exact BQ_V2nat_4 | exact BQ_V2nat_5 | exact BQ_V2nat_6
                                                  | exact BQ_V2nat_7 | exact BQ_V2nat_8 | exact BQ_V2nat_9 | exact BQ_V2nat_10 | exact BQ_V2nat_11 | exact BQ_V2nat_12 | exact BQ_V2nat_13]]).
          + clear - FR; lia. + exact F8. + exact FS1. + exact FS2. + exact FBIG. + exact FSHD4. + exact FLC4. + exact FLP. + exact FLNC. + exact FFL. + exact FLBIG.
          + exact OF. + exact OFL. + exact OSHF. + exact AOB. + exact O0'. + exact Hfb. + exact O16'. + exact O24'. + exact SZ4.
          + clear - LEN; lia. + exact MODE. + exact KT. }
        destruct (Nat.le_gt_cases n len) as [GE|LT].
        -- (* [comment removed for export] *)
           apply RT. left; exact GE.
           intros fx7 R7 M7 model7 LK7 RP7 O0f O8f KEEP ZERO E47 D47 DEF7 RT7 AM7 LKI7 HH7.
           apply (KONT fx7 R7 M7 model7 Same LB cr LK7 A4).
           ** split. exact RP7. cbn [resize_post L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_data]. split. { destruct DN as [X|X]; [left; exact X | right; clear - X; lia]. } split. reflexivity. split. reflexivity.
              destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
              split. { exists sto. split.
                { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact O0f. split. exact Hfb. split. exact O8f.
                  destruct sto as [v0 v1|cap q]; cbn [L5.bo_fb L5.bo_len L5.bo_st] in OST'.
                  - destruct OST' as (B0 & X16 & X24 & Hl2 & Rv0 & Rv1). split. exact B0. split. apply KEEP. clear; lia. clear; lia. left; exact GE. exact X16.
                    split. apply KEEP. clear; lia. clear; lia. left; exact GE. exact X24. split. clear - GE Hl2; lia. split. exact Rv0. exact Rv1.
                  - destruct OST' as (B0 & X16 & X24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH). split. exact B0. split. apply KEEP. clear; lia. clear; lia. left; exact GE. exact X16.
                    split. apply KEEP. clear; lia. clear; lia. left; exact GE. exact X24. split. clear - GE Hlc; lia. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH. }
                split. 2:{ destruct sto; [exact I | split; reflexivity]. }
                split. rewrite resize_limbs_length. reflexivity. split. apply resize_limbs_range. exact Rws.
                cbn [L5.bo_st L5.bo_len]. rewrite resize_limbs_short by (rewrite Lws; exact GE).
                destruct sto as [v0 v1|cap q]; cbn [L5.bo_fb L5.bo_len L5.bo_st] in OST' |- *.
                - rewrite LAT. apply L5C.firstn_firstn_le. exact GE.
                - destruct OST' as (B0 & X16 & X24 & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
                  intros i Hi. rewrite length_firstn in Hi. rewrite nth_firstn. assert (Ei : (i <? n)%nat = true) by (apply Nat.ltb_lt; clear - Hi; lia). rewrite Ei.
                  assert (Hi1 : (i < length ws)%nat) by (clear - Hi; lia).
                  eapply L5C.u64_at_agree. 4: exact (LAT i Hi1). 2: clear - Q4096; lia. 2: rewrite Lws in Hi1; clear - Hi1 Q47 Hlc; lia.
                  intros j Hj.
                  assert (KP : akept L ar LB FF (spq + 16) (RESIZE_SCR + 16) [(o, 32)] j).
                  { split. rewrite Lws in Hi1; clear - Hj Hi1 Q4096 Q47 Hlc; lia. split. apply (block_client L ar LB FF _ _ q (8 * cap)). apply INB; reflexivity.
                    rewrite Lws in Hi1; clear - Hj Hi1 Hlc; lia. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd].
                    destruct AOB as (g & Hg & X1 & X2 & _).
                    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) _ (INB cap q eq_refl))))))) g ltac:(apply in_or_app; left; exact Hg)) as Y.
                    cbn [fst snd] in Y. rewrite Lws in Hi1; clear - Hj Hi1 Hlc Y X1 X2; lia. }
                  rewrite (E47 j KP). apply E04. exact KP. }
              apply ahpres_of. 2: exact DEF7. 2: eapply dk_trans; [exact D04 | exact D47].
              eapply ek_trans. { eapply ek_W. exact E04. intros a Ho rr [<-|[]]. apply Ho. left; reflexivity. }
              eapply ek_W. exact E47. intros a Ho rr [<-|[]]. apply Ho. left; reflexivity.
           ** eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4. exact RT7.
           ** exact IA4.
           ** exact AM7.
           ** eapply incl_tran. exact LKI7. eapply incl_tran. exact LKI4. exact LKI2.
           ** exact HH7.
        -- destruct sto as [v0 v1|cap q].
           ++ (* [comment removed for export] *)
              cbn [L5.bo_fb L5.bo_len L5.bo_st] in OST'. destruct OST' as (B0 & X16 & X24 & Hl2 & Rv0 & Rv1).
              assert (N2 : (n <= 2)%nat). { destruct DN as [DN|DN]. unfold L5.bo_dyn in DN; cbn [L5.bo_fb] in DN. rewrite B0 in DN. discriminate. clear - DN; lia. }
              apply RT. right. split. exact B0. split. exact LT. exact N2.
              intros fx7 R7 M7 model7 LK7 RP7 O0f O8f KEEP ZERO E47 D47 DEF7 RT7 AM7 LKI7 HH7.
              apply (KONT fx7 R7 M7 model7 Same LB cr LK7 A4).
              ** split. exact RP7. cbn [resize_post L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_data]. split. { destruct DN as [X|X]; [left; exact X | right; clear - X; lia]. } split. reflexivity. split. reflexivity.
                 destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
                 split. { exists (L5.BInl (if Nat.eqb len 0 then 0 else v0) 0).
                   assert (V16 : L5.u64_at RSEGS M7 (o + 16) (if Nat.eqb len 0 then 0 else v0)).
                   { destruct len as [|len']. replace (o + 16) with (o + 16 + 8 * 0) by (clear; lia). apply ZERO. exact LT. clear; lia.
                     cbn [Nat.eqb]. apply KEEP. clear; lia. clear; lia. right; clear; lia. exact X16. }
                   assert (V24 : L5.u64_at RSEGS M7 (o + 24) 0). { replace (o + 24) with (o + 16 + 8 * 1) by (clear; lia). apply ZERO. exact LT. clear - LT N2; lia. }
                   split. { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact O0f. split. exact Hfb. split. exact O8f. split. exact B0. split. exact V16. split. exact V24.
                            split. exact N2. split. destruct (Nat.eqb len 0); [clear; lia | exact Rv0]. clear; lia. }
                   split. 2: exact I.
                   split. rewrite resize_limbs_length. reflexivity. split. apply resize_limbs_range. exact Rws.
                   cbn [L5.bo_st L5.bo_len]. rewrite LAT. clear - LT N2.
                   destruct len as [|[|len']]; destruct n as [|[|[|n']]]; cbn; try reflexivity; exfalso; lia. }
                 apply ahpres_of. 2: exact DEF7. 2: eapply dk_trans; [exact D04 | exact D47].
                 eapply ek_trans. { eapply ek_W. exact E04. intros a Ho rr [<-|[]]. apply Ho. left; reflexivity. }
                 eapply ek_W. exact E47. intros a Ho rr [<-|[]]. apply Ho. left; reflexivity.
              ** eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4. exact RT7.
              ** exact IA4.
              ** exact AM7.
              ** eapply incl_tran. exact LKI7. eapply incl_tran. exact LKI4. exact LKI2.
              ** exact HH7.
           ++ (* [comment removed for export] *)
              clear O16' O24'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OST'. destruct OST' as (B0 & O16' & O24' & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
              apply (dyn_tail fx4 R4 M4 model4 K LB FF LK4 cr A4 o spq r n len fb q cap F fl R HH4 AM4 HK G1 RA G2 A32 G4 ASTK4 Hn
                       R4_2 R4_8 R4_9 R4_18 R4_19 R4_20 R4_21 R4_22 R4_23 R4_24 R4_25 R4_26 R4_3 R4_4 R4_27).
              all: try (apply XC4; [clear; lia | first [exact BQ_V2nat_1 | exact BQ_V2nat_2 | exact BQ_V2nat_3 | exact BQ_V2nat_4 | exact BQ_V2nat_5 | exact BQ_V2nat_6
                                                      | exact BQ_V2nat_7 | exact BQ_V2nat_8 | exact BQ_V2nat_9 | exact BQ_V2nat_10 | exact BQ_V2nat_11 | exact BQ_V2nat_12 | exact BQ_V2nat_13]]).
              ** clear - FR; lia. ** exact F8. ** exact FS1. ** exact FS2. ** exact FBIG. ** exact FSHD4. ** exact FLC4. ** exact FLP. ** exact FLNC. ** exact FFL. ** exact FLBIG.
              ** exact OF. ** exact OFL. ** exact OSHF. ** exact AOB. ** exact O0'. ** exact B0. ** exact Hfb. ** exact O16'. ** exact O24'.
              ** intros j Hj. unfold byte_at, S. rewrite E04. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj.
                 split. clear - Hj OR; unfold SB; lia. split. apply OCLSH. exact Hj. intros rr [<-|[]]; unfold L5.in_rng; cbn [fst snd]. clear - Hj OR OBIG; unfold SB in *; lia.
              ** apply INB. reflexivity.
              ** exact LT.
              ** apply CAP. exact B0.
              ** clear - Hcap; lia.
              ** (* [comment removed for export] *)
                 intros fx7 R7 M7 model7 LK7 RP7 O0f O8f O16f O24f OLD NEW E47 D47 DEF7 RT7 AM7 LKI7 HH7.
                 apply (KONT fx7 R7 M7 model7 Same LB cr LK7 A4).
                 --- split. exact RP7. cbn [resize_post L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_data]. split. { left. exact B0. } split. reflexivity. split. reflexivity.
                     split. { exists (L5.BDyn cap q). split.
                       { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact O0f. split. exact Hfb. split. exact O8f. split. exact B0. split. exact O16f. split. exact O24f.
                         split. apply CAP. exact B0. split. exact Hcap. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH. }
                       split. 2: split; reflexivity.
                       destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT. split. rewrite resize_limbs_length. reflexivity. split. apply resize_limbs_range. exact Rws.
                       cbn [L5.bo_st L5.bo_len]. rewrite resize_limbs_long by (rewrite Lws; clear - LT; lia). intros i Hi. rewrite length_app, repeat_length in Hi.
                       destruct (Nat.lt_ge_cases i (length ws)) as [Hi1|Hi1].
                       - rewrite app_nth1 by exact Hi1. apply OLD. clear - Q4096; lia. rewrite Lws in Hi1; clear - Hi1; lia.
                         eapply L5C.u64_at_agree. 4: exact (LAT i Hi1). 2: clear - Q4096; lia. 2: rewrite Lws in Hi1; clear - Hi1 Q47 Hlc; lia.
                         intros j Hj. apply E04. split. rewrite Lws in Hi1; clear - Hj Hi1 Q4096 Q47 Hlc; lia. split. apply (block_client L ar LB FF _ _ q (8 * cap)). apply INB; reflexivity.
                         rewrite Lws in Hi1; clear - Hj Hi1 Hlc; lia. intros rr [<-|[]]. unfold L5.in_rng; cbn [fst snd].
                         destruct AOB as (g & Hg & X1 & X2 & _).
                         pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) _ (INB cap q eq_refl))))))) g ltac:(apply in_or_app; left; exact Hg)) as Y.
                         cbn [fst snd] in Y. rewrite Lws in Hi1; clear - Hj Hi1 Hlc Y X1 X2; lia.
                       - rewrite app_nth2 by exact Hi1. rewrite nth_repeat. apply NEW. rewrite Lws in Hi1. rewrite Lws in Hi. clear - Hi Hi1; lia. }
                     apply ahpres_of. 2: exact DEF7. 2: eapply dk_trans; [exact D04 | exact D47].
                     eapply ek_trans. { eapply ek_W. exact E04. intros a Ho rr [<-|[]]. apply Ho. left; reflexivity. }
                     eapply ek_W. exact E47. intros a Ho rr [<-|[<-|[]]]. apply Ho. left; reflexivity.
                     replace (8 * (Z.of_nat n - Z.of_nat len)) with (8 * Z.max 0 (Z.of_nat n - Z.of_nat len)) by (clear - LT; lia). apply Ho. right; left; reflexivity.
                 --- eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4. exact RT7.
                 --- exact IA4.
                 --- exact AM7.
                 --- eapply incl_tran. exact LKI7. eapply incl_tran. exact LKI4. exact LKI2.
                 --- exact HH7.
      * (* [comment removed for export] *)
        destruct POST as (B0 & N3 & ECAP & -> & -> & FRESH & (v0 & v1 & Esto & Qv0 & Qv1) & OB4 & PRES4).
        pose proof FRESH as (BRq & BAq & FAq & DEFq & SHBq).
        destruct (COMMON [(o, 32)] PRES4 ltac:(intros a X; exact X)) as (ASTK4 & AG34 & FSHD4 & E04 & D04). clear COMMON.
        set (LB4 := (q', 8 * cap') :: LB) in *.
        set (H4 := ahid A4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
        pose proof OB4 as (O0' & Hfb1 & O8' & OST'). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0', O8', OST'.
        destruct OST' as (B1 & O16' & O24' & Hlc & Hcap & Q8 & Q4096 & Q47 & QH).
        assert (XC4 : forall a v, spq - 128 <= a <= spq + 8 -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV4 a v).
        { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia. intros j Hj. apply AG34. clear - Ha Hj; lia. }
        assert (FLC4 : L5.u64_at RSEGS MV4 (F + 120) fl).   (* [comment removed for export] *)
        { pose proof (proj2 (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model4 F 1 _ _ fl HH2 HH4 (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) FLC)) as X.
          change (ff_bytes 1) with 128 in X. replace (F + 128 - 8) with (F + 120) in X by (clear; lia). exact X. }
        pose proof BRq as (P0 & P1 & P2 & P3 & P4 & P5). rewrite (aly_img_lo L C LY), (aly_img_hi L C LY) in P1. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in P5.
        assert (RUN : Z.of_nat n < round_up (Z.of_nat n) <= Z.of_nat n + 8 /\ 8 <= round_up (Z.of_nat n) <= 8388616).
        { unfold round_up. clear - Hn. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        subst cap'. cbn [L5.bo_st] in Esto. subst sto.
        (* [comment removed for export] *)
        assert (FLNC4 : ~ aclient L ar LB4 FF' 0 0 fl).
        { intros X. destruct (aclient_consb_inv L ar LB FF' _ 0 0 fl X) as [Y|[Y|Y]]. exact (FLNC Y).
          - cbn [fst snd] in Y. pose proof (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) _ (or_introl eq_refl)) as Z6. cbn [fst snd] in Z6.
            destruct Z6 as (_ & _ & _ & _ & _ & _ & Z7). clear - Y FLP Z7. unfold FS_BYTES in *. lia.
          - cbn [fst snd] in Y. unfold in_shadow_of, S in Y.
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
            assert (QSH : SB <= q' / 8 + SB /\ (q' + 8 * round_up (Z.of_nat n) - 1) / 8 + SB < 0x10007fff8000) by (clear - P0 P5 RUN; unfold SB; lia).
            Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
            clear - Y FLBIG QSH. unfold SB in *. lia. }
        destruct OL as (Lws & Rws & LAT). cbn [L5.bo_len L5.bo_st] in Lws, LAT.
        pose proof (proj1 (proj2 (proj2 (proj2 OST)))) as Hl2.
        apply (dyn_tail fx4 R4 M4 model4 K LB4 FF LK4 (adebit L cr (8 * round_up (Z.of_nat n))) A4 o spq r n len (Z.lor fb 1) q' (round_up (Z.of_nat n)) F fl R HH4 AM4 HK G1 RA G2 A32 G4 ASTK4 Hn
                 R4_2 R4_8 R4_9 R4_18 R4_19 R4_20 R4_21 R4_22 R4_23 R4_24 R4_25 R4_26 R4_3 R4_4 R4_27).
        all: try (apply XC4; [clear; lia | first [exact BQ_V2nat_1 | exact BQ_V2nat_2 | exact BQ_V2nat_3 | exact BQ_V2nat_4 | exact BQ_V2nat_5 | exact BQ_V2nat_6
                                                | exact BQ_V2nat_7 | exact BQ_V2nat_8 | exact BQ_V2nat_9 | exact BQ_V2nat_10 | exact BQ_V2nat_11 | exact BQ_V2nat_12 | exact BQ_V2nat_13]]).
        -- clear - FR; lia. -- exact F8. -- exact FS1. -- exact FS2. -- exact FBIG. -- exact FSHD4. -- exact FLC4. -- exact FLP. -- exact FLNC4. -- exact FFL. -- exact FLBIG.
        -- exact OF. -- exact OFL. -- exact OSHF. -- exact AOB. -- exact O0'. -- exact B1. -- exact Hfb1. -- exact O16'. -- exact O24'.
        -- intros j Hj. unfold byte_at, S. rewrite E04. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj.
           split. clear - Hj OR; unfold SB; lia. split. apply OCLSH. exact Hj. intros rr [<-|[]]; unfold L5.in_rng; cbn [fst snd]. clear - Hj OR OBIG; unfold SB in *; lia.
        -- left; reflexivity.
        -- clear - N3 Hl2 RUN; lia.
        -- clear - N3 Hl2 RUN; lia.
        -- clear - N3 Hl2 RUN; lia.
        -- (* [comment removed for export] *)
           intros fx7 R7 M7 model7 LK7 RP7 O0f O8f O16f O24f OLD NEW E47 D47 DEF7 RT7 AM7 LKI7 HH7.
           apply (KONT fx7 R7 M7 model7 (Grown q' (round_up (Z.of_nat n))) LB4 (adebit L cr (8 * round_up (Z.of_nat n))) LK7 A4).
           ++ split. exact RP7. cbn [resize_post L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_data].
              split. exact B0. split. clear - N3; lia. split. reflexivity. split. reflexivity. split. reflexivity.
              split. { (* [comment removed for export] *)
                split. exact BRq. split. exact BAq. split. { eapply fframes_apart_incl. exact FAq. intros g Hg. apply in_app_or in Hg. apply in_or_app. destruct Hg as [Hg|Hg]. left; right; exact Hg. right; apply LKI7; exact Hg. }
                split. { intros i Hi. apply D47. clear - Hi P0 P5; lia. apply (block_client L ar LB4 FF _ _ q' (8 * round_up (Z.of_nat n))). left; reflexivity. clear - Hi; lia. apply DEFq. exact Hi. }
                destruct SHBq as [SZq SPq]. split. 2:{ intros X. exfalso. apply X. clear. rewrite Z.mul_comm. apply Z_mod_mult. }
                replace (8 * round_up (Z.of_nat n) / 8) with (round_up (Z.of_nat n)) in SZq |- * by (clear; rewrite Z.mul_comm, Z_div_mult; [reflexivity | lia]).
                Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
                assert (QSH : SB <= q' / 8 + SB /\ (q' + 8 * round_up (Z.of_nat n) - 1) / 8 = q' / 8 + round_up (Z.of_nat n) - 1 /\ q' / 8 * 8 = q') by (clear - P0 P2 P5 RUN; unfold SB; lia).
                Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
                intros j Hj. unfold byte_at. rewrite E47. apply SZq. exact Hj.
                split. unfold S; clear - Hj QSH P0 P5; unfold SB in *; lia. split.
                { right; right; right; right; right; right. exists (q', 8 * round_up (Z.of_nat n)). split. left; reflexivity. cbn [fst snd]. unfold in_shadow_of, S. destruct QSH as (X1 & X2 & X3). rewrite X2. clear - Hj X3; lia. }
                intros rr [<-|[<-|[]]]; unfold L5.in_rng, S; cbn [fst snd]. clear - Hj QSH OR OBIG P0 P5 RUN; unfold SB in *; lia. clear - Hj QSH P0 P5 RUN LEN; unfold SB in *; lia. }
              split. { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact O0f. split. exact Hfb1. split. exact O8f. split. exact B1. split. exact O16f. split. exact O24f.
                       split. clear - RUN; lia. split. clear - RUN Hn; lia. split. exact Q8. split. exact Q4096. split. exact Q47. exact QH. }
              split. { split. rewrite resize_limbs_length. reflexivity. split. apply resize_limbs_range. exact Rws.
                cbn [L5.bo_st L5.bo_len]. rewrite resize_limbs_long by (rewrite Lws; clear - N3 Hl2; lia). intros i Hi. rewrite length_app, repeat_length in Hi.
                destruct (Nat.lt_ge_cases i (length ws)) as [Hi1|Hi1].
                - rewrite app_nth1 by exact Hi1. apply OLD. clear - P0; lia. rewrite Lws in Hi1; clear - Hi1; lia.
                  rewrite LAT. rewrite Lws in Hi1. assert (X : i = 0%nat \/ i = 1%nat) by (clear - Hi1 Hl2; lia).
                  destruct X as [-> | ->]. { destruct len as [|len']. exfalso; clear - Hi1; lia. cbn [firstn nth]. replace (q' + 8 * Z.of_nat 0) with q' by (clear; lia). exact Qv0. }
                  destruct len as [|[|len']]. exfalso; clear - Hi1; lia. exfalso; clear - Hi1; lia. cbn [firstn nth]. replace (q' + 8 * Z.of_nat 1) with (q' + 8) by (clear; lia). exact Qv1.
                - rewrite app_nth2 by exact Hi1. rewrite nth_repeat. apply NEW. rewrite Lws in Hi1. rewrite Lws in Hi. clear - Hi Hi1; lia. }
              apply ahpres_of. 2: exact DEF7. 2:{ eapply dk_trans. exact D04. apply (dk_tl L ar LB (q', 8 * round_up (Z.of_nat n))). exact D47. }
              eapply ek_trans. exact E04.
              intros a (Ha & Hc & Ho). apply E47. split. exact Ha. split. apply aclient_consb. exact Hc.
              intros rr [<-|[<-|[]]]. apply Ho. left; reflexivity.
              unfold L5.in_rng; cbn [fst snd]. intros X.
              refine (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ (spq + 16) (RESIZE_SCR + 16) q' (8 * round_up (Z.of_nat n)) a HH SPT BRq BAq _ _ Hc).
              eapply fframes_apart_incl. exact FAq. intros g Hg; apply in_or_app; left; right; exact Hg. clear - X RUN LEN N3 Hl2; lia.
           ++ eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3. eapply L5LZ.model_rt_trans. exact RT4. exact RT7.
           ++ exact IA4.
           ++ exact AM7.
           ++ eapply incl_tran. exact LKI7. eapply incl_tran. exact LKI4. exact LKI2.
           ++ exact HH7.
Qed.

End WithIface.
End SCFG_1.
End L5ARZ16.
