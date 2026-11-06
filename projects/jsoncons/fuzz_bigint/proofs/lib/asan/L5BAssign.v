(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun Bo0_code_8f368_90368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BAssignP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AASG.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AASGP.
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

(* [comment removed for export] *)
Lemma asg_tail fx2 R2 M2 model2 K LB2 FF LK2 cr2 A2 (o o' sp r : Z) (leny : nat) (fb' fbR : Z) (stR : L5.bstore) (src : Z) (ws' : list Z) (R : bvmap 5 word) :
  let H2 := ahid A2 model2 in let MV2 := mrestrict H2 M2 in let dst := L5.bo_data o (L5.BO fbR leny stR) in let n8 := 8 * Z.of_nat leny in
  ri_inv HI LB2 FF LK2 cr2 A2 M2 (vml_of model2) -> amodel_ok A2 model2 -> K [] ->
  getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r -> getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> astk ar M2 sp ASSIGN_SCR ->
  getr R2 (reg 2) = Z_to_bv 64 (sp - 64) -> getr R2 (reg 8) = Z_to_bv 64 o -> getr R2 (reg 9) = Z_to_bv 64 o' -> getr R2 (reg 18) = Z_to_bv 64 src ->
  getr R2 (reg 19) = Z_to_bv 64 (Z.of_nat leny) -> getr R2 (reg 20) = Z_to_bv 64 (o' / 8 + SB) -> getr R2 (reg 21) = Z_to_bv 64 SB ->
  getr R2 (reg 3) = getr R (reg 3) -> getr R2 (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr R2 (reg 22) = getr R (reg 22) -> getr R2 (reg 23) = getr R (reg 23) -> getr R2 (reg 24) = getr R (reg 24) -> getr R2 (reg 25) = getr R (reg 25) ->
  getr R2 (reg 26) = getr R (reg 26) -> getr R2 (reg 27) = getr R (reg 27) ->
  L5.u64_at RSEGS MV2 (sp - 8) (U R 1) -> L5.u64_at RSEGS MV2 (sp - 16) (U R 8) -> L5.u64_at RSEGS MV2 (sp - 24) (U R 9) -> L5.u64_at RSEGS MV2 (sp - 32) (U R 18) ->
  L5.u64_at RSEGS MV2 (sp - 40) (U R 19) -> L5.u64_at RSEGS MV2 (sp - 48) (U R 20) -> L5.u64_at RSEGS MV2 (sp - 56) (U R 21) ->
  aobj FF o 32 -> aobj FF o' 32 -> (o + 32 <= o' \/ o' + 32 <= o) ->
  L5.big_at RSEGS M2 o (L5.BO fbR leny stR) -> shadow_zero M2 o 4 -> L5.u8_at RSEGS M2 o' fb' -> 0 <= fb' < 256 -> L5.u64_at RSEGS M2 (o' + 8) (Z.of_nat leny) -> shadow_zero M2 o' 4 ->
  Z.of_nat leny <= 2 ^ 23 -> (forall c q, stR = L5.BDyn c q -> In (q, 8 * c) LB2) ->
  L5.limbs_at RSEGS M2 src ws' -> length ws' = leny -> aacc M2 src n8 -> 4096 <= src /\ src + n8 <= 2 ^ 47 -> app_rng ar src n8 ->
  (forall i, 0 <= i < n8 -> aclient L ar LB2 FF (sp - 64) 2560 (src + i)) ->        (* [comment removed for export] *)
  ((0 < leny)%nat -> dst + n8 <= src \/ src + n8 <= dst) ->
  (forall i, 0 <= i < n8 -> ~ (o <= src + i < o + 1)) ->
  src mod 8 = 0 ->                                      (* [comment removed for export] *)
  (forall (fx7 : FPState) R7 M7 model7 LK7, regs_preserved R R7 -> getr R7 (reg 10) = Z_to_bv 64 o ->
      L5.u8_at RSEGS M7 o (if Nat.eqb leny 0 then fbR else Z.lor (Z.land fbR 253) (Z.land fb' 2)) -> L5.u64_at RSEGS M7 (o + 8) (Z.of_nat leny) ->
      (forall a v, o + 16 <= a -> a + 8 <= o + 32 -> (a + 8 <= dst \/ dst + n8 <= a) -> L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS M7 a v) ->
      L5.limbs_at RSEGS M7 dst ws' ->
      ek L ar LB2 FF sp ASSIGN_SCR [(o, 32); (dst, n8)] M2 M7 -> dk L ar LB2 FF sp ASSIGN_SCR M2 M7 -> L5.defined M7 (sp - ASSIGN_SCR) ASSIGN_SCR ->
      model_rt model2 model7 -> amodel_ok A2 model7 -> incl LK7 LK2 -> ri_inv HI LB2 FF LK7 cr2 A2 M7 (vml_of model7) ->
      srealizes RSEGS SCFG (cfg (fx:=fx7) R7 r M7 model7) K) ->
  srealizes RSEGS SCFG (cfg (fx:=fx2) R2 0x8fbac M2 model2) K.
Proof.
  intros H2 MV2 dst n8 HH2 AM2 HK G1 RA G2 G4 ASTK2 Q2 Q8 Q9 Q18 Q19 Q20 Q21 Q3 Q4 Q22 Q23 Q24 Q25 Q26 Q27
         C8 C16 C24 C32 C40 C48 C56 AOB AOB' APART OB2 SZ O0' Hfb' O8' SZ' Hn INB LAT Lws ACC SRC SAPP SCL NOV SRCO SAL KONT.
  assert (ALSRC : aligned src 8) by exact SAL.
  pose proof ASTK2 as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487232 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  pose proof (statics_vis LB2 FF LK2 cr2 A2 M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2). fold H2 MV2 in IMGC2, CSB2, CUAR2.
  pose proof (aobj_facts L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 o 32 sp ASSIGN_SCR HH2 AOB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF2 & OVIS2 & OVSH2 & OCL & OCLSH). change (32 / 8) with 4 in OVSH2, OCLSH. fold H2 in OVIS2, OVSH2.
  pose proof (aobj_facts L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 o' 32 sp ASSIGN_SCR HH2 AOB' ltac:(clear; lia) ltac:(reflexivity))
    as (YR & YBIG & YDEF2 & YVIS2 & YVSH2 & YCL & YCLSH). change (32 / 8) with 4 in YVSH2, YCLSH. fold H2 in YVIS2, YVSH2.
  pose proof OB2 as (O0 & HfbR & O8 & OST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in O0, HfbR, O8, OST.
  assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
  assert (W64 : L5.writable RSEGS MV2 (sp - 64) 64).
  { apply (proj2 (writable_vis H2 M2 (sp - 64) 64 (VIS2 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M2 sp). exact ASTK2. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR. clear; lia. clear; lia. clear; lia. }
  assert (XV : forall a n' v, avis H2 a n' -> 0 <= a -> a + 8 <= 2 ^ 64 -> 8 <= n' ->
            (L5.u64_at RSEGS M2 a v -> L5.u64_at RSEGS MV2 a v) /\ (L5.u8_at RSEGS M2 a v -> L5.u8_at RSEGS MV2 a v)).
  { intros a n' v Va Ha H8 Hm. split; intros Hc.
    apply (proj2 (u64_at_vis H2 M2 a v ltac:(eapply avis_sub; [exact Va | clear; lia | clear - Hm; lia]) Ha H8)). exact Hc.
    apply (proj2 (u8_at_vis H2 M2 a v ltac:(eapply avis_sub; [exact Va | clear; lia | clear - Hm; lia]) Ha ltac:(clear - H8; lia))). exact Hc. }
  assert (OB0v : L5.u8_at RSEGS MV2 o fbR). { apply (proj2 (XV o 32 fbR OVIS2 ltac:(clear - OR; lia) ltac:(clear - OR; lia) ltac:(clear; lia))). exact O0. }
  assert (YB0v : L5.u8_at RSEGS MV2 o' fb'). { apply (proj2 (XV o' 32 fb' YVIS2 ltac:(clear - YR; lia) ltac:(clear - YR; lia) ltac:(clear; lia))). exact O0'. }
  assert (Y8v : L5.u64_at RSEGS MV2 (o' + 8) (Z.of_nat leny)).
  { apply (proj1 (XV (o' + 8) 24 _ ltac:(eapply avis_sub; [exact YVIS2 | clear; lia | clear; lia]) ltac:(clear - YR; lia) ltac:(clear - YR; lia) ltac:(clear; lia))). exact O8'. }
  assert (OZv : L5KA.zeros_at MV2 (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H2 M2 _ 4 OVSH2)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (YZv : L5KA.zeros_at MV2 (o' / 8 + SB) 4). { apply (proj2 (zeros_at_vis H2 M2 _ 4 YVSH2)). intros i Hi. unfold shadow_zero, byte_at, S in SZ'. apply SZ'. exact Hi. }
  assert (OWv : L5.writable RSEGS MV2 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H2 M2 o 32 OVIS2)). exact ODEF2. clear - OR; lia. clear - OR; lia. }
  assert (SO : sp - 64 + 64 <= o \/ o + 32 <= sp - 64) by (clear - OR SLO; lia).
  assert (SY : sp - 64 + 64 <= o' \/ o' + 32 <= sp - 64) by (clear - YR SLO; lia).
  assert (RPF : forall R7 (KS : list nat), (forall x, In x KS -> getr R7 (reg x) = getr R2 (reg x)) -> incl [3; 4; 22; 23; 24; 25; 26; 27]%nat KS ->
            getr R7 (reg 2) = Z_to_bv 64 sp -> getr R7 (reg 8) = Z_to_bv 64 (U R 8) -> getr R7 (reg 9) = Z_to_bv 64 (U R 9) ->
            getr R7 (reg 18) = Z_to_bv 64 (U R 18) -> getr R7 (reg 19) = Z_to_bv 64 (U R 19) -> getr R7 (reg 20) = Z_to_bv 64 (U R 20) -> getr R7 (reg 21) = Z_to_bv 64 (U R 21) ->
            forall k, In k cs_all -> getr R7 (reg k) = getr R (reg k)).
  { intros R7 KS HKS HKI E2 E8 E9 E18 E19 E20 E21 k Hk. cbn in Hk.
    destruct Hk as [<-|Hk]. { rewrite E2. rewrite <- r2, G2. reflexivity. }
    destruct Hk as [<-|Hk]. { rewrite (HKS 3%nat (HKI 3%nat (or_introl eq_refl))). exact Q3. }
    destruct Hk as [<-|Hk]. { rewrite (HKS 4%nat (HKI 4%nat (or_intror (or_introl eq_refl)))). rewrite Q4, <- r4, G4. reflexivity. }
    repeat (destruct Hk as [<-|Hk]; [first [rewrite E8 | rewrite E9 | rewrite E18 | rewrite E19 | rewrite E20 | rewrite E21
      | (rewrite (HKS 22%nat (HKI 22%nat ltac:(cbn; repeat (first [left; reflexivity | right])))); exact Q22) | (rewrite (HKS 23%nat (HKI 23%nat ltac:(cbn; repeat (first [left; reflexivity | right])))); exact Q23)
      | (rewrite (HKS 24%nat (HKI 24%nat ltac:(cbn; repeat (first [left; reflexivity | right])))); exact Q24) | (rewrite (HKS 25%nat (HKI 25%nat ltac:(cbn; repeat (first [left; reflexivity | right])))); exact Q25)
      | (rewrite (HKS 26%nat (HKI 26%nat ltac:(cbn; repeat (first [left; reflexivity | right])))); exact Q26) | (rewrite (HKS 27%nat (HKI 27%nat ltac:(cbn; repeat (first [left; reflexivity | right])))); exact Q27)];
      try (symmetry; apply U_to) |]). destruct Hk. }
  set (VZ := fun j : nat => match j with 2%nat => sp | 33%nat => o | 34%nat => o' | 36%nat => fb' | 37%nat => Z.of_nat leny | 38%nat => src
              | 39%nat => match stR with L5.BDyn _ q => q | _ => 0 end | 40%nat => fbR
              | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R 21 | 48%nat => U R2 1 | _ => 0 end).
  destruct (Nat.eq_dec leny 0) as [L0|LNZ].
  - (* [comment removed for export] *)
    assert (RUN : exists fx7 R7 M7v, mem_grows MV2 M7v /\ (forall i, 0 <= i < 2 ^ 64 -> M7v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i))
              /\ msteps RSEGS (st fx2 R2 0x8fbac MV2) (st fx7 R7 r M7v) /\ (forall k, In k cs_all -> getr R7 (reg k) = getr R (reg k)) /\ getr R7 (reg 10) = Z_to_bv 64 o).
    { rewrite L0 in Q19. destruct stR as [v0 v1|c q].
      + destruct OST as (B0 & _). pose proof (asgZi_conc fx2 R2 MV2 VZ) as P. cbn beta iota delta [VZ] in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx7 & R7 & M7v & MG7 & ZiFR & ZiFZ & (ZiMS & ZiKS & ZiR1 & ZiR2 & ZiR8 & ZiR9 & ZiR10 & ZiR11 & ZiR12 & ZiR18 & ZiR19 & ZiR20 & ZiR21)).
        exists fx7, R7, M7v. split. exact MG7. split. exact ZiFZ.
        split. { eapply msteps_trans. exact ZiMS. apply (ret_to fx7 R7 M7v 0x8fc50 W_8fc50 r F_8fc50 eq_refl D_8fc50). rewrite ZiR1, UR1; reflexivity. exact (proj1 RA). exact (proj2 RA). }
        split. { apply (RPF R7 KS_asgZi ZiKS). refine (L5K.incl_b _ _ _); vm_compute; reflexivity. all: assumption. } exact ZiR10.
      + destruct OST as (B0 & O16 & O24 & Hlc & Hcap & QQ8 & Q4096 & Q47 & QH). pose proof (asgZd_conc fx2 R2 MV2 VZ) as P. cbn beta iota delta [VZ] in P.
        assert (O24v : L5.u64_at RSEGS MV2 (o + 24) q). { apply (proj1 (XV (o + 24) 8 q ltac:(eapply avis_sub; [exact OVIS2 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia) ltac:(clear; lia))). exact O24. }
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx7 & R7 & M7v & MG7 & ZdFR & ZdFZ & (ZdMS & ZdKS & ZdR1 & ZdR2 & ZdR8 & ZdR9 & ZdR10 & ZdR11 & ZdR12 & ZdR13 & ZdR18 & ZdR19 & ZdR20 & ZdR21)).
        exists fx7, R7, M7v. split. exact MG7. split. exact ZdFZ.
        split. { eapply msteps_trans. exact ZdMS. apply (ret_to fx7 R7 M7v 0x8fc50 W_8fc50 r F_8fc50 eq_refl D_8fc50). rewrite ZdR1, UR1; reflexivity. exact (proj1 RA). exact (proj2 RA). }
        split. { apply (RPF R7 KS_asgZd ZdKS). refine (L5K.incl_b _ _ _); vm_compute; reflexivity. all: assumption. } exact ZdR10. }
    destruct RUN as (fx7 & R7 & M7v & MG7 & FZ7 & MS7 & RP7 & R7_10).
    apply (apiece_ro L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 fx2 fx7 R2 0x8fbac R7 r M7v K HH2 AM2 MS7 MG7 FZ7).
    intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 EQ7. pose proof (mem_eq_of_agree M2 M7 EQ7) as EM. subst M7.
    apply (KONT fx7 R7 M2 model7 LK2). apply preserved_by_index; exact RP7. exact R7_10.
    rewrite L0; cbn [Nat.eqb]; exact O0. exact O8. intros a v _ _ _ X; exact X.
    rewrite L0 in Lws. destruct ws' as [|? ?]. apply L5C.limbs_at_nil. cbn in Lws; discriminate.
    intros a _; reflexivity. intros a _ _ X; exact X. eapply astk_defined. exact ASTK2. clear; lia. clear; lia.
    exact RT7. exact AM7. apply incl_refl. exact HH7.
  - (* [comment removed for export] *)
    assert (LPOS : 1 <= Z.of_nat leny) by (clear - LNZ; lia).
    assert (DST : 4096 <= dst /\ (dst + n8 <= 2 ^ 47 /\ dst + n8 <= ahl_ceil ar /\ (0x7fff7000 + 17592186048512 <= dst \/ dst + n8 <= 0x7fff7000)) /\ (forall i, 0 <= i < n8 -> aclientw L ar LB2 FF (sp - 64) 2560 (dst + i)) /\ L5.defined M2 dst n8 /\ avis H2 dst n8
                  /\ (forall i, 0 <= i < n8 -> ~ (sp - 64 <= dst + i < sp) /\ ~ (o <= dst + i < o + 16))
                  /\ (forall a, dst <= a < dst + n8 -> byte_at M2 (S a) 0)).
    { subst dst n8. destruct stR as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st].
      - destruct OST as (B0 & _ & _ & Hl2 & _). split. clear - OR; lia. split. clear - OR Hl2 OBIG; lia.
        split. { intros i Hi. apply (obj_client L ar LB2 FF _ _ o 32 (o + 16 + i) AOB). clear - Hi Hl2; lia. }
        split. { eapply L5.defined_sub. exact ODEF2. clear; lia. clear - Hl2; lia. } split. { eapply avis_sub. exact OVIS2. clear; lia. clear - Hl2; lia. }
        split. { intros i Hi. clear - Hi Hl2 OR SLO; lia. }
        intros a Ha. unfold byte_at, S. unfold shadow_zero, byte_at, S in SZ. replace (a / 8 + SB) with (o / 8 + SB + (a / 8 - o / 8)) by (clear; lia). apply SZ.
        clear - Ha Hl2 OR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        destruct OST as (B0 & O16 & O24 & Hlc & Hcap & QQ8 & Q4096 & Q47 & QH). specialize (INB c q eq_refl).
        pose proof (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) _ INB) as ((P0 & P1 & P2 & P3 & P4 & P5) & PDEF & PSH & _). cbn [fst snd] in P0, P1, P2, P3, P4, P5, PDEF, PSH.
        split. exact Q4096. split. clear - Q47 Hlc P4 P5; unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in P5; lia.
        split. { intros i Hi. apply (block_client L ar LB2 FF _ _ q (8 * c)). exact INB. clear - Hi Hlc; lia. }
        split. { eapply L5.defined_sub. exact PDEF. clear; lia. clear - Hlc; lia. } split. { apply (VBLK2 q (8 * c) q _ INB). clear; lia. clear - Hlc; lia. }
        split. { intros i Hi. destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) _ INB)))))) g ltac:(apply in_or_app; left; exact Hg)) as X.
                 cbn [fst snd] in X. clear - Hi Hlc X X1 X2 P4 SLO; lia. }
        intros a Ha. destruct PSH as [PZ _]. unfold byte_at, S. unfold shadow_zero, byte_at, S in PZ. replace (a / 8 + SB) with (q / 8 + SB + (a / 8 - q / 8)) by (clear; lia). apply PZ.
        clear - Ha Hlc P2. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct DST as (D0 & D1 & DCL & DDEF & DVIS & DNF & DSH).
    (* [comment removed for export] *)
    assert (RUN : exists fx5 R5 M5v, mem_grows MV2 M5v /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (o <= i < o + 1) -> M5v (Z_to_bv 64 i) = MV2 (Z_to_bv 64 i))
              /\ msteps RSEGS (st fx2 R2 0x8fbac MV2) (st fx5 R5 0x5e354 M5v) /\ (forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R2 (reg k))
              /\ getr R5 (reg 1) = Z_to_bv 64 588844 /\ getr R5 (reg 10) = Z_to_bv 64 dst /\ getr R5 (reg 11) = Z_to_bv 64 src /\ getr R5 (reg 12) = Z_to_bv 64 n8
              /\ L5.u8_at RSEGS M5v o (Z.lor (Z.land fb' 2) (Z.land fbR 253))).
    { subst dst n8. destruct stR as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st].
      + destruct OST as (B0 & _). pose proof (asgMi_conc fx2 R2 MV2 VZ) as P. cbn beta iota delta [VZ] in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx5 & R5 & M5v & MG5 & MiFR & MiFZ & (MiMS & MiKS & MiR1 & MiR10 & MiR11 & MiR12 & MiR13 & MiB_V33nat)).
        exists fx5, R5, M5v. split. exact MG5. split. { intros i Hi Hn'. apply MiFZ. exact Hi. clear - Hn'; lia. } split. exact MiMS.
        split. { intros k Hk. apply MiKS. revert Hk. refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity. }
        split. exact MiR1. split. exact MiR10. split. exact MiR11. split. rewrite MiR12. f_equal; clear; lia. exact MiB_V33nat.
      + destruct OST as (B0 & O16 & O24 & Hlc & Hcap & QQ8 & Q4096 & Q47 & QH).
        assert (O24v : L5.u64_at RSEGS MV2 (o + 24) q). { apply (proj1 (XV (o + 24) 8 q ltac:(eapply avis_sub; [exact OVIS2 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia) ltac:(clear; lia))). exact O24. }
        assert (ALQ : aligned q 8) by exact QQ8.
        pose proof (asgMd_conc fx2 R2 MV2 VZ) as P. cbn beta iota delta [VZ] in P.
        feed P ltac:(first [apply UR | apply U_to | sc]).
        destruct P as (fx5 & R5 & M5v & MG5 & MdFR & MdFZ & (MdMS & MdKS & MdR1 & MdR10 & MdR11 & MdR12 & MdR13 & MdB_V33nat)).
        exists fx5, R5, M5v. split. exact MG5. split. { intros i Hi Hn'. apply MdFZ. exact Hi. clear - Hn'; lia. } split. exact MdMS.
        split. { intros k Hk. apply MdKS. revert Hk. refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity. }
        split. exact MdR1. split. exact MdR10. split. exact MdR11. split. rewrite MdR12. f_equal; clear; lia. exact MdB_V33nat. }
    destruct RUN as (fx5 & R5 & M5v & MG5 & FZ5 & MS5 & KS5 & R5_1 & R5_10 & R5_11 & R5_12 & OB5v).
    apply (apiece L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 fx2 fx5 R2 0x8fbac R5 0x5e354 M5v (fun a => o <= a < o + 1) K HH2 AM2 MS5 MG5 FZ5).
    { intros a Ha Wa. split. apply (obj_client L ar LB2 FF 0 0 o 32 a AOB). clear - Wa; lia. clear - Wa OR; lia. }
    intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 FRM5 EQ5.
    assert (ASTK5 : astk ar M5 sp ASSIGN_SCR). { eapply astk_grows. exact ASTK2. exact MGM5. }
    (* [comment removed for export] *)
    pose proof (aio_memcpy _ _ _ _ _ HIok) as MC. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MC.
    rewrite (aly_segs L C LY), (aly_memcpy L C LY), (aly_scr_mem L C LY) in MC.
    assert (U2 : bv_unsigned (getr R5 2%bv) = sp - 64). { rewrite r2, (KS5 2%nat) by inl. rewrite Q2. apply L5.unsigned_lit. clear - SPR; lia. }
    eapply (MC fx5 R5 M5 model5 LB2 FF LK2 cr2 A2 dst src n8 (limb_bytes ws') K); clear MC.
    { split. exact HH5. split. exact (proj1 AM5). split. exact (proj2 AM5).
      split. rewrite r10. exact R5_10. split. rewrite r12. exact R5_12. split. clear - D1 D0 Hn LPOS; subst n8; lia.
      split. rewrite r4, (KS5 4%nat) by inl. exact Q4. split. rewrite r1, R5_1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
      split. { rewrite U2. apply (astack_ok_of_astk L ar C LY M2 M5 sp ASSIGN_SCR 64 2560 ASTK2 MGM5). clear; lia. clear; lia.
               unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia.
               clear - A16. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
      split. { intros a Ha. left. unfold byte_at. rewrite FRM5. apply DSH. exact Ha. all: clear - Ha D0 D1 OR OBIG; unfold S, SB.
               Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      split. { intros i Hi. rewrite U2. apply DCL. exact Hi. }
      split. { intros i m Hi Hm. apply (L5C.writable_of_defined RSEGS M5 dst n8). eapply L5.defined_grows. exact MGM5. exact DDEF. clear - D0; lia. clear - D1; lia. exact Hi. exact Hm. }
      split. exact HK.
      subst dst n8. pose proof OB2 as (_ & _ & _ & OSTd). destruct stR as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st L5.bo_len] in *.
      - destruct OSTd as (_ & _ & _ & Hl2d & _). apply (app_rng_aobj L ar C HI HIok LB2 FF LK2 cr2 A2 M5 _ o 32 (o + 16) _ HH5 AOB). clear; lia. clear - Hl2d; lia.
      - destruct OSTd as (_ & _ & _ & Hlcd & _). apply (app_rng_block L ar C HI HIok LB2 FF LK2 cr2 A2 M5 _ q (8 * c) q _ HH5 (INB c q eq_refl)). clear; lia. clear - Hlcd; lia. }
    { rewrite r11. exact R5_11. }
    { intros a Ha. unfold byte_at. rewrite FRM5. apply ACC. exact Ha. all: clear - Ha SRC OR OBIG; unfold S, SB.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    { clear - SRC; lia. }
    { exact SAPP. }
    { intros i Hi. right. rewrite U2. apply SCL. exact Hi. }
    { unfold n8. rewrite <- Lws. replace (Z.to_nat (8 * Z.of_nat (length ws'))) with (8 * length ws')%nat by (clear; lia).
      apply rdn_of_limbs_at. 2: clear - SRC; lia. 2: rewrite Lws; clear - SRC; lia.
      eapply L5C.limbs_at_agree. 4: exact LAT. 2: clear - SRC; lia. 2: rewrite Lws; clear - SRC; lia. intros j Hj. apply FRM5. rewrite Lws in Hj; clear - Hj SRC; lia.
      rewrite Lws in Hj. pose proof (SRCO (j - src) ltac:(clear - Hj; lia)) as X. replace (src + (j - src)) with j in X by (clear; lia). exact X. }
    { intros _. apply NOV. clear - LNZ; lia. }
    (* [comment removed for export] *)
    intros R6 M6 model6 mR10 RP6 BYTES PRES6 SDEF6 RT6 MI6 HH6. rewrite U2 in PRES6, SDEF6. rewrite r1, R5_1.
    assert (Hh6 : m_halted model6 = None). { rewrite (L5LZ.model_rt_halted _ _ RT6). exact (proj1 AM5). }
    assert (ASTK6 : astk ar M6 sp ASSIGN_SCR).
    { apply (astk_after_eq L ar C HI HIok LB2 FF LK2 cr2 A2 M5 M5 M6 _ sp _ (sp - 64) 2560 HH5 ASTK5 (mem_grows_refl M5)).
      intros a Ha Hs Hns. apply PRES6. exact Ha. apply stack_client. exact Hs. exact Hns. clear - Hs D1; lia.
      exact SDEF6. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. clear; lia.
      unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK2 cr2 A2 M6 model6 HH6) as (HOFF6 & VIS6 & _).
    pose proof (statics_vis LB2 FF LK2 cr2 A2 M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
    set (H6 := ahid A2 model6) in *. set (MV6 := mrestrict H6 M6) in *.
    pose proof (aobj_facts L ar C HI LY HIok LB2 FF LK2 cr2 A2 M6 model6 o 32 0 0 HH6 AOB ltac:(clear; lia) ltac:(reflexivity)) as (_ & _ & ODEF6 & OVIS6 & OVSH6 & _).
    change (32 / 8) with 4 in OVSH6. fold H6 in OVIS6, OVSH6.
    assert (AG26 : forall a, (sp - 64 <= a < sp \/ o / 8 + SB <= a < o / 8 + SB + 4) -> MV6 (Z_to_bv 64 a) = MV2 (Z_to_bv 64 a)).
    { intros a Ra. assert (Ha : 0 <= a < 2 ^ 64) by (clear - Ra SPR OR; unfold SB in *; lia).
      unfold MV6. rewrite (mrestrict_visible H6 M6).
      2:{ destruct Ra as [Ra|Ra]. replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS6 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH6 (a - (o / 8 + SB))). clear - Ra; lia. }
      rewrite (PRES6 a Ha). 2:{ destruct Ra as [Ra|Ra]. apply stack_client. clear - Ra SLO SHI SPT; lia. clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (aclient_narrow L ar LB2 FF sp ASSIGN_SCR). apply OCLSH. clear - Ra; lia. clear - Ra OR SLO SPT; unfold SB in *; lia. }
      2:{ destruct Ra as [Ra|Ra]. clear - Ra D1 SLO; lia. clear - Ra D0 D1 OR OBIG SLO SPT; unfold SB in *; lia. }
      rewrite (EQ5 (Z_to_bv 64 a)). 2:{ destruct Ra as [Ra|Ra]. replace a with ((sp - 64) + (a - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH2 (a - (o / 8 + SB))). clear - Ra; lia. }
      apply FZ5. exact Ha. clear - Ra OR SLO SPT OBIG; unfold SB in *; lia. }
    assert (XC6 : forall a v, sp - 64 <= a <= sp - 8 -> L5.u64_at RSEGS MV2 a v -> L5.u64_at RSEGS MV6 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia. intros j Hj. apply AG26. clear - Ha Hj; lia. }
    assert (W64f : L5.writable RSEGS MV6 (sp - 64) 64).
    { apply (proj2 (writable_vis H6 M6 (sp - 64) 64 (VIS6 (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
      eapply (astk_writable ar M6 sp). exact ASTK6. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR. clear; lia. clear; lia. clear; lia. }
    assert (OZ6 : L5KA.zeros_at MV6 (o / 8 + SB) 4). { eapply L5KA.zeros_at_agree1. 2: exact OZv. intros j Hj. apply AG26. clear - Hj; lia. }
    assert (OW6 : L5.writable RSEGS MV6 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H6 M6 o 32 OVIS6)). exact ODEF6. clear - OR; lia. clear - OR; lia. }
    (* [comment removed for export] *)
    pose proof (asgE_conc fx5 R6 MV6 (fun j : nat => match j with 2%nat => sp | 33%nat => o | 34%nat => o'
                  | 41%nat => U R 1 | 42%nat => U R 8 | 43%nat => U R 9 | 44%nat => U R 18 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R 21 | 48%nat => U R6 1 | _ => 0 end)) as P.
    cbn beta iota in P.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XC6; [clear; lia | sc]) ]).
    destruct P as (fx7 & R7 & M7v & MG7 & EFR & EFZ & (EMS & EKS & ER1 & ER2 & ER8 & ER9 & ER10 & ER18 & ER19 & ER20 & ER21)).
    pose proof (ret_to fx7 R7 M7v 0x8fc50 W_8fc50 r F_8fc50 eq_refl D_8fc50 ltac:(rewrite ER1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
    pose proof (msteps_trans _ _ _ _ EMS RET) as MS8. clear EMS RET.
    apply (apiece_ro L ar C HI LY HIok LB2 FF LK2 cr2 A2 M6 model6 fx5 fx7 R6 0x8fc2c R7 r M7v K HH6 (conj Hh6 MI6) MS8 MG7 EFZ).
    intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 EQ7. pose proof (mem_eq_of_agree M6 M7 EQ7) as EM. subst M7.
    (* [comment removed for export] *)
    assert (E26 : ek L ar LB2 FF sp ASSIGN_SCR [(o, 32); (dst, n8)] M2 M6).
    { eapply ek_trans. { apply (ek_piece L ar LB2 FF sp ASSIGN_SCR _ M2 M5 _ FRM5). intros a Ha Hc Ho X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia. }
      apply (ek_mem L ar LB2 FF sp ASSIGN_SCR (sp - 64) 2560 (fun a => dst <= a < dst + n8) _ M5 M6 PRES6).
      unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. clear; lia.
      intros a _ Ho X. apply (Ho (dst, n8)). right; left; reflexivity. exact X. }
    assert (D26 : dk L ar LB2 FF sp ASSIGN_SCR M2 M6).
    { eapply dk_trans. apply dk_grows. exact MGM5.
      apply (dk_mem L ar LB2 FF sp ASSIGN_SCR (sp - 64) 2560 (fun a => dst <= a < dst + n8) M5 M6 PRES6 SDEF6).
      intros a Ha. destruct (BYTES (a - dst) ltac:(clear - Ha; lia)) as (v & _ & Bv). unfold byte_at in Bv. replace (dst + (a - dst)) with a in Bv by (clear; lia). rewrite Bv. discriminate.
      intros a; destruct (rng_dec a dst (dst + n8)) as [X|X]; [left; exact X | right; exact X].
      unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. clear; lia. }
    apply (KONT fx7 R7 M6 model7 LK2).
    + apply preserved_by_index. apply (RPF R7 [3; 4; 22; 23; 24; 25; 26; 27]%nat).
      { intros k Hk. rewrite (EKS k). rewrite (cs_of_preserved R5 R6 k RP6). apply KS5.
        revert Hk; refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity. revert Hk; refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity.
        revert Hk; refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity. }
      apply incl_refl. all: assumption.
    + exact ER10.
    + replace (Nat.eqb leny 0) with false by (symmetry; apply Nat.eqb_neq; exact LNZ). rewrite Z.lor_comm.
      eapply L5C.u8_at_agree. 4:{ apply (proj1 (u8_at_vis H2 M5 o _ ltac:(eapply avis_sub; [exact OVIS2 | clear; lia | clear; lia]) ltac:(clear - OR; lia) ltac:(clear - OR; lia))). unfold H2. rewrite VIS5. exact OB5v. }
      2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. apply PRES6. clear - Hj OR; lia. apply (obj_client L ar LB2 FF _ _ o 32 j AOB). clear - Hj; lia.
      intros Y. pose proof (DNF (j - dst) ltac:(clear - Y; lia)) as [_ X]. clear - Hj X Y. lia.
    + eapply L5C.u64_at_agree. 4: exact O8. 2: clear - OR; lia. 2: clear - OR; lia. intros j Hj. rewrite PRES6. apply FRM5. clear - Hj OR; lia. clear - Hj; lia. clear - Hj OR; lia.
      apply (obj_client L ar LB2 FF _ _ o 32 j AOB). clear - Hj; lia. intros Y. pose proof (DNF (j - dst) ltac:(clear - Y; lia)) as [_ X]. clear - Hj X Y. lia.
    + intros a v Ha Ha8 Hd Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha OR; lia. 2: clear - Ha8 OR; lia.
      intros j Hj. rewrite PRES6. apply FRM5. clear - Hj Ha Ha8 OR; lia. clear - Hj Ha; lia. clear - Hj Ha Ha8 OR; lia.
      apply (obj_client L ar LB2 FF _ _ o 32 j AOB). clear - Hj Ha Ha8; lia. clear - Hj Ha Ha8 Hd; lia.
    + apply limbs_at_of_bytes. clear - D0; lia. rewrite Lws; clear - D1; lia.
      intros i Hi. rewrite Lws in Hi. destruct (BYTES (Z.of_nat i) ltac:(clear - Hi; subst n8; lia)) as (v & [Nv _] & Bv). unfold byte_at in Bv.
      rewrite Nat2Z.id in Nv. rewrite Bv. symmetry. exact Nv.
    + exact E26.
    + exact D26.
    + eapply astk_defined. exact ASTK6. clear; lia. clear; lia.
    + eapply L5LZ.model_rt_trans. exact RT5. eapply L5LZ.model_rt_trans. exact RT6. exact RT7.
    + exact AM7.
    + apply incl_refl.
    + exact HH7.
Qed.

(* [comment removed for export] *)
Theorem assign_ok : resize_spec L ar HI -> assign_spec L ar HI.
Proof.
  intros RZ fx R M model K LB FF LK cr A o o' sp r b b' ws' HH AM HK G10 G11 Hn CAP CR G1 RA G2 A32 G4 STK ROOM RS OB AOB SZ OB' OL' AOB' SZ' INB INB' APART NOALIAS KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR in SLO, DSCR.
  assert (SPR : 0 <= sp < 2 ^ 64 /\ 140735332487232 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
  assert (SA32 : (sp - 64) mod 32 = 0 /\ (sp - 64) mod 16 = 0). { clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp ASSIGN_SCR HH AOB ltac:(clear; lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o' 32 sp ASSIGN_SCR HH AOB' ltac:(clear; lia) ltac:(reflexivity)) as (YR & YBIG & YDEF & YVIS & YVSH & YCL & YCLSH). change (32 / 8) with 4 in YVSH, YCLSH.
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  destruct b as [fb len sto]. pose proof OB as (O0 & Hfb & O8 & OST). destruct b' as [fb' leny sto']. pose proof OB' as (O0' & Hfb' & O8' & OST').
  cbn [L5.bo_fb L5.bo_len L5.bo_st L5.bo_dyn L5.bo_cap L5.bo_data] in *.
  destruct OL' as (Lws' & Rws' & LAT'). cbn [L5.bo_len L5.bo_st] in Lws', LAT'.
  set (src := L5.bo_data o' (L5.BO fb' leny sto')) in *.
  set (n8 := 8 * Z.of_nat leny).
  (* [comment removed for export] *)
  assert (SAPP : app_rng ar src n8).
  { subst src n8. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st L5.bo_len] in *.
    - destruct OST' as (_ & _ & _ & Hl2' & _). apply (app_rng_aobj L ar C HI HIok LB FF LK cr A M _ o' 32 (o' + 16) _ HH AOB'). clear; lia. clear - Hl2'; lia.
    - destruct OST' as (_ & _ & _ & Hlc' & _). apply (app_rng_block L ar C HI HIok LB FF LK cr A M _ q' (8 * c') q' _ HH (INB' c' q' eq_refl)). clear; lia. clear - Hlc'; lia. }
  assert (YD : 4096 <= src /\ src + n8 <= 2 ^ 47 /\ src + n8 <= ahl_ceil ar /\ (0x7fff7000 + 17592186048512 <= src \/ src + n8 <= 0x7fff7000)
               /\ L5.limbs_at RSEGS M src ws' /\ (forall i, 0 <= i < n8 -> ~ (o <= src + i < o + 32))
               /\ (forall i, 0 <= i < n8 -> aclient L ar LB FF sp ASSIGN_SCR (src + i))
               /\ (forall c q, sto = L5.BDyn c q -> src + n8 <= q \/ q + 8 * c <= src)).
  { subst src n8. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st] in *.
    - destruct OST' as (B0' & O16' & O24' & Hl2' & Rw0 & Rw1). split. clear - YR; lia. split. clear - YR Hl2'; lia. split. clear - YR Hl2'; lia. split. clear - YBIG Hl2'; lia.
      split. { rewrite LAT'. intros i Hi. rewrite length_firstn in Hi. cbn [length Nat.min] in Hi.
               destruct i as [|[|i]].
               - destruct leny as [|ly]. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o' + 16 + 8 * Z.of_nat 0) with (o' + 16) by (clear; lia). exact O16'.
               - destruct leny as [|[|ly]]. exfalso; clear - Hi; lia. exfalso; clear - Hi; lia. cbn [firstn nth]. replace (o' + 16 + 8 * Z.of_nat 1) with (o' + 24) by (clear; lia). exact O24'.
               - exfalso. destruct leny as [|[|[|ly]]]; cbn in Hi; clear - Hi Hl2'; lia. }
      split. { intros i Hi. clear - Hi APART Hl2'; lia. } split. { intros i Hi. replace (o' + 16 + i) with (o' + (16 + i)) by (clear; lia). apply YCL. clear - Hi Hl2'; lia. }
      intros c q E. subst sto. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ (INB c q eq_refl)))))))) as X.
      destruct AOB' as (g & Hg & X1 & X2 & _). specialize (X g ltac:(apply in_or_app; left; exact Hg)). cbn [fst snd] in X. clear - X X1 X2 Hl2'; lia.
    - destruct OST' as (B0' & O16' & O24' & Hlc' & Hcap' & YQ8 & YQ4096 & YQ47 & YQH). specialize (INB' c' q' eq_refl).
      pose proof (proj1 (WB _ INB')) as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5). cbn [fst snd] in Y0, Y1, Y2, Y3, Y4, Y5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Y5.
      split. exact YQ4096. split. clear - YQ47 Hlc'; lia. split. clear - Y4 Hlc'; lia. split. clear - Y5 Hlc'; lia. split. exact LAT'.
      split. { intros i Hi. destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ INB')))))) g ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X.
               clear - Hi X X1 X2 Hlc'; lia. }
      split. { intros i Hi. apply (block_client L ar LB FF _ _ q' (8 * c')). exact INB'. clear - Hi Hlc'; lia. }
      intros c q E. subst sto. specialize (NOALIAS c q c' q' eq_refl eq_refl). destruct OST as (B0 & _). cbn [L5.bo_dyn L5.bo_fb L5.bo_cap L5.bo_st] in CAP. specialize (CAP B0).
      clear - NOALIAS Hlc' CAP. lia. }
  destruct YD as (S0 & S1 & S2 & SBIG & SLAT & SNO & SCL & SNQ).
  assert (SAL0 : src mod 8 = 0).
  { subst src. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st] in *.
    - clear - YR. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      destruct OST' as (_ & _ & _ & _ & _ & Q8' & _). exact Q8'. }
  (* [comment removed for export] *)
  assert (WST : exists wsT, L5C.obj_limbs RSEGS M (L5.BO fb len sto) wsT).
  { destruct sto as [v0 v1|c q].
    - exists (firstn len [v0; v1]). destruct OST as (_ & _ & _ & Hl2 & R0 & R1). split. cbn. rewrite length_firstn. cbn. clear - Hl2; lia.
      split. cbn. destruct len as [|[|[|k]]]; cbn; repeat constructor; clear - R0 R1; lia. reflexivity.
    - destruct OST as (B0 & O16 & O24 & Hlc & Hc & Aq & Qlo & Qhi & _). pose proof (proj1 (proj2 (WB _ (INB c q eq_refl)))) as QD. cbn [fst snd] in QD.
      destruct (limbs_of_defined M q len ltac:(eapply L5.defined_sub; [exact QD | clear; lia | clear - Hlc; lia]) ltac:(clear - Qlo; lia) ltac:(clear - Qhi Hlc; lia)) as (ws & L1 & R1 & LA).
      exists ws. split. cbn. exact L1. split. exact R1. cbn. exact LA. }
  destruct WST as (wsT & OLT).
  assert (W64 : L5.writable RSEGS MV (sp - 64) 64).
  { apply (proj2 (writable_vis H M (sp - 64) 64 (VIS (sp - 64) 64 ltac:(clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR. clear; lia. clear; lia. clear; lia. }
  assert (XV : forall a m v, avis H a m -> 0 <= a -> a + 8 <= 2 ^ 64 -> 8 <= m -> (L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV a v) /\ (L5.u8_at RSEGS M a v -> L5.u8_at RSEGS MV a v)).
  { intros a m v Va Ha H8 Hm. split; intros Hc.
    apply (proj2 (u64_at_vis H M a v ltac:(eapply avis_sub; [exact Va | clear; lia | clear - Hm; lia]) Ha H8)). exact Hc.
    apply (proj2 (u8_at_vis H M a v ltac:(eapply avis_sub; [exact Va | clear; lia | clear - Hm; lia]) Ha ltac:(clear - H8; lia))). exact Hc. }
  assert (YB0v : L5.u8_at RSEGS MV o' fb'). { apply (proj2 (XV o' 32 fb' YVIS ltac:(clear - YR; lia) ltac:(clear - YR; lia) ltac:(clear; lia))). exact O0'. }
  assert (Y8v : L5.u64_at RSEGS MV (o' + 8) (Z.of_nat leny)). { apply (proj1 (XV (o' + 8) 24 _ ltac:(eapply avis_sub; [exact YVIS | clear; lia | clear; lia]) ltac:(clear - YR; lia) ltac:(clear - YR; lia) ltac:(clear; lia))). exact O8'. }
  assert (OZv : L5KA.zeros_at MV (o / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 OVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. }
  assert (YZv : L5KA.zeros_at MV (o' / 8 + SB) 4). { apply (proj2 (zeros_at_vis H M _ 4 YVSH)). intros i Hi. unfold shadow_zero, byte_at, S in SZ'. apply SZ'. exact Hi. }
  assert (OWv : L5.writable RSEGS MV o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H M o 32 OVIS)). exact ODEF. clear - OR; lia. clear - OR; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Time assert (NEQ : 1 <= (o - o') mod 2 ^ 64) by (clear - APART OR YR; lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  set (VA := fun j : nat => match j with 2%nat => sp | 33%nat => o | 34%nat => o' | 36%nat => fb' | 37%nat => Z.of_nat leny | 38%nat => src | _ => 0 end).
  assert (RUN : exists fx1 R1 M1v, mem_grows MV M1v /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 64 <= i < sp - 64 + 64) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
            /\ msteps RSEGS (st fx R ASSIGN MV) (st fx1 R1 RESIZE M1v) /\ (forall k, In k [3; 4; 10; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg k) = getr R (reg k))
            /\ getr R1 (reg 1) = Z_to_bv 64 588716 /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 64) /\ getr R1 (reg 8) = Z_to_bv 64 o /\ getr R1 (reg 9) = Z_to_bv 64 o'
            /\ getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat leny) /\ getr R1 (reg 18) = Z_to_bv 64 src /\ getr R1 (reg 19) = Z_to_bv 64 (Z.of_nat leny)
            /\ getr R1 (reg 20) = Z_to_bv 64 (o' / 8 + SB) /\ getr R1 (reg 21) = Z_to_bv 64 SB
            /\ L5.u64_at RSEGS M1v (sp - 8) (U R 1) /\ L5.u64_at RSEGS M1v (sp - 16) (U R 8) /\ L5.u64_at RSEGS M1v (sp - 24) (U R 9) /\ L5.u64_at RSEGS M1v (sp - 32) (U R 18)
            /\ L5.u64_at RSEGS M1v (sp - 40) (U R 19) /\ L5.u64_at RSEGS M1v (sp - 48) (U R 20) /\ L5.u64_at RSEGS M1v (sp - 56) (U R 21)).
  { subst src. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st] in *.
    - destruct OST' as (B0' & _). pose proof (asgAi_conc fx R MV VA) as P. cbn beta iota delta [VA] in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1v & MG1 & AFR & AFZ & (AMS & AKS & AR1 & AR2 & AR8 & AR9 & AR11 & AR18 & AR19 & AR20 & AR21 & AQ_V2nat & AQ_V2nat_1 & AQ_V2nat_2 & AQ_V2nat_3 & AQ_V2nat_4 & AQ_V2nat_5 & AQ_V2nat_6)).
      exists fx1, R1, M1v. split. exact MG1. split. exact AFZ. split. exact AMS. split. { intros k Hk. apply AKS. revert Hk. refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity. }
      unfold U. repeat split; assumption.
    - destruct OST' as (B0' & O16' & O24' & _). pose proof (asgAd_conc fx R MV VA) as P. cbn beta iota delta [VA] in P.
      assert (Y24v : L5.u64_at RSEGS MV (o' + 24) q'). { apply (proj1 (XV (o' + 24) 8 q' ltac:(eapply avis_sub; [exact YVIS | clear; lia | clear; lia]) ltac:(clear - YR; lia) ltac:(clear - YR; lia) ltac:(clear; lia))). exact O24'. }
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx1 & R1 & M1v & MG1 & AFR & AFZ & (AMS & AKS & AR1 & AR2 & AR8 & AR9 & AR11 & AR18 & AR19 & AR20 & AR21 & AQ_V2nat & AQ_V2nat_1 & AQ_V2nat_2 & AQ_V2nat_3 & AQ_V2nat_4 & AQ_V2nat_5 & AQ_V2nat_6)).
      exists fx1, R1, M1v. split. exact MG1. split. exact AFZ. split. exact AMS. split. { intros k Hk. apply AKS. revert Hk. refine (L5K.incl_b _ _ _ k); vm_compute; reflexivity. }
      unfold U. repeat split; assumption. }
  destruct RUN as (fx1 & R1 & M1v & MG1 & AFZ & AMS & AKS & AR1 & AR2 & AR8 & AR9 & AR11 & AR18 & AR19 & AR20 & AR21 & C8 & C16 & C24 & C32 & C40 & C48 & C56).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R ASSIGN R1 RESIZE M1v (fun a => sp - 64 <= a < sp) K HH AM AMS MG1).
  { intros a Ha Hna. apply AFZ. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. clear - Wa SLO SHI SPT; lia. clear; lia. clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  assert (ASTK1 : astk ar M1 sp ASSIGN_SCR). { eapply astk_grows. exact STK. exact MGM1. }
  assert (U1 : forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ o' <= a < o' + 32 \/ o' / 8 + SB <= a < o' / 8 + SB + 4 \/ src <= a < src + n8 \/
                          exists c q, sto = L5.BDyn c q /\ q <= a < q + 8 * c) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ra. apply FRM1. destruct Ra as [Ra|[Ra|[Ra|[Ra|[Ra|(c & q & E & Ra)]]]]]; try (clear - Ra OR YR OBIG YBIG S0 S1 S2 SBIG SLO SPT; unfold SB in *; lia).
    subst sto. pose proof (proj1 (WB _ (INB c q eq_refl))) as (Q0 & _ & _ & _ & Q4 & Q5). cbn [fst snd] in Q0, Q4, Q5. unfold app_mem in Q5. clear - Ra Q0 Q4 Q5; lia.
    destruct Ra as [Ra|[Ra|[Ra|[Ra|[Ra|(c & q & E & Ra)]]]]]; try (clear - Ra OR YR OBIG YBIG S0 S1 S2 SBIG SLO SPT; unfold SB in *; lia).
    subst sto. pose proof (proj1 (WB _ (INB c q eq_refl))) as (Q0 & _ & _ & _ & Q4 & Q5). cbn [fst snd] in Q0, Q4, Q5. clear - Ra Q4 SLO; lia. }
  (* [comment removed for export] *)
  apply (RZ fx1 R1 M1 model1 K LB FF LK cr A o (sp - 64) 0x8fbac leny (L5.BO fb len sto) wsT HH1 AM1 HK).
  - rewrite r10, (AKS 10%nat) by inl. rewrite <- r10. exact G10.
  - rewrite r11. exact AR11.
  - exact Hn.
  - exact CAP.
  - exact CR.
  - rewrite r1. exact AR1.
  - split. clear; lia. reflexivity.
  - rewrite r2. exact AR2.
  - exact (proj1 SA32).
  - rewrite r4, (AKS 4%nat) by inl. rewrite <- r4. exact G4.
  - apply (astk_sub ar M1 M1 sp ASSIGN_SCR 64 RESIZE_SCR ASTK1 (mem_grows_refl M1)). clear; lia. unfold RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
    unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. exact (proj2 SA32).
  - exact ROOM.
  - eapply ffrs_le. exact RS. clear; lia.
  - eapply (L5C.big_at_agree RSEGS M M1). intros j Hj. apply U1. left; clear - Hj; lia. clear - OR; lia. clear - OR; lia. exact OB.
  - destruct OLT as (LT & RT & VT). split. exact LT. split. exact RT. cbn [L5.bo_st L5.bo_len] in VT |- *.
    destruct sto as [v0 v1|c q]. exact VT. cbn in LT.
    destruct OST as (B0 & O16 & O24 & Hlc & Hc & Aq & Qlo & Qhi & _).
    eapply (L5C.limbs_at_agree RSEGS M M1). intros j Hj. apply U1. right; right; right; right; right. exists c, q. split. reflexivity. rewrite LT in Hj; clear - Hj Hlc; lia.
    clear - Qlo; lia. rewrite LT; clear - Qhi Hlc; lia. exact VT.
  - exact AOB.
  - intros j Hj. unfold byte_at, S. rewrite U1. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj. right; left; clear - Hj; lia.
  - exact INB.
  - (* [comment removed for export] *)
    cbn [L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_cap L5.bo_data].
    intros fx2 R2 M2 model2 gr LB2 cr2 LK2 A2 [RP2 POST] RT2 IA2 AM2 LKI2 HH2.
    (* [comment removed for export] *)
    assert (SIT : exists (fbR : Z) (stR : L5.bstore) (Wrz : list L5.range),
              L5.big_at RSEGS M2 o (L5.BO fbR leny stR) /\ (forall c q, stR = L5.BDyn c q -> In (q, 8 * c) LB2) /\ incl LB LB2
              /\ ahpres L ar LB FF (sp - 64) RESIZE_SCR Wrz M1 M2
              /\ (forall a, L5.outside [(o, 32); (L5.bo_data o (L5.BO fb len sto), n8)] a -> L5.outside Wrz a)
              /\ (forall a, L5.outside [(o, 32); (L5.bo_data o (L5.BO fb len sto), 8 * L5.bo_cap (L5.BO fb len sto))] a -> L5.outside Wrz a)
              /\ ((0 < leny)%nat -> L5.bo_data o (L5.BO fbR leny stR) + n8 <= src \/ src + n8 <= L5.bo_data o (L5.BO fbR leny stR))
              /\ (forall b0, In b0 LB2 -> ~ In b0 LB -> ~ aclient L ar LB FF sp ASSIGN_SCR (fst b0) /\ (forall a, fst b0 <= a < fst b0 + snd b0 -> ~ aclient L ar LB FF sp ASSIGN_SCR a))
              /\ match gr with
                 | Same => LB2 = LB /\ cr2 = cr /\ fbR = fb /\ (Z.testbit fb 0 = true \/ (leny <= 2)%nat)
                           /\ match sto, stR with L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end
                 | Grown q cap => Z.testbit fb 0 = false /\ (3 <= leny)%nat /\ cap = round_up (Z.of_nat leny) /\ LB2 = (q, 8 * cap) :: LB /\ cr2 = adebit L cr (8 * cap)
                           /\ afresh L ar LB (FF ++ LK2) M2 q (8 * cap) /\ stR = L5.BDyn cap q /\ fbR = Z.lor fb 1 /\ (forall a, L5.outside [(o, 32)] a -> L5.outside Wrz a)
                 end).
    { destruct gr as [|q cap].
      - destruct POST as (DN & -> & -> & (stR & OBR & OLR & MT) & PRES). exists fb, stR, [(o, 32); (L5.bo_data o (L5.BO fb len sto) + 8 * Z.of_nat len, 8 * Z.max 0 (Z.of_nat leny - Z.of_nat len))].
        split. exact OBR. split. { intros c q E. subst stR. destruct sto as [v0 v1|c0 q0]. destruct MT. destruct MT as [-> ->]. apply INB. reflexivity. }
        split. apply incl_refl. split. exact PRES.
        split. { intros a Ho rr [<-|[<-|[]]]. apply Ho. left; reflexivity. unfold L5.in_rng; cbn [fst snd]. intros X. apply (Ho (L5.bo_data o (L5.BO fb len sto), n8)). right; left; reflexivity.
                 unfold L5.in_rng; cbn [fst snd]. subst n8; clear - X; lia. }
        split. { intros a Ho rr [<-|[<-|[]]]. apply Ho. left; reflexivity. unfold L5.in_rng; cbn [fst snd]. intros X.
                 destruct sto as [v0 v1|c0 q0]; cbn [L5.bo_data L5.bo_st L5.bo_cap L5.bo_dyn L5.bo_fb] in *.
                 - destruct OST as (B0 & _ & _ & Hl2 & _). assert (L2 : Z.of_nat leny <= 2). { destruct DN as [DN|DN]. unfold L5.bo_dyn in DN; cbn [L5.bo_fb] in DN. rewrite B0 in DN; discriminate. clear - DN; lia. }
                   apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X Hl2 L2; lia.
                 - destruct OST as (B0 & _ & _ & Hlc & _). specialize (CAP B0). apply (Ho (q0, 8 * c0)). right; left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X Hlc CAP; lia. }
        split. { intros LP. destruct sto as [v0 v1|c0 q0]; destruct stR as [r0 r1|c1 q1]; try (exfalso; exact MT); cbn [L5.bo_data L5.bo_st] in *.
                 destruct OBR as (_ & _ & _ & (_ & _ & _ & Hl2 & _)). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Hl2. clear - SNO LP Hl2; subst n8. pose proof (SNO 0 ltac:(lia)). pose proof (SNO (8 * Z.of_nat leny - 1) ltac:(lia)). lia.
                 destruct MT as [-> ->]. destruct OST as (B0 & _). cbn [L5.bo_dyn L5.bo_fb L5.bo_cap L5.bo_st] in CAP. specialize (CAP B0). pose proof (SNQ c0 q0 eq_refl) as X. clear - X CAP LP; subst n8; lia. }
        split. intros b0 X Y. exfalso. exact (Y X).
        split. reflexivity. split. reflexivity. split. reflexivity. split. exact DN. exact MT.
      - destruct POST as (B0 & N3 & ECAP & -> & -> & FRESH & OBR & OLR & PRES). exists (Z.lor fb 1), (L5.BDyn cap q), [(o, 32)].
        split. exact OBR. split. { intros c q' E. injection E; intros <- <-. left; reflexivity. }
        split. { intros b0 Hb. right; exact Hb. } split. exact PRES.
        split. { intros a Ho rr [<-|[]]. apply Ho. left; reflexivity. }
        split. { intros a Ho rr [<-|[]]. apply Ho. left; reflexivity. }
        pose proof FRESH as (BRq & BAq & FAq & DEFq & SHBq).
        split. { intros _. cbn [L5.bo_data L5.bo_st]. subst src n8. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st] in *.
                 destruct AOB' as (g & Hg & X1 & X2 & _). specialize (FAq g ltac:(apply in_or_app; left; exact Hg)). destruct OST' as (_ & _ & _ & Hl2' & _). clear - FAq X1 X2 Hl2' N3 Hn ECAP.
                 assert (LC : 8 * 3 <= 8 * cap). { rewrite ECAP; unfold round_up. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
                 Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). clear - FAq X1 X2 Hl2' LC. lia.
                 destruct OST' as (_ & _ & _ & Hlc' & _). specialize (BAq _ (INB' c' q' eq_refl)). cbn [fst snd] in BAq.
                 assert (LC : Z.of_nat leny <= cap). { rewrite ECAP; unfold round_up. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear; lia. }
                 Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). clear - BAq Hlc' LC; lia. }
        split. { intros b0 [<-|Hb] NI. 2: exfalso; exact (NI Hb). cbn [fst snd]. split.
          apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp ASSIGN_SCR q _ q HH SPT BRq BAq). eapply fframes_apart_incl. exact FAq. intros g Hg; apply in_or_app; left; exact Hg. destruct BRq as (_ & _ & _ & P3 & _); clear - P3; lia.
          intros a Ha. apply (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp ASSIGN_SCR q _ a HH SPT BRq BAq). eapply fframes_apart_incl. exact FAq. intros g Hg; apply in_or_app; left; exact Hg. exact Ha. }
        split. exact B0. split. exact N3. split. exact ECAP. split. reflexivity. split. reflexivity. split. exact FRESH. split. reflexivity. split. reflexivity. intros a X; exact X. }
    destruct SIT as (fbR & stR & Wrz & OBR & INBR & LBI & PRES2 & HWrz & HWX & NOVR & FRESHNC & FIN).
    assert (ASTK2 : astk ar M2 sp ASSIGN_SCR).
    { apply (astk_after L ar C HI HIok LB FF LK cr A M1 M1 M2 _ sp _ (sp - 64) RESIZE_SCR Wrz HH1 ASTK1 (mem_grows_refl M1) PRES2).
      unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. clear; lia. unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB2 FF LK2 cr2 A2 M2 model2 HH2) as (HOFF2 & VIS2 & _ & _ & VBLK2 & _).
    set (H2 := ahid A2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
    (* [comment removed for export] *)
    assert (E02g : forall WW, (forall a, L5.outside WW a -> L5.outside Wrz a) -> ek L ar LB FF sp ASSIGN_SCR WW M M2).
    { intros WW HWW. eapply ek_trans. { apply (ek_piece L ar LB FF sp ASSIGN_SCR _ M M1 _ FRM1). intros a Ha Hc _ X.
        destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp ASSIGN_SCR a HH SPT Hc) as [Y|Y].
        unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR in Y; clear - X Y; lia. clear - X Y SLO; lia. }
      apply (ek_callee L ar LB [] FF [] sp ASSIGN_SCR (sp - 64) RESIZE_SCR _ Wrz M1 M2 PRES2).
      unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. clear; lia. intros a _ Ho. apply HWW. exact Ho. }
    pose proof (E02g _ HWrz) as E02. pose proof (E02g _ HWX) as E02X.
    assert (D02 : dk L ar LB FF sp ASSIGN_SCR M M2).
    { eapply dk_trans. apply dk_grows. exact MGM1. apply (dk_callee L ar LB [] FF [] sp ASSIGN_SCR (sp - 64) RESIZE_SCR Wrz M1 M2 PRES2).
      unfold ASSIGN_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, MEM_SCR; clear; lia. clear; lia. }
    (* [comment removed for export] *)
    assert (YRNG : forall a, (o' <= a < o' + 32 \/ o' / 8 + SB <= a < o' / 8 + SB + 4 \/ o / 8 + SB <= a < o / 8 + SB + 4 \/ src <= a < src + n8) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ra. apply E02X. split. clear - Ra OR YR S0 S1; unfold SB in *; lia. split.
      { destruct Ra as [Ra|[Ra|[Ra|Ra]]]. apply (obj_client L ar LB FF _ _ o' 32 a AOB'). exact Ra.
        replace a with (o' / 8 + SB + (a - (o' / 8 + SB))) by (clear; lia). apply YCLSH. clear - Ra; lia.
        replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ra; lia.
        replace a with (src + (a - src)) by (clear; lia). apply SCL. clear - Ra; lia. }
      intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd].
      - destruct Ra as [Ra|[Ra|[Ra|Ra]]]. clear - Ra APART; lia. clear - Ra YR YBIG OR OBIG; unfold SB in *; lia. clear - Ra OR OBIG; unfold SB in *; lia.
        pose proof (SNO (a - src) ltac:(clear - Ra; lia)) as X. replace (src + (a - src)) with a in X by (clear; lia). exact X.
      - destruct sto as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st L5.bo_cap].
        + destruct Ra as [Ra|[Ra|[Ra|Ra]]]. clear - Ra APART OR; lia. clear - Ra YR YBIG OR OBIG; unfold SB in *; lia. clear - Ra OR OBIG; unfold SB in *; lia.
          pose proof (SNO (a - src) ltac:(clear - Ra; lia)) as X. replace (src + (a - src)) with a in X by (clear; lia). clear - X; lia.
        + pose proof (proj1 (WB _ (INB c q eq_refl))) as (Q0 & _ & _ & _ & Q4 & Q5). cbn [fst snd] in Q0, Q4, Q5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
          destruct Ra as [Ra|[Ra|[Ra|Ra]]].
          * destruct AOB' as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ (INB c q eq_refl))))))) g ltac:(apply in_or_app; left; exact Hg)) as X. cbn [fst snd] in X.
            clear - Ra X X1 X2; lia.
          * clear - Ra Q5 Q0 YR; unfold SB in *; lia.
          * clear - Ra Q5 Q0 OR; unfold SB in *; lia.
          * pose proof (SNQ c q eq_refl) as X. clear - Ra X; lia. }
    assert (O0Y : L5.u8_at RSEGS M2 o' fb'). { eapply L5C.u8_at_agree. 4: exact O0'. 2: clear - YR; lia. 2: clear - YR; lia. intros j Hj. apply YRNG. left; clear - Hj; lia. }
    assert (O8Y : L5.u64_at RSEGS M2 (o' + 8) (Z.of_nat leny)). { eapply L5C.u64_at_agree. 4: exact O8'. 2: clear - YR; lia. 2: clear - YR; lia. intros j Hj. apply YRNG. left; clear - Hj; lia. }
    assert (SZY : shadow_zero M2 o' 4). { intros j Hj. unfold byte_at, S. rewrite YRNG. unfold shadow_zero, byte_at, S in SZ'. apply SZ'. exact Hj. right; left; clear - Hj; lia. }
    assert (SZO : shadow_zero M2 o 4). { intros j Hj. unfold byte_at, S. rewrite YRNG. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hj. right; right; left; clear - Hj; lia. }
    assert (LAT2 : L5.limbs_at RSEGS M2 src ws'). { eapply L5C.limbs_at_agree. 4: exact SLAT. 2: clear - S0; lia. 2: rewrite Lws'; clear - S1; subst n8; lia. intros j Hj. apply YRNG. right; right; right. rewrite Lws' in Hj; subst n8; clear - Hj; lia. }
    assert (ACC2 : aacc M2 src n8).
    { subst src. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st] in *.
      - destruct OST' as (_ & _ & _ & Hl2' & _). intros a Ha. left. unfold shadow_zero, byte_at, S in SZY |- *. replace (a / 8 + SB) with (o' / 8 + SB + (a / 8 - o' / 8)) by (clear; lia). apply SZY.
        clear - Ha Hl2' YR; subst n8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        destruct OST' as (_ & _ & _ & Hlc' & _). pose proof (proj1 (proj2 (proj2 (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) _ (LBI _ (INB' c' q' eq_refl)))))) as [PZ _]. cbn [fst snd] in PZ.
        pose proof (proj1 (proj1 (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) _ (LBI _ (INB' c' q' eq_refl)))) as (_ & _ & P2 & _). cbn [fst snd] in P2.
        intros a Ha. left. unfold shadow_zero, byte_at, S in PZ |- *. replace (a / 8 + SB) with (q' / 8 + SB + (a / 8 - q' / 8)) by (clear; lia). apply PZ.
        clear - Ha Hlc' P2; subst n8. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    assert (SCL2 : forall i, 0 <= i < n8 -> aclient L ar LB2 FF (sp - 64) 2560 (src + i)).      (* [comment removed for export] *)
    { subst src. destruct sto' as [w0 w1|c' q']; cbn [L5.bo_data L5.bo_st] in *.
      - destruct OST' as (_ & _ & _ & Hl2' & _). intros i Hi. apply (obj_client L ar LB2 FF _ _ o' 32 (o' + 16 + i) AOB'). clear - Hi Hl2'; subst n8; lia.
      - destruct OST' as (_ & _ & _ & Hlc' & _). intros i Hi. apply (block_client L ar LB2 FF _ _ q' (8 * c')). exact (LBI _ (INB' c' q' eq_refl)). clear - Hi Hlc'; subst n8; lia. }
    (* [comment removed for export] *)
    assert (XC2 : forall a v, sp - 64 <= a <= sp - 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. 2: clear - Ha SPR; lia. 2: clear - Ha SPR; lia. intros j Hj.
      unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace j with ((sp - 64) + (j - (sp - 64))) by (clear; lia). apply (VIS2 (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ha Hj; lia. }
      rewrite (proj1 PRES2 j). 2:{ split. clear - Ha Hj SPR; lia. split. apply stack_client. clear - Ha Hj SLO SHI SPT; lia. clear - Ha Hj; lia. apply HWX.
          intros rr [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]. clear - Ha Hj OR SLO; lia.
          destruct sto as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st L5.bo_cap]. clear - Ha Hj OR SLO; lia.
          pose proof (proj1 (WB _ (INB c q eq_refl))) as (_ & _ & _ & _ & Q4 & _). cbn [fst snd] in Q4. clear - Ha Hj Q4 SLO; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. replace j with ((sp - 64) + (j - (sp - 64))) by (clear; lia). apply (VIS (sp - 64) 64). clear - SLO; lia. clear - SPR; lia. clear - Ha Hj; lia. }
    apply (asg_tail fx2 R2 M2 model2 K LB2 FF LK2 cr2 A2 o o' sp r leny fb' fbR stR src ws' R HH2 AM2 HK G1 RA G2 G4 ASTK2).
    all: try (apply XC2; [clear; lia | assumption]).
    + rk. + rk. + rk. + rk. + rk. + rk. + rk.
    + rewrite (cs_of_preserved R1 R2 3 RP2) by inl. apply AKS. inl.
    + rk.
    + rewrite (cs_of_preserved R1 R2 22 RP2) by inl. apply AKS. inl. + rewrite (cs_of_preserved R1 R2 23 RP2) by inl. apply AKS. inl.
    + rewrite (cs_of_preserved R1 R2 24 RP2) by inl. apply AKS. inl. + rewrite (cs_of_preserved R1 R2 25 RP2) by inl. apply AKS. inl.
    + rewrite (cs_of_preserved R1 R2 26 RP2) by inl. apply AKS. inl. + rewrite (cs_of_preserved R1 R2 27 RP2) by inl. apply AKS. inl.
    + exact AOB. + exact AOB'. + exact APART. + exact OBR. + exact SZO. + exact O0Y. + exact Hfb'. + exact O8Y. + exact SZY. + exact Hn. + exact INBR.
    + exact LAT2. + exact Lws'. + exact ACC2. + clear - S0 S1; lia. + exact SAPP. + exact SCL2. + exact NOVR.
    + intros i Hi. pose proof (SNO i Hi). clear - H0; lia.
    + exact SAL0.
    + (* [comment removed for export] *)
      intros fx7 R7 M7 model7 LK7 RP7 R7_10 O0f O8f KEEP LIMBS E27 D27 DEF7 RT7 AM7 LKI7 HH7. subst n8.
      pose proof OBR as (_ & HfbR & _ & OSTR). cbn [L5.bo_fb L5.bo_len L5.bo_st] in HfbR, OSTR.
      assert (FBF : forall grown : bool, fbR = (if grown then Z.lor fb 1 else fb) ->
                L5.u8_at RSEGS M7 o (assign_fb fb fb' leny grown) /\ 0 <= assign_fb fb fb' leny grown < 256 /\ Z.testbit (assign_fb fb fb' leny grown) 0 = Z.testbit fbR 0).
      { intros grown E. unfold assign_fb. rewrite <- E. destruct (Nat.eqb leny 0). split. exact O0f. split. exact HfbR. reflexivity.
        pose proof (signcopy_facts fbR fb' HfbR Hfb') as [X1 X2]. split. exact O0f. split. exact X1. exact X2. }
      destruct gr as [|q cap].
      -- (* [comment removed for export] *)
        destruct FIN as (-> & -> & EfbR & DN & MT).
        destruct (FBF false EfbR) as (F0 & F1 & F2).
        apply (KONT fx7 R7 M7 model7 Same LB cr LK7 A2).
        ** split. exact RP7. split. rewrite r10. exact R7_10. cbn [assign_post L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data].
          split. { destruct DN as [X|X]. left; exact X. right; exact X. } split. reflexivity. split. reflexivity.
          split.
          { destruct stR as [r0 r1|c q].
            - (* [comment removed for export] *)
              destruct sto as [v0 v1|c0 q0]. 2: destruct MT. destruct OSTR as (BR0 & R16 & R24 & Hl2R & Rr0 & Rr1). cbn [L5.bo_data L5.bo_st] in *.
              set (w0 := if Nat.leb 1 leny then nth 0 ws' 0 else r0). set (w1 := if Nat.leb 2 leny then nth 1 ws' 0 else r1).
              assert (W0 : L5.u64_at RSEGS M7 (o + 16) w0 /\ 0 <= w0 < 2 ^ 64).
              { subst w0. destruct (Nat.leb_spec 1 leny).
                - split. pose proof (LIMBS 0%nat ltac:(rewrite Lws'; exact H0)) as X. replace (o + 16 + 8 * Z.of_nat 0) with (o + 16) in X by (clear; lia). exact X.
                  rewrite Forall_forall in Rws'. apply Rws'. apply nth_In. rewrite Lws'. exact H0.
                - split. apply KEEP. clear; lia. clear; lia. right. clear - H0; lia. exact R16. exact Rr0. }
              assert (W1 : L5.u64_at RSEGS M7 (o + 24) w1 /\ 0 <= w1 < 2 ^ 64).
              { subst w1. destruct (Nat.leb_spec 2 leny).
                - split. pose proof (LIMBS 1%nat ltac:(rewrite Lws'; exact H0)) as X. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) in X by (clear; lia). exact X.
                  rewrite Forall_forall in Rws'. apply Rws'. apply nth_In. rewrite Lws'. exact H0.
                - split. apply KEEP. clear; lia. clear; lia. right. clear - H0; lia. exact R24. exact Rr1. }
              exists (L5.BInl w0 w1). split.
              { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F0. split. exact F1. split. exact O8f. split. rewrite F2. exact BR0.
                split. exact (proj1 W0). split. exact (proj1 W1). split. exact Hl2R. split. exact (proj2 W0). exact (proj2 W1). }
              split. 2: exact I. split. cbn. exact Lws'. split. exact Rws'. cbn [L5.bo_st L5.bo_len].
              subst w0 w1. clear - Lws' Hl2R. destruct ws' as [|a0 [|a1 [|a2 l]]]; cbn in Lws' |- *; subst leny; cbn; try reflexivity. exfalso; lia.
            - destruct sto as [v0 v1|c0 q0]. destruct MT. destruct MT as [-> ->]. destruct OSTR as (BR1 & R16 & R24 & HlcR & HcapR & RQ8 & RQ4096 & RQ47 & RQH). cbn [L5.bo_data L5.bo_st] in *.
              destruct AOB as (g & Hg & X1 & X2 & _). pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (WB _ (INB c0 q0 eq_refl))))))) g ltac:(apply in_or_app; left; exact Hg)) as GX. cbn [fst snd] in GX.
              exists (L5.BDyn c0 q0). split.
              { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F0. split. exact F1. split. exact O8f. split. rewrite F2. exact BR1.
                split. apply KEEP. clear; lia. clear; lia. clear - GX X1 X2 HlcR; lia. exact R16.
                split. apply KEEP. clear; lia. clear; lia. clear - GX X1 X2 HlcR; lia. exact R24.
                split. exact HlcR. split. exact HcapR. split. exact RQ8. split. exact RQ4096. split. exact RQ47. exact RQH. }
              split. 2: split; reflexivity. split. cbn. exact Lws'. split. exact Rws'. cbn [L5.bo_st L5.bo_len]. exact LIMBS. }
          apply ahpres_of. 2: exact DEF7. 2:{ eapply dk_trans. exact D02. exact D27. }
          eapply ek_trans. exact E02. eapply ek_W. exact E27. intros a Ho rr [<-|[<-|[]]]. apply Ho. left; reflexivity.
          destruct stR as [r0 r1|c q]; cbn [L5.bo_data L5.bo_st]. intros X. apply (Ho (o, 32)). left; reflexivity. unfold L5.in_rng in X |- *; cbn [fst snd] in X |- *.
          { destruct sto as [v0 v1|c0 q0]. 2: destruct MT. destruct OSTR as (_ & _ & _ & Hl2R & _). clear - X Hl2R; lia. }
          destruct sto as [v0 v1|c0 q0]. destruct MT. destruct MT as [-> ->]. cbn [L5.bo_data L5.bo_st]. apply Ho. right; left; reflexivity.
        ** eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT7.
        ** exact IA2.
        ** exact AM7.
        ** eapply incl_tran. exact LKI7. exact LKI2.
        ** exact HH7.
      -- (* [comment removed for export] *)
        destruct FIN as (B0 & N3 & ECAP & -> & -> & FRESH & -> & EfbR & HW32).
        destruct (FBF true EfbR) as (F0 & F1 & F2). pose proof FRESH as (BRq & BAq & FAq & DEFq & SHBq).
        destruct OSTR as (BR1 & R16 & R24 & HlcR & HcapR & RQ8 & RQ4096 & RQ47 & RQH). cbn [L5.bo_data L5.bo_st] in *.
        destruct AOB as (g & Hg & X1 & X2 & _). pose proof (FAq g ltac:(apply in_or_app; left; exact Hg)) as GX.
        pose proof BRq as (P0 & P1 & P2 & P3 & P4 & P5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in P5.
        apply (KONT fx7 R7 M7 model7 (Grown q cap) ((q, 8 * cap) :: LB) (adebit L cr (8 * cap)) LK7 A2).
        ** split. exact RP7. split. rewrite r10. exact R7_10. cbn [assign_post L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data].
          split. exact B0. split. exact N3. split. exact ECAP. split. reflexivity. split. reflexivity.
          split. { split. exact BRq. split. exact BAq. split. { eapply fframes_apart_incl. exact FAq. intros g' Hg'. apply in_app_or in Hg'. apply in_or_app. destruct Hg' as [Hg'|Hg']. left; exact Hg'. right; apply LKI7; exact Hg'. }
                   split. { intros i Hi. apply D27. clear - Hi P0 P5; lia. apply (block_client L ar _ FF _ _ q (8 * cap)). left; reflexivity. clear - Hi; lia. apply DEFq. exact Hi. }
                   destruct SHBq as [SZq SPq]. split. 2:{ intros X. exfalso. apply X. clear. rewrite Z.mul_comm. apply Z_mod_mult. }
                   replace (8 * cap / 8) with cap in SZq |- * by (clear; rewrite Z.mul_comm, Z_div_mult; [reflexivity | lia]).
                   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
                   assert (QSH : SB <= q / 8 + SB /\ (q + 8 * cap - 1) / 8 = q / 8 + cap - 1 /\ q / 8 * 8 = q) by (clear - P0 P2 P3 P5; unfold SB; lia).
                   Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
                   intros j Hj. unfold byte_at. rewrite E27. apply SZq. exact Hj.
                   split. unfold S; clear - Hj QSH P0 P5 P3; unfold SB in *; lia. split.
                   { right; right; right; right; right; right. exists (q, 8 * cap). split. left; reflexivity. cbn [fst snd]. unfold in_shadow_of, S. destruct QSH as (Q1 & Q2 & Q3). rewrite Q2. clear - Hj Q3; lia. }
                   intros rr [<-|[<-|[]]]; unfold L5.in_rng, S; cbn [fst snd]. clear - Hj QSH OR OBIG P0 P5 P3; unfold SB in *; lia. clear - Hj QSH P0 P5 P3 HlcR; unfold SB in *; lia. }
          split. { unfold L5.big_at; cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. exact F0. split. exact F1. split. exact O8f. split. rewrite F2. exact BR1.
                   split. apply KEEP. clear; lia. clear; lia. clear - GX X1 X2 HlcR; lia. exact R16.
                   split. apply KEEP. clear; lia. clear; lia. clear - GX X1 X2 HlcR; lia. exact R24.
                   split. exact HlcR. split. exact HcapR. split. exact RQ8. split. exact RQ4096. split. exact RQ47. exact RQH. }
          split. { split. cbn. exact Lws'. split. exact Rws'. cbn [L5.bo_st L5.bo_len]. exact LIMBS. }
          apply ahpres_of. 2: exact DEF7. 2:{ eapply dk_trans. exact D02. apply (dk_tl L ar LB (q, 8 * cap)). exact D27. }
          eapply ek_trans. { apply (E02g [(o, 32)]). exact HW32. }
          intros a (Ha & Hc & Ho). apply E27. split. exact Ha. split. apply aclient_consb. exact Hc.
          intros rr [<-|[<-|[]]]. apply Ho. left; reflexivity. unfold L5.in_rng; cbn [fst snd]. intros X.
          exact (proj2 (FRESHNC (q, 8 * cap) (or_introl eq_refl) ltac:(intros Y; exact (fresh_block_not_client L ar C HI LY HIok LB FF LK cr A M _ sp ASSIGN_SCR q _ q HH SPT BRq BAq ltac:(eapply fframes_apart_incl; [exact FAq | intros g' Hg'; apply in_or_app; left; exact Hg']) ltac:(clear - P3; lia) (block_client L ar LB FF _ _ q _ q Y ltac:(clear - P3; lia))))) a ltac:(cbn [fst snd]; clear - X HlcR; lia) Hc).
        ** eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. exact RT7.
        ** exact IA2.
        ** exact AM7.
        ** eapply incl_tran. exact LKI7. exact LKI2.
        ** exact HH7.
Qed.

End WithIface.
End SCFG_1.
End L5AASG.
