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
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun Bo0_code_90368_91368 BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5LazyA L5DefsAB0
     L5CoreAB0 L5CoreSpecsAB0 L5StepAB0 L5BAlloc L5BAReserveP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5AARS.
Import L5A. Import L5CA. Import L5CSA. Import L5SA. Import L5AARSP.
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

(* [comment removed for export] *)
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

Theorem areserve_ok : roundup_spec L ar HI -> opnew_spec L ar HI -> areserve_spec L ar HI.
Proof.
  intros RU NEW fx R M model K LB FF LK cr A o n sp r HH AM HK G10 G11 Hn CR G1 RA G2 A32 G4 STK ROOM RS OB SZ Co8 Co24 KONT.
  pose proof STK as (A16 & SLO & SHI & SPT & DSCR & DUP). unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in SLO, DSCR.
  set (s := sp - 16).
  assert (SA : s mod 32 = 0 /\ (s - 128) mod 32 = 0 /\ (s - 128) mod 16 = 0).
  { subst s. clear - A32. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  destruct SA as (SA32 & SA32' & SA16).
  assert (SPR : 0 <= s < 2 ^ 64 /\ 140735332487424 <= s <= 140737488355312) by (subst s; clear - SLO SHI SPT; lia).
  pose proof (vis_pack L ar C HI LY HIok LB FF LK cr A M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  pose proof (statics_vis LB FF LK cr A M model HH) as (IMGC & CSB & CUAR).
  set (H := ahid A model) in *. set (MV := mrestrict H M) in *.
  assert (W144 : L5.writable RSEGS MV (s - 128) 144).
  { apply (proj2 (writable_vis H M (s - 128) 144 (VIS (s - 128) 144 ltac:(subst s; clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
    eapply (astk_writable ar M sp). exact STK. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. subst s; clear; lia. subst s; clear; lia. clear; lia. }
  pose proof (aobj_facts L ar C HI LY HIok LB FF LK cr A M model o 32 sp ARESERVE_SCR HH OB ltac:(clear; lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH). change (32 / 8) with 4 in OVSH, OCLSH.
  (* [comment removed for export] *)
  pose proof (arsA_conc fx R MV (fun j => match j with 2%nat => s | 33%nat => o | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
  feed P ltac:(subst s; sc).
  destruct P as (fx1 & R1 & M1v & MG1 & FR1 & FZ1 & (MS1 & KS1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A19 & A20 & A25 &
                 C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C0 & Cp8 & C112)).
  apply (apiece L ar C HI LY HIok LB FF LK cr A M model fx fx1 R ARESERVE R1 SM1 M1v (fun a => s - 128 <= a < s + 16) K HH AM MS1 MG1).
  { intros a Ha Hna. apply FZ1. exact Ha. clear - Hna; lia. }
  { intros a Ha Wa. split. apply stack_client. subst s; clear - Wa SLO SHI SPT; lia. clear; lia. subst s; clear - Wa SLO SPT; lia. }
  intros M1 model1 HH1 AM1 RT1 AH1 VIS1 MGM1 FRM1 EQ1.
  (* [comment removed for export] *)
  pose proof (aio_stack_malloc _ _ _ _ _ HIok 1 ltac:(left; reflexivity)) as SM. unfold astack_malloc_spec in SM.
  rewrite (aly_segs L C LY), (aly_sm1 L C LY), (aly_scr_sm L C LY) in SM.
  assert (U2 : bv_unsigned (getr R1 2%bv) = s - 128). { rewrite r2, A2. apply L5.unsigned_lit. clear - SPR; lia. }
  eapply (SM fx1 R1 M1 model1 LB FF LK cr A K HH1 (proj1 AM1) (proj2 AM1)); clear SM.
  - rewrite r4, (KS1 4%nat) by inl. rewrite <- r4. exact G4.
  - rewrite r1, A1. apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear; lia). reflexivity.
  - rewrite U2. replace (s - 128) with (sp - 144) by (subst s; clear; lia).
    apply (astack_ok_of_astk L ar C LY M M1 sp ARESERVE_SCR 144 512 STK MGM1). clear; lia. clear; lia. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia.
    replace (sp - 144) with (s - 128) by (subst s; clear; lia). exact SA16.
  - clear - ROOM. unfold ffr in ROOM. unfold ff_room. lia.
  - intros f Hf. rewrite U2. specialize (RS f Hf). subst s; clear - RS. lia.
  - exact HK.
  - (* [comment removed for export] *)
    intros R2 M2 model2 F fl LK2 B10 RP2 (FS1 & FS2 & FAL & FAPP & FCEIL) FIMG FAPART FBLK LKI2 FDEF FLC FLP FLNC FLA FLW FSH PRES2 RT2 MI2 HH2.
    rewrite U2 in FLNC. rewrite U2 in PRES2. rewrite U2 in HH2. rewrite ?U2. rewrite r1, A1.
    pose proof (sm_facts L ar C HI LY HIok LB FF LK2 cr A M2 model2 F 1 (s - 128 + 32) fl HH2 ltac:(left; reflexivity) FS1 FS2 FAL FAPP FCEIL FDEF FLC FLP FLNC FLA FSH)
      as (FR & FFL & F32 & F8 & _ & FDEFv & FWv & FBIG & FSHW & FSHZ & FLCv & FLR & FLWv & FLBIG & VF & VSH & VFL).
    change (ff_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
    assert (Hh2 : m_halted model2 = None). { rewrite (L5LZ.model_rt_halted _ _ RT2). exact (proj1 AM1). }
    assert (ASTK2 : astk ar M2 sp ARESERVE_SCR).
    { apply (astk_after_rt L ar C HI HIok LB FF LK cr A M M1 M2 _ sp _ (s - 128) 512 HH STK MGM1 PRES2). unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; subst s; clear; lia. subst s; clear; lia. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
    pose proof (vis_pack L ar C HI LY HIok LB _ LK2 cr A M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & _).
    pose proof (statics_vis LB _ LK2 cr A M2 model2 HH2) as (IMGC2 & CSB2 & CUAR2).
    set (H2 := ahid A model2) in *. set (MV2 := mrestrict H2 M2) in *.
    (* [comment removed for export] *)
    assert (AG2 : forall a, s - 128 <= a < s + 16 -> MV2 (Z_to_bv 64 a) = M1v (Z_to_bv 64 a)).
    { intros a Ha. unfold MV2. rewrite (mrestrict_visible H2 M2). 2:{ replace a with ((s - 128) + (a - (s - 128))) by (clear; lia). apply (VIS2 (s - 128) 144). subst s; clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
      rewrite (proj1 PRES2 a). 2:{ clear - Ha SPR; lia. } 2:{ apply stack_client. subst s; clear - Ha SLO SHI SPT; lia. clear - Ha; lia. }
      rewrite <- VIS1. symmetry. apply mrestrict_visible. replace a with ((s - 128) + (a - (s - 128))) by (clear; lia). apply (VIS (s - 128) 144). subst s; clear - SLO; lia. clear - SPR; lia. clear - Ha; lia. }
    assert (W144b : L5.writable RSEGS MV2 (s - 128) 144).
    { eapply (L5C.writable_agree RSEGS M1v MV2). intros j Hj. apply AG2. clear - Hj; lia. clear - SPR; lia. clear - SPR; lia. eapply L5.writable_grows. exact MG1. exact W144. }
    (* [comment removed for export] *)
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl sp ARESERVE_SCR o 32 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC OCL ltac:(clear; lia)) as (OF & OFSH & OFL).
    pose proof (sm_apart L ar C HI LY HIok LB FF LK2 cr A M2 _ F 1 _ fl sp 0 (s - 128) 144 HH2 SPT ltac:(left; reflexivity)
                  ltac:(clear - FR; lia) FCEIL FAPP FAL FAPART FBLK FLNC
                  ltac:(intros i Hi; apply stack_client; subst s; clear - Hi SLO SHI SPT; lia) ltac:(clear; lia)) as (SF & SFSH & SFL).
    change (ff_bytes 1) with 128 in OF, SF. change (ff_bytes 1 / 8) with 16 in OFSH, SFSH.
    (* [comment removed for export] *)
    pose proof (arsB_conc fx1 R2 MV2 (fun j => match j with 2%nat => s | 33%nat => o | 34%nat => n | 40%nat => F | 41%nat => fl
                  | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R2 1 | 48%nat => U R 25 | _ => 0 end)) as P.
    cbn beta iota in P.
    assert (XC : forall a v, s - 112 <= a <= s + 8 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS MV2 a v).
    { intros a v Ha Hc. xfer AG2 Hc. }
    assert (RS2 : forall k, In k [18; 21; 22; 23; 24; 26]%nat -> getr R2 (reg k) = getr R (reg k)).
    { intros k Hk. rewrite (cs_of_preserved R1 R2 k RP2). apply KS1. revert Hk; apply (L5K.incl_b _ KS_arsA); vm_compute; reflexivity.
      revert Hk; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. }
    Local Ltac rw2 RS := rewrite ?(RS 18%nat), ?(RS 21%nat), ?(RS 22%nat), ?(RS 23%nat), ?(RS 24%nat), ?(RS 26%nat) by inl.
    feed P ltac:(first [apply UR | apply U_to | sc | (apply XC; [clear; lia | unfold U; rw2 RS2; sc]) ]).
    destruct P as (fx3 & R3 & M3v & MG3 & bFR & bFZ & (bMS & bKS & bR1 & bR10 & bR11 & bR12 & bR13 & bR14 & bR18 & bR23 & bR24 & bB_V40nat & bB_V40nat_1 & bB_V40nat_2 & bB_V40nat_3 & bB_V40nat_4 & bB_V40nat_5 & bB_V40nat_6 & bB_V40nat_7 & bB_V40nat_8 & bB_V40nat_9 & bB_V40nat_10 & bB_V40nat_11 & bQ_V40nat & bQ_V40nat_1 & bQ_V40nat_2 & bQ_V2nat & bQ_V2nat_1 & bQ_V2nat_2 & bQ_V2nat_3 & bQ_V2nat_4 & bQ_V2nat_5 & bQ_V2nat_6 & bQ_V2nat_7 & bQ_V2nat_8 & bQ_V2nat_9 & bQ_V2nat_10 & bQ_V2nat_11 & bQ_V2nat_12 & bDF)).
    rewrite (RS2 18%nat) in bQ_V2nat_4 by inl. rewrite (RS2 21%nat) in bQ_V2nat_7 by inl. rewrite (RS2 22%nat) in bQ_V2nat_8 by inl.
    rewrite (RS2 23%nat) in bQ_V2nat_9 by inl. rewrite (RS2 24%nat) in bQ_V2nat_10 by inl. rewrite (RS2 26%nat) in bQ_V2nat_12 by inl. (* [comment removed for export] *)
    apply (apiece L ar C HI LY HIok LB _ LK2 cr A M2 model2 fx1 fx3 R2 0x905b4 R3 ROUNDUP M3v
             (fun a => s - 128 <= a < s + 16 \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16) K HH2 (conj Hh2 MI2) bMS MG3).   (* [comment removed for export] *)
    { intros a Ha Hna. apply bFZ. exact Ha. all: clear - Hna; unfold SB in Hna; lia. }
    { intros a Ha [Wa|[Wa|Wa]].
      - split. apply stack_client. subst s; clear - Wa SLO SHI SPT; lia. clear; lia. subst s; clear - Wa SLO SPT; lia.
      - split. apply (fframe_client L ar LB _ 0 0 F 1 (s - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Wa; lia. clear - Wa FR; lia.
      - split. apply (fframe_shadow_client L ar LB _ 0 0 F 1 (s - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Wa F8. unfold SB in *. lia.
        clear - Wa FR; unfold SB in Wa; lia. }
    intros M3 model3 HH3 AM3 RT3 AH3 VIS3 MGM3 FRM3 EQ3.
    assert (ASTK3 : astk ar M3 sp ARESERVE_SCR). { eapply astk_grows. exact ASTK2. exact MGM3. }
    pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as WF2.
    assert (ND2 : NoDup (map ff_addr (((F, 1, s - 128 + 32) :: FF) ++ LK2))). { clear - WF2. decompose [and] WF2. assumption. }
    (* [comment removed for export] *)
    apply (RU fx3 R3 M3 model3 K LB ((F, 1, s - 128 + 32) :: FF) LK2 cr A n (sp - 144) 0x90664 HH3 AM3 HK).
    + rewrite r10. exact bR10.
    + clear - Hn; lia.
    + rewrite r1. exact bR1.
    + split. clear; lia. reflexivity.
    + rewrite r2. replace (sp - 144) with (s - 128) by (subst s; clear; lia). rk.
    + replace (sp - 144) with (s - 128) by (subst s; clear; lia). exact SA32'.
    + rewrite r4. rk.
    + apply (astk_sub ar M3 M3 sp ARESERVE_SCR 144 ROUNDUP_SCR ASTK3 (mem_grows_refl M3)). clear; lia. unfold ROUNDUP_SCR, SM_SCR; clear; lia.
      unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, ROUNDUP_SCR, SM_SCR; clear; lia. replace (sp - 144) with (s - 128) by (subst s; clear; lia). exact SA16.
    + apply (ffr_push FF LK LK2 (F, 1, s - 128 + 32) 3 2 ROOM LKI2 ND2). clear; lia. clear; lia.
    + apply (ffrs_push FF sp). exact RS. subst s; clear; lia. clear; lia.
    + (* [comment removed for export] *)
      intros fx4 R4 M4 model4 LK4 ruR10 RP4 PRES4 RT4 AM4 LKI4 HH4.
      assert (ASTK4 : astk ar M4 sp ARESERVE_SCR).
      { apply (astk_after L ar C HI HIok LB _ LK2 cr A M3 M3 M4 _ sp _ (sp - 144) ROUNDUP_SCR [] HH3 ASTK3 (mem_grows_refl M3) PRES4).
        unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, ROUNDUP_SCR, SM_SCR; clear; lia. clear; lia. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
      pose proof (vis_pack L ar C HI LY HIok LB _ LK4 cr A M4 model4 HH4) as (HOFF4 & VIS4 & _).
      pose proof (statics_vis LB _ LK4 cr A M4 model4 HH4) as (IMGC4 & CSB4 & CUAR4).
      set (H4 := ahid A model4) in *. set (MV4 := mrestrict H4 M4) in *.
      assert (W144d : L5.writable RSEGS MV4 (s - 128) 144).
      { apply (proj2 (writable_vis H4 M4 (s - 128) 144 (VIS4 (s - 128) 144 ltac:(subst s; clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
        eapply (astk_writable ar M4 sp). exact ASTK4. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. subst s; clear; lia. subst s; clear; lia. clear; lia. }
      assert (RUN : 8 <= round_up n <= n + 8 /\ round_up n <= 8388616).
      { unfold round_up. clear - Hn. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      (* [comment removed for export] *)
      pose proof (arsC_conc fx4 R4 MV4 (fun j => match j with 2%nat => s | 33%nat => o | 34%nat => n | 35%nat => round_up n | 40%nat => F | _ => 0 end)) as P.
      cbn beta iota in P.
      feed P ltac:(first [apply UR | apply U_to | sc]).
      destruct P as (fx5 & R5 & M5v & MG5 & cFR & cFZ & (cMS & cKS & cR1 & cR10 & cR11 & cR20)).
      apply (apiece_ro L ar C HI LY HIok LB _ LK4 cr A M4 model4 fx4 fx5 R4 0x90664 R5 L5BALC.ALLOC M5v K HH4 AM4 cMS MG5 cFZ).
      intros M5 model5 HH5 AM5 RT5 AH5 VIS5 MGM5 EQ5. pose proof (mem_eq_of_agree M4 M5 EQ5) as EM. subst M5.
      (* [comment removed for export] *)
      apply (L5BALC.alloc_ok L ar C HI LY HIok NEW fx5 R5 M4 model5 K LB ((F, 1, s - 128 + 32) :: FF) LK4 cr A (round_up n) (sp - 144) 0x90674 HH5 AM5 HK).
      * rewrite r11. exact cR11.
      * clear - RUN Hn; lia.
      * clear - RUN Hn; lia.
      * exact CR.
      * rewrite r1. exact cR1.
      * split. clear; lia. reflexivity.
      * rewrite r2. replace (sp - 144) with (s - 128) by (subst s; clear; lia). rk.
      * rewrite r4. rk.
      * apply (astk_sub ar M4 M4 sp ARESERVE_SCR 144 OPNEW_SCR ASTK4 (mem_grows_refl M4)). clear; lia. unfold OPNEW_SCR, MALLOC_SCR; clear; lia.
        unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. replace (sp - 144) with (s - 128) by (subst s; clear; lia). exact SA16.
      * (* [comment removed for export] *)
        intros fx6 R6 M6 model6 A6 q eR10 RP6 (BRq & BAq & FAq & DEFq & SHBq) PRES6 RT6 IA6 AM6 HH6.
        set (FF' := (F, 1, s - 128 + 32) :: FF) in *.
        assert (ASTK6 : astk ar M6 sp ARESERVE_SCR).
        { apply (astk_after L ar C HI HIok LB FF' LK4 cr A M4 M4 M6 _ sp _ (sp - 144) OPNEW_SCR [] HH5 ASTK4 (mem_grows_refl M4) PRES6).
          unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. }
        pose proof (vis_pack L ar C HI LY HIok _ FF' LK4 _ A6 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
        pose proof (statics_vis _ FF' LK4 _ A6 M6 model6 HH6) as (IMGC6 & CSB6 & CUAR6).
        set (H6 := ahid A6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
        pose proof (vis_pack L ar C HI LY HIok LB FF' LK2 cr A M2 model2 HH2) as (_ & _ & _ & _ & _ & _ & VFSSH2 & _).
        assert (OB' : aobj FF' o 32). { apply aobj_cons. exact OB. }
        pose proof (aobj_facts L ar C HI LY HIok _ FF' LK4 _ A6 M6 model6 o 32 0 0 HH6 OB' ltac:(clear; lia) ltac:(reflexivity))
          as (_ & _ & ODEF6 & OVIS6 & OVSH6 & OCL6 & OCLSH6). change (32 / 8) with 4 in OVSH6, OCLSH6.
        pose proof (aobj_facts L ar C HI LY HIok LB FF' LK2 cr A M2 model2 o 32 0 0 HH2 (aobj_cons FF _ o 32 OB) ltac:(clear; lia) ltac:(reflexivity))
          as (_ & _ & _ & OVIS2 & OVSH2 & _).  change (32 / 8) with 4 in OVSH2.
        pose proof (fl_writable L ar C HI LY HIok _ FF' LK4 _ A6 M6 _ fl HH6 FLP) as [FLD6 FLW6].
        pose proof (fl_vis L ar C HI LY HIok _ FF' LK4 _ A6 M6 model6 fl HH6 FLP) as FLV6.
        pose proof (BRq) as (Q0 & Q1 & Q2 & Q3 & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
        (* [comment removed for export] *)
        set (RNG := fun a => s - 128 <= a < s + 16 \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16 \/ o <= a < o + 32).
        assert (RCL : forall a, RNG a -> 0 <= a < 2 ^ 64 /\ aclientw L ar LB FF' 0 0 a /\ (a < ahl_ceil ar \/ s - 128 <= a < s + 16)).
        { intros a [Ra|[Ra|[Ra|Ra]]].
          - split. clear - Ra SPR; lia. split. apply stack_client. subst s; clear - Ra SLO SHI SPT; lia. clear; lia. right; exact Ra.
          - split. clear - Ra FR; lia. split. apply (fframe_client L ar LB FF' 0 0 F 1 (s - 128 + 32)). left; reflexivity. change (ff_bytes 1) with 128. clear - Ra; lia. left; clear - Ra FR; lia.
          - split. clear - Ra FR; unfold SB in *; lia. split. apply (fframe_shadow_client L ar LB FF' 0 0 F 1 (s - 128 + 32)). left; reflexivity.
            change (ff_bytes 1) with 128. unfold in_shadow_of, S. clear - Ra F8; unfold SB in *; lia. left. clear - Ra FR SPT; unfold SB in *; lia.
          - split. clear - Ra OR; lia. split. apply (obj_client L ar LB FF' 0 0 o 32 a OB'). exact Ra. left; clear - Ra OR; lia. }
        assert (AG36 : forall a, RNG a -> MV6 (Z_to_bv 64 a) = M3v (Z_to_bv 64 a)).
        { intros a Ra. destruct (RCL a Ra) as (Ha & Ca & Sa). apply aclientw_client in Ca.
          assert (V6 : H6 (Z_to_bv 64 a) = false).
          { destruct Ra as [Ra|[Ra|[Ra|Ra]]].
            - replace a with ((s - 128) + (a - (s - 128))) by (clear; lia). apply (VIS6 (s - 128) 144). subst s; clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
            - replace a with (F + (a - F)) by (clear; lia). apply (VFS6 F 128 FS1 FS2). clear - Ra; lia.
            - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VFSSH6 (F / 8 + SB) 16). 2: clear - Ra; lia.
              intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
            - replace a with (o + (a - o)) by (clear; lia). apply (OVIS6 (a - o)). clear - Ra; lia. }
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
          assert (V2 : ahid A model2 (Z_to_bv 64 a) = false).
          { destruct Ra as [Ra|[Ra|[Ra|Ra]]].
            - replace a with ((s - 128) + (a - (s - 128))) by (clear; lia). apply (VIS2 (s - 128) 144). subst s; clear - SLO; lia. clear - SPR; lia. clear - Ra; lia.
            - replace a with (F + (a - F)) by (clear; lia). apply (VFS2 F 128 FS1 FS2). clear - Ra; lia.
            - replace a with ((F / 8 + SB) + (a - (F / 8 + SB))) by (clear; lia). apply (VSH (a - (F / 8 + SB))). clear - Ra; lia.
            - replace a with (o + (a - o)) by (clear; lia). apply (OVIS2 (a - o)). clear - Ra; lia. }
          unfold MV6. rewrite (mrestrict_visible H6 M6) by exact V6.
          assert (NS : ~ (sp - 144 - OPNEW_SCR <= a < sp - 144) /\ ~ (sp - 144 - ROUNDUP_SCR <= a < sp - 144)).
          { unfold OPNEW_SCR, MALLOC_SCR, ROUNDUP_SCR, SM_SCR. subst s; clear - Sa SLO; lia. }
          rewrite (proj1 PRES6 a). 2:{ split. exact Ha. split. apply (aclient_narrow L ar LB FF' 0 0). exact Ca. exact (proj1 NS). intros rr [ ]. }
          rewrite (proj1 PRES4 a). 2:{ split. exact Ha. split. apply (aclient_narrow L ar LB FF' 0 0). exact Ca. exact (proj2 NS). intros rr [ ]. }
          apply EQ3. exact V2. }
        assert (XC6 : forall a v, (s - 112 <= a <= s + 8 \/ (F <= a <= F + 16 \/ F + 32 <= a <= F + 112) \/ o <= a <= o + 24) -> L5.u64_at RSEGS M3v a v -> L5.u64_at RSEGS MV6 a v).
        { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AG36. unfold RNG. clear - Ha Hj; lia. clear - Ha SPR FR OR; lia. clear - Ha SPR FR OR; lia. }
        assert (W144f : L5.writable RSEGS MV6 (s - 128) 144).
        { apply (proj2 (writable_vis H6 M6 (s - 128) 144 (VIS6 (s - 128) 144 ltac:(subst s; clear - SLO; lia) ltac:(clear - SPR; lia)) ltac:(clear - SPR; lia) ltac:(clear - SPR; lia))).
          eapply (astk_writable ar M6 sp). exact ASTK6. unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR. subst s; clear; lia. subst s; clear; lia. clear; lia. }
        pose proof (aio_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as (WB6 & WF6 & _).
        assert (FDEF6 : L5.defined MV6 F 128). { apply (proj2 (defined_vis H6 M6 F 128 (VFS6 F 128 FS1 FS2))). exact (proj1 (proj2 (proj2 (proj2 (proj2 (WF6 _ (or_introl eq_refl))))))). }
        assert (FW6 : L5.writable RSEGS MV6 F 128). { apply (L5C.writable_of_defined RSEGS). exact FDEF6. clear - FR; lia. clear - FR; lia. }
        assert (ODEF6v : L5.writable RSEGS MV6 o 32). { apply (L5C.writable_of_defined RSEGS). apply (proj2 (defined_vis H6 M6 o 32 OVIS6)). exact ODEF6. clear - OR; lia. clear - OR; lia. }
        assert (FLW6v : L5.writable RSEGS MV6 fl 1). { apply (proj2 (writable_vis H6 M6 fl 1 FLV6 ltac:(clear - FLR; lia) ltac:(clear - FLR; lia))). exact FLW6. }
        (* [comment removed for export] *)
        assert (D36 : dk L ar LB FF' sp ARESERVE_SCR M3 M6).
        { eapply dk_trans. apply (dk_callee L ar LB [] FF' [] sp ARESERVE_SCR (sp - 144) ROUNDUP_SCR [] M3 M4 PRES4). unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, ROUNDUP_SCR, SM_SCR; clear; lia. clear; lia.
          apply (dk_callee L ar LB [] FF' [] sp ARESERVE_SCR (sp - 144) OPNEW_SCR [] M4 M6 PRES6). unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. }
        assert (VSH6 : avis H6 (F / 8 + SB) 16).
        { apply VFSSH6. intros i Hi. unfold in_shadow_of, S. clear - Hi FS1 FS2 F8 FR. unfold FS_BYTES, SB in *.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        assert (FSHW6 : L5.writable RSEGS MV6 (F / 8 + SB) 16).
        { assert (Y1 : 0 <= F / 8 + SB) by (clear - FR F8; unfold SB; lia). assert (Y2 : F / 8 + SB + 16 <= 2 ^ 64) by (clear - FR F8; unfold SB; lia).
          apply (proj2 (writable_vis H6 M6 _ 16 VSH6 Y1 Y2)). apply (L5C.writable_of_defined RSEGS). 2: exact Y1. 2: exact Y2.
          intros i Hi. apply D36. clear - Hi Y1 Y2; lia.
          { apply aclientw_client. apply (aclient_narrow L ar LB FF' 0 0). exact (proj1 (proj2 (RCL (F / 8 + SB + i) ltac:(unfold RNG; clear - Hi; lia)))).
            assert (X : F / 8 + SB + 16 <= sp - ARESERVE_SCR) by (subst s; clear - FR F8 SLO SPT; unfold SB, ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; lia). clear - X Hi. lia. }
          rewrite (EQ3 (Z_to_bv 64 (F / 8 + SB + i))). 2:{ apply (VSH i). exact Hi. }
          apply MG3. eapply (L5KA.zeros_at_defined MV2 _ 16 FSHZ). exact Hi. }
        (* [comment removed for export] *)
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        assert (FQ15 : (F + 128 - 1) / 8 = F / 8 + 15 /\ F mod 8 = 0) by (clear - F8; lia).
        assert (QSH : SB <= q / 8 + SB /\ (q + 8 * round_up n - 1) / 8 + SB < 0x10007fff8000) by (clear - Q0 Q5 RUN; unfold SB; lia).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
        assert (NCF : forall a, (F <= a < F + 128 \/ S F <= a <= S (F + 128 - 1)) -> ~ aclient L ar LB FF sp ARESERVE_SCR a).
        { intros a Ha. apply (fresh_frame_not_client L ar C HI LY HIok LB FF LK cr A M _ sp ARESERVE_SCR F 128 a HH SPT).
          clear - FR; lia. exact FCEIL. exact FAPP. exact (proj2 FQ15). clear; lia. reflexivity.
          eapply fframes_apart_incl. exact FAPART. intros g Hg; apply in_or_app; left; exact Hg. exact FBLK. exact Ha. }
        (* [comment removed for export] *)
        assert (E06 : ek L ar LB FF sp ARESERVE_SCR [] M M6).
        { eapply ek_trans. { apply (ek_piece L ar LB FF sp ARESERVE_SCR [] M M1 (fun a => s - 128 <= a < s + 16) FRM1).
            intros a Ha Hc _ X. destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp ARESERVE_SCR a HH SPT Hc) as [Y|Y].
            subst s; clear - X Y; unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; lia. subst s; clear - X Y SLO; lia. }
          eapply ek_trans. { apply (ek_rt L ar LB FF [] sp ARESERVE_SCR (s - 128) 512 [] M1 M2 PRES2). subst s; unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. subst s; clear; lia. }
          eapply ek_trans. { apply (ek_piece L ar LB FF sp ARESERVE_SCR [] M2 M3 _ FRM3).
            intros a Ha Hc _ [X|[X|X]].
            - destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp ARESERVE_SCR a HH SPT Hc) as [Y|Y].
              subst s; clear - X Y; unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; lia. subst s; clear - X Y SLO; lia.
            - apply (NCF a). left. clear - X; lia. exact Hc.
            - apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc. }
          eapply ek_trans. { apply (ek_callee L ar LB [] FF [(F, 1, s - 128 + 32)] sp ARESERVE_SCR (sp - 144) ROUNDUP_SCR [] [] M3 M4 PRES4).
            unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, ROUNDUP_SCR, SM_SCR; clear; lia. clear; lia. intros a _ X; exact X. }
          apply (ek_callee L ar LB [] FF [(F, 1, s - 128 + 32)] sp ARESERVE_SCR (sp - 144) OPNEW_SCR [] [] M4 M6 PRES6).
          unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia. intros a _ X; exact X. }
        assert (AGO : forall a, (o <= a < o + 32 \/ o / 8 + SB <= a < o / 8 + SB + 4) -> MV6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
        { intros a Ha. unfold MV6. rewrite (mrestrict_visible H6 M6).
          2:{ destruct Ha as [Ha|Ha]. replace a with (o + (a - o)) by (clear; lia). apply (OVIS6 (a - o)). clear - Ha; lia.
              replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply (OVSH6 (a - (o / 8 + SB))). clear - Ha; lia. }
          apply E06. split. clear - Ha OR; unfold SB in Ha; lia. split. 2: intros rr [ ].
          destruct Ha as [Ha|Ha]. replace a with (o + (a - o)) by (clear; lia). apply OCL. clear - Ha; lia.
          replace a with (o / 8 + SB + (a - (o / 8 + SB))) by (clear; lia). apply OCLSH. clear - Ha; lia. }
        assert (XO6 : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS MV6 a v).
        { intros a v Ha Hc. eapply L5C.u64_at_agree. 4: exact Hc. intros j Hj. apply AGO. clear - Ha Hj; lia. clear - Ha OR; lia. clear - Ha OR; lia. }
        assert (OZ6 : L5KA.zeros_at MV6 (o / 8 + SB) 4).
        { intros i Hi. rewrite AGO. unfold shadow_zero, byte_at, S in SZ. apply SZ. exact Hi. clear - Hi; lia. }
        (* [comment removed for export] *)
        pose proof (flagptr_now L ar C HI LY HIok _ _ _ _ _ _ _ _ _ _ _ _ _ model6 F 1 _ _ fl HH2 HH6 (or_introl eq_refl) (or_introl eq_refl) (or_introl eq_refl) FLC) as [FLC6 FL6].
        change (ff_bytes 1) with 128 in FLC6, FL6. replace (F + 128 - 8) with (F + 120) in FLC6, FL6 by (clear; lia).
        (* [comment removed for export] *)
        pose proof (arsD_conc fx6 R6 MV6 (fun j => match j with 2%nat => s | 33%nat => o | 35%nat => round_up n | 36%nat => q | 40%nat => F | 41%nat => fl
                      | 42%nat => U R 1 | 43%nat => U R 8 | 44%nat => U R 9 | 45%nat => U R 19 | 46%nat => U R 20 | 47%nat => U R6 1 | 48%nat => U R 25
                      | 49%nat => U R 18 | 50%nat => U R 24 | 51%nat => U R 23 | _ => 0 end)) as P.
        cbn beta iota in P.
        assert (RS6 : forall k, In k [21; 22; 26]%nat -> getr R6 (reg k) = getr R (reg k)).
        { intros k Hk. destruct Hk as [<-|[<-|[<-|[]]]]; rk. }
        Local Ltac rw6 RS := rewrite ?(RS 21%nat), ?(RS 22%nat), ?(RS 26%nat) by inl.
        feed P ltac:(first [apply UR | apply U_to | sc | (apply XC6; [clear; lia | unfold U; rw6 RS6; sc]) | (apply XO6; [clear; lia | sc]) | exact FL6 ]).
        destruct P as (fx7 & R7 & M7v & MG7 & dFR & dFZ & (dMS & dKS & dR1 & dR2 & dR8 & dR9 & dR10 & dR11 & dR12 & dR18 & dR19 & dR20 & dR23 & dR24 & dR25 & dB_V41nat & dB_V40nat & dB_V40nat_1 & dB_V40nat_2 & dB_V40nat_3 & dB_V40nat_4 & dB_V40nat_5 & dB_V40nat_6 & dB_V40nat_7 & dB_V40nat_8 & dB_V40nat_9 & dB_V40nat_10 & dB_V40nat_11 & dB_V40nat_12 & dB_V40nat_13 & dB_V40nat_14 & dB_V40nat_15 & dQ_V40nat & dQ_V33nat & dQ_V33nat_1 & dDF)).
        assert (UR1 : U R 1 = r). { apply (U_of R 1 r). rewrite <- r1. exact G1. destruct RA as [X _]. clear - X; lia. }
        pose proof (ret_to fx7 R7 M7v 0x907e4 W_907e4 r F_907e4 eq_refl D_907e4 ltac:(rewrite dR1, UR1; reflexivity) (proj1 RA) (proj2 RA)) as RET.
        pose proof (msteps_trans _ _ _ _ dMS RET) as MS8. clear dMS RET.
        set (W7 := fun a => (s - 128 <= a < s + 16 \/ (F <= a < F + 24 \/ F + 32 <= a < F + 120) \/ F / 8 + SB <= a < F / 8 + SB + 16) \/ a = fl \/ o + 16 <= a < o + 32).
        apply (apiece_retire L ar C HI LY HIok _ FF LK4 _ A6 M6 model6 fx6 fx7 R6 0x90674 R7 r M7v W7 F 1 (s - 128 + 32) fl K HH6 AM6).
        { change (ff_bytes 1) with 128. replace (F + 128 - 8) with (F + 120) by (clear; lia).
          exact FLC6. }
        { intros X. destruct (aclient_consb_inv L ar LB FF' _ 0 0 fl X) as [Y|[Y|Y]]. exact (FLNC Y).
          - cbn [fst snd] in Y. pose proof (WB6 (q, 8 * round_up n) (or_introl eq_refl)) as Z6. cbn [fst snd] in Z6.
            destruct Z6 as (_ & _ & _ & _ & _ & _ & Z7). clear - Y FLP Z7. unfold FS_BYTES in *. lia.
          - cbn [fst snd] in Y. unfold in_shadow_of, S in Y. clear - Y FLBIG QSH. unfold SB in *. lia. }
        { exact FLV6. }
        { clear - FLR; lia. }
        { exact MS8. }
        { exact MG7. }
        { intros a Ha Hna. apply dFZ. exact Ha. all: clear - Hna; subst W7; cbn beta in Hna; unfold SB in *; lia. }
        { intros a Ha Wa. subst W7; cbn beta in Wa. destruct Wa as [Wa|[Wa|Wa]].
          - right. apply aclient_consb. exact (proj1 (proj2 (RCL a ltac:(unfold RNG; clear - Wa; tauto)))).
          - left; exact Wa.
          - right. apply aclient_consb. apply (obj_client L ar LB FF' 0 0 o 32 a OB'). clear - Wa; lia. }
        { intros a. subst W7; cbn beta. repeat match goal with X : _ |- _ => clear X end.
          destruct (rng_dec a (s - 128) (s + 16)); [left; tauto|]. destruct (rng_dec a F (F + 24)); [left; tauto|]. destruct (rng_dec a (F + 32) (F + 120)); [left; tauto|].
          destruct (rng_dec a (F / 8 + SB) (F / 8 + SB + 16)); [left; tauto|]. destruct (Z.eq_dec a fl); [left; tauto|]. destruct (rng_dec a (o + 16) (o + 32)); [left; tauto|]. right; tauto. }
        { exact dB_V41nat. }
        intros M7 model7 HH7 AM7 RT7 AH7 VIS7 MGM7 FRM7 EQ7.
        assert (ASTK7 : astk ar M7 sp ARESERVE_SCR). { eapply astk_grows. exact ASTK6. exact MGM7. }
        apply (KONT fx7 R7 M7 model7 LK4 A6 q).
        -- (* [comment removed for export] *)
           apply preserved_by_index. intros k Hk. cbn in Hk.
           destruct Hk as [<-|Hk]. { rewrite dR2. rewrite <- r2, G2. f_equal. subst s; clear; lia. }
           destruct Hk as [<-|Hk]. { rk. }
           destruct Hk as [<-|Hk]. { rk. }
           destruct Hk as [<-|Hk]. { rewrite dR8. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rewrite dR9. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rewrite dR18. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rewrite dR19. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rewrite dR20. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rk. }
           destruct Hk as [<-|Hk]. { rk. }
           destruct Hk as [<-|Hk]. { rewrite dR23. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rewrite dR24. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rewrite dR25. symmetry. apply U_to. }
           destruct Hk as [<-|Hk]. { rk. }
           destruct Hk as [<-|Hk]. { rk. }
           destruct Hk.
        -- (* [comment removed for export] *)
           split. exact BRq. split. exact BAq. split. { eapply fframes_apart_tl. exact FAq. }
           split. { eapply L5.defined_grows. exact MGM7. exact DEFq. }
           destruct SHBq as [SZq _]. split. 2:{ intros X. exfalso. apply X. clear. rewrite Z.mul_comm. apply Z_mod_mult. }
           replace (8 * round_up n / 8) with (round_up n) in SZq |- * by (clear; rewrite Z.mul_comm, Z_div_mult; [reflexivity|lia]).
           intros j Hj. unfold byte_at. rewrite FRM7. apply SZq. exact Hj. unfold S; clear - Hj QSH RUN; unfold SB in *. 
           { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
           Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
           (* [comment removed for export] *)
           assert (FQA : q + 8 * round_up n <= F \/ F + 128 <= q). { apply (FAq (F, 1, s - 128 + 32)). left; reflexivity. }
           Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
           assert (SHJ : SB <= S q + j < 0x10007fff8000 /\ (S q + j + 1 <= F / 8 + SB \/ F / 8 + SB + 16 <= S q + j)).
           { unfold S. clear - Hj QSH RUN FQA F8 Q2. unfold SB in *. lia. }
           Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
           subst W7; cbn beta. clear - SHJ SPR FR FBIG FLR FLBIG OR OBIG SLO SPT. unfold SB in *. subst s. lia.
        -- (* [comment removed for export] *)
           assert (OV8 : forall a v, o <= a <= o + 24 -> L5.u64_at RSEGS M7v a v -> L5.u64_at RSEGS M7 a v).
           { intros a v Ha Hc. apply (proj1 (u64_at_vis H6 M7 a v ltac:(eapply avis_sub; [exact OVIS6 | clear - Ha; lia | clear - Ha; lia]) ltac:(clear - Ha OR; lia) ltac:(clear - Ha OR; lia))).
             unfold H6. rewrite <- AH7. rewrite AH7. rewrite VIS7. exact Hc. }
           split. apply OV8. clear; lia. exact dQ_V33nat_1. apply OV8. clear; lia. exact dQ_V33nat.
        -- (* [comment removed for export] *)
           apply ahpres_of.
           ++ intros a (Ha & Hc & Ho). rewrite <- (E06 a). 2:{ split. exact Ha. split. exact Hc. intros rr [ ]. }
              apply FRM7. exact Ha. subst W7; cbn beta. intros [[X|[X|X]]|[X|X]].
              ** destruct (aclient_cases L ar C HI LY HIok LB FF LK cr A M _ sp ARESERVE_SCR a HH SPT Hc) as [Y|Y].
                 subst s; clear - X Y; unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR in Y; lia. subst s; clear - X Y SLO; lia.
              ** apply (NCF a). left. clear - X; lia. exact Hc.
              ** apply (NCF a). right. unfold S. rewrite (proj1 FQ15). clear - X. unfold SB in X |- *. lia. exact Hc.
              ** subst a. apply FLNC. apply aclient_cons. eapply aclient_00. exact Hc.
              ** apply (Ho (o + 16, 16)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. clear - X; lia.
           ++ eapply astk_defined. exact ASTK7. clear; lia. clear; lia.
           ++ eapply dk_trans. apply dk_grows. exact MGM1.
              eapply dk_trans. apply (dk_rt L ar LB FF [] sp ARESERVE_SCR (s - 128) 512 M1 M2 PRES2). subst s; unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. subst s; clear; lia.
              eapply dk_trans. apply dk_grows. exact MGM3.
              eapply dk_trans. apply (dk_callee L ar LB [] FF [(F, 1, s - 128 + 32)] sp ARESERVE_SCR (sp - 144) ROUNDUP_SCR [] M3 M4 PRES4).
              unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR, ROUNDUP_SCR, SM_SCR; clear; lia. clear; lia.
              eapply dk_trans. apply (dk_callee L ar LB [] FF [(F, 1, s - 128 + 32)] sp ARESERVE_SCR (sp - 144) OPNEW_SCR [] M4 M6 PRES6).
              unfold ARESERVE_SCR, OPNEW_SCR, MALLOC_SCR; clear; lia. clear; lia.
              apply dk_grows. exact MGM7.
        -- eapply L5LZ.model_rt_trans. exact RT1. eapply L5LZ.model_rt_trans. exact RT2. eapply L5LZ.model_rt_trans. exact RT3.
           eapply L5LZ.model_rt_trans. exact RT4. eapply L5LZ.model_rt_trans. exact RT5. eapply L5LZ.model_rt_trans. exact RT6. exact RT7.
        -- exact IA6.
        -- exact AM7.
        -- eapply incl_tran. exact LKI4. exact LKI2.
        -- exact HH7.
Qed.

End WithIface.
End SCFG_1.
End L5AARS.
