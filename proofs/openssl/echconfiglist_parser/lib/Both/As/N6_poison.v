(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_rip N6_quick N6_memset F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition poison_entry := 0x1c06e0%Z.
Definition ACF_CLRTHR_CELL : Z := 0x73c4a0.   (* [comment removed for export] *)

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (addr size v lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(sh addr, sh addr + size / 8); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (sh addr) [CB (Z.to_nat (size / 8)) (poison_bytes (Z.to_nat (size / 8)) v)]
    /\ ACONST m'.

Lemma ACONST_layout_poison : forall m, ACONST m ->
  rw_cells asegs m ACANPOISON_CELL [C1 (b8 1)] /\ rw_cells asegs m AGOT_MEMSETP [C8 (wz AMEMSETP_CELL)] /\
  rw_cells asegs m AMEMSETP_CELL [C8 (wz AREAL_MEMSET)] /\ rw_cells asegs m AGOT_CFLAGS [C8 (wz 0x73c428)].
Proof. intros m AC. repeat split; (eapply ACONST_cell; [exact AC| in_nth]). Qed.

Section POISON.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size v lo : Z) (junk : list byte).
  Hypothesis AL : addr mod 8 = 0 /\ size mod 8 = 0 /\ 8 <= size /\ size / 8 < 65536.
  Hypothesis HV : 0 <= v < 256.
  Hypothesis RNG : AHI_LO <= addr /\ addr + size <= AAPP_HI.
  Hypothesis SHJ : rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk].
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + 64 <= bv_unsigned sp.
  Hypothesis CEIL : AHI_LO <= lo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis THR : rw_cells asegs m ACF_CLRTHR_CELL [C8 (Z_to_bv 64 18446744073709551615)].   (* [comment removed for export] *)

  Notation POST := (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m).

  Lemma poison_body :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 poison_entry) fc None m (seg_rom asegs)).
  Proof.
    unfold poison_entry. unfold ACF_CLRTHR_CELL in THR.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_poison m AC) as (C5 & G6 & C6 & G7).
    unfold ACANPOISON_CELL, AGOT_MEMSETP, AMEMSETP_CELL, AREAL_MEMSET, AGOT_CFLAGS, wz in C5, G6, C6, G7.
    change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof RNG as RNG'. unfold AHI_LO, AAPP_HI in RNG. unfold AHI_LO in CEIL.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (sh_range_app addr ltac:(unfold AAPP_HI; lia)) as SR. unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR.
    pose proof (rw_cells_bound _ _ _ _ SHJ) as SB. cbn [cells_size csize Nat.add] in SB.
    assert (SRS : sh addr + size / 8 <= 17594333495296).
    { unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(sh addr, sh addr + size / 8); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 64%nat ST.
    do 8 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (J : forall x13 : word,
      evt asegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v)
                             x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x1c0714) fc None mc (seg_rom asegs))) end.
    { intros x13.
      zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite land_7 in K0; lia|].
      do 7 zstep.
      replace (Z.land (Z.land (Z.b2z (2147450880 <? 2147450879) + -1) 18446744073709551615) 2147450879)
        with 2147450879 by reflexivity.
      zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
      do 7 zstep. replace (0 + -1) with (-1) by reflexivity.
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      do 5 zstep. change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
      zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
      zstep. if_cases K4; zify_cond K4; [| exfalso; lia].
      (* [comment removed for export] *)
      do 3 zstep. change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
      zstep. if_cases K5; zify_cond K5; [exfalso; lia|].
      zstep. if_cases K6; zify_cond K6; [| exfalso; lia].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K0'; zify_cond K0'; [exfalso; rewrite land_7 in K0'; lia|].
      do 2 zstep.
      zstep. if_cases K7; zify_cond K7; [exfalso; lia|].
      do 7 zstep. replace (0 + -1) with (-1) by reflexivity.
      zstep. if_cases K8; zify_cond K8; [| exfalso; lia].
      do 5 zstep. change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
      zstep. if_cases K9; zify_cond K9; [exfalso; lia|].
      zstep. if_cases K10; zify_cond K10; [exfalso; lia|].
      (* [comment removed for export] *)
      do 3 zstep.
      zstep. if_cases K11; [exfalso; revert K11; vm_compute; discriminate|].
      do 5 zstep.
      rewrite shr3_sh by lia.
      replace (Z.land ((addr + size + -8) ≫ 3 + 1) 18446744073709551615 - addr ≫ 3) with (size / 8).
      2:{ rewrite land_ones64, !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
          rewrite Z.mod_small by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      assert (SHJ' : rw_cells asegs m0 (bv_unsigned (Z_to_bv 64 (sh addr))) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 (size / 8)))) junk]).
      { rewrite !unsigned_lit by lia. exact SHJ. }
      zstep. if_cases K12; zify_cond K12.
      - do 12 zstep.
        call2 memset_spec; try eassumption.
        release_frame FR ST (bv_unsigned sp);
        match goal with H : munch _ m ?m' |- _ =>
          assert (AC' : ACONST m')
            by (eapply ACONST_frame; [exact AC | exact H | eassumption |];
                constructor; [| constructor; [|constructor]];
                apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val in *; try lia;
                Z.div_mod_to_equations; lia) end;
        match goal with H : rw_cells asegs _ (sh addr) _ |- _ => rewrite (Z.mod_small v 256) in H by lia end;
        apply evt_done; unfold poison_post; do 16 eexists; split; [reflexivity|];
        split; [ match goal with H : munch _ m _ |- _ => first [exact H | replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact H] end |];
        repeat match goal with |- _ /\ _ => split end; try assumption.
      - do 3 zstep. zstep. if_cases K13; zify_cond K13; [| exfalso; lia].
        do 12 zstep.
        call2 memset_spec; try eassumption.
        release_frame FR ST (bv_unsigned sp);
        match goal with H : munch _ m ?m' |- _ =>
          assert (AC' : ACONST m')
            by (eapply ACONST_frame; [exact AC | exact H | eassumption |];
                constructor; [| constructor; [|constructor]];
                apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val in *; try lia;
                Z.div_mod_to_equations; lia) end;
        match goal with H : rw_cells asegs _ (sh addr) _ |- _ => rewrite (Z.mod_small v 256) in H by lia end;
        apply evt_done; unfold poison_post; do 16 eexists; split; [reflexivity|];
        split; [ match goal with H : munch _ m _ |- _ => first [exact H | replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact H] end |];
        repeat match goal with |- _ /\ _ => split end; try assumption. }
    (* [comment removed for export] *)
    zstep. if_cases KV; zify_cond KV.
    - apply J.
    - do 3 zstep. zstep. if_cases KC; [exfalso; revert KC; vm_compute; discriminate|]. apply J.
  Qed.
End POISON.
(* [comment removed for export] *)
Section POISON_LOW.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size v lo : Z) (junk : list byte).
  Hypothesis AL : addr mod 8 = 0 /\ size mod 8 = 0 /\ 8 <= size /\ size / 8 < 65536.
  Hypothesis HV : 0 <= v < 256.
  Hypothesis RNG : AIMG_TOP <= addr /\ addr + size <= ALOWSH_LO.
  Hypothesis SHJ : rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk].
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + 64 <= bv_unsigned sp.
  Hypothesis CEIL : AHI_LO <= lo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis THR : rw_cells asegs m ACF_CLRTHR_CELL [C8 (Z_to_bv 64 18446744073709551615)].   (* [comment removed for export] *)

  Notation POST := (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m).

  Lemma poison_body_low :
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 poison_entry) fc None m (seg_rom asegs)).
  Proof.
    unfold poison_entry. unfold ACF_CLRTHR_CELL in THR.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    destruct (ACONST_layout_poison m AC) as (C5 & G6 & C6 & G7).
    unfold ACANPOISON_CELL, AGOT_MEMSETP, AMEMSETP_CELL, AREAL_MEMSET, AGOT_CFLAGS, wz in C5, G6, C6, G7.
    change (b8 1) with (Z_to_bv 8 1) in C5.
    pose proof RNG as RNG'. unfold AIMG_TOP, ALOWSH_LO in RNG. unfold AHI_LO in CEIL.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (sh_range_app addr ltac:(unfold AAPP_HI; lia)) as SR. unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR.
    pose proof (rw_cells_bound _ _ _ _ SHJ) as SB. cbn [cells_size csize Nat.add] in SB.
    assert (SRS : sh addr + size / 8 <= 0x8fff6e00).
    { unfold sh. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    pose proof (munch_refl [(sh addr, sh addr + size / 8); (bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof ST0 as ST. carve_frame 64%nat ST.
    do 8 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (J : forall x13 : word,
      evt asegs POST (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v)
                             x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x1c0714) fc None mc (seg_rom asegs))) end.
    { intros x13.
      zstep. zstep. if_cases K0; zify_cond K0; [exfalso; rewrite land_7 in K0; lia|].
      do 7 zstep.
      replace (Z.land (Z.land (Z.b2z (2147450880 <? 2147450879) + -1) 18446744073709551615) 2147450879)
        with 2147450879 by reflexivity.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
      (* [comment removed for export] *)
      zstep. zstep. if_cases K0'; zify_cond K0'; [exfalso; rewrite land_7 in K0'; lia|].
      do 2 zstep.
      (* [comment removed for export] *)
      zstep. if_cases K7; zify_cond K7; [| exfalso; lia].
      (* [comment removed for export] *)
      do 3 zstep.
      zstep. if_cases K11; [exfalso; revert K11; vm_compute; discriminate|].
      do 5 zstep.
      rewrite shr3_sh by lia.
      replace (Z.land ((addr + size + -8) ≫ 3 + 1) 18446744073709551615 - addr ≫ 3) with (size / 8).
      2:{ rewrite land_ones64, !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
          rewrite Z.mod_small by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
      assert (SHJ' : rw_cells asegs m0 (bv_unsigned (Z_to_bv 64 (sh addr))) [CB (Z.to_nat (bv_unsigned (Z_to_bv 64 (size / 8)))) junk]).
      { rewrite !unsigned_lit by lia. exact SHJ. }
      zstep. if_cases K12; zify_cond K12.
      - do 12 zstep.
        call2 memset_spec; try eassumption.
        release_frame FR ST (bv_unsigned sp);
        match goal with H : munch _ m ?m' |- _ =>
          assert (AC' : ACONST m')
            by (eapply ACONST_frame; [exact AC | exact H | eassumption |];
                constructor; [| constructor; [|constructor]];
                apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val in *; try lia;
                Z.div_mod_to_equations; lia) end;
        match goal with H : rw_cells asegs _ (sh addr) _ |- _ => rewrite (Z.mod_small v 256) in H by lia end;
        apply evt_done; unfold poison_post; do 16 eexists; split; [reflexivity|];
        split; [ match goal with H : munch _ m _ |- _ => first [exact H | replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact H] end |];
        repeat match goal with |- _ /\ _ => split end; try assumption.
      - do 3 zstep. zstep. if_cases K13; zify_cond K13; [| exfalso; lia].
        do 12 zstep.
        call2 memset_spec; try eassumption.
        release_frame FR ST (bv_unsigned sp);
        match goal with H : munch _ m ?m' |- _ =>
          assert (AC' : ACONST m')
            by (eapply ACONST_frame; [exact AC | exact H | eassumption |];
                constructor; [| constructor; [|constructor]];
                apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP in *; rewrite ?ASHADOW_BASE_val in *; try lia;
                Z.div_mod_to_equations; lia) end;
        match goal with H : rw_cells asegs _ (sh addr) _ |- _ => rewrite (Z.mod_small v 256) in H by lia end;
        apply evt_done; unfold poison_post; do 16 eexists; split; [reflexivity|];
        split; [ match goal with H : munch _ m _ |- _ => first [exact H | replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact H] end |];
        repeat match goal with |- _ /\ _ => split end; try assumption. }
    (* [comment removed for export] *)
    zstep. if_cases KV; zify_cond KV.
    - apply J.
    - do 3 zstep. zstep. if_cases KC; [exfalso; revert KC; vm_compute; discriminate|]. apply J.
  Qed.
End POISON_LOW.

(* [comment removed for export] *)
Definition app_rng (a b : Z) : Prop := (AHI_LO <= a /\ b <= AAPP_HI) \/ (AIMG_TOP <= a /\ b <= ALOWSH_LO).

Lemma app_rng_sub : forall a b a' b', app_rng a b -> a <= a' -> b' <= b -> app_rng a' b'.
Proof. intros a b a' b' H ? ?. unfold app_rng in *. lia. Qed.

Lemma app_rng_of_aapp {HCEIL : HeapCeil} : forall A n a b, aapp A n -> A <= a -> b <= A + n -> app_rng a b.
Proof. intros A n a b H ? ?. acb. unfold aapp, aapp_lo, aapp_hi, app_rng, AAPP_HI in *. lia. Qed.

Lemma poison_body_app :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (addr size v lo : Z) (junk : list byte),
  addr mod 8 = 0 /\ size mod 8 = 0 /\ 8 <= size /\ size / 8 < 65536 ->
  0 <= v < 256 ->
  app_rng addr (addr + size) ->
  rw_cells asegs m (sh addr) [CB (Z.to_nat (size / 8)) junk] ->
  stk asegs m lo (bv_unsigned sp) ->
  lo + 64 <= bv_unsigned sp ->
  AHI_LO <= lo ->
  mem_inv asegs m ->
  ACONST m ->
  rw_cells asegs m ACF_CLRTHR_CELL [C8 (Z_to_bv 64 18446744073709551615)] ->
  evt asegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size v lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 v) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 poison_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros AL HV [RNG|RNG]; intros; [eapply poison_body | eapply poison_body_low]; eassumption.
Qed.
