(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition alloc_sec_t1_post (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (W : list ivl)
    (lo size a msz needed q8 r8 SO TH id pa nch : Z) (TSD CTX sb : Z) (T : list Z) (rest : list word) (d' : depot)
    (AFRm : mem -> list byte -> Prop) : machine_state -> Prop :=
  fun ms' => exists (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j8 sbsU : list byte) (ob0 gb : byte) (hb1 t8 : Z) m',
    ms' = MS (mkR (wz 0x1972b4) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz (msz - 4096)) (wz size) (wz (a + 6144)) (wz (8 * q8)) (wz 0) x13 x14 x15 x16 x17
                  (wz (a + 4096)) (wz needed) (wz (a + 6144)) (wz (a + 6128)) (wz (8 * q8)) (wz SO) (wz 0) (wz (a + 6144 + size + 7)) (wz TH) (wz 1) x28 x29 x30 x31)
             F (Z_to_bv 64 0x1c06e0) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ AENV tp TSD CTX TH sb SO T rest m' /\ AFRm m' j8 /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m' (a + 6128) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ 0 <= hb1 < 256 /\ b1_ok (Z.land hb1 243)
    /\ stk asegs m' (a + 4096) (a + 6128) /\ stk asegs m' (a + 6144) (a + msz)
    /\ u8arr asegs m' (sh (a + 4096)) (repeat (b8 0xfa) 256)
    /\ u8arr asegs m' (sh (a + 6144)) sbsU /\ Z.of_nat (length sbsU) = q8
    /\ rw_cells asegs m' (sh (a + 6144) + q8) [C1 gb] /\ (r8 = 0 -> gb = b8 0xfa)
    /\ u8arr asegs m' (sh (a + 6144) + q8 + 1) (repeat (b8 0xfa) (Z.to_nat t8)) /\ t8 = sh (a + msz) - (sh (a + 6144) + q8 + 1)
    /\ rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs d' m'.
End HCW.

Section SecTail1.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo size SO : Z) (T : list Z) (rest : list word) (d : depot) (TSD CTX TH sb pa nch : Z).
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).   (* [comment removed for export] *)
  Variables (a msz needed q8 r8 nT id : Z).
  Hypothesis DEFS : hidden (needed = round_up (Z.max size 8) 8 + 4096 /\ msz = round_up needed 4096 + 4096 /\ size = 8 * q8 + r8
                            /\ nT = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, bv_unsigned sp) :: (a + 4096, a + msz) :: (sh (a + 4096), sh (a + msz)) :: (TH + 2800, TH + 3168) :: depot_W d.
  Let W2 : list ivl := [(lo, bv_unsigned sp); (a + 4096, a + msz); (sh (a + 4096), sh (a + msz)); (TH + 2800, TH + 3168)]%Z.
  Let AFR := aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 768 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 64512 < size < 2^32. Hypothesis R8 : 0 <= r8 < 8.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX)).
  Hypothesis SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  (* [comment removed for export] *)
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (a + msz <= d_nb d \/ d_nb d + 16 * 65536 <= a) /\ (a + msz <= d_sb d \/ d_sb d + 8 * 131072 <= a)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis NR : 1 <= nT <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + nT + 1 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.

  Let ARE : 12599296 <= a /\ a + msz <= aceil.   (* [comment removed for export] *)
  Proof. destruct DEFS as [(DN & DM & _)]. refine (aapp_env _ _ (proj1 AR) _). rewrite DM, DN. unfold round_up. clear. Z.div_mod_to_equations. lia. Qed.
  Ltac prep :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DNEED & DMSZ & DSZ & DNT & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12599296 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil   (* [comment removed for export] *)
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp <= SO /\ SO + 2064 <= 140737488355328
               /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil /\ 12599296 <= d_nb d /\ 12599296 <= d_sb d)
      by (clear - LO RNG ARE TPR SOR SBR PLCD; try acb; destruct RNG as [RNG']; destruct TPR as [TPR']; destruct SOR as [SOR']; destruct SBR as [SBR']; destruct PLCD as [PLCD'];
          unfold AHI_LO, AIMG_TOP, kSpaceSize in *;
          acb; change (2^47)%Z with 140737488355328%Z in SOR'; aunf; lia);
        region_sides; name_bands;
    assert (GEO : size + 8 <= needed - 4088 /\ needed <= size + 4096 + 8 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ 8 * q8 <= size /\ size < 8 * q8 + 8
                  /\ needed = 8 * q8 + (if r8 =? 0 then 0 else 8) + 4096)
      by (clear - DNEED DMSZ DSZ SZ R8; try acb; subst needed msz; unfold round_up; destruct (Z.eqb_spec r8 0); Z.div_mod_to_equations; nia);
    assert (ALN : exists thq aq mq, TH = 16 * thq /\ a = 4096 * aq /\ msz = 4096 * mq)
      by (clear - RNG AR DMSZ; try acb; destruct RNG as [RNG']; exists (TH / 16), (a / 4096), (msz / 4096); subst msz; unfold round_up; Z.div_mod_to_equations; aunf; lia);
    destruct ALN as (thq & aq & mq & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (SHR : 2148314624 <= sh (a + 4096) /\ sh (a + msz) <= 17594333495296 /\ sh (a + 4096) = sh a + 512 /\ sh (a + msz) = sh a + 512 * mq
                  /\ sh (a + 6144) = sh a + 768)
      by (clear - BND ALN; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    clear DNEED DMSZ.

  Ltac solve_depot_avoid ::=
    unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
    repeat split;
    repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; region_decide |]]).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aenv_sec1_now : forall m0 m1, AENV tp TSD CTX TH sb SO T rest m0 -> munch W m0 m1 -> wmono asegs m0 m1 -> AENV tp TSD CTX TH sb SO T rest m1.
  Proof.
    intros m0 m1 E MU0 WM0. unfold W, depot_W in MU0. prep. open_env E. region_table.
    lazymatch goal with MUh : munch ?W0 _ _ |- _ => region_hull_memo W0 end.   (* [comment removed for export] *)
    econstructor; unfold AGOT_VALS; cbn [map repeat];
      first [ eapply rw_cells_transport; [eassumption| exact MU0| exact WM0| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; region_decide]
            | eapply u64arr_transport; [eassumption| exact MU0| exact WM0| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; region_decide] ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_sec_t1c : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mX : mem) (j8 : list byte) (ob0 : byte) (hb1 nd8 : Z),
    needed = 8 * nd8 ->
    AENV tp TSD CTX TH sb SO T rest mX -> mem_inv asegs mX ->
    AFR mX j8 -> stk asegs mX lo (bv_unsigned sp + -128) ->
    rw_cells asegs mX (a + 6128) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] -> 0 <= hb1 < 256 -> b1_ok (Z.land hb1 243) ->
    stk asegs mX (a + 4096) (a + 6128) -> stk asegs mX (a + 6144) (a + msz) ->
    rw_cells asegs mX (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)] ->
    rw_cells asegs mX a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)] ->
    stk asegs mX (sh (a + 4096)) (sh (a + 4096) + nd8) ->
    u8arr asegs mX (sh (a + 4096) + nd8) (repeat (b8 0xfa) (Z.to_nat ((msz - 4096 - needed) / 8))) ->
    stk asegs mX (TH + 2800) (TH + 3168) ->
    DEPOT asegs (d_put d (depot_hash T) nT) mX ->
    evt asegs (alloc_sec_t1_post sp gp tp F fc mX W lo size a msz needed q8 r8 SO TH id pa nch TSD CTX sb T rest (d_put d (depot_hash T) nT) AFR)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 0) (wz size) (wz sb) x11 x12 x13 x14 x15 x16 x17
               (wz (a + 4096)) (wz needed) (wz (a + 6144)) (wz (a + 6128)) (wz AINST) (wz SO) (wz 0) (wz (a + 6144 + size)) (wz TH) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x197214) fc None mX (seg_rom asegs)).
  Proof.
    intros until nd8. intros ND1 ENV MI FR ST HDR HB1R HB1M CHL USR INST64 LHDR SHJ SHT TST DEPN.
    prep. pose proof ENV as ENV0. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold AINST in *.
    change (6976152 + 64) with 6976216 in *.
    pose proof (munch_refl W mX) as MU. pose proof (wmono_refl asegs mX) as WM. unfold W, depot_W in MU.
    assert (ND : (msz - 4096 - needed) / 8 = 512 * mq - 512 - nd8 /\ nd8 = q8 + (if r8 =? 0 then 0 else 1) + 512)
      by (clear - GEO ALN ND1; try acb; destruct (r8 =? 0); Z.div_mod_to_equations; lia).
    destruct ND as [ND3 ND4]. rewrite ND3 in SHT.
    assert (SHTN : Z.of_nat (length (repeat (b8 250) (Z.to_nat (512 * mq - 512 - nd8)))) = 512 * mq - 512 - nd8) by (rewrite repeat_length; clear - GEO ALN ND4 R8; try acb; destruct (r8 =? 0); lia).
    region_table.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit (a + 4096)) by lia.
    replace (Z.land 4095 (a + 4096)) with 0 by (rewrite Z.land_comm; change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; clear - ALN; try acb; Z.div_mod_to_equations; lia).
    step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (a + 4096)) by lia. replace (a + 4096 - 4096) with a by lia. step. step. step. step.
    rewrite (unsigned_lit (needed + 4095)) by lia. change 18446744073709547520 with (2^64 - 2^12)%Z. rewrite StrFun.land_align_down by lia.
    replace (needed + 4095 - (needed + 4095) mod 2 ^ 12) with (msz - 4096) by (clear - GEO ALN; try acb; change (2^12) with 4096; Z.div_mod_to_equations; lia).
    step.
    (* [comment removed for export] *)
    assert (TB : exists tb8, tb8 = q8 + (if r8 =? 0 then 0 else 1) /\ nd8 = tb8 + 512 /\ 8 * q8 <= size <= 8 * tb8 /\ q8 <= tb8 <= q8 + 1)
      by (exists (q8 + (if r8 =? 0 then 0 else 1)); clear - GEO ND4 R8 DSZ; try acb; destruct (Z.eqb_spec r8 0); lia).
    destruct TB as (tb8 & TB1 & TB2 & TB3 & TB4).
    (* [comment removed for export] *)
    step. step.
    rewrite (unsigned_lit (a + 6144 + size + 7)) by lia. change 18446744073709551608 with (2^64 - 2^3)%Z. rewrite StrFun.land_align_down by lia.
    replace (a + 6144 + size + 7 - (a + 6144 + size + 7) mod 2 ^ 3) with (a + 6144 + 8 * tb8)
      by (clear - TB1 DSZ R8 ALN; try acb; change (2^3) with 8; destruct (Z.eqb_spec r8 0); Z.div_mod_to_equations; lia).
    step. rewrite (unsigned_lit (a + 6144)), (unsigned_lit (a + 4096)) by lia. replace (a + 6144 - (a + 4096)) with (8 * 256) by lia.
    step. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (sh (a + 4096)) (sh (a + 4096) + 256) (sh (a + 4096) + nd8) SHJ ltac:(hci; lia)) as [SH1 SH2]. clear SHJ.
    destruct (stk_cells _ _ _ SH1 ltac:(hci; lia)) as [lz LZ]. clear SH1. replace (sh (a + 4096) + 256 - sh (a + 4096)) with 256 in LZ by lia.
    assert (LZN : Z.of_nat (length lz) = 256) by (destruct LZ as [[WF _] _]; rewrite (proj1 WF); reflexivity). apply u8arr_of_rw_cells in LZ.
    (* [comment removed for export] *)
    step.
    callD (poison_shadow_specK _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (a + 4096) (sh (a + 4096)) 256 250 lz)
      by (rewrite ?unsigned_lit by lia; try eassumption; try (lia_guard; (lia_guard; first [clear - HI; lia | lia])); try reflexivity; try (unfold wz; f_equal; (lia_guard; (lia_guard; lia)));
          try (unfold AGOT_LO, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, ACANPOISON; eassumption)).
    all: try (unfold AHI_LO, ALOWSH_LO; clear - BND GEO ALN AR SZ; try acb; aunf; repeat split; try lia; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rename POST into SHL. change (Z.to_nat 256) with 256%nat in SHL.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit (a + 4096)), (unsigned_lit (a + 6144 + 8 * tb8)) by lia.
    replace (a + 4096 - (a + 6144 + 8 * tb8) + (msz - 4096)) with (8 * (512 * mq - 768 - tb8)) by (clear - ALN; try acb; lia).
    step. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (sh (a + 4096) + 256) (sh (a + 4096) + 256 + tb8) (sh (a + 4096) + nd8) SH2 ltac:(hci; lia)) as [SHU SH3]. clear SH2.
    destruct (stk_cells _ _ _ SH3 ltac:(hci; lia)) as [rj RJ]. clear SH3. replace (sh (a + 4096) + nd8 - (sh (a + 4096) + 256 + tb8)) with 256 in RJ by lia.
    assert (RJN : Z.of_nat (length rj) = 256) by (destruct RJ as [[WF _] _]; rewrite (proj1 WF); reflexivity). apply u8arr_of_rw_cells in RJ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RS : u8arr asegs mm (sh (a + 4096) + 256 + tb8) (rj ++ repeat (b8 250) (Z.to_nat (512 * mq - 512 - nd8)))) end.
    { apply u8arr_app. split; [exact RJ|]. rewrite RJN. replace (sh (a + 4096) + 256 + tb8 + 256) with (sh (a + 4096) + nd8) by lia. exact SHT. }
    assert (RSN : Z.of_nat (length (rj ++ repeat (b8 250) (Z.to_nat (512 * mq - 512 - nd8)))) = 512 * mq - 768 - tb8) by (rewrite length_app, repeat_length; lia).
    clear RJ SHT RJN SHTN.
    (* [comment removed for export] *)
    step.
    callD (poison_shadow_specK _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (a + 6144 + 8 * tb8) (sh (a + 4096) + 256 + tb8) (512 * mq - 768 - tb8) 250
             (rj ++ repeat (b8 250) (Z.to_nat (512 * mq - 512 - nd8))))
      by (rewrite ?unsigned_lit by lia; try eassumption; try (lia_guard; (lia_guard; (lia_guard; first [clear - HI; lia | lia]))); try reflexivity; try (unfold wz; f_equal; (lia_guard; (lia_guard; (lia_guard; lia))));
          try (unfold AGOT_LO, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, ACANPOISON; eassumption)).
    all: try (unfold sh, ASHADOW_BASE; clear - ALN; try acb; Z.div_mod_to_equations; lia).
    all: try (unfold AHI_LO, ALOWSH_LO; clear - BND GEO ALN TB3 TB4 AR SZ; try acb; aunf; repeat split; try lia; Z.div_mod_to_equations; lia).
    rename POST into SHTL.
    (* [comment removed for export] *)
    step. step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 size)) 281474976710648) with (8 * q8)
      by (rewrite (unsigned_lit size), land_m48_8 by lia; clear - DSZ R8; try acb; Z.div_mod_to_equations; lia).
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. clear - K GEO SZ; try acb. lia. } clear K.
    step. step. step. step.
    (* [comment removed for export] *)
    pose proof (aenv_sec1_now _ _ ENV0 MU WM) as ENV'.
    destruct (stk_split asegs _ (sh (a + 4096) + 256) (sh (a + 4096) + 256 + q8) (sh (a + 4096) + 256 + tb8) SHU ltac:(hci; lia)) as [SU1 SU2]. clear SHU.
    destruct (stk_cells _ _ _ SU1 ltac:(hci; lia)) as [sbsU SBU]. clear SU1. replace (sh (a + 4096) + 256 + q8 - (sh (a + 4096) + 256)) with q8 in SBU by lia.
    assert (SBUN : Z.of_nat (length sbsU) = q8) by (destruct SBU as [[WF _] _]; rewrite (proj1 WF); lia). apply u8arr_of_rw_cells in SBU.
    replace (sh (a + 4096) + 256) with (sh (a + 6144)) in SBU, SU2, SHTL by lia.
    apply evt_done. unfold alloc_sec_t1_post.
    destruct (Z.eqb_spec r8 0) as [R0|R1].
    - (* [comment removed for export] *)
      replace tb8 with q8 in * by lia.
      replace (Z.to_nat (512 * mq - 768 - q8)) with (S (Z.to_nat (512 * mq - 769 - q8))) in SHTL by lia.
      change (repeat (b8 250) (S (Z.to_nat (512 * mq - 769 - q8)))) with ([b8 250] ++ repeat (b8 250) (Z.to_nat (512 * mq - 769 - q8))) in SHTL.
      apply u8arr_app in SHTL. destruct SHTL as [GB SHTL]. cbn [length Z.of_nat Pos.of_succ_nat] in SHTL.
      apply (rw_cells_of_u8arr asegs) in GB. cbn [length] in GB. apply rw_cells_CB1 in GB.
      do 12 eexists. exists j8, sbsU, ob0, (b8 250), hb1, (512 * mq - 769 - q8). eexists.
      split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
      all: try (unfold wz; assumption).
    - (* [comment removed for export] *)
      replace tb8 with (q8 + 1) in * by lia.
      destruct (stk_cells _ _ _ SU2 ltac:(hci; lia)) as [gbl GB]. replace (sh (a + 6144) + (q8 + 1) - (sh (a + 6144) + q8)) with 1 in GB by lia.
      change (Z.to_nat 1) with 1%nat in GB.
      assert (LGB : length gbl = 1%nat) by (destruct GB as [[WF _] _]; exact (proj1 WF)).
      destruct gbl as [|gb [|]]; [cbn in LGB; lia| |cbn in LGB; lia]. apply rw_cells_CB1 in GB.
      replace (sh (a + 6144) + (q8 + 1)) with (sh (a + 6144) + q8 + 1) in SHTL by lia.
      replace (512 * mq - 768 - (q8 + 1)) with (512 * mq - 769 - q8) in SHTL by lia.
      do 12 eexists. exists j8, sbsU, ob0, gb, hb1, (512 * mq - 769 - q8). eexists.
      split; [reflexivity|].
      repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try (first [clear - HB1R R8 R1 SZ ARE SPR BND GEO SHR; lia | lia]).
      all: try (unfold wz; assumption).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_sec_t1 : forall (x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m1 : mem) (j8 : list byte),
    AENV tp TSD CTX TH sb SO T rest m1 -> mem_inv asegs m1 ->
    AFR m1 j8 -> stk asegs m1 lo (bv_unsigned sp + -128) ->
    rw_cells asegs m1 (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)] ->
    rw_cells asegs m1 a [C8 (wz a); C8 (wz msz); C8 (wz needed); C8 (wz nch)] ->
    stk asegs m1 (a + 4096) (a + msz) ->
    stk asegs m1 (sh (a + 4096)) (sh (a + 4096) + needed / 8) ->
    u8arr asegs m1 (sh (a + 4096) + needed / 8) (repeat (b8 0xfa) (Z.to_nat ((msz - 4096 - needed) / 8))) ->
    stk asegs m1 (TH + 2800) (TH + 3168) ->
    DEPOT asegs d m1 ->
    evt asegs (alloc_sec_t1_post sp gp tp F fc m1 W lo size a msz needed q8 r8 SO TH id pa nch TSD CTX sb T rest (d_put d (depot_hash T) nT) AFR)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 0) (wz size) (wz (a + 4096)) x11 x12 (wz 8) x14 x15 x16 x17
               (wz 8) (wz needed) (wz 2048) (wz size) (wz AINST) (wz SO) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x19709c) fc None m1 (seg_rom asegs)).
  Proof.
    intros until j8. intros ENV MI FR ST INST64 LHDR CHUNK SHJ SHT TST DEP.
    prep. pose proof ENV as ENV0. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold AINST in *.
    change (6976152 + 64) with 6976216 in *.
    pose proof (munch_refl W m1) as MU. pose proof (wmono_refl asegs m1) as WM. unfold W, depot_W in MU.
    pose proof (munch_refl W2 m1) as MUC. pose proof (wmono_refl asegs m1) as WMC. unfold W2 in MUC.
    assert (ND8 : exists nd8, needed = 8 * nd8 /\ needed / 8 = nd8 /\ (msz - 4096 - needed) / 8 = 512 * mq - 512 - nd8 /\ nd8 = q8 + (if r8 =? 0 then 0 else 1) + 512)
      by (exists (needed / 8); clear - GEO ALN; try acb; destruct (r8 =? 0); Z.div_mod_to_equations; lia).
    destruct ND8 as (nd8 & ND1 & ND2 & ND3 & ND4). rewrite ND2 in SHJ, SHT.
    assert (SHTN : Z.of_nat (length (repeat (b8 250) (Z.to_nat ((msz - 4096 - needed) / 8)))) = 512 * mq - 512 - nd8) by (rewrite repeat_length; clear - GEO ALN ND3 ND4 R8; try acb; destruct (r8 =? 0); lia).
    region_table.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit (a + 6144)) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    replace ((a + 6144) mod 8) with 0 by (clear - ALN; try acb; Z.div_mod_to_equations; lia).
    step. step. if_cases K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ (a + 4096) (a + 6128) (a + msz) CHUNK ltac:(hci; lia)) as [CHL CH2]. clear CHUNK.
    destruct (stk_split asegs _ (a + 6128) (a + 6144) (a + msz) CH2 ltac:(hci; lia)) as [CH3 USR]. clear CH2.
    destruct (stk_cells _ _ _ CH3 ltac:(hci; lia)) as [hj HDR]. clear CH3. replace (a + 6144 - (a + 6128)) with 16 in HDR by lia. change (Z.to_nat 16) with 16%nat in HDR.
    assert (LHJ : length hj = 16%nat) by (destruct HDR as [[WF _] _]; exact (proj1 WF)).
    destruct hj as [|ob0 [|ob1 hj']]; [cbn in LHJ; lia| cbn in LHJ; lia|].
    apply (rw_cells_split_CB asegs _ _ [] 16 (ob0 :: ob1 :: hj') [] [1;1;2;4;8]%nat) in HDR; [| reflexivity].
    cbn [mk_CB_cells firstn skipn app] in HDR. change (take 0 hj') with (@nil byte) in HDR. change (drop 0 hj') with hj' in HDR.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    rewrite (unsigned_lit size) by lia. rewrite (Z.shiftr_div_pow2 size 32), (Z.shiftr_div_pow2 size 48) by lia.
    replace (size / 2 ^ 32) with 0 by (symmetry; apply Z.div_small; clear - SZ; try acb; lia).
    replace (size / 2 ^ 48) with 0 by (symmetry; apply Z.div_small; clear - SZ; try acb; lia).
    unfold zxb. pose proof (bv_unsigned_in_range _ ob1) as OB1. change (bv_modulus 8) with 256 in OB1.
    remember (bv_unsigned ob1) as o1 eqn:EO1. clear EO1.
    match goal with |- context [Z_to_bv 64 (Z.lor ?x 1)] => remember (Z.lor x 1) as x1v eqn:EX1 end.
    rewrite (unsigned_lit o1) in EX1 by lia. change 18446744073709551612 with (2^64 - 2^2)%Z in EX1. rewrite StrFun.land_align_down in EX1 by lia.
    rewrite unsigned_lit in EX1 by (clear - OB1; try acb; Z.div_mod_to_equations; lia).
    assert (X1R : 0 <= x1v < 256).
    { subst x1v. change 256 with (2^8). apply lor_lt_pow2; [| lia]. clear - OB1; try acb. Z.div_mod_to_equations. lia. }
    assert (X1h : hidden (x1v = Z.lor (o1 - o1 mod 2 ^ 2) 1)) by (constructor; exact EX1). clear EX1.
    (* [comment removed for export] *)
    st1. st1. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. st1.
    rewrite (unsigned_lit x1v) in * by lia.
    assert (L143 : 0 <= Z.land x1v 143 < 256) by (split; [apply Z.land_nonneg; lia| change 256 with (2^8); apply land_lt_pow2; lia]).
    rewrite (unsigned_lit (Z.land x1v 143)) in * by lia.
    remember (Z.lor (Z.land x1v 143) 16) as hb1 eqn:EHB in *.
    assert (HB1F : 0 <= hb1 < 256 /\ b1_ok (Z.land hb1 243)).
    { unhide_hyp X1h. subst hb1 x1v. exact (hb1_facts o1 OB1). }
    replace (hb1 mod 256) with hb1 in HDR by (symmetry; apply Z.mod_small; (first [clear - HB1F; lia | lia])).
    clear X1h L143 EHB X1R x1v OB1 o1.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    step. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 0)) ≪ 32)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    apply rw_cells_CB1 in HDR. destruct HB1F as [HB1R HB1M].
    (* [comment removed for export] *)
    step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs d _ mm) in DEP; [| exact MUC | exact WMC | solve_depot_avoid] end.
    clear MUC WMC.
    assert (IDR : 1 <= id < 65536) by (rewrite DID; apply d_putid_range; [exact (proj1 DEP)| lia]).
    step. callDep (depot_put_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo (SO + 16) T rest d).
    all: rewrite <- ?DNT. all: rewrite ?unsigned_lit by (first [clear - HI ARE SPR BND GEO SPQ; lia | lia]). all: try eassumption; try (lia_guard; (first [clear - HI BND NR DCAP DLO; lia | lia])).
    all: try (unfold AIMG_TOP; (lia_guard; lia)). all: try (unfold wz; f_equal; lia).
    clear DEP.
    lazymatch goal with H : DEPOT asegs _ ?mm |- _ => rename H into DEPN;
      pose proof (munch_refl W2 mm) as MUC; pose proof (wmono_refl asegs mm) as WMC; unfold W2 in MUC end.
    (* [comment removed for export] *)
    step. step. step. rewrite <- DID.
    match goal with |- context [Z_to_bv 64 (Z.lor 0 ?x)] => replace (Z_to_bv 64 (Z.lor 0 x)) with (Z_to_bv 64 id) end.
    2:{ f_equal. rewrite Z.lor_0_l. unfold wz. rewrite (unsigned_lit id), Z.shiftl_mul_pow2 by lia.
        rewrite (unsigned_lit (id * 2^32)), Z.shiftr_div_pow2 by (first [clear - SZ ARE SPR BND GEO ND1 SHTN IDR; lia | lia]). rewrite Z.div_mul by lia. rewrite unsigned_lit by lia. reflexivity. }
    step.
    (* [comment removed for export] *)
    step. if_cases K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    step.
    rewrite <- DNT in DEPN.
    (* [comment removed for export] *)
    pose proof SBX as SBX'; destruct SBX' as [SBX']. unfold kSpaceSize in SBX'.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs _ _ mm) in DEPN; [| exact MUC | exact WMC | solve_depot_avoid] end.
    clear MUC WMC.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    2: step; step; step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [clear K2 | exfalso; clear - K K2 SBX' GEO BND SZ; try acb; lia].
    all: clear K SBX'.
    all: eapply evt_mono; [eapply (alloc_sec_t1c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j8 ob0 hb1 nd8); try eassumption; try (unfold wz; eassumption);
                            exact (aenv_sec1_now _ _ ENV0 MU WM) |].
    all: cbv beta; intros ms' P'; unfold alloc_sec_t1_post in P' |- *;
      destruct P' as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & jj & su & o0 & g0 & h1 & tt & m' & E' & MU' & WM' & REST);
      exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, jj, su, o0, g0, h1, tt, m'; split; [exact E'|];
      split; [exact (munch_trans _ _ _ _ MU MU')|]; split; [exact (wmono_trans _ _ _ _ WM WM')|]; exact REST.
  Qed.
End SecTail1.

