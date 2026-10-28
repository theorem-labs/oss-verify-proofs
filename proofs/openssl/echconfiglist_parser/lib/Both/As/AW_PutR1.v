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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition put_frameR (sp cs0 cs2 cs3 cs4 cs5 s6 : word) (U TH : Z) : list cell :=
  [C8 (wz (TH + OT_CACHE)); C8 (Z_to_bv 64 (bv_unsigned sp + -2136)); C8 s6; C8 cs5;
   C8 cs4; C8 cs3; C8 cs2; C8 (wz U); C8 cs0; C8 (wz 0x197a10)].

(* [comment removed for export] *)
Definition put_headR_post (sp gp tp s7 s8 s9 s10 s11 cs0 cs2 cs3 cs4 cs5 s6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size TH qcache : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x19b46c) (Z_to_bv 64 (bv_unsigned sp + -2288)) gp tp t0 t1 t2 (wz (AINST + OI_Q)) (wz (TH + OT_TQ))
                  (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (U + -16)) (wz size) a5 a6 a7
                  (wz size) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (TH + OT_CACHE)) (wz (U + -16)) (wz qcache) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b478) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp + -2208); (sh U, sh U + nsh size)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2288)
    /\ rw_cells asegs m' (bv_unsigned sp + -2288) (put_frameR sp cs0 cs2 cs3 cs4 cs5 s6 U TH)
    /\ u8arr asegs m' (sh U) (repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh size))).
End HCW.

Section PutHeadR.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp t0 t1 t2 a6 a7 t3 t4 t5 t6 s6 s7 s8 s9 s10 s11 cs0 cs2 cs3 cs4 cs5 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U size b1 actx qmax qmin qcache : Z) (sbs : list byte).
  Variables (TSD CTX TH TOP BOT sb : Z).
  Let W : list ivl := [(lo, bv_unsigned sp + -2208); (sh U, sh U + nsh size)].
  Let POST := put_headR_post sp gp tp s7 s8 s9 s10 s11 cs0 cs2 cs3 cs4 cs5 s6 F fc m lo U size TH qcache.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2576 <= bv_unsigned sp.
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis UR : hidden (aapp U (round_up size 8) /\ AIMG_TOP + 16 <= U /\ U + round_up size 8 <= aceil /\ U mod 16 = 0).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis B1 : 0 <= b1 < 256. Hypothesis ACR : 0 <= actx < 2^64.
  Hypothesis QR : 0 < qcache < 2^64 /\ size <= qmax < 2^64 /\ 0 <= qmin < 2^64.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis SBS : Z.of_nat (length sbs) = nsh size.

  Ltac prepP :=
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP
               /\ 12599312 <= U /\ U + round_up size 8 <= aceil /\ 140735193776128 <= aceil)
      by (clear - LO RNG TPR SPT TBR UR; try acb; destruct RNG as [RNG']; destruct TPR as [TPR']; destruct UR as [UR'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        assert (RU0 : 0 <= round_up size 8) by (clear - SZ; unfold round_up; Z.div_mod_to_equations; lia);   (* [comment removed for export] *)
        region_sides; name_bands;
    assert (UQ : exists uq, U = 16 * uq) by (clear - UR; try acb; destruct UR as [UR']; exists (U / 16); Z.div_mod_to_equations; lia);
    assert (UBAND : AHI_LO <= U \/ 0 <= U /\ U + round_up size 8 <= ALOWSH_LO) by (clear - UR; destruct UR as [[UA UR']]; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP in UA; lia);
    destruct UQ as [uq UQ];
    assert (NQ : exists nq r8, size + 7 = 8 * nq + r8 /\ 0 <= r8 < 8 /\ nsh size = nq /\ round_up size 8 = 8 * nq)
      by (clear - SZ; try acb; exists ((size + 7) / 8), ((size + 7) mod 8); unfold nsh, round_up; Z.div_mod_to_equations; lia);
    destruct NQ as (nq & r8 & NQ & R8 & NSH & RUP).

  Lemma ienv_now_pR : forall m1, IENV tp TSD CTX TH sb TOP BOT m -> munch W m m1 -> wmono asegs m m1 -> IENV tp TSD CTX TH sb TOP BOT m1.
  Proof.
    intros m1 E MU WM. unfold W in MU. prepP.
    assert (SHR : 2148314624 <= sh U /\ sh U + nsh size <= 17594333495296) by (clear - BND NSH RUP R8 NQ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (USH : sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) by (destruct UR as [[UA UX]]; clear - UA UX; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, sh, nsh, round_up, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    open_ienv E.
    constructor; unfold AGOT_VALS; cbn [map repeat];
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; (first [clear - BND SHR SZ RU0 RXS RXS3 NQ R8 NSH RXS1; lia | lia])]).
  Qed.

  Theorem put_headR :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) ->
    rw_cells asegs m (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
    rw_cells asegs m (AINST + OI_QMAX) [C8 (wz qmax); C8 (wz qmin); C8 (wz qcache)] ->
    u8arr asegs m (sh U) sbs ->
    evt asegs POST
      (MS (mkR (wz 0x197a10) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 cs0 (wz U)
               (wz (AINST + OI_Q)) (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz (U + -16)) (wz size) a6 a7
               cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19b2c8) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST HDR QC SH.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold W in MU. prepP. unfold AINST, OI_Q, OI_QMAX, OT_TQ, OT_CACHE, wz in *.
    replace (6976152 + 792) with 6976944 in QC by reflexivity. replace (6976152 + 728) with 6976880 by reflexivity.
    assert (SHR : 2148314624 <= sh U /\ sh U + nsh size <= 17594333495296) by (clear - BND NSH RUP R8 NQ; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (USH : sh U + nsh size <= U - 16 \/ U + round_up size 8 <= sh U) by (destruct UR as [[UA UX]]; clear - UA UX; acb; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, ALOWSH_LO, AHI_LO, sh, nsh, round_up, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. carve_frame 80%nat ST. do 8 st1. step. st1. st1.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step.
    pose proof (ienv_now_pR _ ENV MU WM) as E.
    pose proof (i_got _ _ _ _ _ _ _ _ E) as Egot. unfold AGOT_VALS in Egot. cbn [map] in Egot. unfold wz in Egot.
    pose proof (i_fill _ _ _ _ _ _ _ _ E) as Efill. unfold wz in Efill.
    step. step. step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K Egot Efill.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.
    match goal with |- context [Z.lor ?y (bv_unsigned (zx32 (Z_to_bv 64 size)))] =>
      replace (Z.lor y (bv_unsigned (zx32 (Z_to_bv 64 size)))) with size
        by (change y with 0; rewrite Z.lor_0_l; unfold zx32; rewrite (unsigned_lit size), Z.mod_small, unsigned_lit by lia; reflexivity) end.
    rewrite (unsigned_lit (size + 7)) by lia.
    replace (Z.land (size + 7) 18446744073709551608) with (8 * nq)
      by (change 18446744073709551608 with (2^64 - 2^3); rewrite land_mask_down by lia; clear - NQ R8; try acb; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof (i_got _ _ _ _ _ _ _ _ E) as Egot. pose proof (i_can _ _ _ _ _ _ _ _ E) as Ecan. pose proof (i_shb _ _ _ _ _ _ _ _ E) as Eshb.
    pose proof (i_hme _ _ _ _ _ _ _ _ E) as Ehme. pose proof (i_thresh _ _ _ _ _ _ _ _ E) as Ethresh. pose proof (i_rms _ _ _ _ _ _ _ _ E) as Erms. clear E.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : stk asegs mm lo _ |- _ =>
      callD (poison_shadow_specK _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm lo U (sh U) nq kAsanHeapFreeMagic sbs)
        by (rewrite ?unsigned_lit by lia; try eassumption; try (first [clear - HI SZ BND RXb UQ UBAND NQ R8 RUP SBS NSH; lia | lia]); try reflexivity; try (f_equal; lia);
            try (unfold AGOT_LO, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, ACANPOISON; eassumption);
            try (unfold kAsanHeapFreeMagic; first [lia | f_equal; lia]);
            try (clear - BND UQ RUP NQ R8 SZ UBAND; try acb; split; [unfold AHI_LO, ALOWSH_LO in *; lia|]; repeat split; try lia; Z.div_mod_to_equations; lia)) end end.
    rename PC into ST. rename POST0 into SHD. rename MI0 into MI. try clear Egot. try clear Ecan. try clear Eshb. try clear Ehme. try clear Ethresh. try clear Erms.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    apply evt_done. unfold POST, put_headR_post, put_frameR, wz, AINST, OI_Q, OT_TQ, OT_CACHE.
    replace (6976152 + 728) with 6976880 by reflexivity.
    do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FR|]. rewrite NSH. exact SHD.
  Qed.
End PutHeadR.

