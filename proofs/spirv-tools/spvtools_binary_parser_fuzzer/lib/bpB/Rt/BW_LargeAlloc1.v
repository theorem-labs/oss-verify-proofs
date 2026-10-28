(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BllocWalkKit B_memset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_Leaves BW_PoisonShadow BW_MmapFixed BW_SecMmap BecMsb BW_AllocBase BllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocStoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Record SENV (tp : word) (TSD CTX TH : Z) (m : mem) : Prop := mkSENV {
  se_tsdi : rw_cells asegs m 1640608 [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)];
  se_tp   : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)];
  se_tsd  : rw_cells asegs m TSD [C8 (wz CTX)];
  se_ctx  : rw_cells asegs m (CTX + 152) [C8 (wz TH)];
  se_can  : rw_cells asegs m 1640604 [C1 (b8 1)];
  se_got  : rw_cells asegs m 1593472 (map (fun v => C8 (wz v)) AGOT_VALS);
  se_shb  : rw_cells asegs m 1642552 [C8 (wz 2147450880)];
  se_hme  : rw_cells asegs m 1645856 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];
  se_thresh : rw_cells asegs m 2239456 [C8 (wz 0xffffffffffffffff)];
  se_mlim : rw_cells asegs m 2239480 [C8 (wz 0)];
  se_dpm  : rw_cells asegs m 2239596 [C1 (b8 0)];
  se_rms  : rw_cells asegs m 1601864 [C8 (wz 1535652)];
  se_psc  : rw_cells asegs m 2231008 [C8 (wz 4096)];
  se_name : rw_cells asegs m 1601920 [C8 (wz 0x1ae42)]
}.

End HCW.

Ltac open_senv E :=
  destruct E as [Etsdi Etp Etsd Ectx Ecan Egot Eshb Ehme Ethresh Emlim Edpm Erms Epsc Ename];
  unfold AGOT_VALS in Egot; cbn [map] in Egot.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma senv_transport : forall tp TSD CTX TH m m' W,
  SENV tp TSD CTX TH m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W 1640608 8 -> disjoint_from W (bv_unsigned tp + -88) 8 -> disjoint_from W TSD 8 -> disjoint_from W (CTX + 152) 8 ->
  disjoint_from W 1640604 1 -> disjoint_from W 1593472 120 -> disjoint_from W 1642552 8 -> disjoint_from W 1645856 24 ->
  disjoint_from W 2239456 8 -> disjoint_from W 2239480 8 -> disjoint_from W 2239596 1 -> disjoint_from W 1601864 8 ->
  disjoint_from W 2231008 8 -> disjoint_from W 1601920 8 ->
  SENV tp TSD CTX TH m'.
Proof.
  intros tp TSD CTX TH m m' W E MU WM; intros; destruct E; constructor;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | ]);
    unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
Qed.

End HCW2.

Ltac senv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with SENV ?tp ?TSD ?CTX ?TH m =>
      region_table; region_hull_memo W;
      assert (E' : SENV tp TSD CTX TH m');
      [ apply (senv_transport tp TSD CTX TH m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

Section HCW3.
  Context {HCEIL : HeapCeil}.

Lemma poison_shadow_specK0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo addr shA k v : Z) (sbs : list byte),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + 64 <= bv_unsigned sp ->
  a0 = wz addr -> a1 = wz (8 * k) -> a2 = wz v -> shA = sh addr ->
  (AHI_LO + 8 <= addr \/ 8 <= addr /\ addr + 8 * k <= ALOWSH_LO) /\ 0 <= k /\ addr + 8 * k <= aceil /\ addr mod 8 = 0 ->
  0 <= v < 256 ->
  u8arr asegs m shA sbs -> Z.of_nat (length sbs) = k ->
  rw_cells asegs m ACANPOISON [C1 (b8 1)] ->
  rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS) ->
  rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
  rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)] ->
  rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)] ->
  rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)] ->
  evt asegs (poison_postK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo shA k v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbb428) fc None m (seg_rom asegs)).
Proof.
  intros until sbs. intros MI ST LO HI Ha0 Ha1 Ha2 HshA AR VR SH SHL CCAN GOT CSHB CHME CTHR CRMS. subst shA.
  assert (K8 : 8 * k / 8 = k) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  eapply evt_mono.
  - eapply (poison_shadow_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo addr (8 * k) v sbs); try eassumption.
    + destruct AR as (ARS & K1 & ARC & AR8). split; [| repeat split; try lia; rewrite Z.mul_comm; apply Z.mod_mul; lia].
      destruct ARS as [H|H]; [left| right]; lia.
    + rewrite K8. exact SHL.
  - intros ms' PO. unfold poison_post, poison_postK in *. rewrite K8 in PO.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & E & MU & WM & MI' & ST' & PZ).
    unfold poisoned, SHAD, poison_bytes in PZ. destruct PZ as (_ & _ & U8).
    do 16 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'| exact U8].
Qed.

Definition laframe (sp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra : word) (m1 : mem) (j8 : list byte) : Prop :=
  rw_cells asegs m1 (bv_unsigned sp + -96)
    [CB 8 j8; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition large_alloc_seg1_post (sp gp tp t0 t1 t2 a6 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size msz : Z) (s0 s1 s2 s3 s5 s8 ra stat : word) : machine_state -> Prop :=
  fun ms' => exists m' (j8 j12 : list byte),
    ms' = MS (mkR (wz 0xcdec0) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (wz 0x1ae42) (wz msz) (wz 0) (wz msz) (wz 3) (wz 34) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz APAGESZ) (wz size) s4 (wz 8) s6 s7 (wz 7) s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xcc570) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 416, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -144)
    /\ laframe sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra m' j8
    /\ rw_cells asegs m' (bv_unsigned sp + -144) [CB 12 j12; C4 (wz 34); C8 (wz msz); C8 (wz (AINST + 64)); C8 stat; C8 (wz 0x96f88)].

Section Seg1.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size msz TSD CTX TH pa : Z).
  Hypothesis DEFS : hidden (msz = round_up size 4096 + 4096).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 416 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz (AINST + 64). Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz 8.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41 /\ size mod 8 = 0.
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis INST64 : rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].

  Theorem large_alloc_seg1 :
    evt asegs (large_alloc_seg1_post sp gp tp t0 t1 t2 a6 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 F fc m lo size msz s0 s1 s2 s3 s5 s8 ra a1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x96ecc) fc None m (seg_rom asegs)).
  Proof.
    destruct DEFS as [DMSZ].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { subst msz. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; lia).
      exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    unfold AINST, APAGESZ in *. change (1628632 + 64) with 1628696 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 416, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (se_got _ _ _ _ _ ENV) as Egot. unfold AGOT_VALS in Egot; cbn [map] in Egot.
    pose proof (se_name _ _ _ _ _ ENV) as Ename. pose proof (se_psc _ _ _ _ _ ENV) as Epsc. pose proof (se_dpm _ _ _ _ _ ENV) as Edpm.
    subst a0 a2 a3. unfold wz in *.

    step. carve_frame 96%nat ST. do 11 step.
    match type of FR with context [CB 8 ?j] => remember j as J8 eqn:EJ in FR; clear EJ end.

    step. step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

    step. step. step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

    step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709547520)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709547520)) with (Z_to_bv 64 (msz - 4096)) end.
    2:{ rewrite (unsigned_lit (size + 4095)) by lia. change 18446744073709547520 with (2^64 - 2^12)%Z. rewrite BStrFun.land_align_down by lia.
        f_equal. subst msz. unfold round_up. clear - SZ; try acb. Z.div_mod_to_equations. lia. }
    step. replace (v_sltu (Z_to_bv 64 4096) (Z_to_bv 64 8)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    step. step. step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x 8)] => let v := eval vm_compute in (Z.land x 8) in change (Z.land x 8) with v end.
    step. try replace (Z_to_bv 64 (msz - 4096 + 4096 + 0)) with (Z_to_bv 64 msz) by (f_equal; lia).
    try replace (Z_to_bv 64 (msz - 4096 + 4096)) with (Z_to_bv 64 msz) by (f_equal; lia).

    step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.

    step. step. step. step. step. step.
    callN mmap_or_die_seg1; rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (acb; lia); try lia.
    replace (bv_unsigned sp + -96 + -48) with (bv_unsigned sp + -144) in * by lia.
    apply evt_done. unfold large_alloc_seg1_post, laframe. exists x, J8, x0.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    unfold AINST. exact POST.
  Qed.
End Seg1.

End HCW3.

