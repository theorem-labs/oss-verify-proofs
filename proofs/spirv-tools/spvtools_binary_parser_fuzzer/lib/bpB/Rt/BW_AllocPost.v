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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BsDepotInv BsDepotHash BsDepotPut BidBits BW_Combined BW_PoisonShadow BW_Leaves BW_DepotFrame BllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_AllocBase BW_Alloc1 BW_Alloc2 BW_Alloc3 BW_AllocPre BllocTacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocStoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Alloc.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size SO : Z) (T : list Z) (rest : list word) (d : depot).
  Variables (TSD CTX TH : Z).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).

  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).

  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: depot_W d.
  Let W2 : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: nil.
  Let POST := allocate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size AB U rz csz P cnt mc TH id chunks
                            (d_put d (depot_hash T) n).
  Let AFR := aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
  Let Wpre : list ivl := [(lo, bv_unsigned sp)]%Z.
  Let PREPOST := alloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed rz TSD CTX TH sb SO T rest.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 352 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.

  Hypothesis TPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).

  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).

  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 32768 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 32768)).
  Let PLACED : Prop := ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX))
               /\ ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 32768 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 32768 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 32768)).

  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis ABR : hidden (sb <= AB /\ AB + csz <= sb + kSpaceSize).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis NR : 1 <= n <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + n + 1 <= 32768.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 32768 <= lo.

  Ltac prep :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 6762288 <= TSD /\ TSD + 8 <= 7241728 /\ 7241728 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 7241728
               /\ bv_unsigned sp <= SO /\ SO + 2064 <= 140737488355328)
      by (clear - LO RNG SBR ABR TPR SOR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct ABR as [ABR']; destruct TPR as [TPR'];
          destruct SOR as [SOR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SOR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (CSZ : 32 <= csz <= 65536 /\ needed <= csz)
      by (clear - SZ HC DCSZ DNEED DRZ DC; try acb; pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz;
          pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; subst needed rz; pose proof (rz_size_facts size); unfold round_up in *;
                                             Z.div_mod_to_equations; lia)); subst c; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz <= needed /\ 8 + rz <= needed /\ needed < size + rz + 8)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 8 - 1) / 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 4294967296 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T))) by (constructor; repeat split; assumption);
    assert (C8F : 8 * csz8 = csz /\ 1 <= fl <= size /\ fl <= 4096) by (clear - ALN SZ DC8 DFL; try acb; subst csz8 fl; Z.div_mod_to_equations; lia);
    assert (FLh : hidden (fl = Z.min size 4096)) by (constructor; exact DFL);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (LENQ : Z.of_nat (length (wlist (rev (tl chunks)))) = cnt - 1)
      by (clear - CNT HIT; try acb; unfold wlist; rewrite length_map, length_rev; destruct chunks;
          [unfold zlen in CNT; cbn in CNT; lia| cbn [tl]; unfold zlen in CNT; cbn [length] in CNT; lia]);

    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

  Ltac plia :=
    first [ lia
          | match goal with H : hidden PLACED |- _ =>
              let P := fresh "PLu" in pose proof H as P; destruct P as [P]; unfold PLACED, kSpaceSize, AHI_LO in P;
              let A1 := fresh "PA" in let A2 := fresh "PA" in let A3 := fresh "PA" in
              let B1 := fresh "PB" in let B2 := fresh "PB" in let B3 := fresh "PB" in let B4 := fresh "PB" in
              let B5 := fresh "PB" in let B6 := fresh "PB" in let B7 := fresh "PB" in let B8 := fresh "PB" in
              destruct P as [[A1 [A2 A3]] [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]]];
              first [ clear A2 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B5; lia ]
            end ].

  Ltac solve_depot_avoid ::=
    unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
    repeat split;
    repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; plia |]]).

  Ltac remregF n name eqname folded :=
    remreg n name eqname; match type of eqname with ?e = _ => change (e = folded) in eqname end.

  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  Lemma partC_post : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte) (jj0 jj1 jj2 jj3 : word),
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch W m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    rw_cells asegs mB P [C4 (wz (cnt - 1)); C4 (wz mc)] -> u32arr asegs mB (P + 16) (wlist (rev (tl chunks))) ->
    stk asegs mB (P + 16 + 4 * (cnt - 1)) (P + 80) -> rw_cells asegs mB (TH + 208 + 2560) [C8 jj0; C8 jj1; C8 jj2; C8 jj3] ->
    stk asegs mB AB (AB + csz) ->
    u8arr asegs mB (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mB (TH + 2800) (TH + 3168) ->
    DEPOT asegs d mB ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 1) (wz size) (wz AB) x11 x12 x13 x14 x15 x16 x17
               (wz 8) (wz needed) (wz rz) (wz size) (wz AINST) (wz SO) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x9273c) fc None mB (seg_rom asegs)).
  Proof.
    intros until jj3. intros ENV MI MU WM FR ST QC1 QC3 QC4 QSTn CHUNK SHK TST DEP.

    pose proof (munch_refl W mB) as MUB. pose proof (wmono_refl asegs mB) as WMB. unfold W in MUB. pose proof ENV as ENV0.
    unfold W in MU. prep. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold AINST.
    assert (MX : 8 <= Z.max size 8 /\ size <= Z.max size 8 /\ Z.max size 8 <= needed) by (clear - SZ RZB; try acb; lia).
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    remember (Z.max size 8) as mx eqn:EMX in MX |- *. assert (MXh : hidden (mx = Z.max size 8)) by (constructor; exact EMX). clear EMX.
    assert (RZL : 0 <= rz_log size <= 7 /\ rz = Z.shiftl 16 (rz_log size)).
    { unhide_hyp EQh. destruct EQh as (_ & _ & ERZ & _). rewrite ERZ. unfold rz_size, kMinRedzoneLog, kMaxRedzoneLog, rz_log.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; split; try lia; reflexivity. }
    destruct RZL as [RZL1 RZL2].
    destruct EQS as (EU & EP & EAB & En & ECA). unhide_hyp EQh. destruct EQh as (Ec & Ecsz & Erz & Eneeded & Ecp & Eid).
    unfold CACHE_STATS in *. region_table.

    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl W2 mm) as MUC; pose proof (wmono_refl asegs mm) as WMC; unfold W2 in MUC end.

    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    step. rewrite <- EU.
    step. rewrite (unsigned_lit U) by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8.
    replace (U mod 8) with 0 by (clear - EU EAB ALN; try acb; Z.div_mod_to_equations; lia).
    step. step. if_cases K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.

    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.

    destruct (stk_split asegs _ AB (U + -16) (AB + csz) CHUNK ltac:(hci; lia)) as [CHL CH2]. clear CHUNK.
    destruct (stk_split asegs _ (U + -16) U (AB + csz) CH2 ltac:(hci; lia)) as [CH3 USR]. clear CH2.
    destruct (stk_cells _ _ _ CH3 ltac:(hci; lia)) as [hj HDR]. clear CH3. replace (U - (U + -16)) with 16 in HDR by lia. change (Z.to_nat 16) with 16%nat in HDR.
    assert (LHJ : length hj = 16%nat) by (destruct HDR as [[WF _] _]; exact (proj1 WF)).
    destruct hj as [|ob0 [|ob1 hj']]; [cbn in LHJ; lia| cbn in LHJ; lia|].
    apply (rw_cells_split_CB asegs _ _ [] 16 (ob0 :: ob1 :: hj') [] [1;1;2;4;8]%nat) in HDR; [| reflexivity].
    cbn [mk_CB_cells firstn skipn app] in HDR. change (take 0 hj') with (@nil byte) in HDR. change (drop 0 hj') with hj' in HDR.

    step. step. step. step. step. step.
    rewrite (unsigned_lit size) by lia. rewrite (Z.shiftr_div_pow2 size 32), (Z.shiftr_div_pow2 size 48) by lia.
    replace (size / 2 ^ 32) with 0 by (symmetry; apply Z.div_small; unfold kMaxSize in SZ; lia).
    replace (size / 2 ^ 48) with 0 by (symmetry; apply Z.div_small; unfold kMaxSize in SZ; lia).
    unfold zxb. pose proof (bv_unsigned_in_range _ ob1) as OB1. change (bv_modulus 8) with 256 in OB1.
    remember (bv_unsigned ob1) as o1 eqn:EO1. clear EO1.
    match goal with |- context [Z_to_bv 64 (Z.lor ?x 1)] => remember (Z.lor x 1) as x1v eqn:EX1 end.
    rewrite (unsigned_lit o1) in EX1 by lia. change 18446744073709551612 with (2^64 - 2^2)%Z in EX1. rewrite BStrFun.land_align_down in EX1 by lia.
    rewrite unsigned_lit in EX1 by (clear - OB1; try acb; Z.div_mod_to_equations; lia).
    assert (X1R : 0 <= x1v < 256).
    { subst x1v. change 256 with (2^8). apply lor_lt_pow2; [| lia]. clear - OB1; try acb. Z.div_mod_to_equations. lia. }
    assert (X1h : hidden (x1v = Z.lor (o1 - o1 mod 2 ^ 2) 1)) by (constructor; exact EX1). clear EX1.

    st1. st1. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.

    step. step. step. step. st1.
    rewrite (unsigned_lit x1v) in * by lia.
    assert (L143 : 0 <= Z.land x1v 143 < 256) by (split; [apply Z.land_nonneg; lia| change 256 with (2^8); apply land_lt_pow2; lia]).
    rewrite (unsigned_lit (Z.land x1v 143)) in * by lia.
    remember (Z.lor (Z.land x1v 143) 16) as hb1 eqn:EHB in *.
    assert (HB1F : 0 <= hb1 < 256 /\ b1_ok (Z.land hb1 243)).
    { unhide_hyp X1h. subst hb1 x1v. exact (hb1_facts o1 OB1). }
    replace (hb1 mod 256) with hb1 in HDR by (symmetry; apply Z.mod_small; lia).
    clear X1h L143 EHB X1R x1v OB1 o1.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV' : AENV tp TSD CTX TH sb SO T rest mm)
        by (eapply aenv_now0 with (cnt := cnt) (chunks := chunks) (n := n) (rz := rz) (c := c) (cp := cp) (fl := fl) (U := U) (id := id)
                                   (needed := needed) (csz := csz) (csz8 := csz8) (CA := CA) (P := P) (AB := AB) (d := d) (lo := lo) (m0 := mB);
            try exact ENV0; try exact MUB; try exact WMB; try exact DEFS; eassumption) end.
    clear ENV0 MUB WMB. open_env ENV'. unfold wz in *.

    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    step. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 0)) ≪ 32)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    apply rw_cells_CB1 in HDR. destruct HB1F as [HB1R HB1M]. unhide_hyp MXh. subst mx.
    eapply partC2; try eassumption; try reflexivity; try (econstructor; eassumption); try lia.
  Qed.
End Alloc.
