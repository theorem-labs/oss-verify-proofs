(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AW_Alloc1 AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Section Alloc.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size SO : Z) (T : list Z) (rest : list word) (d : depot).
  Variables (TSD CTX TH : Z).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).
  (* [comment removed for export] *)
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

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 352 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  (* [comment removed for export] *)
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Let PLACED : Prop := ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX))
               /\ ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).

  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis ABR : hidden (sb <= AB /\ AB + csz <= sb + kSpaceSize).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis NR : 1 <= n <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + n + 1 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.


  (* [comment removed for export] *)
  Ltac prep :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
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
    (* [comment removed for export] *)
    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Ltac remregF n name eqname folded :=
    remreg n name eqname; match type of eqname with ?e = _ => change (e = folded) in eqname end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  Lemma partD : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mD : mem) (j8 : list byte) (jj0 jj1 jj2 jj3 : word) (st0 x2 : Z) (shd : list byte),
    AENV tp TSD CTX TH sb SO T rest mD -> mem_inv asegs mD -> munch W m mD -> wmono asegs m mD ->
    AFR mD j8 -> stk asegs mD lo (bv_unsigned sp + -128) ->
    rw_cells asegs mD P [C4 (wz (cnt - 1)); C4 (wz mc)] -> u32arr asegs mD (P + 16) (wlist (rev (tl chunks))) ->
    stk asegs mD (P + 16 + 4 * (cnt - 1)) (P + 80) -> rw_cells asegs mD (TH + 208 + 2560) [C8 jj0; C8 jj1; C8 jj2; C8 jj3] ->
    rw_cells asegs mD (U + -16) [C1 (b8 st0); C1 (b8 x2); C2 (wz 0); C4 (wz size); C8 (wz id)] ->
    0 <= st0 < 256 -> 0 <= x2 < 256 -> b1_ok (Z.land x2 243) ->
    stk asegs mD AB (U + -16) ->
    stk asegs mD U (AB + csz) ->
    u8arr asegs mD (sh AB) shd -> shd = alloc_shadow rz size csz -> Z.of_nat (length shd) = csz8 ->
    stk asegs mD (TH + 2800) (TH + 3168) ->
    forall mC, DEPOT asegs (d_put d (depot_hash T) n) mC -> munch W2 mC mD -> wmono asegs mC mD ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) x10 x11 x12 x13 x14 x15 x16 x17
               (wz AB) (wz needed) (wz U) (wz (U + -16)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x197348) fc None mD (seg_rom asegs)).
  Proof.
    intros until shd. intros ENV MI MU WM FR ST QC1 QC3 QC4 QST HDR ST0R X2R X2M CHL USR SHD SHDE SHDN TST mC DEPC MUC WMC.
    unfold W in MU. unfold W2 in MUC. prep. open_env ENV. unfold AFR, aframe in FR. unfold wz in *.
    (* [comment removed for export] *)
    step. callD getcurthreadstats_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try (lia_guard; (lia_guard; first [clear - HI BND ALN; lia | lia])).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; (lia_guard; (lia_guard; lia))). all: try (unfold AIMG_TOP; lia).
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ (TH + 2800) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2800) (TH + 2824) (TH + 3168) H ltac:(hci; lia)) as [TS1 TS2]; clear H end.
    destruct (stk_cells _ _ _ TS1 ltac:(hci; lia)) as [sj SJ]. replace (TH + 2824 - (TH + 2800)) with 24 in SJ by lia. change (Z.to_nat 24) with 24%nat in SJ.
    unfold wz.
    step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step.
    (* [comment removed for export] *)
    remember (TH + 2912 + 8 * c) as HB eqn:EHB.
    lazymatch goal with H : stk _ _ (TH + 2824) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2824) HB (TH + 3168) H ltac:(hci; lia)) as [TS3 TS4]; clear H end.
    destruct (stk_split asegs _ HB (HB + 8) (TH + 3168) TS4 ltac:(hci; lia)) as [TS5 TS6]. clear TS4.
    destruct (stk_cells _ _ _ TS5 ltac:(hci; lia)) as [hj HJ]. replace (HB + 8 - HB) with 8 in HJ by lia. change (Z.to_nat 8) with 8%nat in HJ.
    (* [comment removed for export] *)
    Ltac tailD HB :=
      (* [comment removed for export] *)
      step; rewrite (unsigned_lit c), Z.shiftl_mul_pow2 by lia; change (2^3) with 8;
      step; match goal with |- context [Z_to_bv 64 (TH + 2912 + c * 8)] => replace (TH + 2912 + c * 8) with HB by lia end;
      step; step; step;
      let K2 := fresh "K2" in
      step; step; [if_cases K2; [exfalso; revert K2; vm_compute; discriminate|]; clear K2 |..];
      step; step; step; rewrite sx32_wz by lia; step; [if_cases K2; [exfalso; revert K2; vm_compute; discriminate|]; clear K2|..];
      step; step; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      assert (Rsize : 0 <= needed < 18446744073709551616) by lia.
      step. step. step. step. step. step. remregF 11 e1 E1 (cb1 needed).
      step. step. step. step. step. step. remregF 11 e2 E2 (cb2 e1).
      do 8 step. step. step. remregF 11 e3 E3 (cb3 e2).
      step. step. remregF 11 e4 E4 (cb4 e3).
      step. step. remregF 11 e5 E5 (cb5 e4).
      step. step. remregF 11 e6 E6 (cb6 e5).
      step. remregF 11 e7 E7 (cb7 e6).
      step. step. step. remregF 11 e8 E8 (cb8 e7).
      step. step. step. step. remregF 11 e9 E9 (cb9 e8).
      step. step. remregF 11 e10 E10 (cb10 e9).
      step. step. step. step. step. remregF 11 e11 E11 (cb11 e10).
      step. remregF 12 e12 E12 (cb12 e11).
      step. step. remregF 14 e13 E13 (cb13 needed e12).
      step. remregF 12 e14 E14 (cb14 e12).
      step. step. step. step. remregF 12 e15 E15 (cb15 needed e14).
      step. step. step. step. remregF 11 e16 E16 (cb16 e11 e13 e15).
      replace e16 with c in *.
      2:{ symmetry. unhide_hyp EQh. destruct EQh as [-> _].
          eapply (cidbits_ok needed); try eassumption. clear - K SZ; try acb. unfold kMaxSize in SZ. lia. }
      (* [comment removed for export] *)
      tailD HB.
      + pose proof (stk_of_rw_cells _ _ _ _ SJ) as Q1; pose proof (stk_of_rw_cells _ _ _ _ HJ) as Q2;
        cbn [cells_size csize Nat.add] in Q1, Q2; change (Z.of_nat 24) with 24%Z in Q1; change (Z.of_nat 8) with 8%Z in Q2;
        replace (TH + 2800 + 24) with (TH + 2824) in Q1 by lia;
        lazymatch type of Q1 with stk _ ?mm _ _ =>
          assert (TSTn : stk asegs mm (TH + 2800) (TH + 3168))
            by (eapply stk_merge; [exact Q1| eapply stk_merge; [exact TS3| eapply stk_merge; [exact Q2| exact TS6| lia]| lia]| lia]) end;
        clear Q1 Q2 SJ HJ TS3 TS6;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 1668288) _ _ _ _) => step end);
        eapply partE; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]);
        try (unhide_hyp FLh; unfold wz; f_equal; lia).
      + pose proof (stk_of_rw_cells _ _ _ _ SJ) as Q1; pose proof (stk_of_rw_cells _ _ _ _ HJ) as Q2;
        cbn [cells_size csize Nat.add] in Q1, Q2; change (Z.of_nat 24) with 24%Z in Q1; change (Z.of_nat 8) with 8%Z in Q2;
        replace (TH + 2800 + 24) with (TH + 2824) in Q1 by lia;
        lazymatch type of Q1 with stk _ ?mm _ _ =>
          assert (TSTn : stk asegs mm (TH + 2800) (TH + 3168))
            by (eapply stk_merge; [exact Q1| eapply stk_merge; [exact TS3| eapply stk_merge; [exact Q2| exact TS6| lia]| lia]| lia]) end;
        clear Q1 Q2 SJ HJ TS3 TS6;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 1668288) _ _ _ _) => step end);
        eapply partE; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]);
        try (unhide_hyp FLh; unfold wz; f_equal; lia).
    - (* [comment removed for export] *)
      step. step. rewrite (unsigned_lit (needed + 31)), Z.shiftr_div_pow2 by lia. change (2^5) with 32.
      replace ((needed + 31) / 32) with c.
      2:{ unhide_hyp EQh. destruct EQh as [-> _]. unfold class_id. replace (needed <=? 512) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      step. tailD HB.
      + pose proof (stk_of_rw_cells _ _ _ _ SJ) as Q1; pose proof (stk_of_rw_cells _ _ _ _ HJ) as Q2;
        cbn [cells_size csize Nat.add] in Q1, Q2; change (Z.of_nat 24) with 24%Z in Q1; change (Z.of_nat 8) with 8%Z in Q2;
        replace (TH + 2800 + 24) with (TH + 2824) in Q1 by lia;
        lazymatch type of Q1 with stk _ ?mm _ _ =>
          assert (TSTn : stk asegs mm (TH + 2800) (TH + 3168))
            by (eapply stk_merge; [exact Q1| eapply stk_merge; [exact TS3| eapply stk_merge; [exact Q2| exact TS6| lia]| lia]| lia]) end;
        clear Q1 Q2 SJ HJ TS3 TS6;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 1668288) _ _ _ _) => step end);
        eapply partE; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]);
        try (unhide_hyp FLh; unfold wz; f_equal; lia).
      + pose proof (stk_of_rw_cells _ _ _ _ SJ) as Q1; pose proof (stk_of_rw_cells _ _ _ _ HJ) as Q2;
        cbn [cells_size csize Nat.add] in Q1, Q2; change (Z.of_nat 24) with 24%Z in Q1; change (Z.of_nat 8) with 8%Z in Q2;
        replace (TH + 2800 + 24) with (TH + 2824) in Q1 by lia;
        lazymatch type of Q1 with stk _ ?mm _ _ =>
          assert (TSTn : stk asegs mm (TH + 2800) (TH + 3168))
            by (eapply stk_merge; [exact Q1| eapply stk_merge; [exact TS3| eapply stk_merge; [exact Q2| exact TS6| lia]| lia]| lia]) end;
        clear Q1 Q2 SJ HJ TS3 TS6;
        try (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 1668288) _ _ _ _) => step end);
        eapply partE; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]);
        try (unhide_hyp FLh; unfold wz; f_equal; lia).
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Alloc.
