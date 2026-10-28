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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AW_Alloc1 AW_Alloc2 AW_Alloc3 AW_Alloc4 AllocTacX.

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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partC' : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte) (av sv : Z),
    av = Z.max size 8 -> sv = rz_log size ->
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch W m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    rw_cells asegs mB P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs mB (P + 8) [C8 (wz csz)] -> u32arr asegs mB (P + 16) (wlist (rev chunks)) ->
    stk asegs mB (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs mB (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs mB AB (AB + csz) ->
    u8arr asegs mB (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mB (TH + 2800) (TH + 3168) ->
    DEPOT asegs d mB ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 8) (wz 0) (wz av) (wz 8) x12 x13 x14 x15 x16 x17
               (wz 8) (wz sv) (wz 0x10000) (wz size) (wz AINST) (wz SO) (wz 0xffff) (wz 7) (wz (AINST + 2047)) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x196fb0) fc None mB (seg_rom asegs)).
  Proof. intros until sv. intros -> ->. intros. eapply partC; eassumption. Qed.

  (* [comment removed for export] *)
  Lemma partB : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte),
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch W m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    rw_cells asegs mB P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs mB (P + 8) [C8 (wz csz)] -> u32arr asegs mB (P + 16) (wlist (rev chunks)) ->
    stk asegs mB (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs mB (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs mB AB (AB + csz) ->
    u8arr asegs mB (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mB (TH + 2800) (TH + 3168) ->
    DEPOT asegs d mB ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 8) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz 8) (wz (rz_log size)) x20 (wz size) (wz AINST) (wz SO) x24 (wz 7) (wz (AINST + 2047)) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x196f68) fc None mB (seg_rom asegs)).
  Proof.
    intros until j8. intros ENV MI MU WM FR ST QC1 QC2 QC3 QC4 QST CHUNK SHK TST DEP.
    unfold W in MU. prep. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold AINST.
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    assert (RZL : 0 <= rz_log size <= 7)
      by (unfold rz_log; repeat match goal with |- context [if ?b then _ else _] => destruct b end; (first [clear; lia | lia])).
    (* [comment removed for export] *)
    step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => replace (Z_to_bv 64 (Z.land x y)) with (wz 16) by (apply bv_eq; vm_compute; reflexivity) end.
    step. callD rzlog16_spec. all: try reflexivity. all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia.
    (* [comment removed for export] *)
    step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => replace (Z_to_bv 64 (Z.land x y)) with (wz 2048) by (apply bv_eq; vm_compute; reflexivity) end.
    step. callD rzlog2048_spec. all: try reflexivity. all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia.
    unfold wz.
    (* [comment removed for export] *)
    Ltac finishB :=
      lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x196fb0) _ _ _ _) =>
        eapply partC'; try eassumption; try reflexivity; try (econstructor; eassumption); try lia end.
    step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    - (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      + step. step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [finishB| step; finishB].
      + step. step. step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [step; finishB| step; finishB].
    - (* [comment removed for export] *)
      step. step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia. { exfalso. lia. }
      step. step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia; [finishB| step; finishB].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partB' : forall (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte) (sv : Z),
    sv = rz_log size ->
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch W m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    rw_cells asegs mB P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs mB (P + 8) [C8 (wz csz)] -> u32arr asegs mB (P + 16) (wlist (rev chunks)) ->
    stk asegs mB (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs mB (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs mB AB (AB + csz) ->
    u8arr asegs mB (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mB (TH + 2800) (TH + 3168) ->
    DEPOT asegs d mB ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 8) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (wz 8) (wz sv) x20 (wz size) (wz AINST) (wz SO) x24 (wz 7) (wz (AINST + 2047)) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x196f68) fc None mB (seg_rom asegs)).
  Proof. intros until sv. intros ->. intros. eapply partB; eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aenv_now : forall m1, AENV tp TSD CTX TH sb SO T rest m -> munch W m m1 -> wmono asegs m m1 -> AENV tp TSD CTX TH sb SO T rest m1.
  Proof.
    intros m1 E MU WM. unfold W in MU. unfold depot_W in MU. prep. open_env E.
    region_table; lazymatch goal with MUh : munch ?W0 _ _ |- _ => region_hull_memo W0 end.   (* [comment removed for export] *)
    econstructor; unfold AGOT_VALS; cbn [map repeat];
      first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; slia]
            | eapply u64arr_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia] ].
  Qed.

End Alloc.
