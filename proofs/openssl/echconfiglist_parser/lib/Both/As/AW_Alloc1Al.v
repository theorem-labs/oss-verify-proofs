(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AW_AllocBaseAl AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)

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
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: depot_W d.
  Let W2 : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: nil.
  Let POST := allocate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size AB U rz csz P cnt mc TH id chunks
                            (d_put d (depot_hash T) n).
  Let AFR := aframeAl sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

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
  Hypothesis ABA : hidden (AB mod 64 = 0).   (* [comment removed for export] *)
  Hypothesis RZ64 : hidden (rz mod 64 = 0).  (* [comment removed for export] *)
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
    assert (RZB : 16 <= rz <= 2048 /\ size + rz + 64 <= needed /\ 8 + rz <= needed /\ needed < size + rz + 128)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 64 - 1) / 64 * 8 + 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 4294967296 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz
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
  Lemma aenv_now0 : forall m0 m1, AENV tp TSD CTX TH sb SO T rest m0 -> munch W m0 m1 -> wmono asegs m0 m1 -> AENV tp TSD CTX TH sb SO T rest m1.
  Proof.
    intros m0 m1 E MU0 WM0. unfold W in MU0. unfold depot_W in MU0. prep. open_env E.
    region_table; lazymatch goal with MUh : munch ?W0 _ _ |- _ => region_hull_memo W0 end.   (* [comment removed for export] *)
    econstructor; unfold AGOT_VALS; cbn [map repeat];
      first [ eapply rw_cells_transport; [eassumption| exact MU0| exact WM0| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; slia]
            | eapply u64arr_transport; [eassumption| exact MU0| exact WM0| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia] ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partF : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mF : mem) (j8 : list byte) (jj0 jj1 jj2 jj3 : word) (b1 : Z),
    AENV tp TSD CTX TH sb SO T rest mF -> mem_inv asegs mF -> munch W m mF -> wmono asegs m mF ->
    AFR mF j8 -> stk asegs mF lo (bv_unsigned sp + -128) ->
    rw_cells asegs mF P [C4 (wz (cnt - 1)); C4 (wz mc)] -> u32arr asegs mF (P + 16) (wlist (rev (tl chunks))) ->
    stk asegs mF (P + 16 + 4 * (cnt - 1)) (P + 80) -> rw_cells asegs mF (TH + 208 + 2560) [C8 jj0; C8 jj1; C8 jj2; C8 jj3] ->
    rw_cells asegs mF (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)] -> b1_ok b1 ->
    (rz = 16 \/ (rw_cells asegs mF AB [C8 (wz kAllocBegMagic); C8 (wz (U + -16))] /\ stk asegs mF (AB + 16) (U + -16))) ->
    forall fill shd, u8arr asegs mF U fill -> fill = repeat (b8 0xbe) (Z.to_nat fl) -> Z.of_nat (length fill) = fl ->
    stk asegs mF (U + fl) (AB + csz) ->
    u8arr asegs mF (sh AB) shd -> shd = alloc_shadow rz size csz -> Z.of_nat (length shd) = csz8 ->
    stk asegs mF (TH + 2800) (TH + 3168) ->
    forall mC, DEPOT asegs (d_put d (depot_hash T) n) mC -> munch W2 mC mF -> wmono asegs mC mF ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 (wz U) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x197524) fc None mF (seg_rom asegs)).
  Proof.
    intros until b1. intros ENV MI MU WM FR ST QC1 QC3 QC4 QST HDR B1M MAG fill shd FILL FILLE FILLN UTAIL SHD SHDE SHDN TST mC DEPC MUC WMC.
    unfold W in MU. unfold W2 in MUC. prep. open_env ENV. unfold AFR, aframeAl in FR. unfold wz in *.
    (* [comment removed for export] *)
    destruct MAG as [RZ16 | [MAGC MAGS]].
    all: step; step; step; callD run_malloc_hooks_spec. all: rewrite ?unsigned_lit by (first [clear - HI SPR BND ALN SPQ; lia | lia]). all: try eassumption; try (lia_guard; lia).
    (* [comment removed for export] *)
    all: do 16 step.
    all: lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
    all: apply evt_done; unfold POST, allocate_post; do 18 eexists; exists b1; eexists; split; [reflexivity|].
    all: repeat match goal with |- _ /\ _ => split end; try assumption.
    all: try (left; assumption). all: try (right; split; assumption). all: try (subst fill; assumption). all: try (subst shd; assumption).
    all: try exact B1M. all: try (lia_guard; lia). all: try eassumption.
    all: try (unhide_hyp FLh; rewrite <- FLh; first [subst fill; assumption | assumption]).
    all: eapply DEPOT_transport; [exact DEPC| eassumption| eassumption| solve_depot_avoid].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma partE : forall (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mE : mem) (j8 : list byte) (jj0 jj1 jj2 jj3 : word) (st0 x2 : Z) (shd : list byte),
    x12 = wz fl ->
    AENV tp TSD CTX TH sb SO T rest mE -> mem_inv asegs mE -> munch W m mE -> wmono asegs m mE ->
    AFR mE j8 -> stk asegs mE lo (bv_unsigned sp + -128) ->
    rw_cells asegs mE P [C4 (wz (cnt - 1)); C4 (wz mc)] -> u32arr asegs mE (P + 16) (wlist (rev (tl chunks))) ->
    stk asegs mE (P + 16 + 4 * (cnt - 1)) (P + 80) -> rw_cells asegs mE (TH + 208 + 2560) [C8 jj0; C8 jj1; C8 jj2; C8 jj3] ->
    rw_cells asegs mE (U + -16) [C1 (b8 st0); C1 (b8 x2); C2 (wz 0); C4 (wz size); C8 (wz id)] ->
    0 <= st0 < 256 -> 0 <= x2 < 256 -> b1_ok (Z.land x2 243) ->
    stk asegs mE AB (U + -16) ->
    stk asegs mE U (AB + csz) ->
    u8arr asegs mE (sh AB) shd -> shd = alloc_shadow rz size csz -> Z.of_nat (length shd) = csz8 ->
    stk asegs mE (TH + 2800) (TH + 3168) ->
    forall mC, DEPOT asegs (d_put d (depot_hash T) n) mC -> munch W2 mC mE -> wmono asegs mC mE ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) (wz 6979832) x11 x12 x13 x14 x15 x16 x17
               (wz AB) x19 (wz U) (wz (U + -16)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1974c4) fc None mE (seg_rom asegs)).
  Proof.
    intros until shd. intros X12 ENV MI MU WM FR ST QC1 QC3 QC4 QST HDR ST0R X2R X2M CHL USR SHD SHDE SHDN TST mC DEPC MUC WMC. subst x12.
    unfold W in MU. unfold W2 in MUC. prep. open_env ENV. unfold AFR, aframeAl in FR. unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    change (sx32 (Z_to_bv 64 190)) with (sx32 (wz 190)). rewrite sx32_wz by lia. unfold wz.
    destruct (stk_split asegs mE U (U + fl) (AB + csz) USR ltac:(hci; lia)) as [US1 US2].
    destruct (stk_cells _ _ _ US1 ltac:(hci; lia)) as [fj FJ]. replace (U + fl - U) with fl in FJ by lia.
    callD memset_spec. all: rewrite ?unsigned_lit by (first [clear - HI SPR BND CSZ RZB ALN EQS C8F; lia | lia]). all: try exact FJ; try eassumption; try lia.
    change (190 mod 256) with 190 in POST0.
    (* [comment removed for export] *)
    step. callD lsan_disabled_spec. all: try eassumption.
    step. rewrite zxb_b8 by lia. step. step. step. step. step.
    pose proof (land_lt_pow2 x2 243 8 ltac:(hci; lia) ltac:(hci; lia)) as XL. change (2^8) with 256 in XL.
    match goal with |- context [Z_to_bv 64 (Z.lor ?a ?b)] =>
      replace (Z_to_bv 64 (Z.lor a b)) with (Z_to_bv 64 (Z.land x2 243))
        by (f_equal; unfold wz; rewrite (unsigned_lit x2) by lia;
            replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 0))))) with 0 by (vm_compute; reflexivity);
            change (Z.land 0 12) with 0; rewrite (unsigned_lit 0) by lia; rewrite unsigned_lit by lia; rewrite Z.lor_0_r; reflexivity) end.
    (* [comment removed for export] *)
    st1. step. st1. change (Z_to_bv 8 2) with (b8 2) in HDR.
    replace ((Z.land x2 243) mod 256) with (Z.land x2 243) in HDR by (symmetry; apply Z.mod_small; destruct X2M; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ POST0) as FILL. change (Z_to_bv 8 190) with (b8 190) in FILL.
    assert (FILLN : Z.of_nat (length (repeat (b8 190) (Z.to_nat fl))) = fl) by (rewrite repeat_length; lia).
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by lia.
      eapply partF; try eassumption; try reflexivity; try (econstructor; eassumption).
      all: first [ exact X2M | left; lia ].
    - rewrite ?unsigned_lit in K by lia.
      assert (RZ32 : 32 <= rz) by (clear - ALN K RZB EQS; try acb; lia).
      (* [comment removed for export] *)
      step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
      step. step.
      destruct (stk_split asegs _ AB (AB + 16) (U + -16) CHL ltac:(hci; lia)) as [MG1 MG2].
      destruct (stk_cells _ _ _ MG1 ltac:(hci; lia)) as [mj MAGC]. replace (AB + 16 - AB) with 16 in MAGC by lia. change (Z.to_nat 16) with 16%nat in MAGC.
      step. step. st1.
      eapply partF; try eassumption; try reflexivity; try (econstructor; eassumption).
      all: first [ exact X2M
                 | right; split; [| eassumption]; unfold kAllocBegMagic, wz; exact MAGC ].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Alloc.
