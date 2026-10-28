(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BAllocSim BMmapSim BazyRestrict BazyLedger BazySR BazyNodes BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BW_PoisonShadow BW_Leaves BllocWalkKit BW_MmapFixed BW_Efs BW_Populate BW_Gfa BW_InitCache BW_Refill BW_LargeAlloc1 BecLazy BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition rf_n (c : Z) : Z := max_count c / 2.
Section RfArith.
  Variables (c nf mfa au mu : Z) (fl : list Z).
  Let n := rf_n c. Let csz := class_size c.

  Definition rf_k : Z := n - nf.
  Definition rf_total : Z := au + csz * rf_k.

  Definition rf_mu' : Z := if nf <? n then (if mu <? rf_total then mu + pop_ms rf_total mu else mu) else mu.

  Definition rf_nnew : Z := if nf <? n then (rf_mu' - au) / csz else 0.
  Definition rf_nf1 : Z := nf + rf_nnew.
  Definition rf_mfa' : Z := if nf <? n then (if 4 * rf_nf1 <=? mfa then mfa else efs_new rf_nf1) else mfa.
  Definition rf_au' : Z := au + rf_nnew * csz.

  Definition rf_fl1 : list Z := carve_asc au csz 0 (Z.to_nat rf_nnew) ++ fl.
End RfArith.

Lemma rf_batch_small : forall c, 1 <= c <= 30 -> class_size c * rf_n c <= 65536 /\ 16 <= class_size c.
Proof.
  intros c Hc. unfold rf_n.
  assert (CASES : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
                  \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30) by lia.
  clear Hc. repeat match type of CASES with _ \/ _ => destruct CASES as [EC|CASES] | _ => rename CASES into EC end.
  all: subst c;
    match goal with |- context [max_count ?x] => let v := eval vm_compute in (max_count x) in change (max_count x) with v end;
    match goal with |- context [class_size ?x] => let v := eval vm_compute in (class_size x) in change (class_size x) with v end; lia.
Qed.

Lemma fam_transport : forall (CA : Z) (W : list ivl) (m m' : mem) (V : Z -> word -> word -> Prop),
  (forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs] /\ V c' mc cs) ->
  munch W m m' -> wmono asegs m m' ->
  (forall c', 1 <= c' <= 31 -> disjoint_from W (CA + 80 * c' + 4) 4 /\ disjoint_from W (CA + 80 * c' + 8) 8) ->
  (forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m' (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 cs] /\ V c' mc cs).
Proof.
  intros CA W m m' V FAM MU WM DJ c' Hc. destruct (FAM c' Hc) as (mc & cs & A & B & HV). destruct (DJ c' Hc) as [D1 D2].
  exists mc, cs. split; [| split; [| exact HV]].
  - eapply rw_cells_transport; [exact A| exact MU| exact WM| exact D1].
  - eapply rw_cells_transport; [exact B| exact MU| exact WM| exact D2].
Qed.

Record RENV (tp : word) (TSD CTX TH sb ARI : Z) (m : mem) : Prop := mkRENV {
  re_senv : SENV tp TSD CTX TH m;
  re_isb  : rw_cells asegs m 1628664 [C8 (wz sb); C4 (wz 0xffffffff); C4 (wz 0)];
  re_iri  : rw_cells asegs m 1628680 [C8 (wz ARI)];
  re_pmh  : rw_cells asegs m 1628688 [C8 (wz 0)]
}.
Lemma renv_transport : forall tp TSD CTX TH sb ARI m m' W,
  RENV tp TSD CTX TH sb ARI m -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W 1640608 8 -> disjoint_from W (bv_unsigned tp + -88) 8 -> disjoint_from W TSD 8 -> disjoint_from W (CTX + 152) 8 ->
  disjoint_from W 1640604 1 -> disjoint_from W 1593472 120 -> disjoint_from W 1642552 8 -> disjoint_from W 1645856 24 ->
  disjoint_from W 2239456 8 -> disjoint_from W 2239480 8 -> disjoint_from W 2239596 1 -> disjoint_from W 1601864 8 ->
  disjoint_from W 2231008 8 -> disjoint_from W 1601920 8 ->
  disjoint_from W 1628664 16 -> disjoint_from W 1628680 8 -> disjoint_from W 1628688 8 ->
  RENV tp TSD CTX TH sb ARI m'.
Proof.
  intros tp TSD CTX TH sb ARI m m' W [E I1 I2 I3] MU WM; intros; constructor.
  - eapply senv_transport; eassumption.
  - eapply rw_cells_transport; [exact I1 | exact MU | exact WM | assumption].
  - eapply rw_cells_transport; [exact I2 | exact MU | exact WM | assumption].
  - eapply rw_cells_transport; [exact I3 | exact MU | exact WM | assumption].
Qed.

End HCW.

Ltac renv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with RENV ?tp ?TSD ?CTX ?TH ?sb ?ARI m =>
      region_table; region_hull_memo W;
      assert (E' : RENV tp TSD CTX TH sb ARI m');
      [ apply (renv_transport tp TSD CTX TH sb ARI m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma icW_disjoint : forall CA A n, (A + n <= CA + 84 \/ CA + 2496 <= A) -> disjoint_from (icW CA) A n.
Proof. intros CA A n H. unfold icW. cbn. repeat split; lia. Qed.
Lemma icW_disjoint_count : forall CA c, 1 <= c <= 31 -> disjoint_from (icW CA) (CA + 80 * c) 4.
Proof. intros CA c H. unfold icW. cbn. repeat split; lia. Qed.
Lemma icW_disjoint_arr : forall CA c, 1 <= c <= 31 -> disjoint_from (icW CA) (CA + 80 * c + 16) 64.
Proof. intros CA c H. unfold icW. cbn. repeat split; lia. Qed.

Lemma poisoned_0 : forall m A v, 0 <= A -> A mod 8 = 0 -> sh A <= 2^64 -> poisoned m A 0 v.
Proof.
  intros m A v H1 H2 H3. unfold poisoned, SHAD, poison_bytes. cbn [repeat]. split; [exact H1|]. split; [exact H2|].
  split; (split; [| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]); unfold sh, ASHADOW_BASE in *; lia.
Qed.

Definition rf1_at (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu : Z) (fl : list Z) (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a6 a7 s2' x5 x6 x7 x8 x9 s10' s11' t3 t4 t5 t6 q0 q1 q2 q3 : word) (j8 j24 : list byte) m',
  let n := rf_n c in
     lzok asegs L S Zr (mkCfg msF' mo')
  /\ restrict L S msF'
     = MS (mkR (wz 0x97384) (Z_to_bv 64 (bv_unsigned sp + -160)) gp tp t0 t1 t2 (wz R) (wz AINST) (wz (R + 8)) (wz (CA + 2560)) (wz c) (wz (P + 16)) (wz n) (wz nf) a6 a7
               s2' (wz (2^61)) (wz FAB) x5 x6 x7 x8 x9 s10' s11' t3 t4 t5 t6)
          F (Z_to_bv 64 (if nf <? n then 0x976e4 else 0x9759c)) fc None m' (seg_rom asegs)
  /\ same_but_materialized mo mo'
  /\ munch ((lo, bv_unsigned sp) :: (R, R + 8) :: icW CA) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ RENV tp TSD CTX TH sb ARI m'
  /\ stk asegs m' lo (bv_unsigned sp + -160)
  /\ rw_cells asegs m' (bv_unsigned sp + -160)
       [CB 24 j24; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 (wz n); C8 (wz P); C8 (wz 0x97384)]
  /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra]
  /\ rw_cells asegs m' P [C4 (wz 0)] /\ stk asegs m' (P + 16) (P + 80)
  /\ (forall c', 1 <= c' <= 31 -> rw_cells asegs m' (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 (wz (class_size c'))])
  /\ rw_cells asegs m' (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m' (TH + 2800) (TH + 3168)
  /\ rw_cells asegs m' R [C8 (wz kWriterLock)]
  /\ rw_cells asegs m' (R + 8) [C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)]
  /\ stk asegs m' (R + 64) (R + 68) /\ rw_cells asegs m' (R + 68) [C1 (b8 0)] /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev fl)) /\ stk asegs m' (FAB + 4 * nf) (FAB + mfa) /\ stk asegs m' (rbeg + au) (rbeg + mu).

Definition rf_W (lo spv P R FAB rbeg TH CA nf mfa mu mfa' mu' : Z) : list ivl :=
  (lo, spv) :: (P, P + 4) :: (P + 16, P + 80) :: (R, R + 8) :: (R + 16, R + 40) :: (R + 48, R + 56) :: (R + 68, R + 69) :: (R + 72, R + 80)
  :: (FAB + 4 * nf, FAB + mfa') :: (rbeg + mu, rbeg + mu') :: (sh (FAB + mfa), sh (FAB + mfa) + (mfa' - mfa) / 8)
  :: (sh (rbeg + mu), sh (rbeg + mu) + (mu' - mu) / 8) :: (TH + 2792, TH + 3168) :: icW CA.

Definition rf_done (L S Zr : list (word * word)) (mo : Model)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo c CA P R rbeg FAB TH nf mfa au mu : Z) (fl : list Z) (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 q0 q1 q2 q3 : word) m' L' S',
  let n := rf_n c in let mu' := rf_mu' c nf au mu in let nnew := rf_nnew c nf au mu in
  let nf1 := rf_nf1 c nf au mu in let mfa' := rf_mfa' c nf mfa au mu in let au' := rf_au' c nf au mu in let fl1 := rf_fl1 c nf au mu fl in
     lzok asegs L' S' Zr (mkCfg msF' mo')
  /\ restrict L' S' msF'
     = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)

  /\ L' = (if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract L (rbeg + mu) (rbeg + mu') else L) (FAB + mfa) (FAB + mfa')
            else (if mu <? mu' then maps_subtract L (rbeg + mu) (rbeg + mu') else L))
  /\ S' = (if mfa <? mfa' then [(wz (sh (FAB + mfa)), wz ((mfa' - mfa) / 8))] else [])
           ++ (if mu <? mu' then [(wz (sh (rbeg + mu)), wz ((mu' - mu) / 8))] else []) ++ S
  /\ nonvm_same mo mo'
  /\ vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) /\ vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) /\ vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo)
  /\ vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) /\ vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo)
  /\ vm_noaccess (m_vmmaps mo')
     = (if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (vm_noaccess (m_vmmaps mo)) (rbeg + mu) (rbeg + mu') else vm_noaccess (m_vmmaps mo)) (FAB + mfa) (FAB + mfa')
        else (if mu <? mu' then maps_subtract (vm_noaccess (m_vmmaps mo)) (rbeg + mu) (rbeg + mu') else vm_noaccess (m_vmmaps mo)))
  /\ eager_used mo' <= eager_used mo + (mu' - mu) + (mfa' - mfa)

  /\ munch (rf_W lo (bv_unsigned sp) P R FAB rbeg TH CA nf mfa mu mfa' mu') m m'
  /\ wmono asegs m m' /\ mem_inv asegs m'
  /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' P [C4 (wz n)]
  /\ (forall c', 1 <= c' <= 31 -> rw_cells asegs m' (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 (wz (class_size c'))])
  /\ u32arr asegs m' (P + 16) (wlist (rev (firstn (Z.to_nat n) fl1))) /\ stk asegs m' (P + 16 + 4 * n) (P + 80)
  /\ rw_cells asegs m' R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz (nf1 - n)); C8 (wz mfa'); C8 (wz au'); C8 (wz 0); C8 (wz mu'); C8 (wz 0)]
  /\ stk asegs m' (R + 64) (R + 68) /\ rw_cells asegs m' (R + 68) [C1 (b8 0)] /\ stk asegs m' (R + 69) (R + 128)
  /\ u32arr asegs m' FAB (wlist (rev fl1)) /\ stk asegs m' (FAB + 4 * nf1) (FAB + mfa')
  /\ stk asegs m' (rbeg + au) (rbeg + mu')
  /\ poisoned m' (rbeg + mu) (Z.to_nat ((mu' - mu) / 8)) 0xfa /\ poisoned m' (FAB + mfa) (Z.to_nat ((mfa' - mfa) / 8)) 0xfa
  /\ rw_cells asegs m' (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] /\ stk asegs m' (TH + 2800) (TH + 3168).

Section Refill.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).

  Variables (lo sb c CA TH CTX TSD : Z).
  Variables (nf mfa au mu : Z) (fl : list Z) (inited : bool).
  Let ARI := sb + kSpaceSize.
  Let R := ARI + REGIONINFO_SIZE * c.
  Let P := CA + PCLASS_SIZE * c.
  Let rbeg := sb + c * 2^32.
  Let FAB := rbeg + kFreeArrayOffset.
  Let n := rf_n c.
  Let csz := class_size c.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 640 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis CAE : CA = TH + 208.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize + kPageSize <= aceil. Hypothesis SBA : hidden (sb mod 65536 = 0).
  Hypothesis TPR : 6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis THA : hidden (TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).

  Hypothesis NFR : 0 <= nf /\ 4 * nf <= mfa /\ mfa <= kFreeArraySize. Hypothesis MFAA : hidden (mfa mod kFreeArrayMapSize = 0).
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset. Hypothesis MUA : hidden (mu mod kUserMapSize = 0).
  Hypothesis FLL : length fl = Z.to_nat nf.

  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz CA) (wz P) (wz AINST) (wz c) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                        F (Z_to_bv 64 0x97344) fc None m (seg_rom asegs).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis ENV : RENV tp TSD CTX TH sb ARI m.
  Hypothesis LENF : Z.of_nat (length (wlist (rev fl))) = nf.

  Hypothesis PC1 : rw_cells asegs m P [C4 (wz 0); C4 (wz (if inited then max_count c else 0))].
  Hypothesis PCJ : stk asegs m (P + 16) (P + 80).
  Hypothesis FAM : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m (CA + 80 * c' + 8) [C8 cs]
                                             /\ (inited = true -> mc = wz (max_count c') /\ cs = wz (class_size c')).

  Variables (q0 q1 q2 q3 : word).
  Hypothesis QST : rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).

  Hypothesis RI : rw_cells asegs m R [C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)].
  Hypothesis RIJ : stk asegs m (R + 64) (R + 68).
  Hypothesis EXH : rw_cells asegs m (R + 68) [C1 (b8 0)].
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis FARR : u32arr asegs m FAB (wlist (rev fl)).
  Hypothesis FAJ : stk asegs m (FAB + 4 * nf) (FAB + mfa).
  Hypothesis USJ : stk asegs m (rbeg + au) (rbeg + mu).

  Ltac prepR :=
    unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset in NFR, AUR;
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 6762288 <= TSD /\ TSD + 8 <= 7241728 /\ 7241728 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 + 4096 <= aceil
               /\ 6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 7241728 /\ bv_unsigned sp + 16 <= 140737488355328)
      by (clear - LO RNG SBR TPR SPT; try acb; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, kPageSize, AIMG_TOP in *; acb; aunf; lia);
        region_sides; name_bands;
    pose proof (max_count_facts c ltac:(hci; clear - HC; try acb; lia)) as MCF; fold n in MCF;
    assert (NR : 1 <= n <= 8 /\ n + n = max_count c) by (clear - MCF; try acb; subst n; unfold rf_n; destruct MCF as [M1 M2];
       destruct (proj1 (Z.even_spec _) M2) as [k Hk]; rewrite Hk in *; rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia);
    clear MCF;
    assert (CSZ : 16 <= csz <= 65536) by (subst csz; pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as CST; clear - CST HC; try acb; lia);
    assert (GEO : R = sb + 137438953472 + 128 * c /\ P = CA + 80 * c /\ rbeg = sb + c * 4294967296 /\ FAB = rbeg + 3758096384 /\ ARI = sb + 137438953472)
      by (subst R P rbeg FAB ARI; unfold kSpaceSize, REGIONINFO_SIZE, PCLASS_SIZE, kFreeArrayOffset; repeat split; reflexivity);
    destruct GEO as (ER & EP & ERB & EFAB & EARI);
    assert (DEFh : hidden (n = rf_n c /\ csz = class_size c)) by (split; split; reflexivity);

    assert (CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0)
      by (acb; destruct THA as [T16]; match goal with TB : akobj TH 4096 |- _ => clear - BND CAE T16 TB end; try acb; subst CA;
          split; [eapply akobj_sub; [eassumption| lia| lia] | repeat split; [lia| Z.div_mod_to_equations; lia]]);
    assert (ARIR : AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND EARI S64; try acb; rewrite EARI;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    assert (SBR4 : AHI_LO <= sb /\ sb + 2^37 <= aceil /\ sb mod 4096 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND S64; try acb;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    assert (RR : AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND ER S64 HC; try acb; rewrite ER;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);
    assert (RBG : AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0)
      by (unfold AHI_LO; acb; destruct SBA as [S64]; clear - BND ERB S64 HC; try acb; rewrite ERB;
          repeat split; [lia| lia| Z.div_mod_to_equations; lia]);

    assert (ALh : hidden ((akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0) /\ (AHI_LO <= ARI /\ ARI + 4096 <= aceil /\ ARI mod 4096 = 0)
                  /\ (AHI_LO <= sb /\ sb + 2^37 <= aceil /\ sb mod 4096 = 0) /\ (AHI_LO <= R /\ R + 128 <= aceil /\ R mod 128 = 0)
                  /\ (AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0)))
      by (split; exact (conj CAR (conj ARIR (conj SBR4 (conj RR RBG)))));
    clear CAR ARIR SBR4 RR RBG;
    assert (BNDL : sb + 137438953472 + 128 <= R /\ R + 256 <= sb + 137438953472 + 4096 /\ sb + 4294967296 <= rbeg /\ rbeg + 8589934592 <= sb + 137438953472
                   /\ FAB = rbeg + 3758096384 /\ TH + 288 <= P /\ P + 160 <= TH + 2768)
      by (clear - BND ER ERB EP EFAB CAE HC; try acb; subst CA; rewrite ER, ERB, EP; repeat split; lia).

  Ltac getAL CAR ARIR SBR4 RR RBG := lazymatch goal with H : hidden ((akobj _ _ /\ _) /\ _) |- _ =>
    pose proof H as X; destruct X as [(CAR & ARIR & SBR4 & RR & RBG)] end.

  Lemma rf_gfa : forall (t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word) (m1 : mem) (msF1 : machine_state) (mo1 : Model) (j8 : list byte),
    lzok asegs L S Zr (mkCfg msF1 mo1) ->
    restrict L S msF1 = MS (mkR (wz 0x97384) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (wz P) (wz n) (wz AINST) (wz (CA + 2560)) (wz c)
                                 (wz (P + 16)) (wz n) a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (Z_to_bv 64 0x97444) fc None m1 (seg_rom asegs) ->
    same_but_materialized mo mo1 ->
    munch ((lo, bv_unsigned sp) :: (R, R + 8) :: icW CA) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
    stk asegs m1 lo (bv_unsigned sp + -32) ->
    rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
    RENV tp TSD CTX TH sb ARI m1 ->
    rw_cells asegs m1 P [C4 (wz 0)] -> stk asegs m1 (P + 16) (P + 80) ->
    (forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (CA + 80 * c' + 8) [C8 cs]
                                /\ (mc = wz (max_count c') /\ cs = wz (class_size c'))) ->
    rw_cells asegs m1 (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3] -> stk asegs m1 (TH + 2800) (TH + 3168) ->
    rw_cells asegs m1 R [C8 (wz 0)] ->
    rw_cells asegs m1 (R + 8) [C4 (wz 0); C4 (wz 0); C8 (wz nf); C8 (wz mfa); C8 (wz au); C8 (wz 0); C8 (wz mu); C8 (wz 0)] ->
    stk asegs m1 (R + 64) (R + 68) -> rw_cells asegs m1 (R + 68) [C1 (b8 0)] -> stk asegs m1 (R + 69) (R + 128) ->
    u32arr asegs m1 FAB (wlist (rev fl)) -> stk asegs m1 (FAB + 4 * nf) (FAB + mfa) -> stk asegs m1 (rbeg + au) (rbeg + mu) ->
    (forall msF' mo', rf1_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu fl msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros until j8. intros OK1 VIS1 SBM1 MU WM MI1 ST1 FR1 ENV1 PC0 PCJ1 FAM1 QST1 TST1 RI0 RI8 RIJ1 EXH1 RST1 FARR1 FAJ1 USJ1 K.
    clear MI ST ENV PC1 PCJ FAM QST TST RI RIJ EXH RST FARR FAJ USJ VISE OK. prepR.

    pose proof (re_isb _ _ _ _ _ _ _ ENV1) as ISB. pose proof (re_iri _ _ _ _ _ _ _ ENV1) as IRI.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in ISB. destruct ISB as [ISB _].
    lazymatch goal with H : rw_cells asegs m1 (R + 8) _ |- _ =>
      pose proof H as RIx;
      apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in RIx; destruct RIx as [_ RIx];
      apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RIx; destruct RIx as [RNF _]; cbn [cells_size csize Nat.add length] in RNF;
      replace (R + 8 + Z.of_nat 8) with (R + 16) in RNF by lia end.
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF1 _ mo1 Q OK1 VIS1).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (gfa_head _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 lo sb ARI c nf n);
        try eassumption; rewrite ?unsigned_lit by lia; first [eassumption | reflexivity | subst n; reflexivity | unfold kNumClasses; clear - HC; try acb; lia | clear - HI; try acb; lia | clear - NFR NR; try acb; lia]. }
    intros msF2 mo2 OK2 SBM2 HS2 P2.
    destruct P2 as (u0 & u1 & u2 & u6 & u7 & x5 & x6 & x7 & x8 & x9 & m2 & j24 & VIS2 & MU2 & WM2 & MI2 & ST2 & FR2 & LK2).
    rewrite ?unsigned_lit in VIS2, MU2, ST2, FR2 by lia.
    fold R in VIS2, MU2, LK2. fold rbeg in VIS2. fold FAB in VIS2. fold P in VIS2, FR2. unfold rf_n in n. fold n in VIS2, FR2.
    replace (bv_unsigned sp + -32 + -128) with (bv_unsigned sp + -160) in * by lia.
    replace (bv_unsigned sp + -32 - 128) with (bv_unsigned sp + -160) in * by lia.
    clear ISB IRI RI0 RNF.
    assert (FAM2 := fam_transport CA _ m1 m2 _ FAM1 MU2 WM2
            ltac:(hci; intros c' Hc'; cbn [disjoint_from]; destruct PLC as [PLC']; unfold kSpaceSize in PLC'; clear - Hc' BND BNDL CAE HI PLC'; try acb; subst CA; repeat split; lia)).
    clear FAM1. renv_at ENV1 MU2 WM2 ENV2. clear ENV1.
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
    apply K. unfold rf1_at.
    do 24 eexists.
    split; [exact OK2|]. split; [exact VIS2|].
    split; [eapply same_but_materialized_trans; eassumption|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI2|]. split; [exact ENV2|]. split; [exact ST2|]. split; [exact FR2|].
    split; [eassumption|]. split; [assumption|]. split; [assumption|].
    split. { intros c' Hc'. destruct (FAM2 c' Hc') as (mc & cs & A & B & -> & ->). split; [exact A| exact B]. }
    repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  Lemma rf_head : (forall msF' mo', rf1_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu fl msF' mo' -> sreach asegs Q (mkCfg msF' mo')) ->
                  sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. prepR.

    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RI. destruct RI as [RI0 RI8]. cbn [cells_size csize Nat.add length] in RI8.
    replace (R + Z.of_nat 8) with (R + 8) in RI8 by lia.

    pose proof PC1 as PC0. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in PC0. destruct PC0 as [PC0 MC0]. cbn [cells_size csize Nat.add length] in MC0.
    replace (P + Z.of_nat 4) with (P + 4) in MC0 by lia.

    destruct inited.
    - clear MC0. eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
      { getAL CAR ARIR SBR4 RR RBG.
        eapply (refill_head ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (wz 0) F fc m lo CA c);
          try eassumption; [clear - HI; try acb; lia | clear - HC; try acb; lia]. }
      clear PC1. intros msF1 mo1 OK1 SBM1 HS1 P1.
      destruct P1 as (m1 & j8 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1).

      assert (FAM1 := fam_transport CA _ m m1 _ FAM MU1 WM1 ltac:(hci; intros c' Hc'; cbn [disjoint_from]; clear - Hc' BND CAE HI; try acb; subst CA; repeat split; lia)).
      clear FAM. renv_at ENV MU1 WM1 ENV1. clear ENV.
      pose proof (munch_refl ((lo, bv_unsigned sp) :: (R, R + 8) :: icW CA) m) as MU. pose proof (wmono_refl asegs m) as WM.
      transport_after_call asegs m m1 MU1 WM1. clear MU1 WM1.
      rewrite ?unsigned_lit in VIS1 by lia. fold P in VIS1. unfold rf_n in n. fold n in VIS1.
      eapply rf_gfa; try eassumption.
      intros c' Hc'. destruct (FAM1 c' Hc') as (mc & cs & A & B & V). exists mc, cs. split; [exact A| split; [exact B| exact (V eq_refl)]].
    - clear PC1. eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
      { getAL CAR ARIR SBR4 RR RBG.
        eapply (refill_head_init ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo CA c);
          try eassumption; [clear - HI; try acb; lia | clear - HC; try acb; lia |].
        intros c' Hc'. destruct (FAM c' Hc') as (mc & cs & A & B & _). exists mc, cs. split; [exact A| exact B]. }
      clear FAM. intros msF1 mo1 OK1 SBM1 HS1 [P1 FAM1].
      destruct P1 as (t3' & t4' & t5' & m1 & j8 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1). rewrite VIS1 in FAM1. cbn [ms_mem] in FAM1.

      pose proof PLC as PLCx; destruct PLCx as [PLCx]; unfold kSpaceSize in PLCx.
      assert (ENV1 : RENV tp TSD CTX TH sb ARI m1).
      { apply (renv_transport tp TSD CTX TH sb ARI m m1 _ ENV MU1 WM1); cbn [disjoint_from];
          (split; [clear - BND HI CAE PLCx; try acb; lia
                 | apply icW_disjoint; match goal with TB : akobj TH 4096 |- _ => clear - BND HI CAE PLCx TB end; aunf; lia]). }
      clear ENV.
      eapply (rw_cells_transport asegs _ _ _) in PC0; [| exact MU1 | exact WM1 |
        cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; split; [clear - BND BNDL HI; try acb; lia| rewrite EP; apply icW_disjoint_count; clear -HC; lia]].
      Ltac tr_icw H MU WM hyps :=
        first [ eapply (rw_cells_transport asegs _ _ _) in H; [| exact MU | exact WM |
                  cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; split; [| apply icW_disjoint]; hyps; lia]
              | eapply (stk_transport_disjoint asegs _ _ _) in H; [| exact MU | exact WM | cbn [disjoint_from]; split; [| apply icW_disjoint]; hyps; lia]
              | eapply (u32arr_transport asegs _ _ _) in H; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; split; [| apply icW_disjoint]; hyps; lia] ].
      eapply (stk_transport_disjoint asegs _ _ _) in PCJ; [| exact MU1 | exact WM1 |
        cbn [disjoint_from]; split; [clear - BND BNDL HI; try acb; lia| replace (P + 80 - (P + 16)) with 64 by lia; rewrite EP; apply icW_disjoint_arr; clear -HC; lia]].
      tr_icw QST MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE).
      tr_icw TST MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE).
      tr_icw RI8 MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx).
      tr_icw RI0 MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx).
      tr_icw RIJ MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx).
      tr_icw EXH MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx).
      tr_icw RST MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx).
      tr_icw FARR MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx NFR LENF).
      tr_icw FAJ MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx NFR).
      tr_icw USJ MU1 WM1 ltac:(hci; clear - BND BNDL HI CAE PLCx AUR).
      pose proof (munch_refl ((lo, bv_unsigned sp) :: (R, R + 8) :: icW CA) m) as MU. pose proof (wmono_refl asegs m) as WM.
      eapply (munch_trans _ m m m1) in MU; [| eapply munch_weaken; [| exact MU1]; rx_sub_fp_struct].
      eapply (wmono_trans asegs m m m1) in WM; [| exact WM1]. clear MU1 WM1 MI ST.
      rewrite ?unsigned_lit in VIS1 by lia. fold P in VIS1. unfold rf_n in n. fold n in VIS1.
      eapply rf_gfa; try eassumption.
      intros c' Hc'. destruct (FAM1 c' Hc') as [A B]. eexists _, _. split; [exact A| split; [exact B| split; reflexivity]].
  Qed.

  Lemma rf_fast : forall msF1 mo1, n <= nf ->
    rf1_at L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R sb ARI rbeg FAB TH TSD CTX nf mfa au mu fl msF1 mo1 ->
    (forall msF' mo', rf_done L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo c CA P R rbeg FAB TH nf mfa au mu fl msF' mo' ->
                      sreach asegs Q (mkCfg msF' mo')) ->
    sreach asegs Q (mkCfg msF1 mo1).
  Proof.
    intros msF1 mo1 NF A1 K. prepR.
    clear MI ST ENV PC1 PCJ FAM QST TST RI RIJ EXH RST FARR FAJ USJ VISE OK.
    destruct A1 as (u0 & u1 & u2 & u6 & u7 & s2' & x5 & x6 & x7 & x8 & x9 & s10' & s11' & u3 & u4 & u5 & u6' & q0' & q1' & q2' & q3' & j8 & j24 & m1
                    & OK1 & VIS1 & SBM1 & MU & WM & MI1 & ENV1 & ST1 & FRG & FRR & PC0 & PCJ & FAMv & QST & TST & LK & RI8 & RIJ & EXH & RST & FARR & FAJ & USJ).
    fold n in VIS1, FRG. rewrite (proj2 (Z.ltb_ge nf n)) in VIS1 by exact NF.

    pose proof RI8 as RIx. apply (proj1 (rw_cells_app asegs _ _ [_;_] _)) in RIx. destruct RIx as [RI8a RIx].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in RIx. destruct RIx as [RNF RI24]. cbn [cells_size csize Nat.add length] in RNF, RI24.
    replace (R + 8 + Z.of_nat 8) with (R + 16) in RNF by lia. replace (R + 8 + Z.of_nat 8 + Z.of_nat 8) with (R + 24) in RI24 by lia. clear RI8.
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF1 _ mo1 Q OK1 VIS1).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (gfa_mid _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10' s11' _ _ _ _ F fc m1 R nf n);
        [clear - NF NR; try acb; lia | clear - NFR; try acb; lia | clear - RR; try acb; tauto | exact MI1 | exact RNF]. }
    clear OK1 VIS1. intros msF2 mo2 OK2 SBM2 HS2 P2. destruct P2 as (m2 & VIS2 & MU2 & WM2 & MI2 & RNF2).
    renv_at ENV1 MU2 WM2 ENV2. clear ENV1 RNF.
    assert (FAM1 : forall c', 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m1 (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m1 (CA + 80 * c' + 8) [C8 cs]
                                           /\ (mc = wz (max_count c') /\ cs = wz (class_size c')))
      by (intros c' Hc'; destruct (FAMv c' Hc') as [A B]; eexists _, _; split; [exact A| split; [exact B| split; reflexivity]]).
    clear FAMv.
    assert (FAM2 := fam_transport CA _ m1 m2 _ FAM1 MU2 WM2
              ltac:(hci; intros c' Hc'; cbn [disjoint_from]; destruct PLC as [PLC']; unfold kSpaceSize in PLC'; clear - Hc' BND BNDL CAE HI PLC'; try acb; subst CA; repeat split; lia)).
    clear FAM1.

    eapply (munch_weaken _ (rf_W lo (bv_unsigned sp) P R FAB rbeg TH CA nf mfa mu mfa mu)) in MU; [| unfold rf_W; rx_sub_fp_struct]. unfold rf_W in MU.
    transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.

    assert (CHR : akobj (P + 16) 64 /\ P + 16 + 64 <= aceil /\ (P + 16) mod 16 = 0).
    { acb. destruct THA as [T16]. match goal with TB : akobj TH 4096 |- _ => clear - BND BNDL EP CAE T16 HC TB end; try acb; try acb.
      split; [eapply akobj_sub; [eassumption| lia| lia]|]. split; [lia|]. rewrite EP, CAE. Z.div_mod_to_equations. lia. }
    assert (FABR : AHI_LO <= FAB /\ FAB + 4 * (nf - n + n) <= aceil /\ FAB mod 4096 = 0).
    { getAL CAR ARIR SBR4 RR RBG. unfold AHI_LO in *. acb. destruct RBG as (RB1 & RB2 & RB3).
      clear - BND BNDL RB1 RB2 RB3 NFR NR; try acb. repeat split; [lia| lia|]. destruct BNDL as (_ & _ & _ & _ & EF & _). rewrite EF. Z.div_mod_to_equations. lia. }
    assert (SEPT : hidden ((P + 16 + 64 <= FAB \/ FAB + 4 * (nf - n + n) <= P + 16) /\ (P + 16 + 64 <= R \/ R + 128 <= P + 16) /\ (R + 128 <= FAB \/ FAB + 4 * (nf - n + n) <= R))).
    { split. destruct PLC as [PLC']. unfold kSpaceSize in PLC'. clear - BND BNDL NFR NR PLC' CAE; try acb. repeat split; lia. }
    replace (P + 80) with (P + 16 + 64) in PCJ by lia.
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF2 _ mo2 Q OK2 VIS2).
    { getAL CAR ARIR SBR4 RR RBG.
      eapply (gfa_tail _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10' s11' _ _ _ _ _ F fc m2 lo R (P + 16) FAB (nf - n) n fl j24);
        try eassumption; rewrite ?unsigned_lit by lia.
      all: try eassumption. all: try reflexivity. all: try (rewrite FLL; f_equal; clear; lia). all: clear - HI SPR BND NR NF; try acb; lia. }
    clear OK2 VIS2. intros msF3 mo3 OK3 SBM3 HS3 P3.
    destruct P3 as (v0 & v1 & v2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & m3 & VIS3 & MU3 & WM3 & MI3 & ST3 & CHA & CHJ3 & FARR3 & LK3 & RST3).
    rewrite ?unsigned_lit in VIS3, MU3, ST3 by lia.
    replace (bv_unsigned sp + -160 + 128) with (bv_unsigned sp + -32) in * by lia.
    renv_at ENV2 MU3 WM3 ENV3. clear ENV2.
    assert (FAM3 := fam_transport CA _ m2 m3 _ FAM2 MU3 WM3
              ltac:(hci; intros c' Hc'; cbn [disjoint_from]; destruct PLC as [PLC']; unfold kSpaceSize in PLC'; clear - Hc' BND BNDL CAE EP HI PLC' NR NF NFR; try acb; subst CA P; repeat split; lia)).
    clear FAM2 LK FRG. transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.

    replace (ret_pc (wz 619396)) with (Z_to_bv 64 619396) in VIS3 by (unfold wz; symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF3 _ mo3 Q OK3 VIS3).
    { eapply (refill_back _ gp tp _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ F fc m3 j8 s1 s0 ra lo P n);
        try eassumption; rewrite ?unsigned_lit by lia.
      all: try eassumption. all: try (match goal with TB : akobj TH 4096 |- akobj _ _ /\ _ => clear - BND BNDL TB EP CAE HC; split; [eapply akobj_sub; [exact TB| subst CA P; lia| subst CA P; lia] | subst CA P; lia] end).     all: clear - HI SPR BND NR; try acb; lia. }
    clear OK3 VIS3. intros msF4 mo4 OK4 SBM4 HS4 P4.
    destruct P4 as (m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & PC4).
    rewrite ?unsigned_lit in VIS4, MU4, ST4 by lia.
    replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in * by lia.
    renv_at ENV3 MU4 WM4 ENV4. clear ENV3.
    assert (FAM4 := fam_transport CA _ m3 m4 _ FAM3 MU4 WM4
              ltac:(hci; intros c' Hc'; cbn [disjoint_from]; clear - Hc' BND BNDL CAE EP HI; try acb; subst CA P; repeat split; lia)).
    assert (LENCH : Z.of_nat (length (wlist (rev (take (Z.to_nat n) fl)))) = n)
      by (unfold wlist; rewrite length_map, length_rev, length_firstn, FLL; clear - NF NR; try acb; lia).
    clear FAM3 PC0. transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4.

    apply K. unfold rf_done.
    assert (E1 : rf_mu' c nf au mu = mu) by (unfold rf_mu'; fold n; rewrite (proj2 (Z.ltb_ge nf n) NF); reflexivity).
    assert (E2 : rf_nnew c nf au mu = 0) by (unfold rf_nnew; fold n; rewrite (proj2 (Z.ltb_ge nf n) NF); reflexivity).
    assert (E3 : rf_mfa' c nf mfa au mu = mfa) by (unfold rf_mfa'; fold n; rewrite (proj2 (Z.ltb_ge nf n) NF); reflexivity).
    assert (E4 : rf_nf1 c nf au mu = nf) by (unfold rf_nf1; rewrite E2; clear; lia).
    assert (E5 : rf_au' c nf au mu = au) by (unfold rf_au'; rewrite E2; clear; lia).
    assert (E6 : rf_fl1 c nf au mu fl = fl) by (unfold rf_fl1; rewrite E2; reflexivity).
    cbv zeta. rewrite !E1, !E3, !E4, !E5, !E6. fold n.
    rewrite !Z.ltb_irrefl. rewrite !Z.sub_diag. cbn [app].
    do 18 eexists. exists m4, L, S.
    split; [exact OK4|]. split; [rewrite Z_to_bv_bv_unsigned in VIS4; exact VIS4|].
    split; [reflexivity|]. split; [reflexivity|].
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM2) SBM3) SBM4) as SBM.
    split; [apply nonvm_same_mat; exact SBM|].
    pose proof (same_but_materialized_vmmaps _ _ SBM) as VMM. rewrite <- VMM.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [rewrite (same_but_materialized_eager _ _ SBM); clear; lia|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact PC4|].
    split. { intros c' Hc'. destruct (FAM4 c' Hc') as (mc & cs & A & B & -> & ->). split; [exact A| exact B]. }
    split; [exact CHA|]. split; [replace (P + 80) with (P + 16 + 64) by lia; exact CHJ3|].
    split.
    { apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [exact LK3|]. cbn [cells_size csize Nat.add length].
      apply (proj2 (rw_cells_app asegs _ _ [_;_] _)). split; [replace (R + Z.of_nat 8) with (R + 8) by lia; exact RI8a|]. cbn [cells_size csize Nat.add length].
      apply (proj2 (rw_cells_app asegs _ _ [_] _)). split; [replace (R + Z.of_nat 8 + Z.of_nat 8) with (R + 16) by lia; exact RNF2|]. cbn [cells_size csize Nat.add length].
      replace (R + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) with (R + 24) by lia. exact RI24. }
    getAL CAR ARIR SBR4 RR RBG.
    assert (MUQ : exists q, mu = 262144 * q) by (destruct MUA as [MUA']; exists (mu / kUserMapSize); unfold kUserMapSize in *; clear - MUA'; try acb; Z.div_mod_to_equations; lia).
    assert (MFQ : exists q, mfa = 262144 * q) by (destruct MFAA as [MFAA']; exists (mfa / kFreeArrayMapSize); unfold kFreeArrayMapSize in *; clear - MFAA'; try acb; Z.div_mod_to_equations; lia).
    destruct MUQ as [muq MUQ]. destruct MFQ as [mfq MFQ].
    repeat match goal with |- _ /\ _ => split end; try eassumption.
    - change (0 / 8) with 0. cbn [Z.to_nat]. apply poisoned_0; unfold AHI_LO, sh, ASHADOW_BASE in *; acb;
        [clear - RBG AUR; try acb; lia | clear - RBG MUQ; try acb; destruct RBG as (_ & _ & RB3); Z.div_mod_to_equations; lia | clear - RBG AUR; try acb; lia].
    - change (0 / 8) with 0. cbn [Z.to_nat]. apply poisoned_0; unfold AHI_LO, sh, ASHADOW_BASE in *; acb;
        [clear - FABR NFR; try acb; lia | clear - FABR MFQ; try acb; destruct FABR as (_ & _ & F3); Z.div_mod_to_equations; lia | clear - FABR NFR NR; try acb; lia].
  Qed.

End Refill.

End HCW2.

