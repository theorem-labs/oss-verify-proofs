(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange ZdWalkKit ZdDctxRep ZdSeqW ZdTbl KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXPost KXGoF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AMalloc_iface AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR
     AZ_libc_iface AZ_seq_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition rheld (P : Prop) : Prop := P.
Ltac rh_is_arith T :=
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | @eq Z _ _ => idtac | not (@eq Z _ _) => idtac
  | and ?A ?B => rh_is_arith A; rh_is_arith B
  | or ?A ?B => rh_is_arith A; rh_is_arith B
  end.
Ltac rhold_arith := repeat match goal with H : ?T |- _ => rh_is_arith T; change (rheld T) in H end.
Ltac runhold_off := repeat match goal with H : rheld ?T |- _ => change T in H end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma shspan_bounds : forall X n, 0 <= X -> 0 < n -> X + n <= 2^47 ->
  2147450880 <= shad X /\ shad (X + n - 1) + 1 <= 17594333495296 /\ shad X <= shad (X + n - 1).
Proof. intros X n H1 H2 H3. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma shspan_ff : forall X n FF, 0 <= X -> 0 < n -> 0 <= FF -> FF mod 8 = 0 -> (FF + 256 <= X \/ X + n <= FF) ->
  shad X + (shad (X + n - 1) + 1 - shad X) <= shad FF \/ shad FF + 32 <= shad X.
Proof. intros X n FF H1 H2 H3 H4 H5. rewrite !shad_div. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma wb_shadow_disj : forall (DST CAP DCTX SPV FF SHF X n : Z),
  0 <= X -> 0 < n -> X + n <= 2^47 -> 0 <= FF -> FF mod 8 = 0 -> SHF = shad FF -> (FF + 256 <= X \/ X + n <= FF) ->
  (DST + CAP <= 2147450880 \/ 17594333495296 <= DST) ->
  (DCTX + 95992 <= 2147450880 \/ 17594333495296 <= DCTX) ->
  17594333495296 <= SPV - 5056 -> (FF + 256 <= 2147450880 \/ 17594333495296 <= FF) ->
  disjoint_from [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
                 (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)]
                (shad X) (shad (X + n - 1) + 1 - shad X).
Proof.
  intros DST CAP DCTX SPV FF SHF X n H1 H2 H3 H4 H5 -> H7 D1 D2 D3 D4.
  pose proof (shspan_bounds X n H1 H2 H3) as (B1 & B2 & B3).
  pose proof (shspan_ff X n FF H1 H2 H4 H5 H7) as E.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma wb5_shadow_disj : forall (DCTX SPV FF SHF X n : Z),
  0 <= X -> 0 < n -> X + n <= 2^47 -> 0 <= FF -> FF mod 8 = 0 -> SHF = shad FF -> (FF + 256 <= X \/ X + n <= FF) ->
  (DCTX + 95992 <= 2147450880 \/ 17594333495296 <= DCTX) ->
  17594333495296 <= SPV - 5056 -> (FF + 256 <= 2147450880 \/ 17594333495296 <= FF) ->
  disjoint_from [(DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12);
                 (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4); (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)]
                (shad X) (shad (X + n - 1) + 1 - shad X).
Proof.
  intros DCTX SPV FF SHF X n H1 H2 H3 H4 H5 -> H7 D2 D3 D4.
  pose proof (shspan_bounds X n H1 H2 H3) as (B1 & B2 & B3).
  pose proof (shspan_ff X n FF H1 H2 H4 H5 H7) as E.
  unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation. cbn [disjoint_from].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed.

(* [comment removed for export] *)
Lemma munch_drop_empty : forall a W (m m' : amem), munch ((a, a + 0) :: W) m m' -> munch W m m'.
Proof. intros a W m m' MU. eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x Hx. split; [lia | exact Hx]. Qed.

(* [comment removed for export] *)
Lemma unp_tr : forall W (m m1 : amem) X n, unpoisoned m X (X + n) -> munch W m m1 ->
  disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X) -> unpoisoned m1 X (X + n).
Proof. intros W m m1 X n U MU D. eapply unpoisoned_munch; [exact U | exact MU |]. replace (X + n - 1) with (X + n - 1) by lia. exact D. Qed.

(* [comment removed for export] *)
Lemma ablk_lits : forall A B, ablk A B -> (6443008 <= A /\ B <= 2147446784) \/ (17594333495296 <= A /\ B <= ATOP).
Proof. intros A B H. unfold ablk, AIMG_HI, KLS, KHIGH in *. pose proof atop_range. lia. Qed.

(* [comment removed for export] *)
Lemma shad_lits : forall X, 0 <= X < 2^47 -> shad X = 2147450880 + X / 8.
Proof. intros X H. rewrite shad_div. reflexivity. Qed.

(* [comment removed for export] *)
Lemma shz_sub : forall RNG X N A n, rng RNG (shad X) (shspan X N) -> X <= A -> A + n <= X + N ->
  rng RNG (2147450880 + A / 8) ((A + n + 7) / 8 - A / 8).
Proof.
  intros RNG X N A n H H1 H2. eapply rng_sub; [exact H | rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia
  | unfold shspan; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
Qed.
Lemma shz_lit : forall RNG X N, rng RNG (shad X) (shspan X N) -> rng RNG (2147450880 + X / 8) ((X + N + 7) / 8 - X / 8).
Proof. intros RNG X N H. rewrite shad_div in H. unfold ASHOFF in H. unfold shspan in H. exact H. Qed.


Lemma sql_asan_transport : forall P OEND LLO LEND LOCV (m1 : amem),
  sql_static P OEND LLO LEND LOCV -> munch (sql_Wb P) (l_m P) m1 -> wmono bsegs (l_m P) m1 -> sql_asan P m1.
Proof.
  intros P OEND LLO LEND LOCV m1 ST MU WM.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_Wb sql_asan sql_astat l_m] in *.
  sd_static_open ST.
  destruct S62 as (ARD & AHD & ARS & ATB & ACL & AOUT & ARL & AHL & AZS & ARTC).
  destruct S61 as (AST & TP & ATL & SPT & ED8 & ES1 & ES1b & FFa & FFb & FFc & ESHF & RFF & RSHF & AFD & AFO & AFS & AFL & AFT).
  unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, apart in *.
  pose proof atop_range as ATR.
  destruct (ARD ltac:(clear; lia)) as (BD & _). pose proof (ablk_lits _ _ BD) as BDL.
  assert (FF8 : FF mod 8 = 0) by (clear - FFc; Z.div_mod_to_equations; lia).
  assert (FF0 : 0 <= FF) by (unfold AIMG_HI in FFa; clear - FFa; lia).
  assert (STK : 17594333495296 <= SPV - 5056) by (unfold held in S53; clear - S53 S18; lia).
  assert (FFL : FF + 256 <= 2147450880 \/ 17594333495296 <= FF) by (unfold held in S49; clear - S49; lia).
  assert (DCL : DCTX + 95992 <= 2147450880 \/ 17594333495296 <= DCTX) by (clear - BDL; lia).
  (* [comment removed for export] *)
  assert (DJ : exists W, munch W m m1 /\ (forall X n, 0 <= X -> 0 < n -> X + n <= 2^47 -> (FF + 256 <= X \/ X + n <= FF) ->
                 disjoint_from W (shad X) (shad (X + n - 1) + 1 - shad X)) /\
                 (forall A n, 0 <= A -> 0 <= n -> A + n <= 6443008 -> disjoint_from W A n)).
  { destruct (Z.eq_dec CAP 0) as [C0|C0].
    - subst CAP. exists [(DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4);
                         (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)].
      split; [exact (munch_drop_empty DST _ m m1 MU)|]. split.
      + intros X n H1 H2 H3 H4. eapply wb5_shadow_disj; eassumption.
      + intros A n H1 H2 H3. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, AIMG_HI in *. cbn [disjoint_from].
        split; [clear - H3 BDL; lia|]. split; [clear - H3 BDL; lia|]. split; [clear - H3 BDL; lia|]. split; [clear - H3 STK; lia|]. split; [clear - H3 FFa; lia|].
        split; [rewrite ESHF, shad_div; unfold ASHOFF; clear - H3 FF0; Z.div_mod_to_equations; lia| exact I].
    - exists [(DST, DST + CAP); (DCTX + DCTX_entropy_rep, DCTX + DCTX_entropy_rep + 12); (DCTX + DCTX_fseEntropy, DCTX + DCTX_fseEntropy + 4); (DCTX + DCTX_litBufferLocation, DCTX + DCTX_litBufferLocation + 4);
              (SPV - SEQ_LONG_STACK_A, SPV); (FF, FF + 256); (SHF, SHF + 32)].
      split; [exact MU|].
      assert (BB : B0 < B1) by (clear - S2 S3 S4 S5 S6 C0; lia).
      destruct (AOUT BB) as (AO & _). destruct (AO ltac:(clear - BB; lia)) as (BO & _). pose proof (ablk_lits _ _ BO) as BOL.
      split.
      + intros X n H1 H2 H3 H4. eapply wb_shadow_disj; try eassumption. clear - BOL S2 S3 S4 S5 S6. lia.
      + intros A n H1 H2 H3. unfold DCTX_entropy_rep, DCTX_fseEntropy, DCTX_litBufferLocation, AIMG_HI in *. cbn [disjoint_from].
        split; [clear - H3 BOL S2 S3 S4 S5 S6; lia|].
        split; [clear - H3 BDL; lia|]. split; [clear - H3 BDL; lia|]. split; [clear - H3 BDL; lia|]. split; [clear - H3 STK; lia|]. split; [clear - H3 FFa; lia|].
        split; [rewrite ESHF, shad_div; unfold ASHOFF; clear - H3 FF0; Z.div_mod_to_equations; lia| exact I]. }
  destruct DJ as (W & MUW & DJ & DJI).
  (* [comment removed for export] *)
  assert (TU : forall X n, unpoisoned m X (X + n) -> 0 <= X -> 0 < n -> X + n <= 2^47 -> (FF + 256 <= X \/ X + n <= FF) ->
                 unpoisoned m1 X (X + n)).
  { intros X n U H1 H2 H3 H4. eapply unp_tr; [exact U | exact MUW | exact (DJ X n H1 H2 H3 H4)]. }
  assert (TH : forall A n, ahull RNG m A n -> ahull RNG m1 A n).
  { intros A n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W0 & R). exists RLO, RHI.
    do 6 (split; [assumption|]). split; [eapply wr_at_transport; [exact W0 | exact WM] | exact R]. }
  assert (TA : forall X n, areg RNG m X n -> (0 < n -> 0 <= X /\ X + n <= 2^47 /\ (FF + 256 <= X \/ X + n <= FF)) -> areg RNG m1 X n).
  { intros X n A HX Hn. destruct (A Hn) as (B & U & R1 & R2). destruct (HX Hn) as (X1 & X2 & X3).
    split; [exact B|]. split; [exact (TU X n U X1 Hn X2 X3)|]. split; [exact R1 | exact R2]. }
  assert (TR : forall X n, aro RNG m X n -> (0 < n -> 0 <= X /\ X + n <= 2^47 /\ (FF + 256 <= X \/ X + n <= FF)) -> aro RNG m1 X n).
  { intros X n (U & R1 & R2) HX. split; [| split; [exact R1 | exact R2]].
    destruct (Z_lt_le_dec 0 n) as [Hn|Hn].
    - destruct (HX Hn) as (X1 & X2 & X3). exact (TU X n U X1 Hn X2 X3).
    - destruct U as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. lia. }
  assert (TC : forall A cs, rw_cells bsegs m A cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m1 A cs).
  { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MUW | exact WM | apply DJI; lia]. }
  pose proof (seq_pow_le _ _ OKLL) as P1. pose proof (seq_pow_le _ _ OKML) as P3.
  assert (P2 : 1 <= 2^(st_log tOF) <= 256).
  { destruct OKOF as ((T1 & T2) & _). cbn [kind_maxLog] in T2. split; [pose proof (Z.pow_pos_nonneg 2 (st_log tOF)); lia|].
    change 256 with (2^8). apply Z.pow_le_mono_r; lia. }
  split; [eapply TA; [exact ARD | intros _; clear - S19 S20 AFD; lia]|].
  split; [exact (TH _ _ AHD)|].
  split; [eapply TA; [exact ARS | intros Hn0; specialize (AFS Hn0); clear - S13 S14 AFS; lia]|].
  split.
  { intros HN. destruct (ATB HN) as (A1 & A2 & A3). destruct (AFT HN) as (F1 & F2 & F3).
    split; [eapply TR; [exact A1 | intros _; clear - S21 F1 P1; lia]|].
    split; [eapply TR; [exact A2 | intros _; clear - S22 F2 P2; lia]|].
    eapply TR; [exact A3 | intros _; clear - S23 F3 P3; lia]. }
  split.
  { apply (aro_client_transport_gen RNG m m1 W WM ACL MUW). intros A n HIn.
    destruct (aclient_bounds A n HIn) as (B1' & B2' & B3'). apply DJ; try (clear - B1' B2' B3'; lia).
    right. unfold AIMG_HI in FFa. clear - B3' FFa. lia. }
  split.
  { intros BB. destruct (AOUT BB) as (AO & AH). split; [eapply TA; [exact AO | intros _; specialize (AFO BB); clear - S1 S6 S7 AFO BB; lia] | exact (TH _ _ AH)]. }
  split; [eapply TA; [exact ARL | intros _; clear - S70 AFL; lia]|].
  split; [exact (TH _ _ AHL)|].
  split.
  { destruct AZS as (RLO & RHI & U & HB & W0 & AB & R). exists RLO, RHI.
    split; [| split; [exact HB | split; [eapply wr_at_transport; [exact W0 | exact WM] | split; [exact AB | exact R]]]].
    replace SPV with (lo + (SPV - lo)) in U |- * by lia.
    apply TU; [exact U | clear - S18; lia | clear - S18; lia | clear - S17; lia | clear - S50 S18; lia]. }
  destruct ARTC as (G1 & G2 & G3 & G4 & G5 & G6). unfold art.
  split; [apply TC; [exact G1 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G2 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G3 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G4 | clear; lia | cbn; clear; lia]|].
  split; [apply TC; [exact G5 | clear; lia | cbn; clear; lia]|].
  apply TC; [exact G6 | clear; lia | cbn; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma aro_cell_shadow : forall RNG (m1 : amem) T8 ntl s, aro RNG m1 (8 * T8) (8 * (1 + ntl)) -> 0 <= s < ntl ->
  rdn bsegs m1 (wa (2147450880 + T8 + s + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
  rng RNG (8 * T8 + 8 * s + 8) 8 /\ rng RNG (2147450880 + T8 + s + 1) 1.
Proof.
  intros RNG m1 T8 ntl s (U & R1 & R2) Hs.
  assert (Z0 : m1 (wa (shad (8 * T8 + 8 * s + 8))) = Some (Z_to_bv 8 0)).
  { eapply (unp_shadow_zero m1 (8 * T8) (8 * (1 + ntl)) (8 * T8 + 8 * s + 8)); [exact U | lia | ].
    Z.div_mod_to_equations. lia. }
  rewrite shad_div in Z0. unfold ASHOFF in Z0.
  replace ((8 * T8 + 8 * s + 8) / 8) with (T8 + s + 1) in Z0 by (Z.div_mod_to_equations; lia).
  split; [| split].
  - cbn [rdn]. replace (2147450880 + T8 + s + 1) with (2147450880 + (T8 + s + 1)) by lia. rewrite Z0. reflexivity.
  - eapply rng_sub'; [exact R1 | lia].
  - eapply rng_sub'; [exact R2 |]. unfold shspan. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma sql_asan_now : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_asan P m1.
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  eapply (sql_asan_transport P OEND LLO LEND LOCV m1 ST).
  - destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [sql_xinv sql_Wb l_m] in *. destruct XI as (_ & _ & _ & _ & _ & _ & _ & MU & _). exact MU.
  - destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1]. cbn [sql_xinv l_m] in *. destruct XI as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _). exact WM.
Qed.

(* [comment removed for export] *)
Lemma sql_dec_asan : forall P OEND LLO LEND LOCV BND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  sql_lfacts P OEND LLO LEND BND OP LP bc ptr sLL sOF sML ->
  exists L8 O8 M8, l_LLT P = 8 * L8 /\ l_OFT P = 8 * O8 /\ l_MLT P = 8 * M8 /\
    rdn bsegs m1 (wa (2147450880 + L8 + sLL + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
    rdn bsegs m1 (wa (2147450880 + O8 + sOF + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
    rdn bsegs m1 (wa (2147450880 + M8 + sML + 1)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) /\
    rng (l_RNG P) (8 * L8 + 8 * sLL + 8) 8 /\ rng (l_RNG P) (8 * O8 + 8 * sOF + 8) 8 /\ rng (l_RNG P) (8 * M8 + 8 * sML + 8) 8 /\
    rng (l_RNG P) (2147450880 + L8 + sLL + 1) 1 /\ rng (l_RNG P) (2147450880 + O8 + sOF + 1) 1 /\ rng (l_RNG P) (2147450880 + M8 + sML + 1) 1.
Proof.
  intros P OEND LLO LEND LOCV BND m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP OP ST INV LF.
  pose proof (sql_asan_now P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS.
  destruct LF as (_ & _ & L3 & L4 & L5 & _).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_asan l_LLT l_OFT l_MLT l_RNG l_tLL l_tOF l_tML] in *.
  sd_static_open ST.
  destruct AS as (_ & _ & _ & ATB & _).
  destruct (ATB ltac:(lia)) as (AL & AO & AM).
  exists (LLT / 8), (OFT / 8), (MLT / 8).
  assert (EL : LLT = 8 * (LLT / 8)) by (clear - S44; Z.div_mod_to_equations; lia).
  assert (EO : OFT = 8 * (OFT / 8)) by (clear - S45; Z.div_mod_to_equations; lia).
  assert (EM : MLT = 8 * (MLT / 8)) by (clear - S46; Z.div_mod_to_equations; lia).
  rewrite EL in AL. rewrite EO in AO. rewrite EM in AM.
  destruct (aro_cell_shadow RNG m1 (LLT / 8) (2 ^ st_log tLL) sLL AL L3) as (ZL & RL1 & RL2).
  destruct (aro_cell_shadow RNG m1 (OFT / 8) (2 ^ st_log tOF) sOF AO L4) as (ZO & RO1 & RO2).
  destruct (aro_cell_shadow RNG m1 (MLT / 8) (2 ^ st_log tML) sML AM L5) as (ZM & RM1 & RM2).
  repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Lemma sql_fsh_unp : forall (m1 : amem) SHF FF (a b : list byte),
  rw_cells bsegs m1 SHF [CB 4 a; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 14 b] ->
  SHF = 2147450880 + FF / 8 -> FF mod 8 = 0 -> 0 <= FF -> FF + 256 <= 2^47 ->
  unpoisoned m1 (FF + 32) (FF + 32 + 112).
Proof.
  intros m1 SHF FF a b RW ESH F8 F0 F1.
  destruct RW as [(WF & BA) _].
  cbn [cells_wf cell_wf] in WF. destruct WF as (LA & _ & _ & _ & LB & _).
  cbn [cells_bytes cbytes] in BA. destruct BA as (_ & _ & BA).
  split; [lia|]. split; [lia|]. intros G Hlt H1 H2.
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  assert (HK : 4 <= G - FF / 8 < 18) by (Z.div_mod_to_equations; lia).
  assert (NTH : forall i, 0 <= i < 14 -> nth_error (a ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ le2 (Z_to_bv 64 0) ++ b ++ []) (Z.to_nat (4 + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. rewrite nth_error_app2 by (rewrite LA; lia). rewrite LA. replace (Z.to_nat (4 + i) - 4)%nat with (Z.to_nat i) by lia.
    assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]; reflexivity. }
  specialize (BA (Z.to_nat (4 + (G - FF / 8 - 4)))).
  rewrite NTH in BA by lia. specialize (BA ltac:(rewrite !length_app, LA, LB; cbn [length le8 le4 le2 word_to_le_bytes]; lia)).
  replace (SHF + Z.of_nat (Z.to_nat (4 + (G - FF / 8 - 4)))) with (ASHOFF + G) in BA by (unfold ASHOFF; lia).
  rewrite ref_mrd_overlay in BA; [exact BA|]. rewrite wa_unsigned by (unfold ASHOFF; lia). unfold ASHOFF. lia.
Qed.

Lemma sql_linv_fsh : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  unpoisoned m1 (l_FF P + 32) (l_FF P + 32 + 112).
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & XI).
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_xinv sql_astat l_FF] in *.
  sd_static_open ST. destruct XI as (_ & _ & _ & _ & _ & _ & SHS & _).
  destruct S61 as (_ & _ & _ & _ & _ & _ & _ & FFa & FFb & FFc & ESHF & _).
  unfold AIMG_HI in FFa. unfold held in S49.
  eapply sql_fsh_unp; [exact SHS | rewrite ESHF, shad_div; reflexivity | clear - FFc; Z.div_mod_to_equations; lia | lia | clear - S49 S50 S18 S17; lia].
Qed.

(* [comment removed for export] *)
Lemma sql_seq_asan : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  unpoisoned m1 (l_SEQ P) (l_SEQ P + zlen (l_sq P)) /\ rng (l_RNG P) (l_SEQ P) (zlen (l_sq P)) /\
  rng (l_RNG P) (shad (l_SEQ P)) (shspan (l_SEQ P) (zlen (l_sq P))).
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  pose proof (sql_asan_now P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_asan l_SEQ l_sq l_RNG] in *.
  sd_static_open ST. destruct AS as (_ & _ & ARS & _).
  destruct (ARS ltac:(clear - S15; lia)) as (_ & U & R1 & R2). split; [exact U | split; [exact R1 | exact R2]].
Qed.

(* [comment removed for export] *)
Lemma sql_bm_asan : forall P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP,
  sql_static P OEND LLO LEND LOCV -> sql_linv P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ->
  unpoisoned m1 0x22180 (0x22180 + 128) /\ rng (l_RNG P) 0x22180 128 /\ rng (l_RNG P) (shad 0x22180) (shspan 0x22180 128).
Proof.
  intros P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV.
  pose proof (sql_asan_now P OEND LLO LEND LOCV m1 c8 c16 c24 c32 c88 c96 c120 c128 c160 c224 c232 c248 c264 c304 c312 c320 c328 c336 c352 c368 c376 cw bc ptr sLL sOF sML p0 p1 p2 rl rm ro LP ST INV) as AS.
  destruct P as [ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m0 FRB FF SHF D8 j0 j384 jfh j144 jsh0 jsh1].
  cbn [sql_asan l_RNG] in *. destruct AS as (_ & _ & _ & _ & ACL & _).
  assert (A : aro RNG m1 0x22180 128) by aro_cl ACL.
  destruct A as (U & R1 & R2). split; [exact U | split; [exact R1 | exact R2]].
Qed.

End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sql_dead_pc (pc : Z) : bool :=
  existsb (Z.eqb pc) [0x5ac8c; 0x5ad2c; 0x5adcc; 0x5ae6c; 0x5afac; 0x5b0ec; 0x5b2cc; 0x5b36c]
  || existsb (fun r => (fst r <=? pc) && (pc <? snd r)) [
    (0x89ae4, 0x89ae8); (0x89b08, 0x89b0c); (0x89b40, 0x89b44); (0x89b68, 0x89b6c); (0x89b7c, 0x89b80);
    (0x89b94, 0x89b98); (0x89bac, 0x89bb0); (0x89c1c, 0x89c20); (0x89c44, 0x89c48); (0x89c74, 0x89c78);
    (0x89c9c, 0x89ca0); (0x89d00, 0x89d04); (0x89d18, 0x89d1c); (0x89e1c, 0x89e20); (0x89f18, 0x89f1c);
    (0x89f64, 0x89f68); (0x89f90, 0x89f94); (0x89fbc, 0x89fc0); (0x89fe8, 0x89fec); (0x8a014, 0x8a018);
    (0x8a040, 0x8a044); (0x8a070, 0x8a074); (0x8a110, 0x8a114); (0x8a12c, 0x8a130); (0x8a15c, 0x8a160);
    (0x8a1d0, 0x8a1d4); (0x8a1e8, 0x8a1fc); (0x8a254, 0x8a258); (0x8a26c, 0x8a270); (0x8a2ec, 0x8a2f0);
    (0x8a308, 0x8a30c); (0x8a330, 0x8a334); (0x8a3a4, 0x8a3a8); (0x8a3bc, 0x8a3d0); (0x8a3f4, 0x8a3f8);
    (0x8a40c, 0x8a410); (0x8a48c, 0x8a490); (0x8a4ac, 0x8a4b0); (0x8a4d8, 0x8a4dc); (0x8a554, 0x8a558);
    (0x8a56c, 0x8a580); (0x8a5a4, 0x8a5a8); (0x8a5bc, 0x8a5c0); (0x8a98c, 0x8a998); (0x8aad4, 0x8aae0);
    (0x8abe4, 0x8abe8); (0x8ac24, 0x8ad14); (0x8ad24, 0x8ad58); (0x8ae84, 0x8ae88); (0x8aeb0, 0x8aeb4);
    (0x8aed4, 0x8aed8); (0x8aef0, 0x8aef4); (0x8af0c, 0x8af10); (0x8af28, 0x8af2c); (0x8af40, 0x8af44);
    (0x8af58, 0x8af5c); (0x8af70, 0x8af74); (0x8af8c, 0x8af90); (0x8afa8, 0x8afac); (0x8afc4, 0x8afc8);
    (0x8b094, 0x8b098); (0x8b0cc, 0x8b0d0); (0x8b104, 0x8b108); (0x8b180, 0x8b184); (0x8b198, 0x8b1a4);
    (0x8b204, 0x8b208); (0x8b21c, 0x8b220); (0x8b2b4, 0x8b2b8); (0x8b62c, 0x8b644); (0x8b6a8, 0x8b6c0);
    (0x8b6e0, 0x8b6e4); (0x8b8c0, 0x8b8c4); (0x8b8d8, 0x8b8e4); (0x8b930, 0x8b940); (0x8ba10, 0x8ba14);
    (0x8ba28, 0x8ba2c); (0x8bd00, 0x8bd04); (0x8c010, 0x8c048); (0x8c618, 0x8c650); (0x8c860, 0x8c898);
    (0x8c938, 0x8ca4c); (0x8ca5c, 0x8cd74); (0x8ce3c, 0x8ce40); (0x8ce78, 0x8ce7c); (0x8d208, 0x8d220);
    (0x8d278, 0x8d290); (0x8d2b0, 0x8d2b4); (0x8d9c0, 0x8d9f8); (0x8dfa4, 0x8dfdc); (0x8e1f4, 0x8e22c);
    (0x8e2dc, 0x8e5a0); (0x8e760, 0x8e778); (0x8e7e8, 0x8f1e4)].
(* [comment removed for export] *)
Ltac sql_oranges := repeat match goal with
  | KXK : know_ok _ ?E _ _, H : context [bv_unsigned (edenot ?E ?e)] |- _ =>
      lazymatch type of H with know_ok _ _ _ _ => fail | reads_ok _ _ _ _ _ => fail | _ =>
      lazymatch goal with _ : _ <= bv_unsigned (edenot E e) <= _ |- _ => fail | _ => let H' := fresh "KXOR" in kx_erange H' e end end
  | KXK : know_ok _ ?E _ _ |- context [bv_unsigned (edenot ?E ?e)] =>
      lazymatch goal with _ : _ <= bv_unsigned (edenot E e) <= _ |- _ => fail | _ => let H' := fresh "KXOR" in kx_erange H' e end
  end.
Ltac sql_bvr := repeat match goal with
  | |- context [bv_unsigned (edenot ?E ?e)] =>
      lazymatch goal with _ : 0 <= bv_unsigned (edenot E e) < _ |- _ => fail | _ =>
        let H' := fresh "KXBV" in pose proof (bv_unsigned_in_range 64 (edenot E e)) as H'; unfold bv_modulus in H'; change (2 ^ Z.of_N 64) with 18446744073709551616 in H' end
  | H : context [bv_unsigned (edenot ?E ?e)] |- _ =>
      lazymatch type of H with 0 <= bv_unsigned (edenot E e) < _ => fail | _ =>
      lazymatch goal with _ : 0 <= bv_unsigned (edenot E e) < _ |- _ => fail | _ =>
        let H' := fresh "KXBV" in pose proof (bv_unsigned_in_range 64 (edenot E e)) as H'; unfold bv_modulus in H'; change (2 ^ Z.of_N 64) with 18446744073709551616 in H' end end
  end.
Ltac sql_dead_core := first [ kx_sh_dead0_any | kx_sh_dead_any 1 | kx_sh_dead_any 2 | kx_sh_dead_any 4 | kx_sh_dead_any 8 ].
Ltac sql_dead_leaf :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let b := eval vm_compute in (sql_dead_pc pc) in
      lazymatch b with true => try sql_oranges; try sql_bvr; sql_dead_core end
  end.
(* [comment removed for export] *)
Ltac sql_acc_any :=
  lazymatch goal with
  | |- accP _ ?RNG _ => match goal with H : rng RNG _ _ |- _ => kx_sh_acc H end
  end.
Ltac sql_side :=
  first [ lazymatch goal with |- sc_resid _ _ _ (SCReadBase _ _ _ _) => kx_sh_rd_any end
        | lazymatch goal with |- sc_resid _ _ _ (SCDisj _ _ _ _) => kx_z end
        | sql_acc_any ].
Ltac sql_aclose :=
  lazymatch goal with
  | |- evtF _ _ _ _ => sql_dead_leaf
  | |- _ => try sql_oranges; try sql_bvr; sql_side
  end.
(* [comment removed for export] *)
Ltac sql_clear_nonkx := repeat match goal with H : ?T |- _ => lazymatch T with context [edenot] => fail | _ => clear H end end.
