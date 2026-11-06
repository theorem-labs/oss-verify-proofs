(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib2.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLoop.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTab.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTabLoop.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15Dith2LL.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15Dith2LL1.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Module O15LeptDith2.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLoop.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTabLoop.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15Dith2LL.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15Dith2LL1.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac dl_get2 :=
  first [ eassumption
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get2 end ].

Section PixLoops.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (lined bufs1 bufs2 tabval tab38 tab14 w1 wpl wpld : Z).
(* [comment removed for export] *)
Definition px_geom : Prop :=
  (4096 <= lined /\ lined + 4 * wpld < 2 ^ 47 /\ lined mod 4 = 0 /\ 4096 <= bufs1 /\ bufs1 + 4 * wpl < 2 ^ 47 /\ bufs1 mod 4 = 0 /\
   4096 <= bufs2 /\ bufs2 + 4 * wpl < 2 ^ 47 /\ bufs2 mod 4 = 0 /\ 4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\
   4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\ 4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0 /\
   0 <= w1 <= 19999 /\ w1 + 1 <= 4 * wpl /\ w1 + 1 <= 16 * wpld)%Z.
(* [comment removed for export] *)
Definition PXL : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl); (bufs2, 4 * wpl); (tabval, 1024); (tab38, 1024); (tab14, 1024)]%Z.
Definition px_disj : Prop := pairwise PXL.
Hypothesis G : px_geom.
Hypothesis GD : px_disj.
Ltac geom := pose proof G as (Gl0 & Gl1 & ALl & Gb10 & Gb11 & ALb1 & Gb20 & Gb21 & ALb2 & Gt00 & Gt01 & ALt0 & Gt80 & Gt81 & ALt8 & Gt40 & Gt41 & ALt4 & Gw & Gwpl & Gwpld).
Ltac al4 :=
  match goal with H : (bufs1 mod 4 = 0)%Z |- _ => let c := fresh "cb1" in let E := fresh "Ecb1" in destruct (al4_ex _ H) as [c E] end;
  match goal with H : (bufs2 mod 4 = 0)%Z |- _ => let c := fresh "cb2" in let E := fresh "Ecb2" in destruct (al4_ex _ H) as [c E] end.

Definition R3 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl); (bufs2, 4 * wpl)]%Z.
Definition R2 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl)]%Z.
Lemma R2_R3 : forall r, In r R2 -> In r R3.
Proof. intros r Hr. unfold R2, R3 in *. cbn [In] in *. tauto. Qed.

(* [comment removed for export] *)
Lemma tab_apart : forall (i : nat) tab, (3 <= i <= 5)%nat -> nth i PXL (0, 0)%Z = (tab, 1024%Z) ->
  forall r, In r R3 -> (tab + 1024 <= fst r \/ fst r + snd r <= tab)%Z.
Proof.
  intros i tab Hi E r Hr. unfold R3 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
  - pose proof (pairwise_nth _ 0 i (0, 0)%Z GD ltac:(unfold PXL; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd PXL] in D. lia.
  - pose proof (pairwise_nth _ 1 i (0, 0)%Z GD ltac:(unfold PXL; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd PXL] in D. lia.
  - pose proof (pairwise_nth _ 2 i (0, 0)%Z GD ltac:(unfold PXL; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd PXL] in D. lia.
Qed.
Definition tabs_ok (M : word -> option byte) : Prop :=
  tab_ok SEGS false (fun _ => True) M tabval /\ tab_ok SEGS true (fun _ => True) M tab38 /\ tab_ok SEGS true (fun _ => True) M tab14.

Ltac cell_in RR :=
  cbn [fst snd]; split; [lia|]; first [ (exists (lined, 4 * wpld)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia])
                                        | (exists (bufs1, 4 * wpl)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia])
                                        | (exists (bufs2, 4 * wpl)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia]) ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pfh : forall j, (0 <= j < w1)%Z -> pf_hyps lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld.
Proof.
  intros j Hj. geom. unfold pf_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GD 0%nat 1%nat D. exact D.
  - unfold dapart. pw GD 0%nat 2%nat D. exact D.
  - unfold dapart. pw GD 0%nat 4%nat D. exact D.
  - unfold dapart. pw GD 0%nat 5%nat D. exact D.
Qed.
Lemma pf_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R3 (pf_1b2bc_cells_def lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold pf_1b2bc_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R3 |]). destruct Hc.
Qed.

Definition f0regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 8 = Z_to_bv 64 w1 /\ getr regs 10 = Z_to_bv 64 lined /\ getr regs 12 = Z_to_bv 64 j /\ getr regs 13 = Z_to_bv 64 (bufs1 + j) /\
  getr regs 14 = Z_to_bv 64 (bufs2 + j) /\ getr regs 19 = Z_to_bv 64 tabval /\ getr regs 20 = Z_to_bv 64 tab38 /\ getr regs 21 = Z_to_bv 64 tab14 /\
  getr regs 27 = Z_to_bv 64 268435455.

Lemma pf_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R3 -> tabs_ok Mr ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R3 Mr Mi -> f0regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1b3b8) Mi rom) (mkst regs' (Z_to_bv 64 0x1b478) Mi' rom)
    /\ rinv R3 Mr Mi' /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) regs regs'.
Proof.
  intros Mr ROr (TK0 & TK38 & TK14). geom.
  pose proof (tab_apart 3%nat tabval ltac:(lia) eq_refl) as AP0. pose proof (tab_apart 4%nat tab38 ltac:(lia) eq_refl) as AP38.
  pose proof (tab_apart 5%nat tab14 ltac:(lia) eq_refl) as AP14.
  induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H8 & H10 & H12 & H13 & H14 & H19 & H20 & H21 & H27).
  pose proof (pf_cells_in j Hj) as CI.
  pose proof (cells_ok_of SEGS Mr Mi R3 _ ROr (proj1 RI) CI) as CK.
  destruct (pf_1b2bc_path rom lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld (pfh j Hj) fx regs Mi CK
              (tab_rd_of SEGS false _ R3 _ Mr Mi tabval TK0 RI CI AP0) (tab_rd_of SEGS true _ R3 _ Mr Mi tab38 TK38 RI CI AP38)
              (tab_rd_of SEGS true _ R3 _ Mr Mi tab14 TK14 RI CI AP14) H8 H10 H12 H13 H14 H19 H20 H21 H27)
    as (r1 & m1 & RUN1 & FR1 & E12 & E13 & E14 & E15 & E16 & E17 & AG1).
  pose proof (rinv_cells R3 _ Mr Mi m1 RI FR1 CI) as RI1.
  assert (CI0 : cells_in R3 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - destruct (pf_1b2b8f rom lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld (pfh j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f0regs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (pf_1b2b8t rom lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld (pfh j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pch : pc_hyps lined bufs1 bufs2 tabval tab38 w1 wpl wpld.
Proof.
  geom. unfold pc_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GD 0%nat 2%nat D. exact D.
  - unfold dapart. pw GD 0%nat 4%nat D. exact D.
Qed.
Lemma pc_cells_in : cells_in R3 (pc_1b380_cells_def lined bufs1 bufs2 tabval tab38 w1 wpl wpld).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 16 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold pc_1b380_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R3 |]). destruct Hc.
Qed.
Lemma pc_run : forall (Mr : word -> option byte), regions_ok SEGS Mr R3 -> tabs_ok Mr ->
  forall regs Mi, rinv R3 Mr Mi ->
  getr regs 9 = Z_to_bv 64 bufs1 -> getr regs 10 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 w1 -> getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval -> getr regs 20 = Z_to_bv 64 tab38 ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1b47c) Mi rom) (mkst regs' (Z_to_bv 64 0x1b30c) Mi' rom)
    /\ rinv R3 Mr Mi' /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 15; 16]%list) regs regs'.
Proof.
  intros Mr ROr (TK0 & TK38 & TK14) regs Mi RI H9 H10 H11 H18 H19 H20.
  pose proof (tab_apart 3%nat tabval ltac:(lia) eq_refl) as AP0. pose proof (tab_apart 4%nat tab38 ltac:(lia) eq_refl) as AP38.
  pose proof pc_cells_in as CI. pose proof (cells_ok_of SEGS Mr Mi R3 _ ROr (proj1 RI) CI) as CK.
  destruct (pc_1b380_path rom lined bufs1 bufs2 tabval tab38 w1 wpl wpld pch fx regs Mi CK
              (tab_rd_of SEGS false _ R3 _ Mr Mi tabval TK0 RI CI AP0) (tab_rd_of SEGS true _ R3 _ Mr Mi tab38 TK38 RI CI AP38) H9 H10 H11 H18 H19 H20)
    as (r1 & m1 & RUN1 & FR1 & E10 & E14 & AG1).
  exists r1, m1. split; [exact RUN1|]. split; [exact (rinv_cells R3 _ Mr Mi m1 RI FR1 CI) | exact AG1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pgh : forall j, (0 <= j < w1)%Z -> pg_hyps lined bufs1 tabval tab38 j w1 wpl wpld.
Proof.
  intros j Hj. geom. unfold pg_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GD 0%nat 1%nat D. exact D.
  - unfold dapart. pw GD 0%nat 4%nat D. exact D.
Qed.
Lemma pg_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R2 (pg_1b474_cells_def lined bufs1 tabval tab38 j w1 wpl wpld).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold pg_1b474_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R2 |]). destruct Hc.
Qed.
Definition f1regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 10 = Z_to_bv 64 lined /\ getr regs 13 = Z_to_bv 64 j /\ getr regs 14 = Z_to_bv 64 w1 /\ getr regs 16 = Z_to_bv 64 (bufs1 + j) /\
  getr regs 19 = Z_to_bv 64 tabval /\ getr regs 20 = Z_to_bv 64 tab38 /\ getr regs 27 = Z_to_bv 64 268435455.

Lemma pg_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R2 -> tabs_ok Mr ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R2 Mr Mi -> f1regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1b570) Mi rom) (mkst regs' (Z_to_bv 64 0x1b600) Mi' rom)
    /\ rinv R2 Mr Mi' /\ regs_agree (fun r => In r [5; 6; 7; 12; 13; 16; 17; 28; 29]%list) regs regs'.
Proof.
  intros Mr ROr (TK0 & TK38 & TK14). geom.
  pose proof (fun r Hr => tab_apart 3%nat tabval ltac:(lia) eq_refl r (R2_R3 r Hr)) as AP0.
  pose proof (fun r Hr => tab_apart 4%nat tab38 ltac:(lia) eq_refl r (R2_R3 r Hr)) as AP38.
  induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H10 & H13 & H14 & H16 & H19 & H20 & H27).
  pose proof (pg_cells_in j Hj) as CI.
  pose proof (cells_ok_of SEGS Mr Mi R2 _ ROr (proj1 RI) CI) as CK.
  destruct (pg_1b474_path rom lined bufs1 tabval tab38 j w1 wpl wpld (pgh j Hj) fx regs Mi CK
              (tab_rd_of SEGS false _ R2 _ Mr Mi tabval TK0 RI CI AP0) (tab_rd_of SEGS true _ R2 _ Mr Mi tab38 TK38 RI CI AP38) H10 H13 H14 H16 H19 H20 H27)
    as (r1 & m1 & RUN1 & FR1 & E13 & E16 & E17 & E28 & AG1).
  pose proof (rinv_cells R2 _ Mr Mi m1 RI FR1 CI) as RI1.
  assert (CI0 : cells_in R2 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - destruct (pg_1b470f rom lined bufs1 tabval tab38 j w1 wpl wpld (pgh j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R2 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f1regs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (pg_1b470t rom lined bufs1 tabval tab38 j w1 wpl wpld (pgh j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R2 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

(* [comment removed for export] *)
Lemma plh : pl_hyps lined bufs1 tabval w1 wpl wpld.
Proof. geom. unfold pl_hyps. repeat split; try assumption; try lia. Qed.
Lemma pl_cells_in : cells_in R2 (pl_1b504_cells_def lined bufs1 tabval w1 wpl wpld).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 16 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold pl_1b504_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R2 |]). destruct Hc.
Qed.
Lemma pl_run : forall (Mr : word -> option byte), regions_ok SEGS Mr R2 -> tabs_ok Mr ->
  forall regs Mi, rinv R2 Mr Mi ->
  getr regs 8 = Z_to_bv 64 w1 -> getr regs 9 = Z_to_bv 64 bufs1 -> getr regs 10 = Z_to_bv 64 lined -> getr regs 19 = Z_to_bv 64 tabval ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1b600) Mi rom) (mkst regs' (Z_to_bv 64 0x1b650) Mi' rom)
    /\ rinv R2 Mr Mi' /\ regs_agree (fun r => In r [10; 12; 13; 14; 15]%list) regs regs'.
Proof.
  intros Mr ROr (TK0 & TK38 & TK14) regs Mi RI H8 H9 H10 H19.
  pose proof (fun r Hr => tab_apart 3%nat tabval ltac:(lia) eq_refl r (R2_R3 r Hr)) as AP0.
  pose proof pl_cells_in as CI. pose proof (cells_ok_of SEGS Mr Mi R2 _ ROr (proj1 RI) CI) as CK.
  destruct (pl_1b504_path rom lined bufs1 tabval w1 wpl wpld plh fx regs Mi CK (tab_rd_of SEGS false _ R2 _ Mr Mi tabval TK0 RI CI AP0) H8 H9 H10 H19)
    as (r1 & m1 & RUN1 & FR1 & E10 & AG1).
  exists r1, m1. split; [exact RUN1|]. split; [exact (rinv_cells R2 _ Mr Mi m1 RI FR1 CI) | exact AG1].
Qed.

End PixLoops.
End O15LeptDith2.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15_code_gqD.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15DithBinLL.
Module O15LeptDithBin.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15_code_gqD.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15DithBinLL.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Section LineLow.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Variables (s lined bufs1 bufs2 w1 lc uc wpl wpld : Z).
Definition ll_geom : Prop :=
  (4096 <= s - 32 /\ s < 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= lined /\ lined + 4 * wpld < 2 ^ 47 /\ 4096 <= bufs1 /\ bufs1 + 4 * wpl < 2 ^ 47 /\
   4096 <= bufs2 /\ bufs2 + 4 * wpl < 2 ^ 47 /\ lined mod 4 = 0 /\ bufs1 mod 4 = 0 /\ bufs2 mod 4 = 0 /\
   0 <= w1 <= 19999 /\ w1 + 1 <= 4 * wpl /\ w1 + 1 <= 32 * wpld /\ 0 <= lc <= 255 /\ 0 <= uc <= 255 /\
   (bufs1 + 4 * wpl <= bufs2 \/ bufs2 + 4 * wpl <= bufs1) /\ (lined + 4 * wpld <= bufs1 \/ bufs1 + 4 * wpl <= lined) /\
   (lined + 4 * wpld <= bufs2 \/ bufs2 + 4 * wpl <= lined) /\ (s <= lined \/ lined + 4 * wpld <= s - 32) /\
   (s <= bufs1 \/ bufs1 + 4 * wpl <= s - 32) /\ (s <= bufs2 \/ bufs2 + 4 * wpl <= s - 32))%Z.
Hypothesis G : ll_geom.
Variable M0 : word -> option byte.
Definition R3 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl); (bufs2, 4 * wpl)]%Z.
Hypothesis RO : regions_ok SEGS M0 R3.

Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gl0 & Gl1 & Gb10 & Gb11 & Gb20 & Gb21 & ALl & ALb1 & ALb2 & Gw & Gwpl & Gwpld & Glc & Guc & D12 & Dl1 & Dl2 & Dsl & Ds1 & Ds2).

Lemma blh : forall j, (0 <= j < w1)%Z -> bl_hyps lined bufs1 bufs2 j w1 lc uc wpl.
Proof. intros j Hj. geom. unfold bl_hyps. repeat split; lia. Qed.
Lemma bch : bc_hyps lined bufs1 bufs2 w1 lc uc wpl.
Proof. geom. unfold bc_hyps. repeat split; lia. Qed.

Ltac al4 :=
  match goal with H : (lined mod 4 = 0)%Z |- _ => let c := fresh "cl" in let E := fresh "Ecl" in destruct (al4_ex _ H) as [c E] end;
  match goal with H : (bufs1 mod 4 = 0)%Z |- _ => let c := fresh "cb1" in let E := fresh "Ecb1" in destruct (al4_ex _ H) as [c E] end;
  match goal with H : (bufs2 mod 4 = 0)%Z |- _ => let c := fresh "cb2" in let E := fresh "Ecb2" in destruct (al4_ex _ H) as [c E] end.
Ltac cell_in := cbn [fst snd]; split; [lia|]; first [ (exists (lined, 4 * wpld)%Z; split; [unfold R3; dl_in0 | cbn [fst snd]; dl_lia])
                                                     | (exists (bufs1, 4 * wpl)%Z; split; [unfold R3; dl_in0 | cbn [fst snd]; dl_lia])
                                                     | (exists (bufs2, 4 * wpl)%Z; split; [unfold R3; dl_in0 | cbn [fst snd]; dl_lia]) ].

Lemma bl_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R3 (bl_1a6d0_cells_def lined bufs1 bufs2 j w1 lc uc wpl).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold bl_1a6d0_cells_def in Hc. cbn [In] in Hc.
  repeat (destruct Hc as [<- | Hc]; [cell_in |]). destruct Hc.
Qed.
Lemma bc_cells_in : cells_in R3 (bc_1a82c_cells_def lined bufs1 bufs2 w1 lc uc wpl).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold bc_1a82c_cells_def in Hc. cbn [In] in Hc.
  repeat (destruct Hc as [<- | Hc]; [cell_in |]). destruct Hc.
Qed.

(* [comment removed for export] *)
Definition lregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 5 = Z_to_bv 64 (bufs2 + 1) /\ getr regs 6 = Z_to_bv 64 (bufs1 + 1) /\ getr regs 7 = Z_to_bv 64 134217727 /\
  getr regs 10 = Z_to_bv 64 lined /\ getr regs 11 = Z_to_bv 64 j /\ getr regs 12 = Z_to_bv 64 bufs1 /\ getr regs 13 = Z_to_bv 64 bufs2 /\
  getr regs 14 = Z_to_bv 64 lc /\ getr regs 15 = Z_to_bv 64 uc /\ getr regs 16 = Z_to_bv 64 j /\ getr regs 28 = Z_to_bv 64 w1 /\
  getr regs 29 = Z_to_bv 64 18446744071562067968.

(* [comment removed for export] *)
Lemma bl_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R3 ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R3 Mr Mi -> lregs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1a7cc) Mi rom) (mkst regs' (Z_to_bv 64 0x1a928) Mi' rom)
    /\ rinv R3 Mr Mi' /\ regs_agree (fun r => In r [8; 9; 11; 16; 18; 30; 31]%list) regs regs'.
Proof.
  intros Mr ROr. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H5 & H6 & H7 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H28 & H29).
  pose proof (cells_ok_of SEGS Mr Mi R3 _ ROr (proj1 RI) (bl_cells_in j Hj)) as CK.
  destruct (bl_1a6d0_path rom lined bufs1 bufs2 j w1 lc uc wpl (blh j Hj) fx regs Mi CK H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H28 H29)
    as (r1 & m1 & RUN1 & FR1 & E11 & E16 & AG1).
  pose proof (rinv_cells R3 _ Mr Mi m1 RI FR1 (bl_cells_in j Hj)) as RI1.
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - (* [comment removed for export] *)
    destruct (bl_1a6ccf rom lined bufs1 bufs2 j w1 lc uc wpl (blh j Hj) fx r1 m1 ltac:(ex_br)
                ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get))
      as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (CI0 : cells_in R3 []) by (intros c []).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold lregs. repeat split; dl_get. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - (* [comment removed for export] *)
    destruct (bl_1a6cct rom lined bufs1 bufs2 j w1 lc uc wpl (blh j Hj) fx r1 m1 ltac:(ex_br)
                ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get))
      as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (CI0 : cells_in R3 []) by (intros c []).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

(* [comment removed for export] *)
Lemma ll_ret : forall regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (mkst regs (Z_to_bv 64 0x1a9d4) m rom) (mkst regs ret m rom).
Proof.
  intros regs m ret Hret H1. replace (Z_to_bv 64 0x1a9d4) with (0x1a9d4 : word) by (apply bv_eq; reflexivity).
  stepret F_1a97c D_1a97c ret ltac:(exact H1). apply mst_refl.
Qed.

Definition R4 : list (Z * Z) := ((s - 32)%Z, 32%Z) :: R3.
Lemma R3_R4 : forall r, In r R3 -> In r R4.
Proof. intros r Hr. right. exact Hr. Qed.

(* [comment removed for export] *)
Lemma dbll0_run : forall regs (ret : word), ret_ok ret ->
  store_ok SEGS M0 (Z_to_bv 64 (s - 32)) 32 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 -> getr regs 13 = Z_to_bv 64 bufs2 -> getr regs 14 = Z_to_bv 64 lc -> getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 0 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1a6a0) M0 rom) (mkst regs' ret M' rom)
    /\ rinv R4 M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18
    /\ regs_agree (fun r => In r [2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 15; 16; 17; 18; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros regs ret Hret SOKF H2 H1 H10 H11 H12 H13 H14 H15 H16. geom.
  assert (HYPp : bp_hyps s lined bufs1 bufs2 w1 lc uc) by (unfold bp_hyps; repeat split; lia).
  assert (HYPe : be_hyps s) by (unfold be_hyps; repeat split; lia).
  (* [comment removed for export] *)
  destruct (bp_1a5a4 rom s lined bufs1 bufs2 w1 lc uc HYPp fx regs M0
              (reg_sok SEGS M0 M0 (s - 32) 32 (s - 8) 8 (mem_grows_refl _) SOKF ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))
              (reg_sok SEGS M0 M0 (s - 32) 32 (s - 16) 8 (mem_grows_refl _) SOKF ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))
              (reg_sok SEGS M0 M0 (s - 32) 32 (s - 24) 8 (mem_grows_refl _) SOKF ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia))
              H2 H10 H11 H12 H13 H14 H15 H16)
    as (r1 & m1 & RUN1 & FR1 & E2 & E16 & E17 & SV8 & SV9 & SV18 & AG1).
  assert (RI1 : rinv R4 M0 m1).
  { apply (rinv_cells R4 _ M0 M0 m1 (rinv_refl _ _) FR1). intros c Hc. cbn [In] in Hc.
    repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 32)%Z, 32%Z); split; [left; reflexivity | cbn [fst snd]; lia] |]). destruct Hc. }
  (* [comment removed for export] *)
  assert (RO1 : regions_ok SEGS m1 R3).
  { intros r Hr. destruct (RO r Hr) as (A0 & A1 & A2 & A3). repeat split; try assumption. eapply store_ok_mono; [exact (proj1 FR1) | exact A3]. }
  assert (MID : exists r3 m3, msteps SEGS (mkst r1 (Z_to_bv 64 0x1a790) m1 rom) (mkst r3 (Z_to_bv 64 0x1a928) m3 rom)
                  /\ rinv R3 m1 m3 /\ getr r3 17 = Z_to_bv 64 w1
                  /\ regs_agree (fun r => In r [5; 6; 7; 8; 9; 11; 16; 17; 18; 28; 29; 30; 31]%list) r1 r3).
  { destruct (Z.eq_dec w1 0) as [W0|W1].
    - destruct (bp_1a694t rom s lined bufs1 bufs2 w1 lc uc HYPp fx r1 m1 ltac:(ex_br)
                  ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get))
        as (r2 & m2 & RUN2 & FR2 & F17 & AG2).
      exists r2, m2. split; [exact RUN2|]. split; [apply (rinv_cells R3 [] m1 m1 m2 (rinv_refl _ _) FR2); intros c []|].
      split; [rewrite F17; f_equal; lia | ra_chain].
    - destruct (bp_1a694f rom s lined bufs1 bufs2 w1 lc uc HYPp fx r1 m1 ltac:(ex_br)
                  ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get))
        as (r2 & m2 & RUN2 & FR2 & F5 & F6 & F7 & F11 & F16 & F28 & F29 & AG2).
      assert (RI2 : rinv R3 m1 m2) by (apply (rinv_cells R3 [] m1 m1 m2 (rinv_refl _ _) FR2); intros c []).
      destruct (bl_loop m1 RO1 (Z.to_nat w1) 0%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
      { unfold lregs. repeat split; dl_get. }
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN2 RUN3)|]. split; [exact RI3|].
      split; [rewrite (AG3 17%bv) by notin_list; rewrite (AG2 17%bv) by notin_list; exact E17 | ra_chain]. }
  destruct MID as (r3 & m3 & RUN3 & RI3 & G17 & AG3).
  (* [comment removed for export] *)
  pose proof (cells_ok_of SEGS m1 m3 R3 _ RO1 (proj1 RI3) bc_cells_in) as CK3.
  destruct (bc_1a82c_path rom lined bufs1 bufs2 w1 lc uc wpl bch fx r3 m3 CK3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) G17)
    as (r4 & m4 & RUN4 & FR4 & AG4).
  pose proof (rinv_cells R3 _ m1 m3 m4 RI3 FR4 bc_cells_in) as RI4.
  (* [comment removed for export] *)
  assert (FRM : forall k (v : word), (k = 8 \/ k = 16 \/ k = 24)%Z -> rdn SEGS m1 (Z_to_bv 64 (s - k)) 8 = Some (word_to_le_bytes 8 v) ->
                                      rdn SEGS m4 (Z_to_bv 64 (s - k)) 8 = Some (word_to_le_bytes 8 v)).
  { intros k v Hk R. rewrite <- R. apply (rinv_rdn SEGS R3 m1 m4 (s - k) 8 RI4); [lia | cbn; lia |].
    intros r Hr. unfold R3 in Hr. cbn [In] in Hr. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
    repeat (destruct Hr as [<- | Hr]; [cbn [fst snd]; lia |]). destruct Hr. }
  destruct (be_1a8c8 rom s HYPe fx r4 m4 _ _ _ (FRM 8%Z _ ltac:(lia) SV8) (FRM 16%Z _ ltac:(lia) SV9) (FRM 24%Z _ ltac:(lia) SV18) ltac:(dl_get))
    as (r5 & m5 & RUN5 & FR5 & X2 & X8 & X9 & X18 & AG5).
  rewrite rdv_word8 in X8, X9, X18.
  pose proof (ll_ret r5 m5 ret Hret ltac:(dl_get)) as RUN6.
  exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 (msteps_trans _ _ _ _ RUN5 RUN6))))|].
  split.
  { apply (rinv_trans R4 M0 m1 m5 RI1). apply (rinv_incl R3 R4 m1 m5); [| exact R3_R4].
    apply (rinv_cells R3 [] m1 m4 m5 RI4 FR5). intros c []. }
  split; [exact X2|]. split; [exact X8|]. split; [exact X9|]. split; [exact X18|]. ra_chain.
Qed.

End LineLow.
End O15LeptDithBin.

From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTab1.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require O15ThrLut.
Module O15LeptThrLut.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.leptonica.grayquant_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLoop.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTab1.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTabLoop.
Import OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15.O15ThrLut.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Ltac dl_get2 :=
  first [ eassumption
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get2 end ].

Section Lut.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (sp datad datat qtab w h wpld wplt : Z).
Definition lut_geom : Prop :=
  (4096 <= sp /\ sp + 64 < 2 ^ 47 /\ 4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\
   4096 <= datat /\ datat + 4 * (wplt * h) < 2 ^ 47 /\ datat mod 4 = 0 /\ 4096 <= qtab /\ qtab + 1024 < 2 ^ 47 /\ qtab mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wpld <= 5000 /\ 1 <= wplt <= 5000 /\ w <= 4 * wpld /\ w <= 4 * wplt)%Z.
(* [comment removed for export] *)
Definition lut_disj : Prop :=
  (datad + 4 * (wpld * h) <= sp \/ sp + 64 <= datad)%Z /\ (datad + 4 * (wpld * h) <= qtab \/ qtab + 1024 <= datad)%Z.
Hypothesis G : lut_geom.
Hypothesis GD : lut_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gd0 & Gd1 & ALd & Gt0 & Gt1 & ALt & Gq0 & Gq1 & ALq & Gw & Gh & Gwd & Gwt & Gw4d & Gw4t).

Definition RD : Z * Z := (datad, 4 * (wpld * h))%Z.
Definition RS : Z * Z := (datat, 4 * (wplt * h))%Z.
Definition kcs (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (sp + 48)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M (Z_to_bv 64 (sp + 52)) 4 = Some (Z_to_le_bytes 4 w) /\
  rdn SEGS M (Z_to_bv 64 (sp + 56)) 8 = Some (Z_to_le_bytes 8 qtab).
(* [comment removed for export] *)
Definition qtab_ok (M : word -> option byte) : Prop :=
  forall k, (0 <= k <= 255)%Z -> exists bs, rdn SEGS M (Z_to_bv 64 (qtab + 4 * k)) 1 = Some bs.

Lemma kcs_keep : forall (M1 Mi : word -> option byte), rinv [RD] M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3). geom. destruct GD as (DF & DQ). unfold kcs.
  repeat split; [rewrite <- K1 | rewrite <- K2 | rewrite <- K3];
    (apply (rinv_rdn SEGS [RD] M1 Mi _ _ RI); [lia | cbn; lia | intros r [<- | []]; unfold RD; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.
Lemma qtab_keep : forall (M1 Mi : word -> option byte), rinv [RD] M1 Mi -> qtab_ok M1 -> qtab_ok Mi.
Proof.
  intros M1 Mi RI QK k Hk. geom. destruct GD as (DF & DQ). destruct (QK k Hk) as (bs & R). exists bs. rewrite <- R.
  apply (rinv_rdn SEGS [RD] M1 Mi _ _ RI); [lia | cbn; lia | intros r [<- | []]; unfold RD; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Row.
Variables (drow srow : Z).
Hypothesis Hdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h) /\ drow mod 4 = 0)%Z.
Hypothesis Hsr : (datat <= srow /\ srow + 4 * wplt <= datat + 4 * (wplt * h) /\ srow mod 4 = 0)%Z.
Definition RL : list (Z * Z) := [(drow, 4 * wpld)%Z].
Definition RLS : list (Z * Z) := [(drow, 4 * wpld); (srow, 4 * wplt)]%Z.

Lemma qph : forall j, (0 <= j < w)%Z -> qp_hyps sp drow srow qtab w h j wpld wplt.
Proof.
  intros j Hj. geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3). destruct Hsr as (S1 & S2 & S3).
  unfold qp_hyps. repeat split; try assumption; try lia. unfold dapart. lia.
Qed.
Lemma qp_cells_in : forall j, (0 <= j < w)%Z -> cells_in RLS (qp_1be4c_cells_def sp drow srow qtab w h j wpld wplt).
Proof.
  intros j Hj. geom. destruct Hdr as (D1 & D2 & D3). destruct Hsr as (S1 & S2 & S3).
  destruct (al4_ex _ D3) as [cd Ecd]. destruct (al4_ex _ S3) as [cs Ecs].
  intros c Hc. unfold qp_1be4c_cells_def in Hc. cbn [In] in Hc. destruct Hc as [<- | [<- | []]]; cbn [fst snd]; (split; [lia|]).
  - exists (srow, 4 * wplt)%Z. split; [unfold RLS; dl_in0 | cbn [fst snd]; dl_lia].
  - exists (drow, 4 * wpld)%Z. split; [unfold RLS; dl_in0 | cbn [fst snd]; dl_lia].
Qed.
Lemma qp_wcells_in : forall j, (0 <= j < w)%Z -> cells_in RL (qp_1be4c_cells_w_def sp drow srow qtab w h j wpld wplt).
Proof.
  intros j Hj. geom. destruct Hdr as (D1 & D2 & D3). destruct (al4_ex _ D3) as [cd Ecd].
  intros c Hc. unfold qp_1be4c_cells_w_def in Hc. cbn [In] in Hc. destruct Hc as [<- | []]; cbn [fst snd]; (split; [lia|]).
  exists (drow, 4 * wpld)%Z. split; [unfold RL; dl_in0 | cbn [fst snd]; dl_lia].
Qed.

Definition pregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 sp /\ getr regs 11 = Z_to_bv 64 j /\ getr regs 13 = Z_to_bv 64 (srow + j) /\ getr regs 15 = Z_to_bv 64 (drow + j).

Lemma kcs_row : forall (M1 Mi : word -> option byte), rinv RL M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3). geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3). unfold kcs.
  repeat split; [rewrite <- K1 | rewrite <- K2 | rewrite <- K3];
    (apply (rinv_rdn SEGS RL M1 Mi _ _ RI); [lia | cbn; lia | intros r [<- | []]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

(* [comment removed for export] *)
Lemma px_tab : forall (Mr Mi : word -> option byte) j, (0 <= j < w)%Z -> rinv RL Mr Mi -> qtab_ok Mr ->
  tab_rdn SEGS 1 false (fun _ => True) (qp_1be4c_cells_w_def sp drow srow qtab w h j wpld wplt) Mi qtab.
Proof.
  intros Mr Mi j Hj RI QK m' k FR Hk. geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3).
  destruct (QK k Hk) as (bs & R). exists bs. split; [|exact I]. rewrite <- R.
  apply (rinv_rdn SEGS RL Mr m' _ _ (rinv_cells RL _ Mr Mi m' RI FR (qp_wcells_in j Hj))); [lia | cbn; lia |].
  intros r [<- | []]. cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Lemma px_kcs : forall (Mr Mi : word -> option byte) j, (0 <= j < w)%Z -> rinv RL Mr Mi -> kcs Mr ->
  forall m', mframe (qp_1be4c_cells_w_def sp drow srow qtab w h j wpld wplt) Mi m' -> kcs m'.
Proof.
  intros Mr Mi j Hj RI (K1 & K2 & K3) m' FR. geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3).
  pose proof (rinv_cells RL _ Mr Mi m' RI FR (qp_wcells_in j Hj)) as RI'. unfold kcs.
  repeat split; [rewrite <- K1 | rewrite <- K2 | rewrite <- K3];
    (apply (rinv_rdn SEGS RL Mr m' _ _ RI'); [lia | cbn; lia | intros r [<- | []]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

Lemma px_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr RLS -> kcs Mr -> qtab_ok Mr ->
  forall (n : nat) j regs Mi, (w - j <= Z.of_nat n)%Z -> (0 <= j < w)%Z -> rinv RL Mr Mi -> pregs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1bf48) Mi rom) (mkst regs' (Z_to_bv 64 0x1bf7c) Mi' rom)
    /\ rinv RL Mr Mi' /\ getr regs' 12 = Z_to_bv 64 w /\ regs_agree (fun r => In r [11; 12; 13; 15; 16]%list) regs regs'.
Proof.
  intros Mr ROr KC QK. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H2 & H11 & H13 & H15).
  pose proof (cells_ok_of SEGS Mr Mi RLS _ ROr (proj1 RI) (qp_cells_in j Hj)) as CK.
  pose proof (px_kcs Mr Mi j Hj RI KC) as KM.
  destruct (qp_1be4c_path rom sp drow srow qtab w h j wpld wplt (qph j Hj) fx regs Mi CK (px_tab Mr Mi j Hj RI QK)
              (fun m' F => proj1 (KM m' F)) (fun m' F => proj1 (proj2 (KM m' F))) (fun m' F => proj2 (proj2 (KM m' F))) H2 H11 H13 H15)
    as (r1 & m1 & RUN1 & FR1 & FW1 & E11 & E12 & E13 & E15 & E16 & AG1).
  pose proof (rinv_cells RL _ Mr Mi m1 RI FW1 (qp_wcells_in j Hj)) as RI1.
  destruct (kcs_row Mr m1 RI1 KC) as (K1 & K2 & K3).
  assert (CI0 : cells_in RL []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w) as [LT|GE].
  - destruct (qp_1be7ct rom sp drow srow qtab w h j wpld wplt (qph j Hj) fx r1 m1 ltac:(ex_br) K1 K2 K3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RL _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & X12 & AG3).
    { unfold pregs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|]. split; [exact X12 | ra_chain].
  - destruct (qp_1be7cf rom sp drow srow qtab w h j wpld wplt (qph j Hj) fx r1 m1 ltac:(ex_br) K1 K2 K3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RL _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|]. split; [dl_get2 | ra_chain].
Qed.

End Row.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rregs (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 sp /\ getr regs 9 = Z_to_bv 64 (datad + 4 * (wpld * i)) /\ getr regs 10 = Z_to_bv 64 i /\ getr regs 12 = Z_to_bv 64 w /\
  getr regs 14 = Z_to_bv 64 (4 * wplt) /\ getr regs 18 = Z_to_bv 64 (datat + 4 * (wplt * i)) /\ getr regs 19 = Z_to_bv 64 (4 * wpld).

Lemma row_loop : forall (M0 : word -> option byte), regions_ok SEGS M0 [RD; RS] -> kcs M0 -> qtab_ok M0 ->
  forall (n : nat) i regs Mi, (h - i <= Z.of_nat n)%Z -> (0 <= i < h)%Z -> rinv [RD] M0 Mi -> rregs regs i ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1bf38) Mi rom) (mkst regs' (Z_to_bv 64 0x1bf84) Mi' rom)
    /\ rinv [RD] M0 Mi' /\ regs_agree (fun r => In r [9; 10; 11; 12; 13; 15; 16; 18]%list) regs regs'.
Proof.
  intros M0 RO0 KC0 QK0. geom. induction n as [|n IH]; intros i regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H9 & H10 & H12 & H14 & H18 & H19).
  pose proof (row_bounds wpld i h ltac:(lia) ltac:(lia) ltac:(lia)) as P1. pose proof (row_bounds wplt i h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  remember (datad + 4 * (wpld * i))%Z as drow eqn:Edr. remember (datat + 4 * (wplt * i))%Z as srow eqn:Esr.
  assert (Hdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h) /\ drow mod 4 = 0)%Z).
  { split; [lia|]. split; [lia|]. subst drow. apply al4_add. exact ALd. }
  assert (Hsr : (datat <= srow /\ srow + 4 * wplt <= datat + 4 * (wplt * h) /\ srow mod 4 = 0)%Z).
  { split; [lia|]. split; [lia|]. subst srow. apply al4_add. exact ALt. }
  assert (Edr' : (datad + 4 * (wpld * (i + 1)))%Z = (drow + 4 * wpld)%Z) by (subst drow; ring).
  assert (Esr' : (datat + 4 * (wplt * (i + 1)))%Z = (srow + 4 * wplt)%Z) by (subst srow; ring).
  clear P1 P2 Edr Esr.
  destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD). destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS).
  unfold RD, RS in *. cbn [fst snd] in *.
  assert (HYPr : qr_hyps sp drow srow w) by (unfold qr_hyps; repeat split; first [assumption | lia]).
  destruct (qr_1be3c rom sp drow srow w HYPr fx regs Mi H2 H9 H12 H18) as (r1 & m1 & RUN1 & FR1 & E11 & E13 & E15 & AG1).
  assert (RI1 : rinv [RD] M0 m1) by (apply (rinv_cells [RD] [] M0 Mi m1 RI FR1); intros c []).
  assert (ROL : regions_ok SEGS m1 (RLS drow srow)).
  { intros r Hr. unfold RLS in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 m1 datad _ drow _ (proj1 RI1) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. apply (reg_sok SEGS M0 m1 datat _ srow _ (proj1 RI1) SOKS); rewrite ?Z2Nat.id by lia; lia. }
  destruct (px_loop drow srow Hdr Hsr m1 ROL (kcs_keep M0 m1 RI1 KC0) (qtab_keep M0 m1 RI1 QK0) (Z.to_nat w) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _))
    as (r2 & m2 & RUN2 & RI2 & X12 & AG2).
  { unfold pregs. repeat split; dl_get2. }
  assert (RI2' : rinv [RD] M0 m2).
  { apply (rinv_trans [RD] M0 m1 m2 RI1). apply (rinv_weaken (RL drow) [RD] m1 m2 RI2).
    intros r [<- | []]. exists (datad, 4 * (wpld * h))%Z. split; [unfold RD; dl_in0 | cbn [fst snd]; lia]. }
  destruct (kcs_keep M0 m2 RI2' KC0) as (K1 & K2 & K3).
  assert (HYPl : ql_hyps sp drow srow qtab w h i (4 * wpld) (4 * wplt)).
  { unfold ql_hyps. repeat split; try assumption; try lia; rewrite Z.mul_comm; apply Z_mod_mult. }
  destruct (ql_1be80 rom sp drow srow qtab w h i (4 * wpld) (4 * wplt) HYPl fx r2 m2 K1 K2 K3 ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r3 & m3 & RUN3 & FR3 & E3_9 & E3_10 & E3_11 & E3_18 & AG3).
  assert (RI3 : rinv [RD] M0 m3) by (apply (rinv_cells [RD] [] M0 m2 m3 RI2' FR3); intros c []).
  destruct (kcs_keep M0 m3 RI3 KC0) as (K1' & K2' & K3').
  destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
  - destruct (ql_1be38f rom sp drow srow qtab w h i (4 * wpld) (4 * wplt) HYPl fx r3 m3 ltac:(ex_br) K1' K2' K3'
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)) as (r4 & m4 & RUN4 & FR4 & AG4).
    assert (RI4 : rinv [RD] M0 m4) by (apply (rinv_cells [RD] [] M0 m3 m4 RI3 FR4); intros c []).
    destruct (IH (i + 1)%Z r4 m4 ltac:(lia) ltac:(lia) RI4) as (r5 & m5 & RUN5 & RI5 & AG5).
    { unfold rregs. rewrite Edr', Esr'. repeat split; dl_get2. }
    exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
    split; [exact RI5 | ra_chain].
  - destruct (ql_1be38t rom sp drow srow qtab w h i (4 * wpld) (4 * wplt) HYPl fx r3 m3 ltac:(ex_br) K1' K2' K3'
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)) as (r4 & m4 & RUN4 & FR4 & AG4).
    assert (RI4 : rinv [RD] M0 m4) by (apply (rinv_cells [RD] [] M0 m3 m4 RI3 FR4); intros c []).
    exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
    split; [exact RI4 | ra_chain].
Qed.

(* [comment removed for export] *)
Lemma lut_run : forall (M0 : word -> option byte) regs, regions_ok SEGS M0 [RD; RS] -> kcs M0 -> qtab_ok M0 ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 h -> getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 18 = Z_to_bv 64 datat -> getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1bf10) M0 rom) (mkst regs' (Z_to_bv 64 0x1bf84) M' rom)
    /\ rinv [RD] M0 M' /\ regs_agree (fun r => In r [9; 10; 11; 12; 13; 14; 15; 16; 18; 19]%list) regs regs'.
Proof.
  intros M0 regs RO0 KC0 QK0 H2 H9 H11 H14 H18 H19. geom. destruct KC0 as (K1 & K2 & K3).
  assert (HYPa : qa_hyps sp qtab w h wpld wplt) by (unfold qa_hyps; repeat split; first [assumption | lia]).
  destruct (qa_1be14 rom sp qtab w h wpld wplt HYPa fx regs M0 K1 K2 K3 H2 H11 H14 H19) as (r1 & m1 & RUN1 & FR1 & E10 & E12 & E14 & E19 & AG1).
  assert (RI1 : rinv [RD] M0 m1) by (apply (rinv_cells [RD] [] M0 M0 m1 (rinv_refl _ _) FR1); intros c []).
  destruct (row_loop M0 RO0 (conj K1 (conj K2 K3)) QK0 (Z.to_nat h) 0%Z r1 m1 ltac:(lia) ltac:(lia) RI1) as (r2 & m2 & RUN2 & RI2 & AG2).
  { unfold rregs. repeat split; dl_get2. }
  exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

End Lut.
End O15LeptThrLut.
