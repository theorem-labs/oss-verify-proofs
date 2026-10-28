(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15_code_gqD.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15DithBinLL.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15DithBinLL0.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Module V15LeptDithBin.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLoop.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15_code_gqD.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15DithBinLL.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15DithBinLL0.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section LineLow.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (s lined bufs1 bufs2 w1 lc uc wpl wpld : Z).
(* [comment removed for export] *)
Definition ll_geom : Prop :=
  (4096 <= s - 48 /\ s < 2 ^ 47 /\ s mod 16 = 0 /\ 4096 <= lined /\ lined + 4 * wpld < 2 ^ 47 /\ 4096 <= bufs1 /\ bufs1 + 4 * wpl < 2 ^ 47 /\
   4096 <= bufs2 /\ bufs2 + 4 * wpl < 2 ^ 47 /\ lined mod 4 = 0 /\ bufs1 mod 4 = 0 /\ bufs2 mod 4 = 0 /\
   0 <= w1 <= 19999 /\ w1 + 1 <= 4 * wpl /\ w1 + 1 <= 32 * wpld /\ 0 <= lc <= 255 /\ 0 <= uc <= 255)%Z.
(* [comment removed for export] *)
Definition apart (a na b nb : Z) : Prop := (a + na <= b \/ b + nb <= a)%Z.
Definition ll_disj : Prop :=
  apart bufs1 (4 * wpl) bufs2 (4 * wpl) /\ apart lined (4 * wpld) bufs1 (4 * wpl) /\ apart lined (4 * wpld) bufs2 (4 * wpl) /\
  apart (s - 48) 48 lined (4 * wpld) /\ apart (s - 48) 48 bufs1 (4 * wpl) /\ apart (s - 48) 48 bufs2 (4 * wpl).
Hypothesis G : ll_geom.
Hypothesis GD : ll_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gl0 & Gl1 & Gb10 & Gb11 & Gb20 & Gb21 & ALl & ALb1 & ALb2 & Gw & Gwpl & Gwpld & Glc & Guc).
Ltac dlia :=
  let go H := (let D_ := fresh "D_" in pose proof H as D_; unfold apart in D_; lia) in
  let D12 := fresh in let Dl1 := fresh in let Dl2 := fresh in let DFl := fresh in let DF1 := fresh in let DF2 := fresh in
  pose proof GD as (D12 & Dl1 & Dl2 & DFl & DF1 & DF2);
  first [ go D12 | go Dl1 | go Dl2 | go DFl | go DF1 | go DF2 ].
Ltac al4 :=
  match goal with H : (bufs1 mod 4 = 0)%Z |- _ => let c := fresh "cb1" in let E := fresh "Ecb1" in destruct (al4_ex _ H) as [c E] end;
  match goal with H : (bufs2 mod 4 = 0)%Z |- _ => let c := fresh "cb2" in let E := fresh "Ecb2" in destruct (al4_ex _ H) as [c E] end.

Definition R3 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl); (bufs2, 4 * wpl)]%Z.
Definition R2 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl)]%Z.

Lemma ll_ret : forall regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (mkst regs (Z_to_bv 64 0x1c094) m rom) (mkst regs ret m rom).
Proof.
  intros regs m ret Hret H1. replace (Z_to_bv 64 0x1c094) with (0x1c094 : word) by (apply bv_eq; reflexivity).
  stepret F_1bf90 D_1bf90 ret ltac:(exact H1). apply mst_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v0h : forall j, (0 <= j < w1)%Z -> v0_hyps lined bufs1 bufs2 j w1 lc uc wpl.
Proof. intros j Hj. geom. unfold v0_hyps. repeat split; first [assumption | lia | dlia]. Qed.
Lemma vt0h : vt0_hyps lined bufs1 bufs2 w1 lc uc wpl.
Proof. geom. unfold vt0_hyps. repeat split; first [assumption | lia | dlia]. Qed.

Ltac cell_in RR :=
  cbn [fst snd]; split; [lia|]; first [ (exists (lined, 4 * wpld)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia])
                                        | (exists (bufs1, 4 * wpl)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia])
                                        | (exists (bufs2, 4 * wpl)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia]) ].

Lemma v0_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R3 (v0_1bcc0_cells_def lined bufs1 bufs2 j w1 lc uc wpl).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold v0_1bcc0_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R3 |]). destruct Hc.
Qed.
Lemma vt0_cells_in : cells_in R3 (vt0_1be64_cells_def lined bufs1 bufs2 w1 lc uc wpl).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold vt0_1be64_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R3 |]). destruct Hc.
Qed.

Definition f0regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 5 = Z_to_bv 64 1 /\ getr regs 6 = Z_to_bv 64 3 /\ getr regs 7 = Z_to_bv 64 2 /\ getr regs 10 = Z_to_bv 64 lined /\
  getr regs 11 = Z_to_bv 64 w1 /\ getr regs 12 = Z_to_bv 64 bufs1 /\ getr regs 13 = Z_to_bv 64 bufs2 /\ getr regs 14 = Z_to_bv 64 lc /\
  getr regs 15 = Z_to_bv 64 uc /\ getr regs 16 = Z_to_bv 64 j /\ getr regs 17 = Z_to_bv 64 j /\ getr regs 28 = Z_to_bv 64 1 /\
  getr regs 29 = Z_to_bv 64 1 /\ getr regs 30 = Z_to_bv 64 134217727 /\ getr regs 31 = Z_to_bv 64 18446744071562067968.

Lemma v0_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R3 ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R3 Mr Mi -> f0regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1bdc4) Mi rom) (mkst regs' (Z_to_bv 64 0x1bf68) Mi' rom)
    /\ rinv R3 Mr Mi' /\ regs_agree (fun r => In r [8; 9; 16; 17; 18; 19; 20; 21]%list) regs regs'.
Proof.
  intros Mr ROr. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H5 & H6 & H7 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 & H30 & H31).
  pose proof (cells_ok_of SEGS Mr Mi R3 _ ROr (proj1 RI) (v0_cells_in j Hj)) as CK.
  destruct (v0_1bcc0_path rom lined bufs1 bufs2 j w1 lc uc wpl (v0h j Hj) fx regs Mi CK H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31)
    as (r1 & m1 & RUN1 & FR1 & E16 & E17 & AG1).
  pose proof (rinv_cells R3 _ Mr Mi m1 RI FR1 (v0_cells_in j Hj)) as RI1.
  assert (CI0 : cells_in R3 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - destruct (v0_1bcbcf rom lined bufs1 bufs2 j w1 lc uc wpl (v0h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f0regs. repeat split; dl_get. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (v0_1bcbct rom lined bufs1 bufs2 j w1 lc uc wpl (v0h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

Definition R4 : list (Z * Z) := ((s - 48)%Z, 48%Z) :: R3.
Lemma R3_R4 : forall r, In r R3 -> In r R4.
Proof. intros r Hr. right. exact Hr. Qed.

(* [comment removed for export] *)
Lemma frame_keep : forall RR (M1 Mi : word -> option byte) (k : Z) v, (forall r, In r RR -> In r R3) -> rinv RR M1 Mi -> (8 <= k <= 48)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) 8 = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) 8 = Some v.
Proof.
  intros RR M1 Mi k v INC RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RR M1 Mi (s - k) 8 RI); [lia | cbn; lia |].
  intros r Hr. specialize (INC r Hr). unfold R3 in INC. cbn [In] in INC. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct INC as [<- | [<- | [<- | []]]]; cbn [fst snd]; dlia.
Qed.

(* [comment removed for export] *)
Lemma ll_tail : forall RR (INC : forall r, In r RR -> In r R3) regs (ret : word) (m1 : word -> option byte) r4 m4, ret_ok ret -> getr regs 1 = ret ->
  rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) -> rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) ->
  rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) -> rdn SEGS m1 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) ->
  rdn SEGS m1 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) -> rdn SEGS m1 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) ->
  rinv RR m1 m4 -> getr r4 2 = Z_to_bv 64 (s - 48) -> getr r4 1 = getr regs 1 ->
  exists r6 m6, msteps SEGS (mkst r4 (Z_to_bv 64 0x1c078) m4 rom) (mkst r6 ret m6 rom) /\ rinv RR m1 m6 /\ getr r6 2 = Z_to_bv 64 s
    /\ getr r6 8 = getr regs 8 /\ getr r6 9 = getr regs 9 /\ getr r6 18 = getr regs 18 /\ getr r6 19 = getr regs 19 /\ getr r6 20 = getr regs 20
    /\ getr r6 21 = getr regs 21 /\ regs_agree (fun r => In r [2; 8; 9; 18; 19; 20; 21]%list) r4 r6.
Proof.
  intros RR INC regs ret m1 r4 m4 Hret H1 SV8 SV9 SV18 SV19 SV20 SV21 RI4 Y2 Y1. geom.
  assert (HYPe : ve_hyps s) by (unfold ve_hyps; repeat split; first [assumption | lia]).
  destruct (ve_1bf74 rom s HYPe fx r4 m4 _ _ _ _ _ _
              (frame_keep RR m1 m4 8 _ INC RI4 ltac:(lia) SV8) (frame_keep RR m1 m4 16 _ INC RI4 ltac:(lia) SV9) (frame_keep RR m1 m4 24 _ INC RI4 ltac:(lia) SV18)
              (frame_keep RR m1 m4 32 _ INC RI4 ltac:(lia) SV19) (frame_keep RR m1 m4 40 _ INC RI4 ltac:(lia) SV20) (frame_keep RR m1 m4 48 _ INC RI4 ltac:(lia) SV21) Y2)
    as (r5 & m5 & RUN5 & FR5 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & AG5).
  rewrite rdv_word8 in X8, X9, X18, X19, X20, X21.
  pose proof (ll_ret r5 m5 ret Hret ltac:(rewrite (AG5 1%bv) by notin_list; rewrite Y1; exact H1)) as RUN6.
  exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN5 RUN6)|]. split; [apply (rinv_cells RR [] m1 m4 m5 RI4 FR5); intros c []|].
  repeat split; assumption.
Qed.

Lemma dbll0_run : forall (M0 : word -> option byte), regions_ok SEGS M0 R3 -> forall regs (ret : word), ret_ok ret ->
  store_ok SEGS M0 (Z_to_bv 64 (s - 48)) 48 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 -> getr regs 13 = Z_to_bv 64 bufs2 -> getr regs 14 = Z_to_bv 64 lc -> getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 0 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1bb88) M0 rom) (mkst regs' ret M' rom)
    /\ rinv R4 M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 RO regs ret Hret SOKF H2 H1 H10 H11 H12 H13 H14 H15 H16. geom.
  assert (sokF : forall k, (8 <= k <= 48)%Z -> store_ok SEGS M0 (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 M0 (s - 48) 48 (s - k) 8 (mem_grows_refl _) SOKF); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  (* [comment removed for export] *)
  assert (PRE : exists r3 m1 m3, msteps SEGS (mkst regs (Z_to_bv 64 0x1bb88) M0 rom) (mkst r3 (Z_to_bv 64 0x1bf68) m3 rom)
                  /\ rinv R4 M0 m1 /\ rinv R3 m1 m3 /\ getr r3 2 = Z_to_bv 64 (s - 48) /\ getr r3 1 = getr regs 1
                  /\ getr r3 10 = Z_to_bv 64 lined /\ getr r3 11 = Z_to_bv 64 w1 /\ getr r3 12 = Z_to_bv 64 bufs1 /\ getr r3 13 = Z_to_bv 64 bufs2
                  /\ getr r3 14 = Z_to_bv 64 lc /\ getr r3 15 = Z_to_bv 64 uc
                  /\ rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
                  /\ rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
                  /\ rdn SEGS m1 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
                  /\ (forall r, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
  { assert (FCI : forall c, In c [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] ->
                             (0 <= snd c)%Z /\ exists r, In r R4 /\ (fst r <= fst c)%Z /\ (fst c + snd c <= fst r + snd r)%Z).
    { intros c Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 48)%Z, 48%Z); split; [left; reflexivity | cbn [fst snd]; lia] |]). destruct Hc. }
    destruct (Z.eq_dec w1 0) as [W0|W1].
    - assert (HYPq : vq_hyps s lined bufs1 bufs2 lc uc) by (unfold vq_hyps; repeat split; first [assumption | lia]).
      destruct (vq_1ba84_f0 rom s lined bufs1 bufs2 lc uc HYPq fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia)) (sokF 32%Z ltac:(lia))
                  (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) H2 H10 ltac:(rewrite H11; f_equal; lia) H12 H13 H14 H15 H16)
        as (r1 & m1 & RUN1 & FR1 & E2 & E11 & E17 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & AG1).
      exists r1, m1, m1. split; [exact RUN1|]. split; [exact (rinv_cells R4 _ M0 M0 m1 (rinv_refl _ _) FR1 FCI)|]. split; [apply rinv_refl|].
      repeat split; try assumption; try dl_get; try (rewrite E11; f_equal; lia); try (apply AG1; notin_list).
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply AG1; notin_list |]). destruct Hr.
    - assert (HYPp : vp_hyps s lined bufs1 bufs2 w1 lc uc) by (unfold vp_hyps; repeat split; first [assumption | lia]).
      destruct (vp_1ba84_f0 rom s lined bufs1 bufs2 w1 lc uc HYPp fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia)) (sokF 32%Z ltac:(lia))
                  (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) H2 H10 H11 H12 H13 H14 H15 H16)
        as (r1 & m1 & RUN1 & FR1 & E2 & E5 & E6 & E7 & E11 & E17 & E28 & E29 & E30 & E31 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & AG1).
      pose proof (regions_ok_grows SEGS M0 m1 R3 RO (proj1 FR1)) as RO1.
      destruct (v0_loop m1 RO1 (Z.to_nat w1) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r3 & m3 & RUN3 & RI3 & AG3).
      { unfold f0regs. repeat split; dl_get. }
      exists r3, m1, m3. split; [exact (msteps_trans _ _ _ _ RUN1 RUN3)|]. split; [exact (rinv_cells R4 _ M0 M0 m1 (rinv_refl _ _) FR1 FCI)|]. split; [exact RI3|].
      repeat split; try assumption; try dl_get; try (rewrite (AG3 1%bv) by notin_list; apply AG1; notin_list).
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [rewrite (AG3 _) by notin_list; apply AG1; notin_list |]). destruct Hr. }
  destruct PRE as (r3 & m1 & m3 & RUN3 & RI1 & RI3 & Y2 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & KP3).
  (* [comment removed for export] *)
  pose proof (regions_ok_grows SEGS M0 m1 R3 RO (proj1 RI1)) as RO1.
  pose proof (cells_ok_of SEGS m1 m3 R3 _ RO1 (proj1 RI3) vt0_cells_in) as CK3.
  destruct (vt0_1be64_path rom lined bufs1 bufs2 w1 lc uc wpl vt0h fx r3 m3 CK3 Y10 Y11 Y12 Y13 Y14 Y15) as (r4 & m4 & RUN4 & FR4 & AG4).
  pose proof (rinv_cells R3 _ m1 m3 m4 RI3 FR4 vt0_cells_in) as RI4.
  destruct (ll_tail R3 (fun r H => H) regs ret m1 r4 m4 Hret H1 SV8 SV9 SV18 SV19 SV20 SV21 RI4
              ltac:(rewrite (AG4 2%bv) by notin_list; exact Y2) ltac:(rewrite (AG4 1%bv) by notin_list; exact Y1))
    as (r6 & m6 & RUN6 & RI6 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & AG6).
  exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN6))|].
  split; [apply (rinv_trans R4 M0 m1 m6 RI1); apply (rinv_incl R3 R4 m1 m6 RI6 R3_R4)|].
  repeat split; try assumption.
  intros r Hr. rewrite <- (KP3 r Hr). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [rewrite (AG6 _) by notin_list; apply AG4; notin_list |]). destruct Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v1h : forall j, (0 <= j < w1)%Z -> v1_hyps lined bufs1 j w1 lc uc wpl.
Proof. intros j Hj. geom. unfold v1_hyps. repeat split; first [assumption | lia]. Qed.
Lemma vt1h : vt1_hyps lined bufs1 w1 wpl.
Proof. geom. unfold vt1_hyps. repeat split; first [assumption | lia]. Qed.
Lemma R2_R3 : forall r, In r R2 -> In r R3.
Proof. intros r Hr. unfold R2, R3 in *. cbn [In] in *. tauto. Qed.

Lemma v1_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R2 (v1_1bb20_cells_def lined bufs1 j w1 lc uc wpl).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold v1_1bb20_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R2 |]). destruct Hc.
Qed.
Lemma vt1_cells_in : cells_in R2 (vt1_1bbe4_cells_def lined bufs1 w1 wpl).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 32 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold vt1_1bbe4_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R2 |]). destruct Hc.
Qed.

Definition f1regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 5 = Z_to_bv 64 3 /\ getr regs 6 = Z_to_bv 64 2 /\ getr regs 7 = Z_to_bv 64 1 /\ getr regs 10 = Z_to_bv 64 lined /\
  getr regs 11 = Z_to_bv 64 w1 /\ getr regs 12 = Z_to_bv 64 bufs1 /\ getr regs 13 = Z_to_bv 64 j /\ getr regs 14 = Z_to_bv 64 lc /\
  getr regs 15 = Z_to_bv 64 uc /\ getr regs 16 = Z_to_bv 64 j /\ getr regs 17 = Z_to_bv 64 1 /\ getr regs 28 = Z_to_bv 64 134217727 /\
  getr regs 29 = Z_to_bv 64 18446744071562067968.

Lemma v1_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R2 ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R2 Mr Mi -> f1regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1bc24) Mi rom) (mkst regs' (Z_to_bv 64 0x1bce8) Mi' rom)
    /\ rinv R2 Mr Mi' /\ regs_agree (fun r => In r [8; 9; 13; 16; 18; 30; 31]%list) regs regs'.
Proof.
  intros Mr ROr. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H5 & H6 & H7 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29).
  pose proof (cells_ok_of SEGS Mr Mi R2 _ ROr (proj1 RI) (v1_cells_in j Hj)) as CK.
  destruct (v1_1bb20_path rom lined bufs1 j w1 lc uc wpl (v1h j Hj) fx regs Mi CK H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29)
    as (r1 & m1 & RUN1 & FR1 & E13 & E16 & AG1).
  pose proof (rinv_cells R2 _ Mr Mi m1 RI FR1 (v1_cells_in j Hj)) as RI1.
  assert (CI0 : cells_in R2 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - destruct (v1_1bb1cf rom lined bufs1 j w1 lc uc wpl (v1h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R2 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f1regs. repeat split; dl_get. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (v1_1bb1ct rom lined bufs1 j w1 lc uc wpl (v1h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R2 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

Definition R4' : list (Z * Z) := ((s - 48)%Z, 48%Z) :: R2.

Lemma dbll1_run : forall (M0 : word -> option byte), regions_ok SEGS M0 R2 -> forall regs (ret : word), ret_ok ret ->
  store_ok SEGS M0 (Z_to_bv 64 (s - 48)) 48 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 -> getr regs 13 = Z_to_bv 64 bufs2 -> getr regs 14 = Z_to_bv 64 lc -> getr regs 15 = Z_to_bv 64 uc ->
  getr regs 16 = Z_to_bv 64 1 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1bb88) M0 rom) (mkst regs' ret M' rom)
    /\ rinv R4' M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
    /\ (forall r, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 RO regs ret Hret SOKF H2 H1 H10 H11 H12 H13 H14 H15 H16. geom.
  assert (sokF : forall k, (8 <= k <= 48)%Z -> store_ok SEGS M0 (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 M0 (s - 48) 48 (s - k) 8 (mem_grows_refl _) SOKF); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (PRE : exists r3 m1 m3, msteps SEGS (mkst regs (Z_to_bv 64 0x1bb88) M0 rom) (mkst r3 (Z_to_bv 64 0x1bce8) m3 rom)
                  /\ rinv R4' M0 m1 /\ rinv R2 m1 m3 /\ getr r3 2 = Z_to_bv 64 (s - 48) /\ getr r3 1 = getr regs 1
                  /\ getr r3 10 = Z_to_bv 64 lined /\ getr r3 11 = Z_to_bv 64 w1 /\ getr r3 12 = Z_to_bv 64 bufs1
                  /\ rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9))
                  /\ rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19))
                  /\ rdn SEGS m1 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21))
                  /\ (forall r, In r [3; 4; 22; 23; 24; 25; 26; 27]%bv -> getr r3 r = getr regs r)).
  { assert (FCI : forall c, In c [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z)] ->
                             (0 <= snd c)%Z /\ exists r, In r R4' /\ (fst r <= fst c)%Z /\ (fst c + snd c <= fst r + snd r)%Z).
    { intros c Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 48)%Z, 48%Z); split; [left; reflexivity | cbn [fst snd]; lia] |]). destruct Hc. }
    destruct (Z.eq_dec w1 0) as [W0|W1].
    - assert (HYPq : vq_hyps s lined bufs1 bufs2 lc uc) by (unfold vq_hyps; repeat split; first [assumption | lia]).
      destruct (vq_1ba84_f1 rom s lined bufs1 bufs2 lc uc HYPq fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia)) (sokF 32%Z ltac:(lia))
                  (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) H2 H10 ltac:(rewrite H11; f_equal; lia) H12 H13 H14 H15 H16)
        as (r1 & m1 & RUN1 & FR1 & E2 & E11 & E17 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & AG1).
      exists r1, m1, m1. split; [exact RUN1|]. split; [exact (rinv_cells R4' _ M0 M0 m1 (rinv_refl _ _) FR1 FCI)|]. split; [apply rinv_refl|].
      repeat split; try assumption; try dl_get; try (rewrite E11; f_equal; lia); try (apply AG1; notin_list).
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply AG1; notin_list |]). destruct Hr.
    - assert (HYPp : vp_hyps s lined bufs1 bufs2 w1 lc uc) by (unfold vp_hyps; repeat split; first [assumption | lia]).
      destruct (vp_1ba84_f1 rom s lined bufs1 bufs2 w1 lc uc HYPp fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia)) (sokF 32%Z ltac:(lia))
                  (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) H2 H10 H11 H12 H13 H14 H15 H16)
        as (r1 & m1 & RUN1 & FR1 & E2 & E5 & E6 & E7 & E11 & E13 & E16 & E17 & E28 & E29 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & AG1).
      pose proof (regions_ok_grows SEGS M0 m1 R2 RO (proj1 FR1)) as RO1.
      destruct (v1_loop m1 RO1 (Z.to_nat w1) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r3 & m3 & RUN3 & RI3 & AG3).
      { unfold f1regs. repeat split; dl_get. }
      exists r3, m1, m3. split; [exact (msteps_trans _ _ _ _ RUN1 RUN3)|]. split; [exact (rinv_cells R4' _ M0 M0 m1 (rinv_refl _ _) FR1 FCI)|]. split; [exact RI3|].
      repeat split; try assumption; try dl_get; try (rewrite (AG3 1%bv) by notin_list; apply AG1; notin_list).
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [rewrite (AG3 _) by notin_list; apply AG1; notin_list |]). destruct Hr. }
  destruct PRE as (r3 & m1 & m3 & RUN3 & RI1 & RI3 & Y2 & Y1 & Y10 & Y11 & Y12 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & KP3).
  pose proof (regions_ok_grows SEGS M0 m1 R2 RO (proj1 RI1)) as RO1.
  pose proof (cells_ok_of SEGS m1 m3 R2 _ RO1 (proj1 RI3) vt1_cells_in) as CK3.
  destruct (vt1_1bbe4_path rom lined bufs1 w1 wpl vt1h fx r3 m3 CK3 Y10 Y11 Y12) as (r4 & m4 & RUN4 & FR4 & AG4).
  pose proof (rinv_cells R2 _ m1 m3 m4 RI3 FR4 vt1_cells_in) as RI4.
  destruct (ll_tail R2 R2_R3 regs ret m1 r4 m4 Hret H1 SV8 SV9 SV18 SV19 SV20 SV21 RI4
              ltac:(rewrite (AG4 2%bv) by notin_list; exact Y2) ltac:(rewrite (AG4 1%bv) by notin_list; exact Y1))
    as (r6 & m6 & RUN6 & RI6 & Z2 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & AG6).
  exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN6))|].
  split; [apply (rinv_trans R4' M0 m1 m6 RI1); apply (rinv_incl R2 R4' m1 m6 RI6); intros r Hr; right; exact Hr|].
  repeat split; try assumption.
  intros r Hr. rewrite <- (KP3 r Hr). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [rewrite (AG6 _) by notin_list; apply AG4; notin_list |]). destruct Hr.
Qed.

End LineLow.
End V15LeptDithBin.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FpBound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptGrayFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15_code_gqR_rmc.
Module V15LeptRmcFP.
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
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FpBound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LibAtomic.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptGrayFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15_code_gqR_rmc.
(* [comment removed for export] *)







Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Ltac fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].
Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.

(* [comment removed for export] *)
Definition gconsts (fr : bvmap 5 word) : Prop :=
  fpv_read fr FMT_S 15 = GC_05f /\ fpv_read fr FMT_S 14 = GC_03f /\ fpv_read fr FMT_S 13 = GC_02f /\
  fpv_read fr FMT_D 12 = GC_05d /\ fpv_read fr FMT_D 11 = GC_m1d /\ fpv_read fr FMT_D 10 = GC_2p32d.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma rmc_L1f : forall (fx : FPState) regs m (r g b : Z),
  frm_zero (@fp_csr fx) -> gconsts (@fp_regs fx) -> (0 <= r < 256)%Z -> (0 <= g < 256)%Z -> (0 <= b < 256)%Z ->
  getr regs 31 = Z_to_bv 64 r -> getr regs 8 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 b ->
  exists fr' cs' regs',
    msteps SEGS (@mkst fx regs (0x1a974 : word) m rom) (@mkst (mkFP fr' cs') regs' (0x1a9a4 : word) m rom)
    /\ frm_zero cs' /\ gconsts fr'
    /\ regs_agree (fun x => In x [31]%list) regs regs'.
Proof.
  intros fx regs m r g b Hz (K15 & K14 & K13 & K12 & K11 & K10) Hr Hg Hb H31 H8 H9.
  eexists _, _, _. split.
  - chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_1a870 | reflexivity | exact D_1a870 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_1a874 | reflexivity | exact D_1a874 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_1a878 | reflexivity | exact D_1a878 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fma; [exact F_1a87c | reflexivity | exact D_1a87c | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_x; [exact F_1a880 | reflexivity | exact D_1a880 | left; split; reflexivity | left; repeat split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fma; [exact F_1a884 | reflexivity | exact D_1a884 | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f; [exact F_1a888 | reflexivity | exact D_1a888 | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fari; [exact F_1a88c | reflexivity | exact D_1a88c | fz Hz | reflexivity] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_1a890 | reflexivity | exact D_1a890] | step_simpl ]; fpn.   (* [comment removed for export] *)
    rewrite K15, K14, K13, K12, K11, H31, H8, H9. rewrite (u_Z2bv r), (u_Z2bv g), (u_Z2bv b) by lia.
    match goal with |- context [fst (fpv_cmp F_LT FMT_D GC_m1d ?X)] =>
      replace (fst (fpv_cmp F_LT FMT_D GC_m1d X)) with true by (symmetry; exact (gray_m_guard_lo r g b Hr Hg Hb)) end.
    stepb_ft F_1a894 D_1a894 ltac:(condZ).   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F_1a898 | reflexivity | exact D_1a898] | step_simpl ]; fpn.   (* [comment removed for export] *)
    rewrite ?K15, ?K14, ?K13, ?K12, ?K10, ?H31, ?H8, ?H9. rewrite ?(u_Z2bv r), ?(u_Z2bv g), ?(u_Z2bv b) by lia.
    match goal with |- context [fst (fpv_cmp F_LT FMT_D ?X GC_2p32d)] =>
      replace (fst (fpv_cmp F_LT FMT_D X GC_2p32d)) with true by (symmetry; exact (gray_m_guard_hi r g b Hr Hg Hb)) end.
    stepb_ft F_1a89c D_1a89c ltac:(condZ).   (* [comment removed for export] *)
    apply mst_refl.
  - split; [fz Hz|]. split.
    + unfold gconsts. cbn [fp_regs]. repeat split; (rewrite !fpv_read_other by reg_neq_tac; assumption).
    + gres; pin; try reflexivity; try solve_regs_agree.
Qed.
(* [comment removed for export] *)
Lemma rmc_S3f : forall (fx : FPState) regs m,
  rdn SEGS m (Z_to_bv 64 0x11720) 4 = Some (Z_to_le_bytes 4 GC_03f) -> rdn SEGS m (Z_to_bv 64 0x11714) 4 = Some (Z_to_le_bytes 4 GC_02f) ->
  rdn SEGS m (Z_to_bv 64 0x11638) 8 = Some (Z_to_le_bytes 8 GC_05d) -> rdn SEGS m (Z_to_bv 64 0x11608) 8 = Some (Z_to_le_bytes 8 GC_m1d) ->
  rdn SEGS m (Z_to_bv 64 0x11618) 8 = Some (Z_to_le_bytes 8 GC_2p32d) ->
  getr regs 17 = Z_to_bv 64 0x3f000000 -> getr regs 5 = Z_to_bv 64 0x118b8 -> getr regs 6 = Z_to_bv 64 0x118bc -> getr regs 7 = Z_to_bv 64 0x118c0 ->
  getr regs 28 = Z_to_bv 64 0x118c4 -> getr regs 29 = Z_to_bv 64 0x118c8 ->
  exists fr',
    msteps SEGS (@mkst fx regs (0x1a8d0 : word) m rom) (@mkst (mkFP fr' (@fp_csr fx)) regs (0x1a8e8 : word) m rom) /\ gconsts fr'.
Proof.
  intros fx regs m K03 K02 K05 Km1 K2p H17 H5 H6 H7 H28 H29.
  eexists. split.
  - chain_step; [ reflexivity | eapply fp_step_fmv_w_x; [exact F_1a7cc | reflexivity | exact D_1a7cc] | step_simpl ]; fpn.   (* [comment removed for export] *)
    chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 0x11720) (bs := Z_to_le_bytes 4 GC_03f); [exact F_1a7d0 | reflexivity | exact D_1a7d0 | gres; imm_norm; addr_tac | exact K03] | step_simpl ]; fpn.
    chain_step; [ reflexivity | eapply fp_step_flw with (a := Z_to_bv 64 0x11714) (bs := Z_to_le_bytes 4 GC_02f); [exact F_1a7d4 | reflexivity | exact D_1a7d4 | gres; imm_norm; addr_tac | exact K02] | step_simpl ]; fpn.
    chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 0x11638) (bs := Z_to_le_bytes 8 GC_05d); [exact F_1a7d8 | reflexivity | exact D_1a7d8 | gres; imm_norm; addr_tac | exact K05] | step_simpl ]; fpn.
    chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 0x11608) (bs := Z_to_le_bytes 8 GC_m1d); [exact F_1a7dc | reflexivity | exact D_1a7dc | gres; imm_norm; addr_tac | exact Km1] | step_simpl ]; fpn.
    chain_step; [ reflexivity | eapply fp_step_fld with (a := Z_to_bv 64 0x11618) (bs := Z_to_le_bytes 8 GC_2p32d); [exact F_1a7e0 | reflexivity | exact D_1a7e0 | gres; imm_norm; addr_tac | exact K2p] | step_simpl ]; fpn.
    apply mst_refl.
  - unfold gconsts. rewrite H17. repeat split; rewrite ?fpv_read_other by reg_neq_tac; rewrite ?fpv_read_S_box, ?fpv_read_D_same; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rmc_L1d : forall (last : bool) (fx : FPState) regs m (dp off n4 : Z),
  frm_zero (@fp_csr fx) -> (0 <= dp)%Z -> (dp + 4 < 2 ^ 63)%Z -> (0 <= off)%Z -> (off + 4 <= n4 <= 1024)%Z ->
  store_ok SEGS m (Z_to_bv 64 dp) 4 = true ->
  (if last then off + 4 = n4 else off + 4 <> n4)%Z ->
  getr regs 31 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 off -> getr regs 30 = Z_to_bv 64 n4 ->
  exists cs' regs' (bs : list byte),
    msteps SEGS (@mkst fx regs (0x1a9bc : word) m rom)
                (@mkst (mkFP (@fp_regs fx) cs') regs' (if last then (0x1a9cc : word) else (0x1a920 : word)) (wbytes m (Z_to_bv 64 dp) bs) rom)
    /\ frm_zero cs' /\ length bs = 4%nat /\ getr regs' 11 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun x => In x [8; 11]%list) regs regs'.
Proof.
  intros last fx regs m dp off n4 Hz Hdp Hdp63 Hoff Hn4 SOK Hlast H31 H11 H30.
  destruct last.
  - eexists _, _, _. split.
    + chain_step; [ reflexivity | eapply fpv_step_fcvt_x_of_f; [exact F_1a8b8 | reflexivity | exact D_1a8b8 | right; left; repeat split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      zv F_1a8bc D_1a8bc (Z_to_bv 64 (off + 4)).   (* [comment removed for export] *)
      match goal with |- context [regupd _ 8 ?v] => stepST F_1a8c0 D_1a8c0 (Z_to_bv 64 dp) v ltac:(store_ok_peel; exact SOK) end.   (* [comment removed for export] *)
      stepb_ft F_1a8c4 D_1a8c4 ltac:(condZ).   (* [comment removed for export] *)
      apply mst_refl.
    + split; [fz Hz|]. split; [apply length_N_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
  - eexists _, _, _. split.
    + chain_step; [ reflexivity | eapply fpv_step_fcvt_x_of_f; [exact F_1a8b8 | reflexivity | exact D_1a8b8 | right; left; repeat split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
      zv F_1a8bc D_1a8bc (Z_to_bv 64 (off + 4)).
      match goal with |- context [regupd _ 8 ?v] => stepST F_1a8c0 D_1a8c0 (Z_to_bv 64 dp) v ltac:(store_ok_peel; exact SOK) end.
      stepb_tk F_1a8c4 D_1a8c4 ltac:(condZ).
      apply mst_refl.
    + split; [fz Hz|]. split; [apply length_N_to_le_bytes|]. repeat split; gres; pin; try reflexivity; try solve_regs_agree.
Qed.

(* [comment removed for export] *)
Lemma rmc_clone_tail : forall (fx : FPState) regs m (pixs : Z) (ret : word),
  (0 <= pixs)%Z -> (pixs + 64 < 2 ^ 63)%Z -> (pixs mod 4 = 0)%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 20)) 4 = Some (Z_to_le_bytes 4 1) -> store_ok SEGS m (Z_to_bv 64 (pixs + 20)) 4 = true ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 11 = Z_to_bv 64 (pixs + 20) -> getr regs 12 = Z_to_bv 64 1 ->
  msteps SEGS (@mkst fx regs (0x179d0 : word) m rom) (@mkst fx regs ret (wbytes m (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) rom).
Proof.
  intros fx regs m pixs ret Hp Hp63 Hal Crc SOK Hret H1 H11 H12.
  chain_step; [ reflexivity
              | eapply step_amoadd_w with (bs := Z_to_le_bytes 4 1) (v := Z_to_bv 64 1);
                [ exact F_178cc | reflexivity | exact D_178cc
                | rewrite H11, u_Z2bv by lia; rewrite <- Z.add_mod_idemp_l, Hal by lia; reflexivity
                | rewrite H11; exact Crc | reflexivity | rewrite H11; exact SOK ]
              | step_simpl ].
  rewrite H11, H12. replace (word_to_le_bytes 4 (v_add (Z_to_bv 64 1) (Z_to_bv 64 1))) with (Z_to_le_bytes 4 2) by reflexivity.
  stepret F_178d0 D_178d0 ret ltac:(exact H1). apply mst_refl.
Qed.

(* [comment removed for export] *)
Lemma rmc_ret : forall (fx : FPState) regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1b53c) m rom) (@mkst fx regs ret m rom).
Proof.
  intros fx regs m ret Hret H1. replace (Z_to_bv 64 0x1b53c) with (0x1b53c : word) by (apply bv_eq; reflexivity).
  stepret F_1b438 D_1b438 ret ltac:(exact H1). apply mst_refl.
Qed.

End Segs.
End V15LeptRmcFP.
