(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherLoop DitherTab DitherTab1 BandLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL1a.
Import V15CL1a.V15BandLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15BandPix8 V15BandPix4 V15BandPix2.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac dl_get2 :=
  first [ eassumption
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get2 end ].

(* [comment removed for export] *)
Definition bp_hyps (D sp datag datad lineg lined w j wplg wpld : Z) : Prop :=
  (4096 <= sp <= 140737488355328)%Z /\ (4096 <= datag <= 140737488355328)%Z /\ (datag mod 4 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= lineg <= 140737488355328)%Z /\ (lineg mod 4 = 0)%Z /\ (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (0 <= j <= 19999)%Z /\ (0 <= j < w)%Z /\ (w * D <= 32 * wplg)%Z /\ (w <= 32 * wpld)%Z /\ dapart lined (4 * wpld) sp 128.

Section Band.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Variable D : Z.
Variables (cells cells_w : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> list (Z * Z)).
Hypothesis PATH : forall sp datag datad lineg lined w j wplg wpld, bp_hyps D sp datag datad lineg lined w j wplg wpld -> forall (fx : FPState) regs m,
  cells_ok SEGS m (cells sp datag datad lineg lined w j wplg wpld) ->
  (forall m', mframe (cells_w sp datag datad lineg lined w j wplg wpld) m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 D)) ->
  (forall m', mframe (cells_w sp datag datad lineg lined w j wplg wpld) m m' -> rdn SEGS m' (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w)) ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 5 = Z_to_bv 64 8 -> getr regs 6 = Z_to_bv 64 134217727 -> getr regs 7 = Z_to_bv 64 3 ->
  getr regs 8 = Z_to_bv 64 2 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 11 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  getr regs 15 = Z_to_bv 64 1 -> getr regs 16 = Z_to_bv 64 4 -> getr regs 18 = Z_to_bv 64 datag -> getr regs 20 = Z_to_bv 64 datad ->
  getr regs 23 = Z_to_bv 64 j -> getr regs 24 = Z_to_bv 64 lineg -> getr regs 28 = Z_to_bv 64 lineg -> getr regs 29 = Z_to_bv 64 lined ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c468) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c450) m' rom)
    /\ mframe (cells sp datag datad lineg lined w j wplg wpld) m m'
    /\ mframe (cells_w sp datag datad lineg lined w j wplg wpld) m m'
    /\ regs_agree (fun r => In r [25; 26; 27]%list) regs regs'.
Hypothesis LATCH : forall sp datag datad lineg lined w j wplg wpld, bp_hyps D sp datag datad lineg lined w j wplg wpld -> forall (fx : FPState) regs m,
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 D) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 23 = Z_to_bv 64 j ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c450) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c464) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 23 = Z_to_bv 64 (j + 1)
    /\ getr regs' 25 = Z_to_bv 64 w
    /\ regs_agree (fun r => In r [21; 23; 25; 30; 31]%list) regs regs'.
Hypothesis LATCHF : forall sp datag datad lineg lined w j wplg wpld, bp_hyps D sp datag datad lineg lined w j wplg wpld -> forall (fx : FPState) regs m,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = false ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 D) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 23 = Z_to_bv 64 (j + 1) -> getr regs 25 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c464) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c468) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Hypothesis LATCHT : forall sp datag datad lineg lined w j wplg wpld, bp_hyps D sp datag datad lineg lined w j wplg wpld -> forall (fx : FPState) regs m,
  branch_taken BC_GE (Z_to_bv 64 (j + 1)) (Z_to_bv 64 w) = true ->
  rdn SEGS m (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 D) ->
  rdn SEGS m (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w) ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 23 = Z_to_bv 64 (j + 1) -> getr regs 25 = Z_to_bv 64 w ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1c464) m rom) (@mkst fx regs' (Z_to_bv 64 0x1c3a4) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.

Variables (sp datad datag w h wpld wplg : Z).
Definition band_geom : Prop :=
  (4096 <= sp /\ sp + 128 <= 2 ^ 47 /\ 4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\
   4096 <= datag /\ datag + 4 * (wplg * h) < 2 ^ 47 /\ datag mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wpld <= 5000 /\ 1 <= wplg <= 5000 /\ w <= 32 * wpld /\ w * D <= 32 * wplg /\
   wpld * h <= 2 ^ 24 /\ wplg * h <= 2 ^ 24)%Z.
(* [comment removed for export] *)
Definition band_disj : Prop := (datad + 4 * (wpld * h) <= sp \/ sp + 128 <= datad)%Z.
Hypothesis G : band_geom.
Hypothesis GD : band_disj.
(* [comment removed for export] *)
Hypothesis CIN : forall lineg lined j, (lineg mod 4 = 0)%Z -> (lined mod 4 = 0)%Z -> (0 <= j < w)%Z ->
  cells_in [(lined, 4 * wpld); (lineg, 4 * wplg)]%Z (cells sp datag datad lineg lined w j wplg wpld).
Hypothesis CWIN : forall lineg lined j, (lineg mod 4 = 0)%Z -> (lined mod 4 = 0)%Z -> (0 <= j < w)%Z ->
  cells_in [(lined, 4 * wpld)]%Z (cells_w sp datag datad lineg lined w j wplg wpld).
Ltac geom := pose proof G as (Gs0 & Gs1 & Gd0 & Gd1 & ALd & Gg0 & Gg1 & ALg & Gw & Gh & Gwd & Gwg & Gw32 & GwD & Gpd & Gpg).

Definition RD : Z * Z := (datad, 4 * (wpld * h))%Z.
Definition RS : Z * Z := (datag, 4 * (wplg * h))%Z.
Definition kcs (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (sp + 12)) 4 = Some (Z_to_le_bytes 4 D) /\ rdn SEGS M (Z_to_bv 64 (sp + 16)) 4 = Some (Z_to_le_bytes 4 h) /\
  rdn SEGS M (Z_to_bv 64 (sp + 20)) 4 = Some (Z_to_le_bytes 4 w).

Lemma kcs_keep : forall (M1 Mi : word -> option byte), rinv [RD] M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3). geom. pose proof GD as DF. unfold band_disj in DF. unfold kcs.
  repeat split; [rewrite <- K1 | rewrite <- K2 | rewrite <- K3];
    (apply (rinv_rdn SEGS [RD] M1 Mi _ _ RI); [lia | cbn; lia | intros r [<- | []]; unfold RD; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Row.
Variables (lined lineg : Z).
Hypothesis Hdr : (datad <= lined /\ lined + 4 * wpld <= datad + 4 * (wpld * h) /\ lined mod 4 = 0)%Z.
Hypothesis Hsr : (datag <= lineg /\ lineg + 4 * wplg <= datag + 4 * (wplg * h) /\ lineg mod 4 = 0)%Z.
Definition RL : list (Z * Z) := [(lined, 4 * wpld)%Z].
Definition RLS : list (Z * Z) := [(lined, 4 * wpld); (lineg, 4 * wplg)]%Z.

Lemma bph : forall j, (0 <= j < w)%Z -> bp_hyps D sp datag datad lineg lined w j wplg wpld.
Proof.
  intros j Hj. geom. pose proof GD as DF. unfold band_disj in DF. destruct Hdr as (D1 & D2 & D3). destruct Hsr as (S1 & S2 & S3).
  unfold bp_hyps. repeat split; try assumption; try lia. unfold dapart. lia.
Qed.

Definition pregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 sp /\ getr regs 5 = Z_to_bv 64 8 /\ getr regs 6 = Z_to_bv 64 134217727 /\ getr regs 7 = Z_to_bv 64 3 /\
  getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 1 /\ getr regs 11 = Z_to_bv 64 1 /\ getr regs 14 = Z_to_bv 64 1 /\
  getr regs 15 = Z_to_bv 64 1 /\ getr regs 16 = Z_to_bv 64 4 /\ getr regs 18 = Z_to_bv 64 datag /\ getr regs 20 = Z_to_bv 64 datad /\
  getr regs 23 = Z_to_bv 64 j /\ getr regs 24 = Z_to_bv 64 lineg /\ getr regs 28 = Z_to_bv 64 lineg /\ getr regs 29 = Z_to_bv 64 lined.

Lemma kcs_row : forall (M1 Mi : word -> option byte), rinv RL M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3). geom. pose proof GD as DF. unfold band_disj in DF. destruct Hdr as (D1 & D2 & D3). unfold kcs.
  repeat split; [rewrite <- K1 | rewrite <- K2 | rewrite <- K3];
    (apply (rinv_rdn SEGS RL M1 Mi _ _ RI); [lia | cbn; lia | intros r [<- | []]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

(* [comment removed for export] *)
Lemma px_kcs : forall (Mr Mi : word -> option byte) j, (0 <= j < w)%Z -> rinv RL Mr Mi -> kcs Mr ->
  forall m', mframe (cells_w sp datag datad lineg lined w j wplg wpld) Mi m' -> kcs m'.
Proof.
  intros Mr Mi j Hj RI KC m' FR. destruct Hdr as (D1 & D2 & D3). destruct Hsr as (S1 & S2 & S3).
  pose proof (rinv_cells RL _ Mr Mi m' RI FR (CWIN lineg lined j S3 D3 Hj)) as RI'. exact (kcs_row Mr m' RI' KC).
Qed.

Lemma px_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr RLS -> kcs Mr ->
  forall (n : nat) j regs Mi, (w - j <= Z.of_nat n)%Z -> (0 <= j < w)%Z -> rinv RL Mr Mi -> pregs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1c468) Mi rom) (mkst regs' (Z_to_bv 64 0x1c3a4) Mi' rom)
    /\ rinv RL Mr Mi' /\ regs_agree (fun r => In r [21; 23; 25; 26; 27; 30; 31]%list) regs regs'.
Proof.
  intros Mr ROr KC. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H2 & H5 & H6 & H7 & H8 & H9 & H11 & H14 & H15 & H16 & H18 & H20 & H23 & H24 & H28 & H29).
  pose proof Hdr as (D1 & D2 & D3). pose proof Hsr as (S1 & S2 & S3).
  pose proof (cells_ok_of SEGS Mr Mi RLS _ ROr (proj1 RI) (CIN lineg lined j S3 D3 Hj)) as CK.
  pose proof (px_kcs Mr Mi j Hj RI KC) as KM.
  destruct (PATH sp datag datad lineg lined w j wplg wpld (bph j Hj) fx regs Mi CK
              (fun m' F => proj1 (KM m' F)) (fun m' F => proj2 (proj2 (KM m' F))) H2 H5 H6 H7 H8 H9 H11 H14 H15 H16 H18 H20 H23 H24 H28 H29)
    as (r1 & m1 & RUN1 & FR1 & FW1 & AG1).
  pose proof (rinv_cells RL _ Mr Mi m1 RI FW1 (CWIN lineg lined j S3 D3 Hj)) as RI1.
  destruct (kcs_row Mr m1 RI1 KC) as (K1 & K2 & K3).
  assert (CI0 : cells_in RL []) by (intros c []).
  destruct (LATCH sp datag datad lineg lined w j wplg wpld (bph j Hj) fx r1 m1 K1 K3 ltac:(dl_get2) ltac:(dl_get2)) as (r2 & m2 & RUN2 & FR2 & E23 & E25 & AG2).
  pose proof (rinv_cells RL _ Mr m1 m2 RI1 FR2 CI0) as RI2.
  destruct (kcs_row Mr m2 RI2 KC) as (K1' & K2' & K3').
  destruct (Z_lt_ge_dec (j + 1) w) as [LT|GE].
  - destruct (LATCHF sp datag datad lineg lined w j wplg wpld (bph j Hj) fx r2 m2 ltac:(ex_br) K1' K3' ltac:(dl_get2) E23 E25) as (r3 & m3 & RUN3 & FR3 & AG3).
    pose proof (rinv_cells RL _ Mr m2 m3 RI2 FR3 CI0) as RI3.
    destruct (IH (j + 1)%Z r3 m3 ltac:(lia) ltac:(lia) RI3) as (r4 & m4 & RUN4 & RI4 & AG4).
    { unfold pregs. repeat split; dl_get2. }
    exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
    split; [exact RI4 | ra_chain].
  - destruct (LATCHT sp datag datad lineg lined w j wplg wpld (bph j Hj) fx r2 m2 ltac:(ex_br) K1' K3' ltac:(dl_get2) E23 E25) as (r3 & m3 & RUN3 & FR3 & AG3).
    pose proof (rinv_cells RL _ Mr m2 m3 RI2 FR3 CI0) as RI3.
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
Qed.

End Row.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rregs (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 sp /\ getr regs 5 = Z_to_bv 64 8 /\ getr regs 6 = Z_to_bv 64 134217727 /\ getr regs 7 = Z_to_bv 64 3 /\
  getr regs 8 = Z_to_bv 64 2 /\ getr regs 9 = Z_to_bv 64 1 /\ getr regs 10 = Z_to_bv 64 wpld /\ getr regs 11 = Z_to_bv 64 1 /\
  getr regs 12 = Z_to_bv 64 (i * wplg) /\ getr regs 13 = Z_to_bv 64 i /\ getr regs 14 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\
  getr regs 16 = Z_to_bv 64 4 /\ getr regs 18 = Z_to_bv 64 datag /\ getr regs 19 = Z_to_bv 64 wplg /\ getr regs 20 = Z_to_bv 64 datad.

Lemma row_loop : forall (M0 : word -> option byte), regions_ok SEGS M0 [RD; RS] -> kcs M0 ->
  forall (n : nat) i regs Mi, (h - i <= Z.of_nat n)%Z -> (0 <= i < h)%Z -> rinv [RD] M0 Mi -> rregs regs i ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1c3b4) Mi rom) (mkst regs' (Z_to_bv 64 0x1c560) Mi' rom)
    /\ rinv [RD] M0 Mi' /\ regs_agree (fun r => In r [12; 13; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros M0 RO0 KC0. geom. induction n as [|n IH]; intros i regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H18 & H19 & H20).
  pose proof (row_bounds wpld i h ltac:(lia) ltac:(lia) ltac:(lia)) as P1. pose proof (row_bounds wplg i h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  assert (Pd24 : (0 <= i * wpld < 2 ^ 24)%Z) by (rewrite (Z.mul_comm i wpld); lia).
  assert (Pg24 : (0 <= i * wplg < 2 ^ 24)%Z) by (rewrite (Z.mul_comm i wplg); lia).
  remember (datad + 4 * (wpld * i))%Z as lined eqn:Edr. remember (datag + 4 * (wplg * i))%Z as lineg eqn:Esr.
  assert (Hdr : (datad <= lined /\ lined + 4 * wpld <= datad + 4 * (wpld * h) /\ lined mod 4 = 0)%Z).
  { split; [lia|]. split; [lia|]. subst lined. apply al4_add. exact ALd. }
  assert (Hsr : (datag <= lineg /\ lineg + 4 * wplg <= datag + 4 * (wplg * h) /\ lineg mod 4 = 0)%Z).
  { split; [lia|]. split; [lia|]. subst lineg. apply al4_add. exact ALg. }
  assert (Edr' : (datad + 4 * (i * wpld))%Z = lined) by (subst lined; ring).
  assert (Esr' : (datag + 4 * (i * wplg))%Z = lineg) by (subst lineg; ring).
  assert (Eacc : (i * wplg + wplg)%Z = ((i + 1) * wplg)%Z) by ring.
  clear P1 P2 Edr Esr.
  destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD). destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS).
  unfold RD, RS in *. cbn [fst snd] in *.
  pose proof KC0 as (K01 & K02 & K03).
  assert (HYPr : br_hyps sp datag datad w h wplg wpld i (i * wplg)) by (unfold br_hyps; repeat split; first [assumption | lia]).
  destruct (kcs_keep M0 Mi RI KC0) as (Ki1 & Ki2 & Ki3).
  destruct (br_1c2b0 rom sp datag datad w h wplg wpld i (i * wplg)%Z HYPr fx regs Mi Ki3 H2 H10 H12 H13 H14 H15 H18 H19 H20)
    as (r1 & m1 & RUN1 & FR1 & E21 & E23 & E24 & E28 & E29 & E30 & E31 & AG1).
  rewrite Esr' in E24, E28. rewrite Edr' in E29.
  assert (RI1 : rinv [RD] M0 m1) by (apply (rinv_cells [RD] [] M0 Mi m1 RI FR1); intros c []).
  assert (ROL : regions_ok SEGS m1 (RLS lined lineg)).
  { intros r Hr. unfold RLS in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 m1 datad _ lined _ (proj1 RI1) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. apply (reg_sok SEGS M0 m1 datag _ lineg _ (proj1 RI1) SOKS); rewrite ?Z2Nat.id by lia; lia. }
  destruct (px_loop lined lineg Hdr Hsr m1 ROL (kcs_keep M0 m1 RI1 KC0) (Z.to_nat w) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _))
    as (r2 & m2 & RUN2 & RI2 & AG2).
  { unfold pregs. repeat split; dl_get2. }
  assert (RI2' : rinv [RD] M0 m2).
  { apply (rinv_trans [RD] M0 m1 m2 RI1). apply (rinv_weaken (RL lined) [RD] m1 m2 RI2).
    intros r [<- | []]. exists (datad, 4 * (wpld * h))%Z. split; [unfold RD; dl_in0 | cbn [fst snd]; lia]. }
  destruct (kcs_keep M0 m2 RI2' KC0) as (K1 & K2 & K3).
  assert (HYPl : bl_hyps sp datag datad w h wplg wpld i (i * wplg)) by (unfold bl_hyps; repeat split; first [assumption | lia]).
  destruct (bl_1c2a0 rom sp datag datad w h wplg wpld i (i * wplg)%Z HYPl fx r2 m2 K2 ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r3 & m3 & RUN3 & FR3 & E3_12 & E3_13 & E3_28 & AG3).
  assert (RI3 : rinv [RD] M0 m3) by (apply (rinv_cells [RD] [] M0 m2 m3 RI2' FR3); intros c []).
  destruct (kcs_keep M0 m3 RI3 KC0) as (K1' & K2' & K3').
  destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
  - destruct (bl_1c2acf rom sp datag datad w h wplg wpld i (i * wplg)%Z HYPl fx r3 m3 ltac:(ex_br) K2' ltac:(dl_get2) ltac:(dl_get2) E3_12 E3_13
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) E3_28) as (r4 & m4 & RUN4 & FR4 & AG4).
    assert (RI4 : rinv [RD] M0 m4) by (apply (rinv_cells [RD] [] M0 m3 m4 RI3 FR4); intros c []).
    destruct (IH (i + 1)%Z r4 m4 ltac:(lia) ltac:(lia) RI4) as (r5 & m5 & RUN5 & RI5 & AG5).
    { unfold rregs. rewrite <- Eacc. repeat split; dl_get2. }
    exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
    split; [exact RI5 | ra_chain].
  - destruct (bl_1c2act rom sp datag datad w h wplg wpld i (i * wplg)%Z HYPl fx r3 m3 ltac:(ex_br) K2' ltac:(dl_get2) ltac:(dl_get2) E3_12 E3_13
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) E3_28) as (r4 & m4 & RUN4 & FR4 & AG4).
    assert (RI4 : rinv [RD] M0 m4) by (apply (rinv_cells [RD] [] M0 m3 m4 RI3 FR4); intros c []).
    exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
    split; [exact RI4 | ra_chain].
Qed.

(* [comment removed for export] *)
Lemma band_run : forall (M0 : word -> option byte) regs, regions_ok SEGS M0 [RD; RS] -> kcs M0 ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 2 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 18 = Z_to_bv 64 datag -> getr regs 19 = Z_to_bv 64 wplg -> getr regs 20 = Z_to_bv 64 datad -> getr regs 23 = Z_to_bv 64 1 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1c36c) M0 rom) (mkst regs' (Z_to_bv 64 0x1c560) M' rom)
    /\ rinv [RD] M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros M0 regs RO0 KC0 H2 H8 H9 H10 H18 H19 H20 H23. geom. pose proof KC0 as (K1 & K2 & K3).
  assert (HYPa : ba_hyps sp datag datad h) by (unfold ba_hyps; repeat split; first [assumption | lia]).
  destruct (ba_1c268 rom sp datag datad h HYPa fx regs M0 K2 H2 H18 H20 H23)
    as (r1 & m1 & RUN1 & FR1 & E5 & E6 & E7 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & AG1).
  assert (RI1 : rinv [RD] M0 m1) by (apply (rinv_cells [RD] [] M0 M0 m1 (rinv_refl _ _) FR1); intros c []).
  destruct (row_loop M0 RO0 KC0 (Z.to_nat h) 0%Z r1 m1 ltac:(lia) ltac:(lia) RI1) as (r2 & m2 & RUN2 & RI2 & AG2).
  { unfold rregs. repeat split; dl_get2. }
  exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

End Band.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Inst.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (sp datad datag w h wpld wplg : Z).

Ltac cin_tac :=
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros lineg lined j AG AD Hj c Hc; cbn [In] in Hc;
  pose proof (dl_div_bounds j 32 ltac:(lia) ltac:(lia)) as DJ; pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ16;
  pose proof (dl_div_bounds j 8 ltac:(lia) ltac:(lia)) as DJ8;
  destruct (al4_ex _ AD) as [cd Ecd]; destruct (al4_ex _ AG) as [cs Ecs];
  repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; (split; [lia|]);
     first [ (exists (lined, 4 * wpld)%Z; split; [dl_in0 | cbn [fst snd]; dl_lia]) | (exists (lineg, 4 * wplg)%Z; split; [dl_in0 | cbn [fst snd]; dl_lia]) ] |]);
  destruct Hc.

Lemma band_run_8 : band_geom 8 sp datad datag w h wpld wplg -> band_disj sp datad h wpld ->
  forall (M0 : word -> option byte) regs, regions_ok SEGS M0 [RD datad h wpld; RS datag h wplg] -> kcs 8 sp w h M0 ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 2 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 18 = Z_to_bv 64 datag -> getr regs 19 = Z_to_bv 64 wplg -> getr regs 20 = Z_to_bv 64 datad -> getr regs 23 = Z_to_bv 64 1 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1c36c) M0 rom) (mkst regs' (Z_to_bv 64 0x1c560) M' rom)
    /\ rinv [RD datad h wpld] M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros G GD. pose proof G as (Gs0 & Gs1 & Gd0 & Gd1 & ALd & Gg0 & Gg1 & ALg & Gw & Gh & Gwd & Gwg & Gw32 & GwD & Gpd & Gpg).
  apply (band_run rom 8 bp8_1c364_cells_def bp8_1c364_cells_w_def (bp8_1c364_path rom) (bp8_1c34c rom) (bp8_1c360f rom) (bp8_1c360t rom)
           sp datad datag w h wpld wplg G GD).
  - unfold bp8_1c364_cells_def. cin_tac.
  - unfold bp8_1c364_cells_w_def. cin_tac.
Qed.

Lemma band_run_4 : band_geom 4 sp datad datag w h wpld wplg -> band_disj sp datad h wpld ->
  forall (M0 : word -> option byte) regs, regions_ok SEGS M0 [RD datad h wpld; RS datag h wplg] -> kcs 4 sp w h M0 ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 2 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 18 = Z_to_bv 64 datag -> getr regs 19 = Z_to_bv 64 wplg -> getr regs 20 = Z_to_bv 64 datad -> getr regs 23 = Z_to_bv 64 1 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1c36c) M0 rom) (mkst regs' (Z_to_bv 64 0x1c560) M' rom)
    /\ rinv [RD datad h wpld] M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros G GD. pose proof G as (Gs0 & Gs1 & Gd0 & Gd1 & ALd & Gg0 & Gg1 & ALg & Gw & Gh & Gwd & Gwg & Gw32 & GwD & Gpd & Gpg).
  apply (band_run rom 4 bp4_1c364_cells_def bp4_1c364_cells_w_def (bp4_1c364_path rom) (bp4_1c34c rom) (bp4_1c360f rom) (bp4_1c360t rom)
           sp datad datag w h wpld wplg G GD).
  - unfold bp4_1c364_cells_def. cin_tac.
  - unfold bp4_1c364_cells_w_def. cin_tac.
Qed.

Lemma band_run_2 : band_geom 2 sp datad datag w h wpld wplg -> band_disj sp datad h wpld ->
  forall (M0 : word -> option byte) regs, regions_ok SEGS M0 [RD datad h wpld; RS datag h wplg] -> kcs 2 sp w h M0 ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 8 = Z_to_bv 64 2 -> getr regs 9 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 wpld ->
  getr regs 18 = Z_to_bv 64 datag -> getr regs 19 = Z_to_bv 64 wplg -> getr regs 20 = Z_to_bv 64 datad -> getr regs 23 = Z_to_bv 64 1 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1c36c) M0 rom) (mkst regs' (Z_to_bv 64 0x1c560) M' rom)
    /\ rinv [RD datad h wpld] M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros G GD. pose proof G as (Gs0 & Gs1 & Gd0 & Gd1 & ALd & Gg0 & Gg1 & ALg & Gw & Gh & Gwd & Gwg & Gw32 & GwD & Gpd & Gpg).
  apply (band_run rom 2 bp2_1c364_cells_def bp2_1c364_cells_w_def (bp2_1c364_path rom) (bp2_1c34c rom) (bp2_1c360f rom) (bp2_1c360t rom)
           sp datad datag w h wpld wplg G GD).
  - unfold bp2_1c364_cells_def. cin_tac.
  - unfold bp2_1c364_cells_w_def. cin_tac.
Qed.

End Inst.
