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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherLoop DitherTab DitherTabLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15ThrLut.
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

Section Lut.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (sp datad datat qtab w h wpld wplt : Z).
Definition lut_geom : Prop :=
  (4096 <= sp /\ sp + 96 < 2 ^ 47 /\ 4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\
   4096 <= datat /\ datat + 4 * (wplt * h) < 2 ^ 47 /\ datat mod 4 = 0 /\ 4096 <= qtab /\ qtab + 1024 < 2 ^ 47 /\ qtab mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wpld <= 5000 /\ 1 <= wplt <= 5000 /\ w <= 4 * wpld /\ w <= 4 * wplt /\
   wpld * h <= 2 ^ 24 /\ wplt * h <= 2 ^ 24)%Z.
(* [comment removed for export] *)
Definition lut_disj : Prop :=
  (datad + 4 * (wpld * h) <= sp \/ sp + 96 <= datad)%Z /\ (datad + 4 * (wpld * h) <= qtab \/ qtab + 1024 <= datad)%Z.
Hypothesis G : lut_geom.
Hypothesis GD : lut_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gd0 & Gd1 & ALd & Gt0 & Gt1 & ALt & Gq0 & Gq1 & ALq & Gw & Gh & Gwd & Gwt & Gw4d & Gw4t & Gdh & Gth).

Definition RD : Z * Z := (datad, 4 * (wpld * h))%Z.
Definition RS : Z * Z := (datat, 4 * (wplt * h))%Z.
Definition kcs (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (sp + 80)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M (Z_to_bv 64 (sp + 84)) 4 = Some (Z_to_le_bytes 4 w) /\
  rdn SEGS M (Z_to_bv 64 (sp + 88)) 8 = Some (Z_to_le_bytes 8 qtab).
(* [comment removed for export] *)
Definition qtab_ok (M : word -> option byte) : Prop :=
  forall k, (0 <= k <= 255)%Z -> exists bs, rdn SEGS M (Z_to_bv 64 (qtab + 4 * k)) 4 = Some bs.

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

Lemma wph : forall j, (0 <= j < w)%Z -> wp_hyps sp drow srow qtab w j wpld wplt.
Proof.
  intros j Hj. geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3). destruct Hsr as (S1 & S2 & S3).
  unfold wp_hyps. repeat split; try assumption; try lia. unfold dapart. lia.
Qed.
Lemma wp_cells_in : forall j, (0 <= j < w)%Z -> cells_in RLS (wp_1dc6c_cells_def sp drow srow qtab w j wpld wplt).
Proof.
  intros j Hj. geom. destruct Hdr as (D1 & D2 & D3). destruct Hsr as (S1 & S2 & S3).
  destruct (al4_ex _ D3) as [cd Ecd]. destruct (al4_ex _ S3) as [cs Ecs].
  intros c Hc. unfold wp_1dc6c_cells_def in Hc. cbn [In] in Hc. destruct Hc as [<- | [<- | []]]; cbn [fst snd]; (split; [lia|]).
  - exists (srow, 4 * wplt)%Z. split; [unfold RLS; dl_in0 | cbn [fst snd]; dl_lia].
  - exists (drow, 4 * wpld)%Z. split; [unfold RLS; dl_in0 | cbn [fst snd]; dl_lia].
Qed.
Lemma wp_wcells_in : forall j, (0 <= j < w)%Z -> cells_in RL (wp_1dc6c_cells_w_def sp drow srow qtab w j wpld wplt).
Proof.
  intros j Hj. geom. destruct Hdr as (D1 & D2 & D3). destruct (al4_ex _ D3) as [cd Ecd].
  intros c Hc. unfold wp_1dc6c_cells_w_def in Hc. cbn [In] in Hc. destruct Hc as [<- | []]; cbn [fst snd]; (split; [lia|]).
  exists (drow, 4 * wpld)%Z. split; [unfold RL; dl_in0 | cbn [fst snd]; dl_lia].
Qed.

Definition pregs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 sp /\ getr regs 5 = Z_to_bv 64 srow /\ getr regs 6 = Z_to_bv 64 j /\ getr regs 7 = Z_to_bv 64 (srow + j) /\
  getr regs 13 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 16 = Z_to_bv 64 3 /\ getr regs 17 = Z_to_bv 64 drow /\
  getr regs 28 = Z_to_bv 64 (drow + j) /\ getr regs 29 = Z_to_bv 64 (drow + j) /\ getr regs 30 = Z_to_bv 64 (srow + j).

Lemma kcs_row : forall (M1 Mi : word -> option byte), rinv RL M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3). geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3). unfold kcs.
  repeat split; [rewrite <- K1 | rewrite <- K2 | rewrite <- K3];
    (apply (rinv_rdn SEGS RL M1 Mi _ _ RI); [lia | cbn; lia | intros r [<- | []]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

(* [comment removed for export] *)
Lemma px_tab : forall (Mr Mi : word -> option byte) j, (0 <= j < w)%Z -> rinv RL Mr Mi -> qtab_ok Mr ->
  tab_rd SEGS true (fun _ => True) (wp_1dc6c_cells_w_def sp drow srow qtab w j wpld wplt) Mi qtab.
Proof.
  intros Mr Mi j Hj RI QK m' k FR Hk. geom. destruct GD as (DF & DQ). destruct Hdr as (D1 & D2 & D3).
  destruct (QK k Hk) as (bs & R). exists bs. split; [|exact I]. rewrite <- R.
  apply (rinv_rdn SEGS RL Mr m' _ _ (rinv_cells RL _ Mr Mi m' RI FR (wp_wcells_in j Hj))); [lia | cbn; lia |].
  intros r [<- | []]. cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
Qed.
Lemma px_kcs : forall (Mr Mi : word -> option byte) j, (0 <= j < w)%Z -> rinv RL Mr Mi -> kcs Mr ->
  forall m', mframe (wp_1dc6c_cells_w_def sp drow srow qtab w j wpld wplt) Mi m' -> kcs m'.
Proof.
  intros Mr Mi j Hj RI KC m' FR. exact (kcs_row Mr m' (rinv_cells RL _ Mr Mi m' RI FR (wp_wcells_in j Hj)) KC).
Qed.

Lemma px_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr RLS -> kcs Mr -> qtab_ok Mr ->
  forall (n : nat) j regs Mi, (w - j <= Z.of_nat n)%Z -> (0 <= j < w)%Z -> rinv RL Mr Mi -> pregs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1dd70) Mi rom) (mkst regs' (Z_to_bv 64 0x1dcd0) Mi' rom)
    /\ rinv RL Mr Mi' /\ regs_agree (fun r => In r [6; 7; 8; 20; 22; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros Mr ROr KC QK. geom. induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H2 & H5 & H6 & H7 & H13 & H15 & H16 & H17 & H28 & H29 & H30).
  pose proof (cells_ok_of SEGS Mr Mi RLS _ ROr (proj1 RI) (wp_cells_in j Hj)) as CK.
  pose proof (px_kcs Mr Mi j Hj RI KC) as KM.
  destruct (wp_1dc6c_path rom sp drow srow qtab w j wpld wplt (wph j Hj) fx regs Mi CK (px_tab Mr Mi j Hj RI QK)
              (fun m' F => proj1 (proj2 (KM m' F))) (fun m' F => proj2 (proj2 (KM m' F))) H2 H5 H6 H7 H13 H15 H16 H17 H28 H29 H30)
    as (r1 & m1 & RUN1 & FR1 & FW1 & E6 & E7 & E8 & E22 & E28 & E29 & E30 & E31 & AG1).
  pose proof (rinv_cells RL _ Mr Mi m1 RI FW1 (wp_wcells_in j Hj)) as RI1.
  destruct (kcs_row Mr m1 RI1 KC) as (K1 & K2 & K3).
  assert (CI0 : cells_in RL []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w) as [LT|GE].
  - destruct (wp_1dcect rom sp drow srow qtab w j wpld wplt (wph j Hj) fx r1 m1 ltac:(ex_br) K2 K3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RL _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold pregs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (wp_1dcecf rom sp drow srow qtab w j wpld wplt (wph j Hj) fx r1 m1 ltac:(ex_br) K2 K3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RL _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

End Row.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rregs (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 sp /\ getr regs 9 = Z_to_bv 64 datat /\ getr regs 10 = Z_to_bv 64 (i * wpld) /\ getr regs 11 = Z_to_bv 64 (i * wplt) /\
  getr regs 12 = Z_to_bv 64 i /\ getr regs 13 = Z_to_bv 64 1 /\ getr regs 14 = Z_to_bv 64 wplt /\ getr regs 15 = Z_to_bv 64 1 /\
  getr regs 16 = Z_to_bv 64 3 /\ getr regs 18 = Z_to_bv 64 datad /\ getr regs 19 = Z_to_bv 64 wpld.

Lemma row_loop : forall (M0 : word -> option byte), regions_ok SEGS M0 [RD; RS] -> kcs M0 -> qtab_ok M0 ->
  forall (n : nat) i regs Mi, (h - i <= Z.of_nat n)%Z -> (0 <= i < h)%Z -> rinv [RD] M0 Mi -> rregs regs i ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1dce4) Mi rom) (mkst regs' (Z_to_bv 64 0x1ddf8) Mi' rom)
    /\ rinv [RD] M0 Mi' /\ regs_agree (fun r => In r [5; 6; 7; 8; 10; 11; 12; 17; 20; 22; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros M0 RO0 KC0 QK0. geom. induction n as [|n IH]; intros i regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H18 & H19).
  pose proof (row_bounds wpld i h ltac:(lia) ltac:(lia) ltac:(lia)) as P1. pose proof (row_bounds wplt i h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  assert (HYPr : wr_hyps sp datad datat w h wpld wplt i (i * wpld) (i * wplt)).
  { unfold wr_hyps. replace (i * wpld)%Z with (wpld * i)%Z by ring. replace (i * wplt)%Z with (wplt * i)%Z by ring. repeat split; first [assumption | lia]. }
  assert (HYPl : wl_hyps sp datad datat w h wpld wplt i (i * wpld) (i * wplt)).
  { unfold wl_hyps. replace ((i + 1) * wpld)%Z with (wpld * i + wpld)%Z by ring. replace ((i + 1) * wplt)%Z with (wplt * i + wplt)%Z by ring.
    replace (i * wpld)%Z with (wpld * i)%Z by ring. replace (i * wplt)%Z with (wplt * i)%Z by ring. repeat split; first [assumption | lia]. }
  remember (datad + 4 * (wpld * i))%Z as drow eqn:Edr. remember (datat + 4 * (wplt * i))%Z as srow eqn:Esr.
  assert (Hdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h) /\ drow mod 4 = 0)%Z).
  { split; [lia|]. split; [lia|]. subst drow. apply al4_add. exact ALd. }
  assert (Hsr : (datat <= srow /\ srow + 4 * wplt <= datat + 4 * (wplt * h) /\ srow mod 4 = 0)%Z).
  { split; [lia|]. split; [lia|]. subst srow. apply al4_add. exact ALt. }
  assert (Edr' : (datad + 4 * (i * wpld))%Z = drow) by (subst drow; ring).
  assert (Esr' : (datat + 4 * (i * wplt))%Z = srow) by (subst srow; ring).
  clear P1 P2 Edr Esr.
  destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD). destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS).
  unfold RD, RS in *. cbn [fst snd] in *.
  destruct (kcs_keep M0 Mi RI KC0) as (K1 & K2 & K3).
  destruct (wr_1dbe0 rom sp datad datat w h wpld wplt i (i * wpld) (i * wplt) HYPr fx regs Mi K2 H2 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19)
    as (r1 & m1 & RUN1 & FR1 & E5 & E6 & E7 & E17 & E28 & E29 & E30 & AG1).
  rewrite Esr' in E5, E7, E30. rewrite Edr' in E17, E28, E29.
  assert (RI1 : rinv [RD] M0 m1) by (apply (rinv_cells [RD] [] M0 Mi m1 RI FR1); intros c []).
  assert (ROL : regions_ok SEGS m1 (RLS drow srow)).
  { intros r Hr. unfold RLS in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 m1 datad _ drow _ (proj1 RI1) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. apply (reg_sok SEGS M0 m1 datat _ srow _ (proj1 RI1) SOKS); rewrite ?Z2Nat.id by lia; lia. }
  destruct (px_loop drow srow Hdr Hsr m1 ROL (kcs_keep M0 m1 RI1 KC0) (qtab_keep M0 m1 RI1 QK0) (Z.to_nat w) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _))
    as (r2 & m2 & RUN2 & RI2 & AG2).
  { unfold pregs. repeat split; dl_get2. }
  assert (RI2' : rinv [RD] M0 m2).
  { apply (rinv_trans [RD] M0 m1 m2 RI1). apply (rinv_weaken (RL drow) [RD] m1 m2 RI2).
    intros r [<- | []]. exists (datad, 4 * (wpld * h))%Z. split; [unfold RD; dl_in0 | cbn [fst snd]; lia]. }
  destruct (kcs_keep M0 m2 RI2' KC0) as (K1b & K2b & K3b).
  destruct (wl_1dbcc rom sp datad datat w h wpld wplt i (i * wpld) (i * wplt) HYPl fx r2 m2 K1b
              ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2))
    as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & E3_12 & E3_17 & AG3).
  assert (RI3 : rinv [RD] M0 m3) by (apply (rinv_cells [RD] [] M0 m2 m3 RI2' FR3); intros c []).
  destruct (kcs_keep M0 m3 RI3 KC0) as (K1c & K2c & K3c).
  destruct (Z_lt_ge_dec (i + 1) h) as [LT|GE].
  - destruct (wl_1dbdcf rom sp datad datat w h wpld wplt i (i * wpld) (i * wplt) HYPl fx r3 m3 ltac:(ex_br) K1c
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)) as (r4 & m4 & RUN4 & FR4 & AG4).
    assert (RI4 : rinv [RD] M0 m4) by (apply (rinv_cells [RD] [] M0 m3 m4 RI3 FR4); intros c []).
    destruct (IH (i + 1)%Z r4 m4 ltac:(lia) ltac:(lia) RI4) as (r5 & m5 & RUN5 & RI5 & AG5).
    { unfold rregs. repeat split; dl_get2. }
    exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|].
    split; [exact RI5 | ra_chain].
  - destruct (wl_1dbdct rom sp datad datat w h wpld wplt i (i * wpld) (i * wplt) HYPl fx r3 m3 ltac:(ex_br) K1c
                ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2) ltac:(dl_get2)) as (r4 & m4 & RUN4 & FR4 & AG4).
    assert (RI4 : rinv [RD] M0 m4) by (apply (rinv_cells [RD] [] M0 m3 m4 RI3 FR4); intros c []).
    exists r4, m4. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 RUN4)))|].
    split; [exact RI4 | ra_chain].
Qed.

(* [comment removed for export] *)
Lemma lut_run : forall (M0 : word -> option byte) regs, regions_ok SEGS M0 [RD; RS] -> kcs M0 -> qtab_ok M0 ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 9 = Z_to_bv 64 datat -> getr regs 11 = Z_to_bv 64 h -> getr regs 14 = Z_to_bv 64 wplt ->
  getr regs 18 = Z_to_bv 64 datad -> getr regs 19 = Z_to_bv 64 wpld ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1dcb0) M0 rom) (mkst regs' (Z_to_bv 64 0x1ddf8) M' rom)
    /\ rinv [RD] M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 8; 10; 11; 12; 13; 15; 16; 17; 20; 22; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros M0 regs RO0 KC0 QK0 H2 H9 H11 H14 H18 H19. geom.
  assert (HYPa : wa_hyps sp datad datat h) by (unfold wa_hyps; repeat split; first [assumption | lia]).
  destruct (wa_1dbac rom sp datad datat h HYPa fx regs M0 H2 H9 H11 H18) as (r1 & m1 & RUN1 & FR1 & E10 & E11 & E12 & E13 & E15 & E16 & AG1).
  assert (RI1 : rinv [RD] M0 m1) by (apply (rinv_cells [RD] [] M0 M0 m1 (rinv_refl _ _) FR1); intros c []).
  destruct (row_loop M0 RO0 KC0 QK0 (Z.to_nat h) 0%Z r1 m1 ltac:(lia) ltac:(lia) RI1) as (r2 & m2 & RUN2 & RI2 & AG2).
  { unfold rregs. repeat split; dl_get2. }
  exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

End Lut.
