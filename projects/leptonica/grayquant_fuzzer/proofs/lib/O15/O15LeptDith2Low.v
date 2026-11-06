(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherLoop DitherTab DitherTabLoop.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Kit.
Import O15Kit.O15MemcpyBase. Import O15Kit.O15Memcpy.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Dith2Low O15LeptDithBinLow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15CL2a.
Import O15CL2a.O15LeptDith2.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac dl_get3 :=
  first [ eassumption
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get3 end
        | match goal with K : keeps ?R ?R' |- getr ?R' ?r = _ => rewrite (K r ltac:(in_kept)); dl_get3 end ].

Ltac dl_same :=
  first [ reflexivity
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_same end
        | match goal with K : keeps ?R ?R' |- getr ?R' ?r = _ => rewrite (K r ltac:(in_kept)); dl_same end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tables.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (tabval tab38 tab14 : Z).
Hypothesis GT : (4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\ 4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\
                 4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0)%Z.
Definition RT : list (Z * Z) := [(tabval, 1024); (tab38, 1024); (tab14, 1024)]%Z.

Lemma tlh : forall i4, (0 <= i4 <= 1020)%Z -> (i4 mod 4 = 0)%Z -> tl_hyps tabval tab38 tab14 i4.
Proof. intros i4 H1 H2. destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3). unfold tl_hyps. repeat split; first [assumption | lia]. Qed.
Lemma tl_cells_in : forall i4, (0 <= i4 <= 1020)%Z -> cells_in RT (tl_1b008_cells_def tabval tab38 tab14 i4).
Proof.
  intros i4 Hi. destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3).
  intros c Hc. unfold tl_1b008_cells_def in Hc. cbn [In] in Hc.
  destruct Hc as [<- | [<- | [<- | []]]]; cbn [fst snd]; (split; [lia|]).
  - exists (tabval, 1024%Z). split; [unfold RT; dl_in0 | cbn [fst snd]; lia].
  - exists (tab38, 1024%Z). split; [unfold RT; dl_in0 | cbn [fst snd]; lia].
  - exists (tab14, 1024%Z). split; [unfold RT; dl_in0 | cbn [fst snd]; lia].
Qed.

Definition tregs (regs : bvmap 5 word) (i4 : Z) : Prop :=
  getr regs 10 = Z_to_bv 64 i4 /\ getr regs 19 = Z_to_bv 64 tabval /\ getr regs 20 = Z_to_bv 64 tab38 /\ getr regs 21 = Z_to_bv 64 tab14 /\
  getr regs 29 = Z_to_bv 64 1024.

Lemma tab_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr RT ->
  forall (n : nat) k regs Mi, (256 - k <= Z.of_nat n)%Z -> (0 <= k <= 255)%Z -> rinv RT Mr Mi -> tregs regs (4 * k) ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1b104) Mi rom) (mkst regs' (Z_to_bv 64 0x1b2b4) Mi' rom)
    /\ rinv RT Mr Mi' /\ regs_agree (fun r => In r [8; 10; 11; 14; 22; 23; 30; 31]%list) regs regs'.
Proof.
  intros Mr ROr. induction n as [|n IH]; intros k regs Mi Hn Hk RI LR; [lia|].
  destruct LR as (H10 & H19 & H20 & H21 & H29).
  assert (Hi4 : (0 <= 4 * k <= 1020)%Z) by lia.
  assert (Al4 : ((4 * k) mod 4 = 0)%Z) by (rewrite Z.mul_comm; apply Z_mod_mult).
  pose proof (tl_cells_in (4 * k) Hi4) as CI.
  pose proof (cells_ok_of SEGS Mr Mi RT _ ROr (proj1 RI) CI) as CK.
  destruct (tl_1b008_path rom tabval tab38 tab14 (4 * k) (tlh _ Hi4 Al4) fx regs Mi CK H10 H19 H20 H21 H29) as (r1 & m1 & RUN1 & FR1 & E10 & E23 & AG1).
  pose proof (rinv_cells RT _ Mr Mi m1 RI FR1 CI) as RI1.
  assert (CI0 : cells_in RT []) by (intros c []).
  destruct (Z_lt_ge_dec (k + 1) 256) as [LT|GE].
  - destruct (tl_1b004f rom tabval tab38 tab14 (4 * k) (tlh _ Hi4 Al4) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RT _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (k + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold tregs. repeat split; dl_get3. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (tl_1b004t rom tabval tab38 tab14 (4 * k) (tlh _ Hi4 Al4) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RT _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

Lemma T_run : forall (M0 : word -> option byte) regs, regions_ok SEGS M0 RT ->
  getr regs 19 = Z_to_bv 64 tabval -> getr regs 20 = Z_to_bv 64 tab38 -> getr regs 21 = Z_to_bv 64 tab14 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1b08c) M0 rom) (mkst regs' (Z_to_bv 64 0x1b2b4) M' rom)
    /\ rinv RT M0 M' /\ regs_agree (fun r => In r [5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 22; 23; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros M0 regs RO H19 H20 H21. destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3).
  assert (HYPi : ti_hyps tabval tab38 tab14) by (unfold ti_hyps; repeat split; first [assumption | lia]).
  destruct (ti_1af90 rom tabval tab38 tab14 HYPi fx regs M0 H19 H20 H21)
    as (r1 & m1 & RUN1 & FR1 & E5 & E6 & E7 & E10 & E11 & E13 & E14 & E15 & E16 & E17 & E28 & E29 & E30 & E31 & AG1).
  assert (RI1 : rinv RT M0 m1) by (apply (rinv_cells RT [] M0 M0 m1 (rinv_refl _ _) FR1); intros c []).
  destruct (tab_loop M0 RO 256%nat 0%Z r1 m1 ltac:(lia) ltac:(lia) RI1) as (r2 & m2 & RUN2 & RI2 & AG2).
  { unfold tregs. repeat split; dl_get3. }
  exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.
End Tables.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Low2.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (s datad w h wpld datat wplt bufs1 bufs2 tabval tab38 tab14 cf : Z).
Definition low2_geom : Prop :=
  (4096 <= s - 208 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\
   4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\ 4096 <= datat /\ datat + 4 * (wplt * h) < 2 ^ 47 /\ datat mod 4 = 0 /\
   4096 <= bufs1 /\ bufs1 + 4 * wplt < 2 ^ 47 /\ bufs1 mod 4 = 0 /\ 4096 <= bufs2 /\ bufs2 + 4 * wplt < 2 ^ 47 /\ bufs2 mod 4 = 0 /\
   4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\ 4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\
   4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wplt <= 5000 /\ 1 <= wpld <= 1250 /\ w <= 4 * wplt /\ w <= 16 * wpld /\ 0 <= cf <= 1 /\
   wplt * h <= 2 ^ 24 /\ wpld * h <= 2 ^ 24)%Z.
(* [comment removed for export] *)
Definition LWL : list (Z * Z) :=
  [(s - 208, 208); (datad, 4 * (wpld * h)); (datat, 4 * (wplt * h)); (bufs1, 4 * wplt); (bufs2, 4 * wplt); (tabval, 1024); (tab38, 1024); (tab14, 1024)]%Z.
Definition low2_disj : Prop := pairwise LWL.
Hypothesis G : low2_geom.
Hypothesis GD : low2_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gd0 & Gd1 & ALd & Gt0 & Gt1 & ALt & Gb10 & Gb11 & ALb1 & Gb20 & Gb21 & ALb2 & Gv0 & Gv1 & ALv & G80 & G81 & AL8 & G40 & G41 & AL4
                                 & Gw & Gh & Gwplt & Gwpld & Gw4 & Gw16 & Gcf & Gth & Gdh).

Definition RD : Z * Z := (datad, 4 * (wpld * h))%Z.
Definition RS : Z * Z := (datat, 4 * (wplt * h))%Z.
Definition RB1 : Z * Z := (bufs1, 4 * wplt)%Z.
Definition RB2 : Z * Z := (bufs2, 4 * wplt)%Z.
(* [comment removed for export] *)
Definition RW3 : list (Z * Z) := [RD; RB1; RB2].
(* [comment removed for export] *)
Definition RWL : list (Z * Z) := [((s - 192)%Z, 16%Z); RD; RB1; RB2].

(* [comment removed for export] *)
Definition kcs (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) /\
  rdn SEGS M (Z_to_bv 64 (s - 144)) 8 = Some (Z_to_le_bytes 8 cf) /\ rdn SEGS M (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 datad) /\
  rdn SEGS M (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 wpld) /\ rdn SEGS M (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 datat) /\
  rdn SEGS M (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 wplt).
Definition kcs2 (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 (h - 1)) /\ rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 (w - 1)).

(* [comment removed for export] *)
Lemma frame_keep : forall (M1 Mi : word -> option byte) (k : Z) (n : nat) v, rinv RW3 M1 Mi -> (Z.of_nat n <= k <= 208)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) n = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) n = Some v.
Proof.
  intros M1 Mi k n v RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RW3 M1 Mi (s - k) n RI); [lia | lia |].
  intros r Hr. unfold RW3 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; unfold RD, RB1, RB2; cbn [fst snd].
  - pw GD 0%nat 1%nat D. lia.
  - pw GD 0%nat 3%nat D. lia.
  - pw GD 0%nat 4%nat D. lia.
Qed.
Lemma kcs_keep : forall (M1 Mi : word -> option byte), rinv RW3 M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3 & K4 & K5 & K6 & K7). unfold kcs.
  repeat split; [apply (frame_keep M1 Mi 108 4%nat _ RI ltac:(cbn; lia) K1) | apply (frame_keep M1 Mi 112 4%nat _ RI ltac:(cbn; lia) K2)
                | apply (frame_keep M1 Mi 144 8%nat _ RI ltac:(cbn; lia) K3) | apply (frame_keep M1 Mi 152 8%nat _ RI ltac:(cbn; lia) K4)
                | apply (frame_keep M1 Mi 160 8%nat _ RI ltac:(cbn; lia) K5) | apply (frame_keep M1 Mi 168 8%nat _ RI ltac:(cbn; lia) K6)
                | apply (frame_keep M1 Mi 176 8%nat _ RI ltac:(cbn; lia) K7)].
Qed.
Lemma kcs2_keep : forall (M1 Mi : word -> option byte), rinv RW3 M1 Mi -> kcs2 M1 -> kcs2 Mi.
Proof.
  intros M1 Mi RI (K1 & K2). unfold kcs2.
  split; [apply (frame_keep M1 Mi 184 8%nat _ RI ltac:(cbn; lia) K1) | apply (frame_keep M1 Mi 192 8%nat _ RI ltac:(cbn; lia) K2)].
Qed.

(* [comment removed for export] *)
Lemma tabs_keep : forall (M1 Mi : word -> option byte), rinv RWL M1 Mi -> tabs_ok tabval tab38 tab14 M1 -> tabs_ok tabval tab38 tab14 Mi.
Proof.
  intros M1 Mi RI (T0 & T38 & T14). geom. unfold tabs_ok.
  split; [|split]; (eapply (tab_ok_rinv SEGS _ _ RWL M1 Mi); [eassumption | exact RI |]);
    intros r Hr; unfold RWL in Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd].
  - pw GD 0%nat 5%nat D. lia.
  - pw GD 1%nat 5%nat D. lia.
  - pw GD 3%nat 5%nat D. lia.
  - pw GD 4%nat 5%nat D. lia.
  - pw GD 0%nat 6%nat D. lia.
  - pw GD 1%nat 6%nat D. lia.
  - pw GD 3%nat 6%nat D. lia.
  - pw GD 4%nat 6%nat D. lia.
  - pw GD 0%nat 7%nat D. lia.
  - pw GD 1%nat 7%nat D. lia.
  - pw GD 3%nat 7%nat D. lia.
  - pw GD 4%nat 7%nat D. lia.
Qed.
Lemma RW3_RWL : forall r, In r RW3 -> In r RWL.
Proof. intros r Hr. right. exact Hr. Qed.

(* [comment removed for export] *)
Lemma px_geom_row : forall drow, (datad <= drow)%Z -> (drow + 4 * wpld <= datad + 4 * (wpld * h))%Z -> (drow mod 4 = 0)%Z ->
  px_geom drow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld.
Proof. intros drow H1 H2 H3. geom. unfold px_geom. repeat split; first [assumption | lia]. Qed.
Lemma px_disj_row : forall drow, (datad <= drow)%Z -> (drow + 4 * wpld <= datad + 4 * (wpld * h))%Z ->
  px_disj drow bufs1 bufs2 tabval tab38 tab14 wplt wpld.
Proof.
  intros drow H1 H2. geom. unfold px_disj, PXL. cbn [pairwise]. repeat split; try exact I;
    intros r' Hr'; cbn [In] in Hr'; repeat (destruct Hr' as [<- | Hr']; [unfold apart2; cbn [fst snd] |]); try (destruct Hr').
  - pw GD 1%nat 3%nat D. lia.
  - pw GD 1%nat 4%nat D. lia.
  - pw GD 1%nat 5%nat D. lia.
  - pw GD 1%nat 6%nat D. lia.
  - pw GD 1%nat 7%nat D. lia.
  - pw GD 3%nat 4%nat D. lia.
  - pw GD 3%nat 5%nat D. lia.
  - pw GD 3%nat 6%nat D. lia.
  - pw GD 3%nat 7%nat D. lia.
  - pw GD 4%nat 5%nat D. lia.
  - pw GD 4%nat 6%nat D. lia.
  - pw GD 4%nat 7%nat D. lia.
  - pw GD 5%nat 6%nat D. lia.
  - pw GD 5%nat 7%nat D. lia.
  - pw GD 6%nat 7%nat D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rowregs (regs : bvmap 5 word) (i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 208) /\ getr regs 8 = Z_to_bv 64 (w - 1) /\ getr regs 9 = Z_to_bv 64 bufs1 /\ getr regs 18 = Z_to_bv 64 bufs2 /\
  getr regs 19 = Z_to_bv 64 tabval /\ getr regs 20 = Z_to_bv 64 tab38 /\ getr regs 21 = Z_to_bv 64 tab14 /\ getr regs 22 = Z_to_bv 64 i /\
  getr regs 23 = Z_to_bv 64 w /\ getr regs 26 = Z_to_bv 64 (wplt * 4) /\ getr regs 27 = Z_to_bv 64 268435455.
Definition exitregs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 208) /\ getr regs 9 = Z_to_bv 64 bufs1 /\ getr regs 18 = Z_to_bv 64 bufs2 /\
  getr regs 19 = Z_to_bv 64 tabval /\ getr regs 20 = Z_to_bv 64 tab38 /\ getr regs 21 = Z_to_bv 64 tab14 /\
  getr regs 23 = Z_to_bv 64 w /\ getr regs 26 = Z_to_bv 64 (wplt * 4) /\ getr regs 27 = Z_to_bv 64 268435455.

Lemma row2_loop : forall (M3 : word -> option byte), regions_ok SEGS M3 [RD; RB1; RB2; RS] -> tabs_ok tabval tab38 tab14 M3 -> kcs M3 -> kcs2 M3 ->
  forall (n : nat) i regs Mi, (h - 1 - i <= Z.of_nat n)%Z -> (0 <= i < h - 1)%Z -> rinv RW3 M3 Mi -> rowregs regs i ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1b314) Mi rom) (mkst regs' (Z_to_bv 64 0x1b50c) Mi' rom)
    /\ rinv RW3 M3 Mi' /\ exitregs regs' /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros M3 RO3 TK3 KC3 KD3. geom. induction n as [|n IH]; intros i regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H26 & H27).
  pose proof (row_bounds wpld i h ltac:(lia) ltac:(lia) ltac:(lia)) as P1.
  pose proof (row_bounds wplt (i + 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  assert (HYPr : lr_hyps s datat bufs1 bufs2 wplt i).
  { unfold lr_hyps. replace ((i + 1) * wplt)%Z with (wplt * (i + 1))%Z by ring. repeat split; first [assumption | lia]. }
  assert (HYPd : forall w2, (2 <= w2 <= 20000)%Z -> le_hyps s datad bufs1 bufs2 wpld i w2).
  { intros w2 Hw2. unfold le_hyps. replace (i * wpld)%Z with (wpld * i)%Z by ring. repeat split; first [assumption | lia]. }
  assert (HYPd1 : ld_hyps s datad bufs1 bufs2 wpld i).
  { unfold ld_hyps. replace (i * wpld)%Z with (wpld * i)%Z by ring. repeat split; first [assumption | lia]. }
  remember (datat + 4 * (wplt * (i + 1)))%Z as srow eqn:Esr. remember (datad + 4 * (wpld * i))%Z as drow eqn:Edr.
  assert (Rsr : (datat <= srow /\ srow + 4 * wplt <= datat + 4 * (wplt * h))%Z) by lia.
  assert (Rdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h))%Z) by lia.
  assert (ALdr : (drow mod 4 = 0)%Z) by (subst drow; apply al4_add; exact ALd).
  assert (Esr' : (datat + 4 * ((i + 1) * wplt))%Z = srow) by (subst srow; ring).
  assert (Edr' : (datad + 4 * (i * wpld))%Z = drow) by (subst drow; ring).
  clear P1 P2 Esr Edr.
  destruct (RO3 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1). destruct (RO3 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2).
  destruct (RO3 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS). destruct (RO3 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  (* [comment removed for export] *)
  destruct (kcs_keep M3 Mi RI KC3) as (Kw & Kh & Kcf & Kdd & Kwd & Kdt & Kwt).
  destruct (lr_1b218 rom s datat bufs1 bufs2 wplt i HYPr fx regs Mi Kdt Kwt H2 H9 H18 H22 H26) as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_10 & E1_11 & E1_12 & E1_24 & AG1).
  assert (RI1 : rinv RW3 M3 m1) by (apply (rinv_cells RW3 [] M3 Mi m1 RI FR1); intros c []).
  destruct (memcpy_step rom M3 m1 r1 bufs1 bufs2 (wplt * 4) bufs1 bufs2 _ _ 111400 (proj1 RI1) SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 3%nat 4%nat D; lia) ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs1) bs2) in *.
  assert (RI2 : rinv RW3 M3 m2).
  { apply (rinv_wbytes RW3 M3 m1 bufs1 (wplt * 4) bs2 RI1 L2); [lia | lia |]. exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M3 m2 RI2 KC3) as (Kw2 & Kh2 & Kcf2 & Kdd2 & Kwd2 & Kdt2 & Kwt2).
  destruct (lr_1b22c rom s datat bufs1 bufs2 wplt i HYPr fx r2 m2 Kdt2 Kwt2 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
    as (r3 & m3 & RUN3 & FR3 & E3_1 & E3_10 & E3_11 & E3_12 & E3_22 & AG3).
  rewrite Esr' in E3_11.
  assert (RI3 : rinv RW3 M3 m3) by (apply (rinv_cells RW3 [] M3 m2 m3 RI2 FR3); intros c []).
  destruct (memcpy_step rom M3 m3 r3 bufs2 srow (wplt * 4) bufs2 datat _ _ 111436 (proj1 RI3) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 2%nat 4%nat D; lia) ltac:(red; apply bv_eq; reflexivity) E3_1 E3_10 E3_11 E3_12)
    as (r4 & bs4 & RUN4 & L4 & K4).
  set (m4 := wbytes m3 (Z_to_bv 64 bufs2) bs4) in *.
  assert (RI4 : rinv RW3 M3 m4).
  { apply (rinv_wbytes RW3 M3 m3 bufs2 (wplt * 4) bs4 RI3 L4); [lia | lia |]. exists (bufs2, 4 * wplt)%Z. split; [unfold RW3, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  pose proof (px_geom_row drow ltac:(lia) ltac:(lia) ALdr) as GPX. pose proof (px_disj_row drow ltac:(lia) ltac:(lia)) as DPX.
  destruct (kcs_keep M3 m4 RI4 KC3) as (Kw4 & Kh4 & Kcf4 & Kdd4 & Kwd4 & Kdt4 & Kwt4).
  assert (ROLL : forall Mx, mem_grows M3 Mx -> regions_ok SEGS Mx (R3 drow bufs1 bufs2 wplt wpld)).
  { intros Mx GX r Hr. unfold R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M3 Mx datad _ drow _ GX SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact GX | exact SOK1].
    - repeat split; try lia. eapply store_ok_mono; [exact GX | exact SOK2]. }
  assert (WK : forall Mx My, rinv (R3 drow bufs1 bufs2 wplt wpld) Mx My -> rinv RW3 Mx My).
  { intros Mx My RIx. apply (rinv_weaken (R3 drow bufs1 bufs2 wplt wpld) RW3 Mx My RIx).
    intros r Hr. unfold R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW3, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs2, 4 * wplt)%Z. split; [unfold RW3, RB2; dl_in0 | cbn [fst snd]; lia]. }
  assert (TKx : forall Mx, rinv RW3 M3 Mx -> tabs_ok tabval tab38 tab14 Mx).
  { intros Mx RIx. apply (tabs_keep M3 Mx); [apply (rinv_incl RW3 RWL M3 Mx RIx RW3_RWL) | exact TK3]. }
  assert (MID : exists r6 m6, msteps SEGS (mkst r4 (Z_to_bv 64 0x1b34c) m4 rom) (mkst r6 (Z_to_bv 64 0x1b47c) m6 rom) /\ rinv RW3 M3 m6
                  /\ getr r6 10 = Z_to_bv 64 drow /\ getr r6 11 = Z_to_bv 64 (w - 1)
                  /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]%list) r4 r6).
  { destruct (Z.eq_dec w 1) as [W1|W2].
    - destruct (ld_1b250 rom s datad bufs1 bufs2 wpld i HYPd1 fx r4 m4 Kdd4 Kwd4 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
        as (r5 & m5 & RUN5 & FR5 & E5_10 & E5_11 & AG5).
      rewrite Edr' in E5_10.
      exists r5, m5. split; [exact RUN5|]. split; [apply (rinv_cells RW3 [] M3 m4 m5 RI4 FR5); intros c []|].
      split; [exact E5_10|]. split; [rewrite E5_11; f_equal; lia|]. intros r Hr. apply AG5. intros X. apply Hr. cbn [In] in *. tauto.
    - destruct (le_1b250 rom s datad bufs1 bufs2 wpld i w (HYPd w ltac:(lia)) fx r4 m4 Kdd4 Kwd4 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
        as (r5 & m5 & RUN5 & FR5 & E5_10 & E5_11 & E5_12 & E5_13 & E5_14 & AG5).
      rewrite Edr' in E5_10.
      assert (RI5 : rinv RW3 M3 m5) by (apply (rinv_cells RW3 [] M3 m4 m5 RI4 FR5); intros c []).
      destruct (pf_loop rom drow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld GPX DPX m5 (ROLL m5 (proj1 RI5)) (TKx m5 RI5)
                  (Z.to_nat w) 0%Z r5 m5 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r6 & m6 & RUN6 & RI6 & AG6).
      { unfold f0regs. repeat split; dl_get3. }
      assert (RI6' : rinv RW3 M3 m6) by (apply (rinv_trans RW3 M3 m5 m6 RI5), WK, RI6).
      destruct (kcs2_keep M3 m6 RI6' KD3) as (Kh1 & Kw1).
      assert (HYPw : lw_hyps s (w - 1)) by (unfold lw_hyps; repeat split; first [assumption | lia]).
      destruct (lw_1b37c rom s (w - 1) HYPw fx r6 m6 Kw1 ltac:(dl_get3)) as (r7 & m7 & RUN7 & FR7 & E7_11 & AG7).
      exists r7, m7. split; [exact (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7))|].
      split; [apply (rinv_cells RW3 [] M3 m6 m7 RI6' FR7); intros c []|].
      split; [dl_get3|]. split; [exact E7_11|]. ra_chain. }
  destruct MID as (r6 & m6 & RUN6 & RI6 & E6_10 & E6_11 & AG6).
  (* [comment removed for export] *)
  destruct (pc_run rom drow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld GPX DPX m6 (ROLL m6 (proj1 RI6)) (TKx m6 RI6) r6 m6 (rinv_refl _ _)
              ltac:(dl_get3) E6_10 E6_11 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3)) as (r7 & m7 & RUN7 & RI7 & AG7).
  assert (RI7' : rinv RW3 M3 m7) by (apply (rinv_trans RW3 M3 m6 m7 RI6), WK, RI7).
  (* [comment removed for export] *)
  destruct (kcs2_keep M3 m7 RI7' KD3) as (Kh7 & Kw7).
  assert (HYPl : ll_hyps s i (h - 1)) by (unfold ll_hyps; repeat split; first [assumption | lia]).
  destruct (ll_1b210 rom s i (h - 1) HYPl fx r7 m7 Kh7 ltac:(dl_get3) ltac:(dl_get3)) as (r8 & m8 & RUN8 & FR8 & E8_10 & AG8).
  assert (RI8 : rinv RW3 M3 m8) by (apply (rinv_cells RW3 [] M3 m7 m8 RI7' FR8); intros c []).
  destruct (kcs2_keep M3 m8 RI8 KD3) as (Kh8 & Kw8).
  assert (CHAIN : msteps SEGS (mkst regs (Z_to_bv 64 0x1b314) Mi rom) (mkst r8 (Z_to_bv 64 0x1b310) m8 rom)).
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4
           (msteps_trans _ _ _ _ RUN6 (msteps_trans _ _ _ _ RUN7 RUN8)))))). }
  destruct (Z_lt_ge_dec (i + 1) (h - 1)) as [LT|GE].
  - destruct (ll_1b214f rom s i (h - 1) HYPl fx r8 m8 ltac:(ex_br) Kh8 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3)) as (r9 & m9 & RUN9 & FR9 & AG9).
    assert (RI9 : rinv RW3 M3 m9) by (apply (rinv_cells RW3 [] M3 m8 m9 RI8 FR9); intros c []).
    destruct (IH (i + 1)%Z r9 m9 ltac:(lia) ltac:(lia) RI9) as (r10 & m10 & RUN10 & RI10 & EX10 & X3 & X4).
    { unfold rowregs. repeat split; dl_get3. }
    exists r10, m10. split; [exact (msteps_trans _ _ _ _ CHAIN (msteps_trans _ _ _ _ RUN9 RUN10))|]. split; [exact RI10|]. split; [exact EX10|].
    split; [rewrite X3 | rewrite X4]; dl_same.
  - destruct (ll_1b214t rom s i (h - 1) HYPl fx r8 m8 ltac:(ex_br) Kh8 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3)) as (r9 & m9 & RUN9 & FR9 & AG9).
    assert (RI9 : rinv RW3 M3 m9) by (apply (rinv_cells RW3 [] M3 m8 m9 RI8 FR9); intros c []).
    exists r9, m9. split; [exact (msteps_trans _ _ _ _ CHAIN RUN9)|]. split; [exact RI9|].
    split; [unfold exitregs; repeat split; dl_get3|]. split; dl_same.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lrow : Z := (datad + 4 * ((h - 1) * wpld))%Z.
Lemma lrow_facts : (datad <= lrow /\ lrow + 4 * wpld <= datad + 4 * (wpld * h) /\ lrow mod 4 = 0)%Z.
Proof.
  geom. unfold lrow. pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P.
  replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. split; [lia|]. split; [lia|]. apply al4_add. exact ALd.
Qed.

(* [comment removed for export] *)
Lemma frame_keepL : forall (M1 Mi : word -> option byte) (k : Z) (n : nat) v, rinv RWL M1 Mi -> (Z.of_nat n <= k <= 176)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) n = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) n = Some v.
Proof.
  intros M1 Mi k n v RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RWL M1 Mi (s - k) n RI); [lia | lia |].
  intros r Hr. unfold RWL in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd].
  - lia.
  - pw GD 0%nat 1%nat D. lia.
  - pw GD 0%nat 3%nat D. lia.
  - pw GD 0%nat 4%nat D. lia.
Qed.
Lemma kcs_keepL : forall (M1 Mi : word -> option byte), rinv RWL M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3 & K4 & K5 & K6 & K7). unfold kcs.
  repeat split; [apply (frame_keepL M1 Mi 108 4%nat _ RI ltac:(cbn; lia) K1) | apply (frame_keepL M1 Mi 112 4%nat _ RI ltac:(cbn; lia) K2)
                | apply (frame_keepL M1 Mi 144 8%nat _ RI ltac:(cbn; lia) K3) | apply (frame_keepL M1 Mi 152 8%nat _ RI ltac:(cbn; lia) K4)
                | apply (frame_keepL M1 Mi 160 8%nat _ RI ltac:(cbn; lia) K5) | apply (frame_keepL M1 Mi 168 8%nat _ RI ltac:(cbn; lia) K6)
                | apply (frame_keepL M1 Mi 176 8%nat _ RI ltac:(cbn; lia) K7)].
Qed.

Lemma L_run : forall (M0 : word -> option byte) regs,
  regions_ok SEGS M0 [((s - 192)%Z, 16%Z); RD; RB1; RB2; RS] -> tabs_ok tabval tab38 tab14 M0 -> kcs M0 ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 9 = Z_to_bv 64 bufs1 -> getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 tabval -> getr regs 20 = Z_to_bv 64 tab38 -> getr regs 21 = Z_to_bv 64 tab14 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1b2b4) M0 rom) (mkst regs' (Z_to_bv 64 0x1b650) M' rom)
    /\ rinv RWL M0 M' /\ getr regs' 11 = Z_to_bv 64 cf
    /\ (forall r, In r [2; 3; 4; 9; 18; 19; 20; 21]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 regs RO0 TK0 KC0 H2 H9 H18 H19 H20 H21. geom.
  destruct (RO0 ((s - 192)%Z, 16%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF). destruct (RO0 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1).
  destruct (RO0 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2). destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS).
  destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  pose proof KC0 as (Kw & Kh & Kcf & Kdd & Kwd & Kdt & Kwt).
  (* [comment removed for export] *)
  assert (HYPa : la_hyps s datad datat bufs1 bufs2 w h wplt wpld cf) by (unfold la_hyps; repeat split; first [assumption | lia]).
  destruct (la_1b1b8 rom s datad datat bufs1 bufs2 w h wplt wpld cf HYPa fx regs M0 Kw Kh Kcf Kdd Kwd Kdt Kwt H2 H9 H18)
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_8 & E1_10 & E1_11 & E1_12 & E1_23 & E1_26 & E1_27 & AG1).
  assert (RI1 : rinv RWL M0 m1) by (apply (rinv_cells RWL [] M0 M0 m1 (rinv_refl _ _) FR1); intros c []).
  pose proof (row_bounds wplt 0 h ltac:(lia) ltac:(lia) ltac:(lia)) as PB0.
  destruct (memcpy_step rom M0 m1 r1 bufs2 datat (wplt * 4) bufs2 datat _ _ 111324 (proj1 RI1) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 2%nat 4%nat D; lia) ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs2) bs2) in *.
  assert (RI2 : rinv RWL M0 m2).
  { apply (rinv_wbytes RWL M0 m1 bufs2 (wplt * 4) bs2 RI1 L2); [lia | lia |]. exists (bufs2, 4 * wplt)%Z. split; [unfold RWL, RB2; dl_in0 | cbn [fst snd]; lia]. }
  assert (sokF : forall k, (8 <= k <= 16)%Z -> store_ok SEGS m2 (Z_to_bv 64 (s - 176 - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 m2 (s - 192) _ (s - 176 - k) 8 (proj1 RI2) SOKF); cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; lia. }
  (* [comment removed for export] *)
  assert (MID : exists r5 m3 m5, msteps SEGS (mkst r2 (Z_to_bv 64 0x1b2dc) m2 rom) (mkst r5 (Z_to_bv 64 0x1b510) m5 rom)
                  /\ rinv RWL M0 m3 /\ rinv RW3 m3 m5 /\ rdn SEGS m3 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 (h - 1))
                  /\ exitregs r5 /\ getr r5 8 = Z_to_bv 64 (w - 1) /\ getr r5 3 = getr r2 3 /\ getr r5 4 = getr r2 4).
  { assert (CIF : forall cells, (forall c, In c cells -> c = ((s - 184)%Z, 8%Z) \/ c = ((s - 192)%Z, 8%Z)) -> cells_in RWL cells).
    { intros cells HC c Hc. destruct (HC c Hc) as [-> | ->]; cbn [fst snd]; (split; [lia|]); exists ((s - 192)%Z, 16%Z); (split; [unfold RWL; dl_in0 | cbn [fst snd]; lia]). }
    destruct (Z.eq_dec h 1) as [Hh1|Hh2].
    - assert (HYPb : lb_hyps s w wplt) by (unfold lb_hyps; repeat split; first [assumption | lia]).
      destruct (lb_1b1e0 rom s w wplt HYPb fx r2 m2 ltac:(replace (s - 184)%Z with (s - 176 - 8)%Z by lia; apply sokF; lia)
                  ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3)) as (r3 & m3 & RUN3 & FR3 & E3_8 & E3_10 & E3_11 & SVh & AG3).
      exists r3, m3, m3. split; [exact RUN3|].
      split; [apply (rinv_cells RWL _ M0 m2 m3 RI2 FR3), CIF; intros c [<- | []]; left; reflexivity|]. split; [apply rinv_refl|].
      split; [replace (h - 1)%Z with 0%Z by lia; rewrite <- w2b_Z by lia; exact SVh|].
      split; [unfold exitregs; repeat split; dl_get3|]. split; [exact E3_8|]. split; dl_same.
    - assert (HYPc : lc_hyps s w wplt h) by (unfold lc_hyps; repeat split; first [assumption | lia]).
      destruct (lc_1b1e0 rom s w wplt h HYPc fx r2 m2 ltac:(replace (s - 184)%Z with (s - 176 - 8)%Z by lia; apply sokF; lia)
                  ltac:(replace (s - 192)%Z with (s - 176 - 16)%Z by lia; apply sokF; lia)
                  ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
        as (r3 & m3 & RUN3 & FR3 & E3_8 & E3_10 & E3_11 & E3_22 & E3_25 & SVh & SVw & AG3).
      assert (RI3 : rinv RWL M0 m3).
      { apply (rinv_cells RWL _ M0 m2 m3 RI2 FR3), CIF. intros c [<- | [<- | []]]; [left | right]; reflexivity. }
      assert (KH : rdn SEGS m3 (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 (h - 1))) by (rewrite <- w2b_Z by lia; exact SVh).
      assert (KW : rdn SEGS m3 (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 (w - 1))) by (rewrite <- w2b_Z by lia; exact SVw).
      assert (RO3 : regions_ok SEGS m3 [RD; RB1; RB2; RS]).
      { apply (regions_ok_grows SEGS M0 m3); [|exact (proj1 RI3)]. intros r Hr. apply RO0. right. exact Hr. }
      destruct (row2_loop m3 RO3 (tabs_keep M0 m3 RI3 TK0) (kcs_keepL M0 m3 RI3 KC0) (conj KH KW) (Z.to_nat h) 0%Z r3 m3 ltac:(lia) ltac:(lia) (rinv_refl _ _))
        as (r4 & m4 & RUN4 & RI4 & EX4 & X3 & X4).
      { unfold rowregs. repeat split; dl_get3. }
      destruct (kcs2_keep m3 m4 RI4 (conj KH KW)) as (Kh4 & Kw4).
      assert (HYPx : lx_hyps s (w - 1)) by (unfold lx_hyps; repeat split; first [assumption | lia]).
      destruct EX4 as (Y2 & Y9 & Y18 & Y19 & Y20 & Y21 & Y23 & Y26 & Y27).
      destruct (lx_1b410 rom s (w - 1) HYPx fx r4 m4 Kw4 Y2) as (r5 & m5 & RUN5 & FR5 & E5_8 & AG5).
      exists r5, m3, m5. split; [exact (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))|]. split; [exact RI3|].
      split; [apply (rinv_cells RW3 [] m3 m4 m5 RI4 FR5); intros c []|]. split; [exact KH|].
      split; [unfold exitregs; repeat split; dl_get3|]. split; [exact E5_8|].
      split; [rewrite (AG5 3%bv) by notin_list; rewrite X3 | rewrite (AG5 4%bv) by notin_list; rewrite X4]; dl_same. }
  destruct MID as (r5 & m3 & m5 & RUN5 & RI3 & RI5 & KH & EX5 & E5_8 & X3 & X4).
  destruct EX5 as (Y2 & Y9 & Y18 & Y19 & Y20 & Y21 & Y23 & Y26 & Y27).
  pose proof (kcs_keepL M0 m3 RI3 KC0) as KC3. pose proof (tabs_keep M0 m3 RI3 TK0) as TK3.
  assert (G03 : mem_grows M0 m3) by exact (proj1 RI3).
  (* [comment removed for export] *)
  assert (HYPm : lm_hyps s bufs1 bufs2 wplt) by (unfold lm_hyps; repeat split; first [assumption | lia]).
  destruct (lm_1b414 rom s bufs1 bufs2 wplt HYPm fx r5 m5 Y2 Y9 Y18 Y26) as (r6 & m6 & RUN6 & FR6 & E6_1 & E6_10 & E6_11 & E6_12 & AG6).
  assert (RI6 : rinv RW3 m3 m6) by (apply (rinv_cells RW3 [] m3 m5 m6 RI5 FR6); intros c []).
  destruct (memcpy_step rom M0 m6 r6 bufs1 bufs2 (wplt * 4) bufs1 bufs2 _ _ 111904 (mem_grows_trans _ _ _ G03 (proj1 RI6))
              SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 3%nat 4%nat D; lia)
              ltac:(red; apply bv_eq; reflexivity) E6_1 E6_10 E6_11 E6_12)
    as (r7 & bs7 & RUN7 & L7 & K7).
  set (m7 := wbytes m6 (Z_to_bv 64 bufs1) bs7) in *.
  assert (RI7 : rinv RW3 m3 m7).
  { apply (rinv_wbytes RW3 m3 m6 bufs1 (wplt * 4) bs7 RI6 L7); [lia | lia |]. exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct lrow_facts as (LR1 & LR2 & LR3).
  pose proof (px_geom_row lrow LR1 LR2 LR3) as GPX. pose proof (px_disj_row lrow LR1 LR2) as DPX.
  pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as PR.
  destruct (kcs_keep m3 m7 RI7 KC3) as (Kw7 & Kh7 & Kcf7 & Kdd7 & Kwd7 & Kdt7 & Kwt7).
  pose proof (frame_keep m3 m7 184 8%nat _ RI7 ltac:(cbn; lia) KH) as KH7.
  assert (ROLL : forall Mx, mem_grows M0 Mx -> regions_ok SEGS Mx (R2 lrow bufs1 wplt wpld)).
  { intros Mx GX r Hr. unfold R2 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 Mx datad _ lrow _ GX SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact GX | exact SOK1]. }
  assert (WK : forall Mx My, rinv (R2 lrow bufs1 wplt wpld) Mx My -> rinv RW3 Mx My).
  { intros Mx My RIx. apply (rinv_weaken (R2 lrow bufs1 wplt wpld) RW3 Mx My RIx).
    intros r Hr. unfold R2 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW3, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia]. }
  assert (TKx : forall Mx, rinv RW3 m3 Mx -> tabs_ok tabval tab38 tab14 Mx).
  { intros Mx RIx. apply (tabs_keep m3 Mx); [apply (rinv_incl RW3 RWL m3 Mx RIx RW3_RWL) | exact TK3]. }
  assert (MID2 : exists r9 m9, msteps SEGS (mkst r7 (Z_to_bv 64 0x1b520) m7 rom) (mkst r9 (Z_to_bv 64 0x1b600) m9 rom) /\ rinv RW3 m3 m9
                   /\ getr r9 8 = Z_to_bv 64 (w - 1) /\ getr r9 10 = Z_to_bv 64 lrow /\ getr r9 11 = Z_to_bv 64 cf
                   /\ regs_agree (fun r => In r [5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29]%list) r7 r9).
  { destruct (Z.eq_dec w 1) as [W1|W2].
    - assert (HYPn : ln_hyps s datad bufs1 wpld (h - 1) cf).
      { unfold ln_hyps. replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. repeat split; first [assumption | lia]. }
      destruct (ln_1b424 rom s datad bufs1 wpld (h - 1) cf HYPn fx r7 m7 Kcf7 Kdd7 Kwd7 KH7 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
        as (r8 & m8 & RUN8 & FR8 & E8_8 & E8_10 & E8_11 & E8_12 & AG8).
      exists r8, m8. split; [exact RUN8|]. split; [apply (rinv_cells RW3 [] m3 m7 m8 RI7 FR8); intros c []|].
      split; [rewrite E8_8; f_equal; lia|]. split; [exact E8_10|]. split; [exact E8_11|].
      intros r Hr. apply AG8. intros X. apply Hr. cbn [In] in *. tauto.
    - assert (HYPo : lo_hyps s datad bufs1 wpld (h - 1) cf w).
      { unfold lo_hyps. replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. repeat split; first [assumption | lia]. }
      destruct (lo_1b424 rom s datad bufs1 wpld (h - 1) cf w HYPo fx r7 m7 Kcf7 Kdd7 Kwd7 KH7 ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
        as (r8 & m8 & RUN8 & FR8 & E8_10 & E8_11 & E8_12 & E8_13 & E8_14 & E8_15 & E8_16 & AG8).
      assert (RI8 : rinv RW3 m3 m8) by (apply (rinv_cells RW3 [] m3 m7 m8 RI7 FR8); intros c []).
      destruct (pg_loop rom lrow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld GPX DPX m8 (ROLL m8 (mem_grows_trans _ _ _ G03 (proj1 RI8))) (TKx m8 RI8)
                  (Z.to_nat w) 0%Z r8 m8 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r9 & m9 & RUN9 & RI9 & AG9).
      { unfold f1regs, lrow. repeat split; dl_get3. }
      exists r9, m9. split; [exact (msteps_trans _ _ _ _ RUN8 RUN9)|]. split; [apply (rinv_trans RW3 m3 m8 m9 RI8), WK, RI9|].
      split; [dl_get3|]. split; [unfold lrow; dl_get3|]. split; [dl_get3|]. ra_chain. }
  destruct MID2 as (r9 & m9 & RUN9 & RI9 & E9_8 & E9_10 & E9_11 & AG9).
  (* [comment removed for export] *)
  destruct (pl_run rom lrow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld GPX DPX m9 (ROLL m9 (mem_grows_trans _ _ _ G03 (proj1 RI9))) (TKx m9 RI9) r9 m9 (rinv_refl _ _)
              E9_8 ltac:(dl_get3) E9_10 ltac:(dl_get3)) as (r10 & m10 & RUN10 & RI10 & AG10).
  exists r10, m10. split.
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6
           (msteps_trans _ _ _ _ RUN7 (msteps_trans _ _ _ _ RUN9 RUN10)))))). }
  split.
  { apply (rinv_trans RWL M0 m3 m10 RI3). apply (rinv_incl RW3 RWL m3 m10); [|exact RW3_RWL].
    apply (rinv_trans RW3 m3 m9 m10 RI9), WK, RI10. }
  split; [rewrite (AG10 11%bv) by notin_list; exact E9_11|].
  intros r Hr. cbn [In] in Hr.
  assert (Z3 : getr r10 3 = getr regs 3) by (rewrite (AG10 3%bv) by notin_list; rewrite (AG9 3%bv) by notin_list; rewrite (K7 3%bv ltac:(in_kept)); rewrite (AG6 3%bv) by notin_list; rewrite X3; dl_same).
  assert (Z4 : getr r10 4 = getr regs 4) by (rewrite (AG10 4%bv) by notin_list; rewrite (AG9 4%bv) by notin_list; rewrite (K7 4%bv ltac:(in_kept)); rewrite (AG6 4%bv) by notin_list; rewrite X4; dl_same).
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]; first [exact Z3 | exact Z4 | idtac].
  - rewrite H2. dl_get3.
  - rewrite H9. dl_get3.
  - rewrite H18. dl_get3.
  - rewrite H19. dl_get3.
  - rewrite H20. dl_get3.
  - rewrite H21. dl_get3.
Qed.

End Low2.
