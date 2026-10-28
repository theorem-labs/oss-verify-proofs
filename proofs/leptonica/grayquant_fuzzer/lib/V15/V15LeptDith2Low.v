(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherLib2 DitherTac DitherLoop DitherTab DitherTabLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Kit.
Import V15Kit.V15MemcpyBase. Import V15Kit.V15Memcpy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Dith2Tab V15Dith2Low V15LeptDithBinLow V15LeptDith2.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac dl_get3 :=
  first [ eassumption
        | match goal with H : getr ?R ?r = Z_to_bv 64 ?z' |- getr ?R ?r = Z_to_bv 64 ?z => rewrite H; f_equal; first [lia | ring] end
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_get3 end
        | match goal with K : keeps ?R ?R' |- getr ?R' ?r = _ => rewrite (K r ltac:(in_kept)); dl_get3 end
        | match goal with KP : (forall r0, In r0 _ -> getr ?R' r0 = getr ?R r0) |- getr ?R' ?r = _ => rewrite (KP r ltac:(in_kept)); dl_get3 end ].
Ltac dl_same :=
  first [ reflexivity
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by notin_list; dl_same end
        | match goal with K : keeps ?R ?R' |- getr ?R' ?r = _ => rewrite (K r ltac:(in_kept)); dl_same end
        | match goal with KP : (forall r0, In r0 _ -> getr ?R' r0 = getr ?R r0) |- getr ?R' ?r = _ => rewrite (KP r ltac:(in_kept)); dl_same end ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tables.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (tabval tab38 tab14 : Z).
Hypothesis GT : (4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\ 4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\
                 4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0)%Z.
Definition RT : list (Z * Z) := [(tabval, 1024); (tab38, 1024); (tab14, 1024)]%Z.
Hypothesis GDT : pairwise RT.

Lemma ulh : forall i4, (0 <= i4 <= 1020)%Z -> (i4 mod 4 = 0)%Z -> ul_hyps tabval tab38 tab14 i4.
Proof.
  intros i4 H1 H2. destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3). unfold ul_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GDT 0%nat 1%nat D. exact D.
  - unfold dapart. pw GDT 0%nat 2%nat D. exact D.
  - unfold dapart. pw GDT 1%nat 2%nat D. exact D.
Qed.
Lemma ul_cells_in : forall i4, (0 <= i4 <= 1020)%Z -> cells_in RT (ul_1c7dc_cells_def tabval tab38 tab14 i4).
Proof.
  intros i4 Hi. destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3).
  intros c Hc. unfold ul_1c7dc_cells_def in Hc. cbn [In] in Hc.
  destruct Hc as [<- | [<- | [<- | []]]]; cbn [fst snd]; (split; [lia|]).
  - exists (tabval, 1024%Z). split; [unfold RT; dl_in0 | cbn [fst snd]; lia].
  - exists (tab38, 1024%Z). split; [unfold RT; dl_in0 | cbn [fst snd]; lia].
  - exists (tab14, 1024%Z). split; [unfold RT; dl_in0 | cbn [fst snd]; lia].
Qed.

(* [comment removed for export] *)
Lemma tv_step : forall (Mi m1 : word -> option byte) (k0 : Z) (i : nat) tab, (0 <= k0 <= 255)%Z -> (1 <= i <= 2)%nat -> nth i RT (0, 0)%Z = (tab, 1024%Z) ->
  tab_ok SEGS true tv_ok Mi tab -> mframe (ul_1c7dc_cells_def tabval tab38 tab14 (4 * k0)) Mi m1 ->
  (exists bs, rdn SEGS m1 (Z_to_bv 64 (tab + 4 * k0)) 4 = Some bs /\ tv_ok (rdv true 4 bs)) -> tab_ok SEGS true tv_ok m1 tab.
Proof.
  intros Mi m1 k0 i tab Hk0 Hi E (T0 & T1 & TK) FR NEW. split; [exact T0|]. split; [exact T1|]. intros k Hk.
  destruct (Z.eq_dec k k0) as [->|NE]; [exact NEW|].
  destruct (TK k Hk) as (bs & Rd & Pb). exists bs. split; [|exact Pb]. rewrite <- Rd.
  destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3).
  pw GDT 0%nat 1%nat D01. pw GDT 0%nat 2%nat D02. pw GDT 1%nat 2%nat D12.
  apply (mframe_rdn SEGS _ Mi m1 (tab + 4 * k) 4 FR); [lia | cbn; lia |].
  intros c Hc. unfold ul_1c7dc_cells_def in Hc. cbn [In] in Hc. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct i as [|[|[|i]]]; try lia; cbn [nth RT] in E; injection E as <-;
    (destruct Hc as [<- | [<- | [<- | []]]]; cbn [fst snd]; lia).
Qed.

Definition tregs (regs : bvmap 5 word) (i4 : Z) : Prop :=
  getr regs 1 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 0 /\ getr regs 10 = Z_to_bv 64 i4 /\ getr regs 12 = Z_to_bv 64 1 /\ getr regs 13 = Z_to_bv 64 1 /\
  getr regs 14 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 16 = Z_to_bv 64 0 /\ getr regs 17 = Z_to_bv 64 0 /\
  getr regs 20 = Z_to_bv 64 tabval /\ getr regs 21 = Z_to_bv 64 tab38 /\ getr regs 22 = Z_to_bv 64 tab14 /\ getr regs 27 = Z_to_bv 64 1 /\
  getr regs 28 = Z_to_bv 64 1024.

Lemma tab_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr RT ->
  forall (n : nat) k regs Mi, (256 - k <= Z.of_nat n)%Z -> (0 <= k <= 255)%Z -> rinv RT Mr Mi ->
  tab_ok SEGS true tv_ok Mi tab38 -> tab_ok SEGS true tv_ok Mi tab14 -> tregs regs (4 * k) ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1c8e0) Mi rom) (mkst regs' (Z_to_bv 64 0x1cc94) Mi' rom)
    /\ rinv RT Mr Mi' /\ tab_ok SEGS true tv_ok Mi' tab38 /\ tab_ok SEGS true tv_ok Mi' tab14
    /\ regs_agree (fun r => In r [6; 7; 8; 10; 11; 19; 23; 30; 31]%list) regs regs'.
Proof.
  intros Mr ROr. induction n as [|n IH]; intros k regs Mi Hn Hk RI TK38 TK14 LR; [lia|].
  destruct LR as (H1 & H5 & H10 & H12 & H13 & H14 & H15 & H16 & H17 & H20 & H21 & H22 & H27 & H28).
  assert (Hi4 : (0 <= 4 * k <= 1020)%Z) by lia.
  assert (Al4 : ((4 * k) mod 4 = 0)%Z) by (rewrite Z.mul_comm; apply Z_mod_mult).
  pose proof (ul_cells_in (4 * k) Hi4) as CI.
  pose proof (cells_ok_of SEGS Mr Mi RT _ ROr (proj1 RI) CI) as CK.
  destruct (ul_1c7dc_path rom tabval tab38 tab14 (4 * k) (ulh _ Hi4 Al4) fx regs Mi CK H1 H5 H10 H12 H13 H14 H15 H16 H17 H20 H21 H22 H27 H28)
    as (r1 & m1 & RUN1 & FR1 & NEW38 & NEW14 & E10 & AG1).
  pose proof (rinv_cells RT _ Mr Mi m1 RI FR1 CI) as RI1.
  pose proof (tv_step Mi m1 k 1%nat tab38 Hk ltac:(lia) eq_refl TK38 FR1 NEW38) as TK38'.
  pose proof (tv_step Mi m1 k 2%nat tab14 Hk ltac:(lia) eq_refl TK14 FR1 NEW14) as TK14'.
  assert (CI0 : cells_in RT []) by (intros c []).
  destruct (Z_lt_ge_dec (k + 1) 256) as [LT|GE].
  - destruct (ul_1c7d8f rom tabval tab38 tab14 (4 * k) (ulh _ Hi4 Al4) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RT _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    assert (EQ2 : forall tab, tab_ok SEGS true tv_ok m1 tab -> tab_ok SEGS true tv_ok m2 tab).
    { intros tab (T0 & T1 & TK). split; [exact T0|]. split; [exact T1|]. intros k' Hk'. destruct (TK k' Hk') as (bs & Rd & Pb). exists bs. split; [|exact Pb].
      rewrite <- Rd. apply (mframe_rdn SEGS [] m1 m2 _ 4 FR2); [lia | cbn; lia | intros c []]. }
    destruct (IH (k + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2 (EQ2 _ TK38') (EQ2 _ TK14')) as (r3 & m3 & RUN3 & RI3 & T38'' & T14'' & AG3).
    { unfold tregs. repeat split; dl_get3. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3|]. split; [exact T38''|]. split; [exact T14'' | ra_chain].
  - destruct (ul_1c7d8t rom tabval tab38 tab14 (4 * k) (ulh _ Hi4 Al4) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells RT _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    assert (EQ2 : forall tab, tab_ok SEGS true tv_ok m1 tab -> tab_ok SEGS true tv_ok m2 tab).
    { intros tab (T0 & T1 & TK). split; [exact T0|]. split; [exact T1|]. intros k' Hk'. destruct (TK k' Hk') as (bs & Rd & Pb). exists bs. split; [|exact Pb].
      rewrite <- Rd. apply (mframe_rdn SEGS [] m1 m2 _ 4 FR2); [lia | cbn; lia | intros c []]. }
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|]. split; [exact (EQ2 _ TK38')|]. split; [exact (EQ2 _ TK14') | ra_chain].
Qed.

Lemma T_run : forall (M0 : word -> option byte) regs, regions_ok SEGS M0 RT ->
  tab_ok SEGS true tv_ok M0 tab38 -> tab_ok SEGS true tv_ok M0 tab14 ->
  getr regs 20 = Z_to_bv 64 tabval -> getr regs 21 = Z_to_bv 64 tab38 -> getr regs 22 = Z_to_bv 64 tab14 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1c860) M0 rom) (mkst regs' (Z_to_bv 64 0x1cc94) M' rom)
    /\ rinv RT M0 M' /\ tab_ok SEGS true tv_ok M' tab38 /\ tab_ok SEGS true tv_ok M' tab14
    /\ regs_agree (fun r => In r [1; 5; 6; 7; 8; 10; 11; 12; 13; 14; 15; 16; 17; 19; 23; 24; 27; 28; 29; 30; 31]%list) regs regs'.
Proof.
  intros M0 regs RO TK38 TK14 H20 H21 H22. destruct GT as (A1 & A2 & A3 & B1 & B2 & B3 & C1 & C2 & C3).
  assert (HYPi : ui_hyps tabval tab38 tab14) by (unfold ui_hyps; repeat split; first [assumption | lia]).
  destruct (ui_1c75c rom tabval tab38 tab14 HYPi fx regs M0 H20 H21 H22)
    as (r1 & m1 & RUN1 & FR1 & E1 & E5 & E6 & E7 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E19 & E27 & E28 & E29 & E30 & E31 & AG1).
  assert (RI1 : rinv RT M0 m1) by (apply (rinv_cells RT [] M0 M0 m1 (rinv_refl _ _) FR1); intros c []).
  assert (EQ1 : forall tab, tab_ok SEGS true tv_ok M0 tab -> tab_ok SEGS true tv_ok m1 tab).
  { intros tab (T0 & T1 & TK). split; [exact T0|]. split; [exact T1|]. intros k' Hk'. destruct (TK k' Hk') as (bs & Rd & Pb). exists bs. split; [|exact Pb].
    rewrite <- Rd. apply (mframe_rdn SEGS [] M0 m1 _ 4 FR1); [lia | cbn; lia | intros c []]. }
  destruct (tab_loop M0 RO 256%nat 0%Z r1 m1 ltac:(lia) ltac:(lia) RI1 (EQ1 _ TK38) (EQ1 _ TK14)) as (r2 & m2 & RUN2 & RI2 & T38 & T14 & AG2).
  { unfold tregs. repeat split; dl_get3. }
  exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2|]. split; [exact T38|]. split; [exact T14 | ra_chain].
Qed.
End Tables.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Low2.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (s datad w h wpld datat wplt bufs1 bufs2 tabval tab38 tab14 : Z).
Definition low2_geom : Prop :=
  (4096 <= s - 288 /\ s <= 2 ^ 47 /\ s mod 16 = 0 /\
   4096 <= datad /\ datad + 4 * (wpld * h) < 2 ^ 47 /\ datad mod 4 = 0 /\ 4096 <= datat /\ datat + 4 * (wplt * h) < 2 ^ 47 /\ datat mod 4 = 0 /\
   4096 <= bufs1 /\ bufs1 + 4 * wplt < 2 ^ 47 /\ bufs1 mod 4 = 0 /\ 4096 <= bufs2 /\ bufs2 + 4 * wplt < 2 ^ 47 /\ bufs2 mod 4 = 0 /\
   4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\ 4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\
   4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0 /\
   1 <= w <= 20000 /\ 1 <= h <= 20000 /\ 1 <= wplt <= 5000 /\ 1 <= wpld <= 1250 /\ w <= 4 * wplt /\ w <= 16 * wpld /\
   wplt * h <= 2 ^ 24 /\ wpld * h <= 2 ^ 24)%Z.
(* [comment removed for export] *)
Definition LWL : list (Z * Z) :=
  [(s - 288, 288); (datad, 4 * (wpld * h)); (datat, 4 * (wplt * h)); (bufs1, 4 * wplt); (bufs2, 4 * wplt); (tabval, 1024); (tab38, 1024); (tab14, 1024)]%Z.
Definition low2_disj : Prop := pairwise LWL.
Hypothesis G : low2_geom.
Hypothesis GD : low2_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gd0 & Gd1 & ALd & Gt0 & Gt1 & ALt & Gb10 & Gb11 & ALb1 & Gb20 & Gb21 & ALb2 & Gv0 & Gv1 & ALv & G80 & G81 & AL8 & G40 & G41 & AL4
                                 & Gw & Gh & Gwplt & Gwpld & Gw4 & Gw16 & Gth & Gdh).

Definition RD : Z * Z := (datad, 4 * (wpld * h))%Z.
Definition RS : Z * Z := (datat, 4 * (wplt * h))%Z.
Definition RB1 : Z * Z := (bufs1, 4 * wplt)%Z.
Definition RB2 : Z * Z := (bufs2, 4 * wplt)%Z.
(* [comment removed for export] *)
Definition RW3 : list (Z * Z) := [((s - 288)%Z, 80%Z); RD; RB1; RB2].
(* [comment removed for export] *)
Definition RWL : list (Z * Z) := [((s - 288)%Z, 80%Z); ((s - 200)%Z, 16%Z); ((s - 176)%Z, 8%Z); RD; RB1; RB2].
Lemma RW3_RWL : forall r, In r RW3 -> In r RWL.
Proof. intros r Hr. unfold RW3, RWL in *. cbn [In] in *. tauto. Qed.

(* [comment removed for export] *)
Definition kcs (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) /\ rdn SEGS M (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) /\
  rdn SEGS M (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) /\ rdn SEGS M (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) /\
  rdn SEGS M (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld).
(* [comment removed for export] *)
Definition kcs3 (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) /\ rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) /\
  rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 (h - 1)).

(* [comment removed for export] *)
Lemma frame_keep : forall (M1 Mi : word -> option byte) (k : Z) (n : nat) v, rinv RW3 M1 Mi -> (Z.of_nat n <= k <= 208)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) n = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) n = Some v.
Proof.
  intros M1 Mi k n v RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RW3 M1 Mi (s - k) n RI); [lia | lia |].
  intros r Hr. unfold RW3 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd].
  - lia.
  - pw GD 0%nat 1%nat D. lia.
  - pw GD 0%nat 3%nat D. lia.
  - pw GD 0%nat 4%nat D. lia.
Qed.
Lemma kcs_keep : forall (M1 Mi : word -> option byte), rinv RW3 M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3 & K4 & K5). unfold kcs.
  repeat split; [apply (frame_keep M1 Mi 108 4%nat _ RI ltac:(cbn; lia) K1) | apply (frame_keep M1 Mi 112 4%nat _ RI ltac:(cbn; lia) K2)
                | apply (frame_keep M1 Mi 152 8%nat _ RI ltac:(cbn; lia) K3) | apply (frame_keep M1 Mi 160 8%nat _ RI ltac:(cbn; lia) K4)
                | apply (frame_keep M1 Mi 168 8%nat _ RI ltac:(cbn; lia) K5)].
Qed.
Lemma kcs3_keep : forall (M1 Mi : word -> option byte), rinv RW3 M1 Mi -> kcs3 M1 -> kcs3 Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3). unfold kcs3.
  repeat split; [apply (frame_keep M1 Mi 176 8%nat _ RI ltac:(cbn; lia) K1) | apply (frame_keep M1 Mi 192 8%nat _ RI ltac:(cbn; lia) K2)
                | apply (frame_keep M1 Mi 200 8%nat _ RI ltac:(cbn; lia) K3)].
Qed.
(* [comment removed for export] *)
Lemma frame_keepL : forall (M1 Mi : word -> option byte) (k : Z) (n : nat) v, rinv RWL M1 Mi -> (Z.of_nat n <= k <= 168)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) n = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) n = Some v.
Proof.
  intros M1 Mi k n v RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RWL M1 Mi (s - k) n RI); [lia | lia |].
  intros r Hr. unfold RWL in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; unfold RD, RB1, RB2; cbn [fst snd].
  - lia.
  - lia.
  - lia.
  - pw GD 0%nat 1%nat D. lia.
  - pw GD 0%nat 3%nat D. lia.
  - pw GD 0%nat 4%nat D. lia.
Qed.
Lemma kcs_keepL : forall (M1 Mi : word -> option byte), rinv RWL M1 Mi -> kcs M1 -> kcs Mi.
Proof.
  intros M1 Mi RI (K1 & K2 & K3 & K4 & K5). unfold kcs.
  repeat split; [apply (frame_keepL M1 Mi 108 4%nat _ RI ltac:(cbn; lia) K1) | apply (frame_keepL M1 Mi 112 4%nat _ RI ltac:(cbn; lia) K2)
                | apply (frame_keepL M1 Mi 152 8%nat _ RI ltac:(cbn; lia) K3) | apply (frame_keepL M1 Mi 160 8%nat _ RI ltac:(cbn; lia) K4)
                | apply (frame_keepL M1 Mi 168 8%nat _ RI ltac:(cbn; lia) K5)].
Qed.

(* [comment removed for export] *)
Lemma tabs_keepL : forall (M1 Mi : word -> option byte), rinv RWL M1 Mi -> tabs_ok tabval tab38 tab14 M1 -> tabs_ok tabval tab38 tab14 Mi.
Proof.
  intros M1 Mi RI (T0 & T38 & T14). geom. unfold tabs_ok.
  split; [|split]; (eapply (tab_ok_rinv SEGS _ _ RWL M1 Mi); [eassumption | exact RI |]);
    intros r Hr; unfold RWL in Hr; cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; unfold RD, RB1, RB2; cbn [fst snd].
  - pw GD 0%nat 5%nat D. lia.
  - pw GD 0%nat 5%nat D. lia.
  - pw GD 0%nat 5%nat D. lia.
  - pw GD 1%nat 5%nat D. lia.
  - pw GD 3%nat 5%nat D. lia.
  - pw GD 4%nat 5%nat D. lia.
  - pw GD 0%nat 6%nat D. lia.
  - pw GD 0%nat 6%nat D. lia.
  - pw GD 0%nat 6%nat D. lia.
  - pw GD 1%nat 6%nat D. lia.
  - pw GD 3%nat 6%nat D. lia.
  - pw GD 4%nat 6%nat D. lia.
  - pw GD 0%nat 7%nat D. lia.
  - pw GD 0%nat 7%nat D. lia.
  - pw GD 0%nat 7%nat D. lia.
  - pw GD 1%nat 7%nat D. lia.
  - pw GD 3%nat 7%nat D. lia.
  - pw GD 4%nat 7%nat D. lia.
Qed.

(* [comment removed for export] *)
Lemma ll2_geom_row : forall drow, (datad <= drow)%Z -> (drow + 4 * wpld <= datad + 4 * (wpld * h))%Z -> (drow mod 4 = 0)%Z ->
  ll2_geom (s - 208) drow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld.
Proof.
  intros drow H1 H2 H3. geom. unfold ll2_geom. repeat split; first [assumption | lia | (apply al16_sub; [assumption | reflexivity])].
Qed.
Lemma ll2_disj_row : forall drow, (datad <= drow)%Z -> (drow + 4 * wpld <= datad + 4 * (wpld * h))%Z ->
  ll2_disj (s - 208) drow bufs1 bufs2 tabval tab38 tab14 wplt wpld.
Proof.
  intros drow H1 H2. geom. unfold ll2_disj, LL2L. cbn [pairwise]. repeat split; try exact I;
    intros r' Hr'; cbn [In] in Hr'; repeat (destruct Hr' as [<- | Hr']; [unfold apart2; cbn [fst snd] |]); try (destruct Hr').
  - pw GD 0%nat 1%nat D. lia.
  - pw GD 0%nat 3%nat D. lia.
  - pw GD 0%nat 4%nat D. lia.
  - pw GD 0%nat 5%nat D. lia.
  - pw GD 0%nat 6%nat D. lia.
  - pw GD 0%nat 7%nat D. lia.
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
Definition rowregs (regs : bvmap 5 word) (i1 : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 208) /\ getr regs 8 = Z_to_bv 64 h /\ getr regs 9 = Z_to_bv 64 bufs1 /\ getr regs 18 = Z_to_bv 64 bufs2 /\
  getr regs 19 = Z_to_bv 64 1 /\ getr regs 20 = Z_to_bv 64 tabval /\ getr regs 21 = Z_to_bv 64 tab38 /\ getr regs 22 = Z_to_bv 64 tab14 /\
  getr regs 23 = Z_to_bv 64 i1 /\ getr regs 24 = Z_to_bv 64 1 /\ getr regs 25 = Z_to_bv 64 datad /\ getr regs 26 = Z_to_bv 64 datat /\
  getr regs 27 = Z_to_bv 64 (wplt * 4).
Definition exitregs (regs : bvmap 5 word) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 208) /\ getr regs 9 = Z_to_bv 64 bufs1 /\ getr regs 18 = Z_to_bv 64 bufs2 /\
  getr regs 20 = Z_to_bv 64 tabval /\ getr regs 21 = Z_to_bv 64 tab38 /\ getr regs 22 = Z_to_bv 64 tab14 /\
  getr regs 25 = Z_to_bv 64 datad /\ getr regs 27 = Z_to_bv 64 (wplt * 4).

Lemma row2_loop : forall (M3 : word -> option byte), regions_ok SEGS M3 [((s - 288)%Z, 80%Z); RD; RB1; RB2; RS] -> tabs_ok tabval tab38 tab14 M3 ->
  kcs M3 -> kcs3 M3 ->
  forall (n : nat) i1 regs Mi, (h - i1 <= Z.of_nat n)%Z -> (1 <= i1 <= h - 1)%Z -> rinv RW3 M3 Mi -> rowregs regs i1 ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1cd08) Mi rom) (mkst regs' (Z_to_bv 64 0x1cddc) Mi' rom)
    /\ rinv RW3 M3 Mi' /\ exitregs regs' /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros M3 RO3 TK3 KC3 KD3. geom. induction n as [|n IH]; intros i1 regs Mi Hn Hi RI LR; [lia|].
  destruct LR as (H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27).
  pose proof (row_bounds wpld (i1 - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as P1.
  pose proof (row_bounds wplt i1 h ltac:(lia) ltac:(lia) ltac:(lia)) as P2.
  assert (HYPr : ur_hyps s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1).
  { unfold ur_hyps. replace (i1 * wplt)%Z with (wplt * i1)%Z by ring. replace ((i1 - 1) * wpld)%Z with (wpld * (i1 - 1))%Z by ring.
    repeat split; first [assumption | lia]. }
  remember (datat + 4 * (wplt * i1))%Z as srow eqn:Esr. remember (datad + 4 * (wpld * (i1 - 1)))%Z as drow eqn:Edr.
  assert (Rsr : (datat <= srow /\ srow + 4 * wplt <= datat + 4 * (wplt * h))%Z) by lia.
  assert (Rdr : (datad <= drow /\ drow + 4 * wpld <= datad + 4 * (wpld * h))%Z) by lia.
  assert (ALdr : (drow mod 4 = 0)%Z) by (subst drow; apply al4_add; exact ALd).
  assert (Esr' : (datat + 4 * (i1 * wplt))%Z = srow) by (subst srow; ring).
  assert (Edr' : (datad + 4 * ((i1 - 1) * wpld))%Z = drow) by (subst drow; ring).
  clear P1 P2 Esr Edr.
  destruct (RO3 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1). destruct (RO3 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2).
  destruct (RO3 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS). destruct (RO3 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  destruct (RO3 ((s - 288)%Z, 80%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  (* [comment removed for export] *)
  destruct (kcs_keep M3 Mi RI KC3) as (Kw & Kh & Kwt & Kdt & Kwd). destruct (kcs3_keep M3 Mi RI KD3) as (Kw3 & Kz3 & Kh3).
  destruct (ur_1cc04 rom s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 HYPr fx regs Mi Kwt Kdt Kwd Kw3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27)
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_10 & E1_11 & E1_12 & AG1).
  assert (RI1 : rinv RW3 M3 m1) by (apply (rinv_cells RW3 [] M3 Mi m1 RI FR1); intros c []).
  destruct (memcpy_step rom M3 m1 r1 bufs1 bufs2 (wplt * 4) bufs1 bufs2 _ _ 118040 (proj1 RI1) SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 3%nat 4%nat D; lia) ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs1) bs2) in *.
  assert (RI2 : rinv RW3 M3 m2).
  { apply (rinv_wbytes RW3 M3 m1 bufs1 (wplt * 4) bs2 RI1 L2); [lia | lia |]. exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M3 m2 RI2 KC3) as (Kwb & Khb & Kwtb & Kdtb & Kwdb). destruct (kcs3_keep M3 m2 RI2 KD3) as (Kw3b & Kz3b & Kh3b).
  destruct (ur_1cc14 rom s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 HYPr fx r2 m2 Kwtb Kdtb Kwdb Kw3b
              ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
    as (r3 & m3 & RUN3 & FR3 & E3_1 & E3_9 & E3_10 & E3_11 & E3_12 & E3_25 & E3_26 & AG3).
  rewrite Esr' in E3_11.
  assert (RI3 : rinv RW3 M3 m3) by (apply (rinv_cells RW3 [] M3 m2 m3 RI2 FR3); intros c []).
  destruct (memcpy_step rom M3 m3 r3 bufs2 srow (wplt * 4) bufs2 datat _ _ 118128 (proj1 RI3) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 2%nat 4%nat D; lia) ltac:(red; apply bv_eq; reflexivity) E3_1 E3_10 E3_11 E3_12)
    as (r4 & bs4 & RUN4 & L4 & K4).
  set (m4 := wbytes m3 (Z_to_bv 64 bufs2) bs4) in *.
  assert (RI4 : rinv RW3 M3 m4).
  { apply (rinv_wbytes RW3 M3 m3 bufs2 (wplt * 4) bs4 RI3 L4); [lia | lia |]. exists (bufs2, 4 * wplt)%Z. split; [unfold RW3, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M3 m4 RI4 KC3) as (Kwc & Khc & Kwtc & Kdtc & Kwdc). destruct (kcs3_keep M3 m4 RI4 KD3) as (Kw3c & Kz3c & Kh3c).
  destruct (ur_1cc6c rom s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 HYPr fx r4 m4 Kwtc Kdtc Kwdc Kw3c
              ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
    as (r5 & m5 & RUN5 & FR5 & E5_1 & E5_9 & E5_10 & E5_11 & E5_12 & E5_13 & E5_14 & E5_15 & E5_16 & E5_17 & E5_25 & E5_26 & AG5).
  rewrite Edr' in E5_10.
  assert (RI5 : rinv RW3 M3 m5) by (apply (rinv_cells RW3 [] M3 m4 m5 RI4 FR5); intros c []).
  pose proof (ll2_geom_row drow ltac:(lia) ltac:(lia) ALdr) as GLL. pose proof (ll2_disj_row drow ltac:(lia) ltac:(lia)) as GDL.
  assert (ROLL : regions_ok SEGS m5 (R3 drow bufs1 bufs2 wplt wpld)).
  { intros r Hr. unfold R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M3 m5 datad _ drow _ (proj1 RI5) SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact (proj1 RI5) | exact SOK1].
    - repeat split; try lia. eapply store_ok_mono; [exact (proj1 RI5) | exact SOK2]. }
  destruct (d2ll0_run rom (s - 208) drow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld GLL GDL m5 ROLL
              (tabs_keepL M3 m5 (rinv_incl RW3 RWL M3 m5 RI5 RW3_RWL) TK3) r5 (Z_to_bv 64 118228) ltac:(red; apply bv_eq; reflexivity)
              ltac:(replace (s - 208 - 80)%Z with (s - 288)%Z by lia; eapply store_ok_mono; [exact (proj1 RI5) | exact SOKF])
              ltac:(dl_get3) E5_1 E5_10 ltac:(dl_get3) E5_12 E5_13 E5_14 E5_15 E5_16 E5_17)
    as (r6 & m6 & RUN6 & RI6 & X2 & KS6 & KP6).
  assert (RI6' : rinv RW3 M3 m6).
  { apply (rinv_trans RW3 M3 m5 m6 RI5). apply (rinv_weaken (R4 (s - 208) drow bufs1 bufs2 wplt wpld) RW3 m5 m6 RI6).
    intros r Hr. unfold R4, R3 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd].
    - exists ((s - 288)%Z, 80%Z). split; [unfold RW3; dl_in0 | cbn [fst snd]; lia].
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RW3, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs2, 4 * wplt)%Z. split; [unfold RW3, RB2; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep M3 m6 RI6' KC3) as (Kwd_ & Khd & Kwtd & Kdtd & Kwdd). destruct (kcs3_keep M3 m6 RI6' KD3) as (Kw3d & Kz3d & Kh3d).
  destruct (ur_1ccd0 rom s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 HYPr fx r6 m6 Kwtd Kdtd Kwdd Kw3d
              ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
    as (r7 & m7 & RUN7 & FR7 & E7_23 & AG7).
  assert (RI7 : rinv RW3 M3 m7) by (apply (rinv_cells RW3 [] M3 m6 m7 RI6' FR7); intros c []).
  destruct (kcs_keep M3 m7 RI7 KC3) as (Kwe & Khe & Kwte & Kdte & Kwde). destruct (kcs3_keep M3 m7 RI7 KD3) as (Kw3e & Kz3e & Kh3e).
  assert (CHAIN : msteps SEGS (mkst regs (Z_to_bv 64 0x1cd08) Mi rom) (mkst r7 (Z_to_bv 64 0x1cdd8) m7 rom)).
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4
           (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6 RUN7)))))). }
  destruct (Z_lt_ge_dec (i1 + 1) h) as [LT|GE].
  - destruct (ur_1ccd4t rom s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 HYPr fx r7 m7 ltac:(ex_br) Kwte Kdte Kwde Kw3e
                ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
      as (r8 & m8 & RUN8 & FR8 & AG8).
    assert (RI8 : rinv RW3 M3 m8) by (apply (rinv_cells RW3 [] M3 m7 m8 RI7 FR8); intros c []).
    destruct (IH (i1 + 1)%Z r8 m8 ltac:(lia) ltac:(lia) RI8) as (r9 & m9 & RUN9 & RI9 & EX9 & X3 & X4).
    { unfold rowregs. repeat split; dl_get3. }
    exists r9, m9. split; [exact (msteps_trans _ _ _ _ CHAIN (msteps_trans _ _ _ _ RUN8 RUN9))|]. split; [exact RI9|]. split; [exact EX9|].
    split; [rewrite X3 | rewrite X4]; dl_same.
  - destruct (ur_1ccd4f rom s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 HYPr fx r7 m7 ltac:(ex_br) Kwte Kdte Kwde Kw3e
                ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
      as (r8 & m8 & RUN8 & FR8 & AG8).
    assert (RI8 : rinv RW3 M3 m8) by (apply (rinv_cells RW3 [] M3 m7 m8 RI7 FR8); intros c []).
    exists r8, m8. split; [exact (msteps_trans _ _ _ _ CHAIN RUN8)|]. split; [exact RI8|].
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

Lemma L_run : forall (M0 : word -> option byte) regs,
  regions_ok SEGS M0 [((s - 288)%Z, 80%Z); ((s - 200)%Z, 16%Z); ((s - 176)%Z, 8%Z); RD; RB1; RB2; RS] -> tabs_ok tabval tab38 tab14 M0 -> kcs M0 ->
  getr regs 2 = Z_to_bv 64 (s - 208) -> getr regs 9 = Z_to_bv 64 bufs1 -> getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 20 = Z_to_bv 64 tabval -> getr regs 21 = Z_to_bv 64 tab38 -> getr regs 22 = Z_to_bv 64 tab14 -> getr regs 25 = Z_to_bv 64 datad ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1cc94) M0 rom) (mkst regs' (Z_to_bv 64 0x1ce54) M' rom)
    /\ rinv RWL M0 M' /\ (forall r, In r [2; 3; 4; 9; 18; 20; 21; 22; 25]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 regs RO0 TK0 KC0 H2 H9 H18 H20 H21 H22 H25. geom.
  destruct (RO0 ((s - 288)%Z, 80%Z) ltac:(dl_in0)) as (Fa & Fb & Fc & SOKF). destruct (RO0 ((s - 200)%Z, 16%Z) ltac:(dl_in0)) as (Ga & Gb & Gc & SOKG).
  destruct (RO0 ((s - 176)%Z, 8%Z) ltac:(dl_in0)) as (Ha & Hb & Hc & SOKH).
  destruct (RO0 RB1 ltac:(dl_in0)) as (B1a & B1b & B1c & SOK1). destruct (RO0 RB2 ltac:(dl_in0)) as (B2a & B2b & B2c & SOK2).
  destruct (RO0 RS ltac:(dl_in0)) as (Sa & Sb & Sc & SOKS). destruct (RO0 RD ltac:(dl_in0)) as (Da & Db & Dc & SOKD).
  unfold RB1, RB2, RS, RD in *. cbn [fst snd] in *.
  pose proof KC0 as (Kw & Kh & Kwt & Kdt & Kwd).
  (* [comment removed for export] *)
  assert (HYPa : ua_hyps s datad datat bufs1 bufs2 w h wplt) by (unfold ua_hyps; repeat split; first [assumption | lia]).
  destruct (ua_1cb90 rom s datad datat bufs1 bufs2 w h wplt HYPa fx regs M0 SOKH Kw Kh Kwt Kdt H2 H9 H18 H25)
    as (r1 & m1 & RUN1 & FR1 & E1_1 & E1_8 & E1_10 & E1_11 & E1_12 & E1_26 & E1_27 & SVw & AG1).
  assert (RI1 : rinv RWL M0 m1).
  { apply (rinv_cells RWL _ M0 M0 m1 (rinv_refl _ _) FR1). intros c [<- | []]. cbn [fst snd]. split; [lia|]. exists ((s - 176)%Z, 8%Z). split; [unfold RWL; dl_in0 | cbn [fst snd]; lia]. }
  pose proof (row_bounds wplt 0 h ltac:(lia) ltac:(lia) ltac:(lia)) as PB0.
  destruct (memcpy_step rom M0 m1 r1 bufs2 datat (wplt * 4) bufs2 datat _ _ 117980 (proj1 RI1) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              SOKS ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 2%nat 4%nat D; lia) ltac:(red; apply bv_eq; reflexivity) E1_1 E1_10 E1_11 E1_12)
    as (r2 & bs2 & RUN2 & L2 & K2).
  set (m2 := wbytes m1 (Z_to_bv 64 bufs2) bs2) in *.
  assert (RI12 : rinv [RB2] m1 m2).
  { apply (rinv_wbytes [RB2] m1 m1 bufs2 (wplt * 4) bs2 (rinv_refl _ _) L2); [lia | lia |]. exists (bufs2, 4 * wplt)%Z. split; [unfold RB2; dl_in0 | cbn [fst snd]; lia]. }
  assert (RI2 : rinv RWL M0 m2).
  { apply (rinv_trans RWL M0 m1 m2 RI1). apply (rinv_incl [RB2] RWL m1 m2 RI12). intros r [<- | []]. unfold RWL, RB2. dl_in0. }
  assert (KW2 : rdn SEGS m2 (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w)).
  { rewrite <- w2b_Z by lia. rewrite <- SVw. apply (rinv_rdn SEGS [RB2] m1 m2 (s - 176) 8 RI12); [lia | cbn; lia |].
    intros r [<- | []]. unfold RB2. cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]. pw GD 0%nat 4%nat D. lia. }
  assert (sokG : forall k, (k = 192 \/ k = 200)%Z -> store_ok SEGS m2 (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 m2 (s - 200) _ (s - k) 8 (proj1 RI2) SOKG); cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; lia. }
  assert (CIG : cells_in RWL [((s - 192)%Z, 8%Z); ((s - 200)%Z, 8%Z)]).
  { intros c [<- | [<- | []]]; cbn [fst snd]; (split; [lia|]); exists ((s - 200)%Z, 16%Z); (split; [unfold RWL; dl_in0 | cbn [fst snd]; lia]). }
  (* [comment removed for export] *)
  assert (MID : exists r5 m3 m5, msteps SEGS (mkst r2 (Z_to_bv 64 0x1ccdc) m2 rom) (mkst r5 (Z_to_bv 64 0x1cddc) m5 rom)
                  /\ rinv RWL M0 m3 /\ rinv RW3 m3 m5 /\ kcs3 m3 /\ exitregs r5 /\ getr r5 3 = getr r2 3 /\ getr r5 4 = getr r2 4).
  { assert (KW3 : forall m3, mframe [((s - 192)%Z, 8%Z); ((s - 200)%Z, 8%Z)] m2 m3 -> rdn SEGS m3 (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w)).
    { intros m3 FR3. rewrite <- KW2. apply (mframe_rdn SEGS _ m2 m3 (s - 176) 8 FR3); [lia | cbn; lia |].
      intros c [<- | [<- | []]]; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    destruct (Z.eq_dec h 1) as [Hh1|Hh2].
    - assert (HYPb : ub_hyps s datad datat bufs1) by (unfold ub_hyps; repeat split; first [assumption | lia]).
      destruct (ub_1cbd8 rom s datad datat bufs1 HYPb fx r2 m2 (sokG 192%Z ltac:(lia)) (sokG 200%Z ltac:(lia))
                  ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3)) as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & SVz & SVh & AG3).
      exists r3, m3, m3. split; [exact RUN3|]. split; [exact (rinv_cells RWL _ M0 m2 m3 RI2 FR3 CIG)|]. split; [apply rinv_refl|].
      split; [unfold kcs3; split; [exact (KW3 m3 FR3)|]; split; [rewrite <- w2b_Z by lia; exact SVz | replace (h - 1)%Z with 0%Z by lia; rewrite <- w2b_Z by lia; exact SVh]|].
      split; [unfold exitregs; repeat split; dl_get3|]. split; dl_same.
    - assert (HYPc : uc_hyps s datad datat bufs1 h) by (unfold uc_hyps; repeat split; first [assumption | lia]).
      destruct (uc_1cbd8 rom s datad datat bufs1 h HYPc fx r2 m2 (sokG 192%Z ltac:(lia)) (sokG 200%Z ltac:(lia))
                  ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
        as (r3 & m3 & RUN3 & FR3 & E3_10 & E3_11 & E3_19 & E3_23 & E3_24 & SVz & SVh & AG3).
      assert (RI3 : rinv RWL M0 m3) by exact (rinv_cells RWL _ M0 m2 m3 RI2 FR3 CIG).
      assert (KD3 : kcs3 m3).
      { unfold kcs3. split; [exact (KW3 m3 FR3)|]. split; rewrite <- w2b_Z by lia; assumption. }
      assert (RO3 : regions_ok SEGS m3 [((s - 288)%Z, 80%Z); RD; RB1; RB2; RS]).
      { apply (regions_ok_grows SEGS M0 m3); [|exact (proj1 RI3)]. intros r Hr. apply RO0. cbn [In] in *. tauto. }
      destruct (row2_loop m3 RO3 (tabs_keepL M0 m3 RI3 TK0) (kcs_keepL M0 m3 RI3 KC0) KD3 (Z.to_nat h) 1%Z r3 m3 ltac:(lia) ltac:(lia) (rinv_refl _ _))
        as (r4 & m4 & RUN4 & RI4 & EX4 & X3 & X4).
      { unfold rowregs. repeat split; dl_get3. }
      exists r4, m3, m4. split; [exact (msteps_trans _ _ _ _ RUN3 RUN4)|]. split; [exact RI3|]. split; [exact RI4|]. split; [exact KD3|].
      split; [exact EX4|]. split; [rewrite X3 | rewrite X4]; dl_same. }
  destruct MID as (r5 & m3 & m5 & RUN5 & RI3 & RI5 & KD3 & EX5 & X3 & X4).
  destruct EX5 as (Y2 & Y9 & Y18 & Y20 & Y21 & Y22 & Y25 & Y27).
  pose proof (kcs_keepL M0 m3 RI3 KC0) as KC3. pose proof (tabs_keepL M0 m3 RI3 TK0) as TK3.
  assert (G03 : mem_grows M0 m3) by exact (proj1 RI3).
  (* [comment removed for export] *)
  pose proof (row_bounds wpld (h - 1) h ltac:(lia) ltac:(lia) ltac:(lia)) as PR.
  assert (HYPx : ux_hyps s datad bufs1 bufs2 tabval tab38 tab14 w wplt wpld (h - 1)).
  { unfold ux_hyps. replace ((h - 1) * wpld)%Z with (wpld * (h - 1))%Z by ring. repeat split; first [assumption | lia]. }
  destruct (kcs_keep m3 m5 RI5 KC3) as (Kw5 & Kh5 & Kwt5 & Kdt5 & Kwd5). destruct (kcs3_keep m3 m5 RI5 KD3) as (Kw35 & Kz35 & Kh35).
  destruct (ux_1ccd8 rom s datad bufs1 bufs2 tabval tab38 tab14 w wplt wpld (h - 1) HYPx fx r5 m5 Kwd5 Kw35 Kz35 Kh35 Y2 Y9 Y18 Y20 Y21 Y22 Y25 Y27)
    as (r6 & m6 & RUN6 & FR6 & E6_1 & E6_10 & E6_11 & E6_12 & AG6).
  assert (RI6 : rinv RW3 m3 m6) by (apply (rinv_cells RW3 [] m3 m5 m6 RI5 FR6); intros c []).
  destruct (memcpy_step rom M0 m6 r6 bufs1 bufs2 (wplt * 4) bufs1 bufs2 _ _ 118260 (mem_grows_trans _ _ _ G03 (proj1 RI6))
              SOK1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(pw GD 3%nat 4%nat D; lia)
              ltac:(red; apply bv_eq; reflexivity) E6_1 E6_10 E6_11 E6_12)
    as (r7 & bs7 & RUN7 & L7 & K7).
  set (m7 := wbytes m6 (Z_to_bv 64 bufs1) bs7) in *.
  assert (RI7 : rinv RW3 m3 m7).
  { apply (rinv_wbytes RW3 m3 m6 bufs1 (wplt * 4) bs7 RI6 L7); [lia | lia |]. exists (bufs1, 4 * wplt)%Z. split; [unfold RW3, RB1; dl_in0 | cbn [fst snd]; lia]. }
  (* [comment removed for export] *)
  destruct (kcs_keep m3 m7 RI7 KC3) as (Kw7 & Kh7 & Kwt7 & Kdt7 & Kwd7). destruct (kcs3_keep m3 m7 RI7 KD3) as (Kw37 & Kz37 & Kh37).
  destruct (ux_1ccf0 rom s datad bufs1 bufs2 tabval tab38 tab14 w wplt wpld (h - 1) HYPx fx r7 m7 Kwd7 Kw37 Kz37 Kh37
              ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3) ltac:(dl_get3))
    as (r8 & m8 & RUN8 & FR8 & E8_1 & E8_10 & E8_11 & E8_12 & E8_13 & E8_14 & E8_15 & E8_16 & E8_17 & AG8).
  assert (RI8 : rinv RW3 m3 m8) by (apply (rinv_cells RW3 [] m3 m7 m8 RI7 FR8); intros c []).
  assert (G08 : mem_grows M0 m8) by exact (mem_grows_trans _ _ _ G03 (proj1 RI8)).
  destruct lrow_facts as (LR1 & LR2 & LR3).
  pose proof (ll2_geom_row lrow LR1 LR2 LR3) as GLL. pose proof (ll2_disj_row lrow LR1 LR2) as GDL.
  assert (ROLL : regions_ok SEGS m8 (R2 lrow bufs1 wplt wpld)).
  { intros r Hr. unfold R2 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd].
    - repeat split; try lia. apply (reg_sok SEGS M0 m8 datad _ lrow _ G08 SOKD); rewrite ?Z2Nat.id by lia; lia.
    - repeat split; try lia. eapply store_ok_mono; [exact G08 | exact SOK1]. }
  destruct (d2ll1_run rom (s - 208) lrow bufs1 bufs2 tabval tab38 tab14 (w - 1) wplt wpld GLL GDL m8 ROLL
              (tabs_keepL m3 m8 (rinv_incl RW3 RWL m3 m8 RI8 RW3_RWL) TK3) r8 (Z_to_bv 64 118356) ltac:(red; apply bv_eq; reflexivity)
              ltac:(replace (s - 208 - 80)%Z with (s - 288)%Z by lia; eapply store_ok_mono; [exact G08 | exact SOKF])
              ltac:(dl_get3) E8_1 ltac:(unfold lrow; dl_get3) ltac:(dl_get3) E8_12 E8_13 E8_14 E8_15 E8_16 E8_17)
    as (r9 & m9 & RUN9 & RI9 & Z2 & KS9 & KP9).
  exists r9, m9. split.
  { exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN5 (msteps_trans _ _ _ _ RUN6
           (msteps_trans _ _ _ _ RUN7 (msteps_trans _ _ _ _ RUN8 RUN9)))))). }
  split.
  { apply (rinv_trans RWL M0 m3 m9 RI3). apply (rinv_trans RWL m3 m8 m9); [exact (rinv_incl RW3 RWL m3 m8 RI8 RW3_RWL)|].
    apply (rinv_weaken (R4' (s - 208) lrow bufs1 wplt wpld) RWL m8 m9 RI9).
    intros r Hr. unfold R4', R2 in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd].
    - exists ((s - 288)%Z, 80%Z). split; [unfold RWL; dl_in0 | cbn [fst snd]; lia].
    - exists (datad, 4 * (wpld * h))%Z. split; [unfold RWL, RD; dl_in0 | cbn [fst snd]; lia].
    - exists (bufs1, 4 * wplt)%Z. split; [unfold RWL, RB1; dl_in0 | cbn [fst snd]; lia]. }
  intros r Hr. cbn [In] in Hr.
  assert (Z3 : getr r9 3 = getr regs 3).
  { rewrite (KP9 3%bv ltac:(in_kept)). rewrite (AG8 3%bv) by notin_list. rewrite (K7 3%bv ltac:(in_kept)). rewrite (AG6 3%bv) by notin_list. rewrite X3. dl_same. }
  assert (Z4 : getr r9 4 = getr regs 4).
  { rewrite (KP9 4%bv ltac:(in_kept)). rewrite (AG8 4%bv) by notin_list. rewrite (K7 4%bv ltac:(in_kept)). rewrite (AG6 4%bv) by notin_list. rewrite X4. dl_same. }
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]]; first [exact Z3 | exact Z4 | idtac].
  - rewrite H2. exact Z2.
  - rewrite H9. rewrite (KS9 9%bv ltac:(in_kept)). dl_get3.
  - rewrite H18. rewrite (KS9 18%bv ltac:(in_kept)). dl_get3.
  - rewrite H20. rewrite (KS9 20%bv ltac:(in_kept)). dl_get3.
  - rewrite H21. rewrite (KS9 21%bv ltac:(in_kept)). dl_get3.
  - rewrite H22. rewrite (KS9 22%bv ltac:(in_kept)). dl_get3.
  - rewrite H25. rewrite (KS9 25%bv ltac:(in_kept)). dl_get3.
Qed.

End Low2.
