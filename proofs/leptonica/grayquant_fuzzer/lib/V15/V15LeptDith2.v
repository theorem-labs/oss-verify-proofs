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
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15_code_gqD V15Dith2LL V15Dith2LL0.
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

Section LineLow2.
Context {fx : FPState}.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Variables (s lined bufs1 bufs2 tabval tab38 tab14 w1 wpl wpld : Z).
Definition ll2_geom : Prop :=
  (4096 <= s - 80 /\ s < 2 ^ 47 /\ s mod 16 = 0 /\
   4096 <= lined /\ lined + 4 * wpld < 2 ^ 47 /\ lined mod 4 = 0 /\ 4096 <= bufs1 /\ bufs1 + 4 * wpl < 2 ^ 47 /\ bufs1 mod 4 = 0 /\
   4096 <= bufs2 /\ bufs2 + 4 * wpl < 2 ^ 47 /\ bufs2 mod 4 = 0 /\ 4096 <= tabval /\ tabval + 1024 < 2 ^ 47 /\ tabval mod 4 = 0 /\
   4096 <= tab38 /\ tab38 + 1024 < 2 ^ 47 /\ tab38 mod 4 = 0 /\ 4096 <= tab14 /\ tab14 + 1024 < 2 ^ 47 /\ tab14 mod 4 = 0 /\
   0 <= w1 <= 19999 /\ w1 + 1 <= 4 * wpl /\ w1 + 1 <= 16 * wpld)%Z.
(* [comment removed for export] *)
Definition LL2L : list (Z * Z) := [(s - 80, 80); (lined, 4 * wpld); (bufs1, 4 * wpl); (bufs2, 4 * wpl); (tabval, 1024); (tab38, 1024); (tab14, 1024)]%Z.
Definition ll2_disj : Prop := pairwise LL2L.
Hypothesis G : ll2_geom.
Hypothesis GD : ll2_disj.
Ltac geom := pose proof G as (Gs0 & Gs1 & Gs2 & Gl0 & Gl1 & ALl & Gb10 & Gb11 & ALb1 & Gb20 & Gb21 & ALb2 & Gt00 & Gt01 & ALt0 & Gt80 & Gt81 & ALt8 & Gt40 & Gt41 & ALt4 & Gw & Gwpl & Gwpld).
Ltac al4 :=
  match goal with H : (bufs1 mod 4 = 0)%Z |- _ => let c := fresh "cb1" in let E := fresh "Ecb1" in destruct (al4_ex _ H) as [c E] end;
  match goal with H : (bufs2 mod 4 = 0)%Z |- _ => let c := fresh "cb2" in let E := fresh "Ecb2" in destruct (al4_ex _ H) as [c E] end.

Definition R3 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl); (bufs2, 4 * wpl)]%Z.
Definition R2 : list (Z * Z) := [(lined, 4 * wpld); (bufs1, 4 * wpl)]%Z.
Definition R4 : list (Z * Z) := ((s - 80)%Z, 80%Z) :: R3.
Definition R4' : list (Z * Z) := ((s - 80)%Z, 80%Z) :: R2.
Lemma R2_R3 : forall r, In r R2 -> In r R3.
Proof. intros r Hr. unfold R2, R3 in *. cbn [In] in *. tauto. Qed.
Lemma R3_R4 : forall r, In r R3 -> In r R4.
Proof. intros r Hr. right. exact Hr. Qed.

Definition tabs_ok (M : word -> option byte) : Prop :=
  tab_ok SEGS false (fun _ => True) M tabval /\ tab_ok SEGS true tv_ok M tab38 /\ tab_ok SEGS true tv_ok M tab14.

(* [comment removed for export] *)
Lemma tab_apart : forall (i : nat) tab, (4 <= i <= 6)%nat -> nth i LL2L (0, 0)%Z = (tab, 1024%Z) ->
  forall r, In r R4 -> (tab + 1024 <= fst r \/ fst r + snd r <= tab)%Z.
Proof.
  intros i tab Hi E r Hr. unfold R4, R3 in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd].
  - pose proof (pairwise_nth _ 0 i (0, 0)%Z GD ltac:(unfold LL2L; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd LL2L] in D. lia.
  - pose proof (pairwise_nth _ 1 i (0, 0)%Z GD ltac:(unfold LL2L; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd LL2L] in D. lia.
  - pose proof (pairwise_nth _ 2 i (0, 0)%Z GD ltac:(unfold LL2L; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd LL2L] in D. lia.
  - pose proof (pairwise_nth _ 3 i (0, 0)%Z GD ltac:(unfold LL2L; cbn [length]; lia)) as D. rewrite E in D. unfold apart2 in D. cbn [nth fst snd LL2L] in D. lia.
Qed.
Lemma tabs_keep : forall RR (M1 Mi : word -> option byte), (forall r, In r RR -> In r R4) -> rinv RR M1 Mi -> tabs_ok M1 -> tabs_ok Mi.
Proof.
  intros RR M1 Mi INC RI (T0 & T38 & T14). unfold tabs_ok.
  split; [|split]; (eapply (tab_ok_rinv SEGS _ _ RR M1 Mi); [eassumption | exact RI |]); intros r Hr.
  - exact (tab_apart 4%nat tabval ltac:(lia) eq_refl r (INC r Hr)).
  - exact (tab_apart 5%nat tab38 ltac:(lia) eq_refl r (INC r Hr)).
  - exact (tab_apart 6%nat tab14 ltac:(lia) eq_refl r (INC r Hr)).
Qed.

Ltac cell_in RR :=
  cbn [fst snd]; split; [lia|]; first [ (exists (lined, 4 * wpld)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia])
                                        | (exists (bufs1, 4 * wpl)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia])
                                        | (exists (bufs2, 4 * wpl)%Z; split; [unfold RR; dl_in0 | cbn [fst snd]; dl_lia]) ].

Lemma ll_ret : forall regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (mkst regs (Z_to_bv 64 0x1f198) m rom) (mkst regs ret m rom).
Proof.
  intros regs m ret Hret H1. replace (Z_to_bv 64 0x1f198) with (0x1f198 : word) by (apply bv_eq; reflexivity).
  stepret F_1f094 D_1f094 ret ltac:(exact H1). apply mst_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v0h : forall j, (0 <= j < w1)%Z -> v0_hyps lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld.
Proof.
  intros j Hj. geom. unfold v0_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GD 1%nat 2%nat D. exact D.
  - unfold dapart. pw GD 1%nat 3%nat D. exact D.
  - unfold dapart. pw GD 1%nat 5%nat D. exact D.
  - unfold dapart. pw GD 1%nat 6%nat D. exact D.
Qed.
Lemma vt0h : vt0_hyps lined bufs1 bufs2 tabval tab38 w1 wpl wpld.
Proof.
  geom. unfold vt0_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GD 1%nat 3%nat D. exact D.
  - unfold dapart. pw GD 1%nat 5%nat D. exact D.
Qed.
Lemma v0_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R3 (v0_1eddc_cells_def lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold v0_1eddc_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R3 |]). destruct Hc.
Qed.
Lemma vt0_cells_in : cells_in R3 (vt0_1ef44_cells_def lined bufs1 bufs2 tabval tab38 w1 wpl wpld).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 16 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold vt0_1ef44_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R3 |]). destruct Hc.
Qed.

Definition f0regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 5 = Z_to_bv 64 j /\ getr regs 6 = Z_to_bv 64 3 /\ getr regs 7 = Z_to_bv 64 1 /\ getr regs 8 = Z_to_bv 64 1 /\
  getr regs 10 = Z_to_bv 64 lined /\ getr regs 11 = Z_to_bv 64 w1 /\ getr regs 12 = Z_to_bv 64 bufs1 /\ getr regs 13 = Z_to_bv 64 bufs2 /\
  getr regs 14 = Z_to_bv 64 tabval /\ getr regs 15 = Z_to_bv 64 tab38 /\ getr regs 16 = Z_to_bv 64 tab14 /\ getr regs 28 = Z_to_bv 64 1 /\
  getr regs 31 = Z_to_bv 64 268435455.

Lemma v0_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R3 -> tabs_ok Mr ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R3 Mr Mi -> f0regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1eee0) Mi rom) (mkst regs' (Z_to_bv 64 0x1f048) Mi' rom)
    /\ rinv R3 Mr Mi' /\ regs_agree (fun r => In r [5; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof.
  intros Mr ROr (TK0 & TK38 & TK14). geom.
  pose proof (fun r Hr => tab_apart 4%nat tabval ltac:(lia) eq_refl r (R3_R4 r Hr)) as AP0.
  pose proof (fun r Hr => tab_apart 5%nat tab38 ltac:(lia) eq_refl r (R3_R4 r Hr)) as AP38.
  pose proof (fun r Hr => tab_apart 6%nat tab14 ltac:(lia) eq_refl r (R3_R4 r Hr)) as AP14.
  induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H5 & H6 & H7 & H8 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H28 & H31).
  pose proof (v0_cells_in j Hj) as CI.
  pose proof (cells_ok_of SEGS Mr Mi R3 _ ROr (proj1 RI) CI) as CK.
  destruct (v0_1eddc_path rom lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld (v0h j Hj) fx regs Mi CK
              (tab_rd_of SEGS false _ R3 _ Mr Mi tabval TK0 RI CI AP0) (tab_rd_of SEGS true _ R3 _ Mr Mi tab38 TK38 RI CI AP38)
              (tab_rd_of SEGS true _ R3 _ Mr Mi tab14 TK14 RI CI AP14) H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H31)
    as (r1 & m1 & RUN1 & FR1 & E5 & E9 & E18 & E19 & AG1).
  pose proof (rinv_cells R3 _ Mr Mi m1 RI FR1 CI) as RI1.
  assert (CI0 : cells_in R3 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - destruct (v0_1edd8f rom lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld (v0h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f0regs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (v0_1edd8t rom lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld (v0h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R3 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

(* [comment removed for export] *)
Lemma frame_keep : forall RR (M1 Mi : word -> option byte) (k : Z) v, (forall r, In r RR -> In r R3) -> rinv RR M1 Mi -> (8 <= k <= 80)%Z ->
  rdn SEGS M1 (Z_to_bv 64 (s - k)) 8 = Some v -> rdn SEGS Mi (Z_to_bv 64 (s - k)) 8 = Some v.
Proof.
  intros RR M1 Mi k v INC RI Hk R. geom. rewrite <- R. apply (rinv_rdn SEGS RR M1 Mi (s - k) 8 RI); [lia | cbn; lia |].
  intros r Hr. specialize (INC r Hr). unfold R3 in INC. cbn [In] in INC. cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
  destruct INC as [<- | [<- | [<- | []]]]; cbn [fst snd].
  - pw GD 0%nat 1%nat D. lia.
  - pw GD 0%nat 2%nat D. lia.
  - pw GD 0%nat 3%nat D. lia.
Qed.

(* [comment removed for export] *)
Definition saved10 (m1 : word -> option byte) (regs : bvmap 5 word) : Prop :=
  rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
  rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 18)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (getr regs 19)) /\
  rdn SEGS m1 (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (getr regs 20)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (getr regs 21)) /\
  rdn SEGS m1 (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (getr regs 22)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (getr regs 23)) /\
  rdn SEGS m1 (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (getr regs 24)) /\ rdn SEGS m1 (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 (getr regs 25)).

Lemma ll_tail : forall RR (INC : forall r, In r RR -> In r R3) regs (ret : word) (m1 : word -> option byte) r4 m4, ret_ok ret -> getr regs 1 = ret ->
  saved10 m1 regs -> rinv RR m1 m4 -> getr r4 2 = Z_to_bv 64 (s - 80) -> getr r4 1 = getr regs 1 ->
  exists r6 m6, msteps SEGS (mkst r4 (Z_to_bv 64 0x1f16c) m4 rom) (mkst r6 ret m6 rom) /\ rinv RR m1 m6 /\ getr r6 2 = Z_to_bv 64 s
    /\ (forall r, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr r6 r = getr regs r)
    /\ regs_agree (fun r => In r [2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%list) r4 r6.
Proof.
  intros RR INC regs ret m1 r4 m4 Hret H1 (SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25) RI4 Y2 Y1. geom.
  assert (HYPe : ve_hyps s) by (unfold ve_hyps; repeat split; first [assumption | lia]).
  destruct (ve_1f068 rom s HYPe fx r4 m4 _ _ _ _ _ _ _ _ _ _
              (frame_keep RR m1 m4 8 _ INC RI4 ltac:(lia) SV8) (frame_keep RR m1 m4 16 _ INC RI4 ltac:(lia) SV9) (frame_keep RR m1 m4 24 _ INC RI4 ltac:(lia) SV18)
              (frame_keep RR m1 m4 32 _ INC RI4 ltac:(lia) SV19) (frame_keep RR m1 m4 40 _ INC RI4 ltac:(lia) SV20) (frame_keep RR m1 m4 48 _ INC RI4 ltac:(lia) SV21)
              (frame_keep RR m1 m4 56 _ INC RI4 ltac:(lia) SV22) (frame_keep RR m1 m4 64 _ INC RI4 ltac:(lia) SV23) (frame_keep RR m1 m4 72 _ INC RI4 ltac:(lia) SV24)
              (frame_keep RR m1 m4 80 _ INC RI4 ltac:(lia) SV25) Y2)
    as (r5 & m5 & RUN5 & FR5 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & AG5).
  rewrite rdv_word8 in X8, X9, X18, X19, X20, X21, X22, X23, X24, X25.
  pose proof (ll_ret r5 m5 ret Hret ltac:(rewrite (AG5 1%bv) by notin_list; rewrite Y1; exact H1)) as RUN6.
  exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN5 RUN6)|]. split; [apply (rinv_cells RR [] m1 m4 m5 RI4 FR5); intros c []|].
  split; [exact X2|]. split; [|exact AG5].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr.
Qed.

(* [comment removed for export] *)
Definition FCELLS : list (Z * Z) :=
  [((s - 8)%Z, 8%Z); ((s - 16)%Z, 8%Z); ((s - 24)%Z, 8%Z); ((s - 32)%Z, 8%Z); ((s - 40)%Z, 8%Z); ((s - 48)%Z, 8%Z); ((s - 56)%Z, 8%Z); ((s - 64)%Z, 8%Z);
   ((s - 72)%Z, 8%Z); ((s - 80)%Z, 8%Z)].
Lemma fcells_in : forall RR, In ((s - 80)%Z, 80%Z) RR -> cells_in RR FCELLS.
Proof.
  intros RR HF c Hc. unfold FCELLS in Hc. cbn [In] in Hc.
  repeat (destruct Hc as [<- | Hc]; [cbn [fst snd]; split; [lia|]; exists ((s - 80)%Z, 80%Z); split; [exact HF | cbn [fst snd]; lia] |]). destruct Hc.
Qed.

Lemma d2ll0_run : forall (M0 : word -> option byte), regions_ok SEGS M0 R3 -> tabs_ok M0 -> forall regs (ret : word), ret_ok ret ->
  store_ok SEGS M0 (Z_to_bv 64 (s - 80)) 80 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 -> getr regs 13 = Z_to_bv 64 bufs2 -> getr regs 14 = Z_to_bv 64 tabval -> getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 -> getr regs 17 = Z_to_bv 64 0 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1ec04) M0 rom) (mkst regs' ret M' rom)
    /\ rinv R4 M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ (forall r, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr regs' r = getr regs r)
    /\ (forall r, In r [3; 4; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 RO TK0 regs ret Hret SOKF H2 H1 H10 H11 H12 H13 H14 H15 H16 H17. geom.
  assert (sokF : forall k, (8 <= k <= 80)%Z -> store_ok SEGS M0 (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 M0 (s - 80) 80 (s - k) 8 (mem_grows_refl _) SOKF); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (PRE : exists r3 m1 m3, msteps SEGS (mkst regs (Z_to_bv 64 0x1ec04) M0 rom) (mkst r3 (Z_to_bv 64 0x1f048) m3 rom)
                  /\ rinv R4 M0 m1 /\ rinv R3 m1 m3 /\ getr r3 2 = Z_to_bv 64 (s - 80) /\ getr r3 1 = getr regs 1
                  /\ getr r3 10 = Z_to_bv 64 lined /\ getr r3 11 = Z_to_bv 64 w1 /\ getr r3 12 = Z_to_bv 64 bufs1 /\ getr r3 13 = Z_to_bv 64 bufs2
                  /\ getr r3 14 = Z_to_bv 64 tabval /\ getr r3 15 = Z_to_bv 64 tab38 /\ saved10 m1 regs
                  /\ (forall r, In r [3; 4; 26; 27]%bv -> getr r3 r = getr regs r)).
  { destruct (Z.eq_dec w1 0) as [W0|W1].
    - assert (HYPq : vq_hyps s lined bufs1 bufs2 tabval tab38 tab14) by (unfold vq_hyps; repeat split; first [assumption | lia]).
      destruct (vq_1eb00_f0 rom s lined bufs1 bufs2 tabval tab38 tab14 HYPq fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia))
                  (sokF 32%Z ltac:(lia)) (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) (sokF 56%Z ltac:(lia)) (sokF 64%Z ltac:(lia)) (sokF 72%Z ltac:(lia))
                  (sokF 80%Z ltac:(lia)) H2 H10 ltac:(rewrite H11; f_equal; lia) H12 H13 H14 H15 H16 H17)
        as (r1 & m1 & RUN1 & FR1 & E2 & E5 & E11 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25 & AG1).
      exists r1, m1, m1. split; [exact RUN1|]. split; [exact (rinv_cells R4 _ M0 M0 m1 (rinv_refl _ _) FR1 (fcells_in R4 ltac:(left; reflexivity)))|].
      split; [apply rinv_refl|]. split; [exact E2|]. split; [apply AG1; notin_list|].
      split; [dl_get2|]. split; [rewrite E11; f_equal; lia|]. split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|].
      split; [unfold saved10; repeat split; assumption|].
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply AG1; notin_list |]). destruct Hr.
    - assert (HYPp : vp_hyps s lined bufs1 bufs2 tabval tab38 tab14 w1) by (unfold vp_hyps; repeat split; first [assumption | lia]).
      destruct (vp_1eb00_f0 rom s lined bufs1 bufs2 tabval tab38 tab14 w1 HYPp fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia))
                  (sokF 32%Z ltac:(lia)) (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) (sokF 56%Z ltac:(lia)) (sokF 64%Z ltac:(lia)) (sokF 72%Z ltac:(lia))
                  (sokF 80%Z ltac:(lia)) H2 H10 H11 H12 H13 H14 H15 H16 H17)
        as (r1 & m1 & RUN1 & FR1 & E2 & E5 & E6 & E7 & E8 & E11 & E28 & E29 & E30 & E31 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25 & AG1).
      assert (RI1 : rinv R4 M0 m1) by exact (rinv_cells R4 _ M0 M0 m1 (rinv_refl _ _) FR1 (fcells_in R4 ltac:(left; reflexivity))).
      pose proof (regions_ok_grows SEGS M0 m1 R3 RO (proj1 FR1)) as RO1.
      destruct (v0_loop m1 RO1 (tabs_keep R4 M0 m1 (fun r H => H) RI1 TK0) (Z.to_nat w1) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r3 & m3 & RUN3 & RI3 & AG3).
      { unfold f0regs. repeat split; dl_get2. }
      exists r3, m1, m3. split; [exact (msteps_trans _ _ _ _ RUN1 RUN3)|]. split; [exact RI1|]. split; [exact RI3|].
      split; [dl_get2|]. split; [rewrite (AG3 1%bv) by notin_list; apply AG1; notin_list|].
      split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|].
      split; [unfold saved10; repeat split; assumption|].
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [rewrite (AG3 _) by notin_list; apply AG1; notin_list |]). destruct Hr. }
  destruct PRE as (r3 & m1 & m3 & RUN3 & RI1 & RI3 & Y2 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & SV & KP3).
  (* [comment removed for export] *)
  pose proof (regions_ok_grows SEGS M0 m1 R3 RO (proj1 RI1)) as RO1.
  pose proof (tabs_keep R4 M0 m1 (fun r H => H) RI1 TK0) as (TK0' & TK38' & TK14').
  pose proof vt0_cells_in as CI.
  pose proof (cells_ok_of SEGS m1 m3 R3 _ RO1 (proj1 RI3) CI) as CK3.
  destruct (vt0_1ef44_path rom lined bufs1 bufs2 tabval tab38 w1 wpl wpld vt0h fx r3 m3 CK3
              (tab_rd_of SEGS false _ R3 _ m1 m3 tabval TK0' RI3 CI (fun r Hr => tab_apart 4%nat tabval ltac:(lia) eq_refl r (R3_R4 r Hr)))
              (tab_rd_of SEGS true _ R3 _ m1 m3 tab38 TK38' RI3 CI (fun r Hr => tab_apart 5%nat tab38 ltac:(lia) eq_refl r (R3_R4 r Hr)))
              Y10 Y11 Y12 Y13 Y14 Y15) as (r4 & m4 & RUN4 & FR4 & E4_7 & E4_10 & AG4).
  pose proof (rinv_cells R3 _ m1 m3 m4 RI3 FR4 CI) as RI4.
  destruct (ll_tail R3 (fun r H => H) regs ret m1 r4 m4 Hret H1 SV RI4
              ltac:(rewrite (AG4 2%bv) by notin_list; exact Y2) ltac:(rewrite (AG4 1%bv) by notin_list; exact Y1))
    as (r6 & m6 & RUN6 & RI6 & Z2 & ZS & AG6).
  exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN6))|].
  split; [apply (rinv_trans R4 M0 m1 m6 RI1); apply (rinv_incl R3 R4 m1 m6 RI6 R3_R4)|].
  split; [exact Z2|]. split; [exact ZS|].
  intros r Hr. rewrite <- (KP3 r Hr). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [rewrite (AG6 _) by notin_list; apply AG4; notin_list |]). destruct Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v1h : forall j, (0 <= j < w1)%Z -> v1_hyps lined bufs1 tabval tab38 j w1 (w1 - j) wpl wpld.
Proof.
  intros j Hj. geom. unfold v1_hyps. repeat split; try assumption; try lia.
  - unfold dapart. pw GD 1%nat 2%nat D. exact D.
  - unfold dapart. pw GD 1%nat 5%nat D. exact D.
Qed.
Lemma vt1h : vt1_hyps lined bufs1 tabval w1 wpl wpld.
Proof. geom. unfold vt1_hyps. repeat split; try assumption; try lia. Qed.
Lemma v1_cells_in : forall j, (0 <= j < w1)%Z -> cells_in R2 (v1_1ebb8_cells_def lined bufs1 tabval tab38 j w1 (w1 - j) wpl wpld).
Proof.
  intros j Hj. geom. al4. pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ.
  intros c Hc. unfold v1_1ebb8_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R2 |]). destruct Hc.
Qed.
Lemma vt1_cells_in : cells_in R2 (vt1_1ec9c_cells_def lined bufs1 tabval w1 wpl wpld).
Proof.
  geom. al4. pose proof (dl_div_bounds w1 16 ltac:(lia) ltac:(lia)) as DW.
  intros c Hc. unfold vt1_1ec9c_cells_def in Hc. cbn [In] in Hc. repeat (destruct Hc as [<- | Hc]; [cell_in R2 |]). destruct Hc.
Qed.

Definition f1regs (regs : bvmap 5 word) (j : Z) : Prop :=
  getr regs 5 = Z_to_bv 64 3 /\ getr regs 6 = Z_to_bv 64 1 /\ getr regs 7 = Z_to_bv 64 1 /\ getr regs 8 = Z_to_bv 64 1 /\
  getr regs 9 = Z_to_bv 64 (bufs1 + j) /\ getr regs 10 = Z_to_bv 64 lined /\ getr regs 11 = Z_to_bv 64 w1 /\ getr regs 12 = Z_to_bv 64 bufs1 /\
  getr regs 14 = Z_to_bv 64 tabval /\ getr regs 15 = Z_to_bv 64 tab38 /\ getr regs 16 = Z_to_bv 64 j /\ getr regs 17 = Z_to_bv 64 (bufs1 + j + 1) /\
  getr regs 18 = Z_to_bv 64 (w1 - j) /\ getr regs 30 = Z_to_bv 64 2 /\ getr regs 31 = Z_to_bv 64 268435455.

Lemma v1_loop : forall (Mr : word -> option byte), regions_ok SEGS Mr R2 -> tabs_ok Mr ->
  forall (n : nat) j regs Mi, (w1 - j <= Z.of_nat n)%Z -> (0 <= j < w1)%Z -> rinv R2 Mr Mi -> f1regs regs j ->
  exists regs' Mi', msteps SEGS (mkst regs (Z_to_bv 64 0x1ecbc) Mi rom) (mkst regs' (Z_to_bv 64 0x1eda0) Mi' rom)
    /\ rinv R2 Mr Mi' /\ regs_agree (fun r => In r [9; 13; 16; 17; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
Proof.
  intros Mr ROr (TK0 & TK38 & TK14). geom.
  pose proof (fun r Hr => tab_apart 4%nat tabval ltac:(lia) eq_refl r (R3_R4 r (R2_R3 r Hr))) as AP0.
  pose proof (fun r Hr => tab_apart 5%nat tab38 ltac:(lia) eq_refl r (R3_R4 r (R2_R3 r Hr))) as AP38.
  induction n as [|n IH]; intros j regs Mi Hn Hj RI LR; [lia|].
  destruct LR as (H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H14 & H15 & H16 & H17 & H18 & H30 & H31).
  pose proof (v1_cells_in j Hj) as CI.
  pose proof (cells_ok_of SEGS Mr Mi R2 _ ROr (proj1 RI) CI) as CK.
  destruct (v1_1ebb8_path rom lined bufs1 tabval tab38 j w1 (w1 - j) wpl wpld (v1h j Hj) fx regs Mi CK
              (tab_rd_of SEGS false _ R2 _ Mr Mi tabval TK0 RI CI AP0) (tab_rd_of SEGS true _ R2 _ Mr Mi tab38 TK38 RI CI AP38)
              H5 H6 H7 H8 H9 H10 H11 H12 H14 H15 H16 H17 H18 H30 H31)
    as (r1 & m1 & RUN1 & FR1 & E9 & E16 & E17 & E18 & E19 & AG1).
  pose proof (rinv_cells R2 _ Mr Mi m1 RI FR1 CI) as RI1.
  assert (CI0 : cells_in R2 []) by (intros c []).
  destruct (Z_lt_ge_dec (j + 1) w1) as [LT|GE].
  - destruct (v1_1ebb4f rom lined bufs1 tabval tab38 j w1 (w1 - j) wpl wpld (v1h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R2 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    destruct (IH (j + 1)%Z r2 m2 ltac:(lia) ltac:(lia) RI2) as (r3 & m3 & RUN3 & RI3 & AG3).
    { unfold f1regs. repeat split; dl_get2. }
    exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact RI3 | ra_chain].
  - destruct (v1_1ebb4t rom lined bufs1 tabval tab38 j w1 (w1 - j) wpl wpld (v1h j Hj) fx r1 m1 ltac:(ex_br) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r2 & m2 & RUN2 & FR2 & AG2).
    pose proof (rinv_cells R2 _ Mr m1 m2 RI1 FR2 CI0) as RI2.
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact RI2 | ra_chain].
Qed.

Lemma R2_R4' : forall r, In r R2 -> In r R4'.
Proof. intros r Hr. right. exact Hr. Qed.
Lemma R4'_R4 : forall r, In r R4' -> In r R4.
Proof. intros r Hr. unfold R4', R4, R2, R3 in *. cbn [In] in *. tauto. Qed.

Lemma d2ll1_run : forall (M0 : word -> option byte), regions_ok SEGS M0 R2 -> tabs_ok M0 -> forall regs (ret : word), ret_ok ret ->
  store_ok SEGS M0 (Z_to_bv 64 (s - 80)) 80 = true ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 lined -> getr regs 11 = Z_to_bv 64 (w1 + 1) ->
  getr regs 12 = Z_to_bv 64 bufs1 -> getr regs 13 = Z_to_bv 64 bufs2 -> getr regs 14 = Z_to_bv 64 tabval -> getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 -> getr regs 17 = Z_to_bv 64 1 ->
  exists regs' M', msteps SEGS (mkst regs (Z_to_bv 64 0x1ec04) M0 rom) (mkst regs' ret M' rom)
    /\ rinv R4' M0 M' /\ getr regs' 2 = Z_to_bv 64 s
    /\ (forall r, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv -> getr regs' r = getr regs r)
    /\ (forall r, In r [3; 4; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros M0 RO TK0 regs ret Hret SOKF H2 H1 H10 H11 H12 H13 H14 H15 H16 H17. geom.
  assert (sokF : forall k, (8 <= k <= 80)%Z -> store_ok SEGS M0 (Z_to_bv 64 (s - k)) 8 = true).
  { intros k Hk. apply (reg_sok SEGS M0 M0 (s - 80) 80 (s - k) 8 (mem_grows_refl _) SOKF); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (PRE : exists r3 m1 m3, msteps SEGS (mkst regs (Z_to_bv 64 0x1ec04) M0 rom) (mkst r3 (Z_to_bv 64 0x1eda0) m3 rom)
                  /\ rinv R4' M0 m1 /\ rinv R2 m1 m3 /\ getr r3 2 = Z_to_bv 64 (s - 80) /\ getr r3 1 = getr regs 1
                  /\ getr r3 10 = Z_to_bv 64 lined /\ getr r3 11 = Z_to_bv 64 w1 /\ getr r3 12 = Z_to_bv 64 bufs1 /\ getr r3 14 = Z_to_bv 64 tabval
                  /\ saved10 m1 regs /\ (forall r, In r [3; 4; 26; 27]%bv -> getr r3 r = getr regs r)).
  { destruct (Z.eq_dec w1 0) as [W0|W1].
    - assert (HYPq : vq_hyps s lined bufs1 bufs2 tabval tab38 tab14) by (unfold vq_hyps; repeat split; first [assumption | lia]).
      destruct (vq_1eb00_f1 rom s lined bufs1 bufs2 tabval tab38 tab14 HYPq fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia))
                  (sokF 32%Z ltac:(lia)) (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) (sokF 56%Z ltac:(lia)) (sokF 64%Z ltac:(lia)) (sokF 72%Z ltac:(lia))
                  (sokF 80%Z ltac:(lia)) H2 H10 ltac:(rewrite H11; f_equal; lia) H12 H13 H14 H15 H16 H17)
        as (r1 & m1 & RUN1 & FR1 & E2 & E5 & E11 & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25 & AG1).
      exists r1, m1, m1. split; [exact RUN1|]. split; [exact (rinv_cells R4' _ M0 M0 m1 (rinv_refl _ _) FR1 (fcells_in R4' ltac:(left; reflexivity)))|].
      split; [apply rinv_refl|]. split; [exact E2|]. split; [apply AG1; notin_list|].
      split; [dl_get2|]. split; [rewrite E11; f_equal; lia|]. split; [dl_get2|]. split; [dl_get2|].
      split; [unfold saved10; repeat split; assumption|].
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [apply AG1; notin_list |]). destruct Hr.
    - assert (HYPp : vp_hyps s lined bufs1 bufs2 tabval tab38 tab14 w1) by (unfold vp_hyps; repeat split; first [assumption | lia]).
      destruct (vp_1eb00_f1 rom s lined bufs1 bufs2 tabval tab38 tab14 w1 HYPp fx regs M0 (sokF 8%Z ltac:(lia)) (sokF 16%Z ltac:(lia)) (sokF 24%Z ltac:(lia))
                  (sokF 32%Z ltac:(lia)) (sokF 40%Z ltac:(lia)) (sokF 48%Z ltac:(lia)) (sokF 56%Z ltac:(lia)) (sokF 64%Z ltac:(lia)) (sokF 72%Z ltac:(lia))
                  (sokF 80%Z ltac:(lia)) H2 H10 H11 H12 H13 H14 H15 H16 H17)
        as (r1 & m1 & RUN1 & FR1 & E2 & E5 & E6 & E7 & E8 & E9 & E11 & E13 & E16 & E17 & E18 & E28 & E29 & E30 & E31
            & SV8 & SV9 & SV18 & SV19 & SV20 & SV21 & SV22 & SV23 & SV24 & SV25 & AG1).
      assert (RI1 : rinv R4' M0 m1) by exact (rinv_cells R4' _ M0 M0 m1 (rinv_refl _ _) FR1 (fcells_in R4' ltac:(left; reflexivity))).
      pose proof (regions_ok_grows SEGS M0 m1 R2 RO (proj1 FR1)) as RO1.
      destruct (v1_loop m1 RO1 (tabs_keep R4' M0 m1 R4'_R4 RI1 TK0) (Z.to_nat w1) 0%Z r1 m1 ltac:(lia) ltac:(lia) (rinv_refl _ _)) as (r3 & m3 & RUN3 & RI3 & AG3).
      { unfold f1regs. repeat split; dl_get2. }
      exists r3, m1, m3. split; [exact (msteps_trans _ _ _ _ RUN1 RUN3)|]. split; [exact RI1|]. split; [exact RI3|].
      split; [dl_get2|]. split; [rewrite (AG3 1%bv) by notin_list; apply AG1; notin_list|].
      split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|]. split; [dl_get2|].
      split; [unfold saved10; repeat split; assumption|].
      intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [rewrite (AG3 _) by notin_list; apply AG1; notin_list |]). destruct Hr. }
  destruct PRE as (r3 & m1 & m3 & RUN3 & RI1 & RI3 & Y2 & Y1 & Y10 & Y11 & Y12 & Y14 & SV & KP3).
  pose proof (regions_ok_grows SEGS M0 m1 R2 RO (proj1 RI1)) as RO1.
  pose proof (tabs_keep R4' M0 m1 R4'_R4 RI1 TK0) as (TK0' & TK38' & TK14').
  pose proof vt1_cells_in as CI.
  pose proof (cells_ok_of SEGS m1 m3 R2 _ RO1 (proj1 RI3) CI) as CK3.
  destruct (vt1_1ec9c_path rom lined bufs1 tabval w1 wpl wpld vt1h fx r3 m3 CK3
              (tab_rd_of SEGS false _ R2 _ m1 m3 tabval TK0' RI3 CI (fun r Hr => tab_apart 4%nat tabval ltac:(lia) eq_refl r (R3_R4 r (R2_R3 r Hr))))
              Y10 Y11 Y12 Y14) as (r4 & m4 & RUN4 & FR4 & E4_12 & AG4).
  pose proof (rinv_cells R2 _ m1 m3 m4 RI3 FR4 CI) as RI4.
  destruct (ll_tail R2 R2_R3 regs ret m1 r4 m4 Hret H1 SV RI4
              ltac:(rewrite (AG4 2%bv) by notin_list; exact Y2) ltac:(rewrite (AG4 1%bv) by notin_list; exact Y1))
    as (r6 & m6 & RUN6 & RI6 & Z2 & ZS & AG6).
  exists r6, m6. split; [exact (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN6))|].
  split; [apply (rinv_trans R4' M0 m1 m6 RI1); apply (rinv_incl R2 R4' m1 m6 RI6 R2_R4')|].
  split; [exact Z2|]. split; [exact ZS|].
  intros r Hr. rewrite <- (KP3 r Hr). cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [rewrite (AG6 _) by notin_list; apply AG4; notin_list |]). destruct Hr.
Qed.

End LineLow2.
