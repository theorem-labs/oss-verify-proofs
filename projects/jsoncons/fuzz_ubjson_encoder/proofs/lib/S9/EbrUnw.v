(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtPoison EbtAllocG EbtUnwind EbtUnwindG.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require HeapIface HeapIfaceA HeapIfaceAEr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r80560_806c8 Eb0_code_r80bc4_80cdc Eb0_code_r67bcc_67d3c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module UWP.
Import HeapIfaceAEr.

Definition uw_out (pc : Z) (acc RC : list Z) : list Z :=
  acc ++ firstn (30 - length acc) (filter (fun x => negb (x =? pc)) RC).

Lemma akey_uw_out : forall pc RC, HAR.akey pc RC = uw_out pc [pc] RC.
Proof. intros. reflexivity. Qed.
Lemma uw_out_nil : forall pc acc, uw_out pc acc [] = acc.
Proof. intros. unfold uw_out. rewrite list_basics.list.filter_nil. rewrite firstn_nil. apply app_nil_r. Qed.
Lemma uw_out_full : forall pc acc RC, (30 <= length acc)%nat -> uw_out pc acc RC = acc.
Proof. intros pc acc RC H. unfold uw_out. replace (30 - length acc)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r. Qed.
Lemma uw_out_skip : forall pc acc RC, uw_out pc acc (pc :: RC) = uw_out pc acc RC.
Proof. intros. unfold uw_out. rewrite list_basics.list.filter_cons_False; [reflexivity|]. rewrite Z.eqb_refl. intros H. exact H. Qed.
Lemma uw_out_store : forall pc acc ra RC, ra <> pc -> (length acc < 30)%nat -> uw_out pc acc (ra :: RC) = uw_out pc (acc ++ [ra]) RC.
Proof.
  intros pc acc ra RC Hne Hl. unfold uw_out. rewrite list_basics.list.filter_cons_True by (destruct (Z.eqb_spec ra pc) as [E|_]; [contradiction | exact I]).
  rewrite length_app. cbn [length]. replace (30 - length acc)%nat with (S (30 - (length acc + 1)))%nat by lia. cbn [firstn].
  rewrite <- app_assoc. reflexivity.
Qed.
Lemma uw_out_len : forall pc acc RC, (length acc <= 30)%nat -> (length acc <= length (uw_out pc acc RC) <= 30)%nat.
Proof.
  intros pc acc RC H. unfold uw_out. rewrite length_app. rewrite length_firstn. lia.
Qed.
Lemma akey_len : forall pc RC, (1 <= length (HAR.akey pc RC) <= 30)%nat.
Proof. intros. rewrite akey_uw_out. pose proof (uw_out_len pc [pc] RC ltac:(cbn; lia)) as H. cbn [length] in H. lia. Qed.

Lemma firstn_sub : forall (A : Type) n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.
Lemma filter_sub : forall pc (l : list Z) x, In x (filter (fun x => negb (x =? pc)) l) -> In x l.
Proof.
  induction l as [|a l IH]; intros x H; [exact H|]. rewrite list_basics.list.filter_cons in H.
  match type of H with context [if ?d then _ else _] => destruct d end;
    [destruct H as [<-|H]; [left; reflexivity | right; apply IH; exact H] | right; apply IH; exact H].
Qed.

Section Ch.
Variable L : HeapIfaceA.asan_layout.
Variable ar : HeapIfaceA.asan_run.

Lemma rchain_words : forall M lo fp RC, HAR.rchain L ar M lo fp RC -> Forall (fun w => 4096 <= w < 2 ^ 64) RC.
Proof. intros M lo fp RC H. induction H; [constructor | constructor | constructor; assumption]. Qed.
Lemma akey_range : forall M lo fp RC pc, HAR.rchain L ar M lo fp RC -> 0 <= pc < 2 ^ 64 -> Forall (fun w => 0 <= w < 2 ^ 64) (HAR.akey pc RC).
Proof.
  intros M lo fp RC pc H Hpc. unfold HAR.akey. constructor; [exact Hpc|].
  pose proof (rchain_words _ _ _ _ H) as F. rewrite Forall_forall in F.
  apply Forall_forall. intros w Hw. apply firstn_sub in Hw. apply filter_sub in Hw. specialize (F _ Hw). lia.
Qed.

Lemma rchain_invalid : forall M lo fp RC, HAR.rchain L ar M lo fp RC -> ~ HAR.fvalid ar lo fp -> RC = [].
Proof. intros M lo fp RC H NV. inversion H; subst; [reflexivity | reflexivity | contradiction]. Qed.
End Ch.
End UWP.
Export UWP.
Import HeapIfaceAEr.

Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition trace_ws (M : word -> option byte) (this size : Z) (ws : list Z) : Prop :=
  size = Z.of_nat (length ws) /\ cellA M (this + 8) 4 size
  /\ forall i, 0 <= i < size -> cellA M (this + 16 + 8 * i) 8 (nth (Z.to_nat i) ws 0).
Definition trace_is (M : word -> option byte) (this : Z) (ws : list Z) : Prop :=
  cellA M (this + 8) 4 (Z.of_nat (length ws))
  /\ forall i, (i < length ws)%nat -> cellA M (this + 16 + 8 * Z.of_nat i) 8 (nth i ws 0).
Lemma trace_ws_is : forall M this size ws, trace_ws M this size ws -> trace_is M this ws.
Proof.
  intros M this size ws (E & C & T). split; [rewrite <- E; exact C|].
  intros i Hi. pose proof (T (Z.of_nat i) ltac:(Lia.lia)) as X. rewrite Nat2Z.id in X. exact X.
Qed.

Lemma trace_is_cells : forall M this ws, Forall (fun w => 0 <= w < 2 ^ 64) ws -> trace_is M this ws -> trace_cells M this (Z.of_nat (length ws)).
Proof.
  intros M this ws F (_ & T) i Hi. pose proof (T (Z.to_nat i) ltac:(Lia.lia)) as X. rewrite Z2Nat.id in X by Lia.lia.
  rewrite Forall_forall in F. assert (R : 0 <= nth (Z.to_nat i) ws 0 < 2 ^ 64) by (apply F; apply nth_In; Lia.lia).
  exists (Z_to_bv 64 (nth (Z.to_nat i) ws 0)). rewrite art_u_lit by Lia.lia. exact X.
Qed.

Section UNW.
Variable L : HeapIfaceA.asan_layout.
Variable ar : HeapIfaceA.asan_run.
Hypothesis HSEG : HeapIfaceA.hl_segs L = ASEGS.
Context {fx : PropExec.FPState}.

Lemma cell_of_is : forall M a v, HeapIfaceA.cell_is (HeapIfaceA.hl_segs L) M a 8 v -> cellA M a 8 v.
Proof. intros M a v C. unfold HeapIfaceA.cell_is in C. rewrite HSEG in C. exact C. Qed.

Lemma art_uwf_loop_fn : forall (m : nat) regs (M M0 rom : word -> option byte) (this pc bp top lo size : Z) (acc RC : list Z),
  (Z.to_nat (top - bp) <= m)%nat ->
  getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc -> getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 4096 ->
  getr regs 14 = Z_to_bv 64 (this + 16) -> getr regs 15 = Z_to_bv 64 size -> getr regs 8 = Z_to_bv 64 30 -> getr regs 9 = Z_to_bv 64 (top - 16) ->
  1 <= size <= 30 -> 0 <= pc < 2 ^ 64 -> 0 <= this -> this + 256 <= bp - 16 -> bp < top - 16 -> top < 2 ^ 63 -> bp mod 8 = 0 -> lo < bp ->
  HeapIfaceA.ar_stack_top ar = top ->
  wrA M this 256 -> HAR.rchain L ar M0 lo bp RC -> (forall x : word, bp - 16 <= U x < top -> M x = M0 x) ->
  trace_ws M this size acc ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x9bbbc : word) M rom) (mkst regs' (0x9bbf8 : word) M' rom)
    /\ (forall r : reg, r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> M' x = M x)
    /\ trace_ws M' this (Z.of_nat (length (uw_out pc acc RC))) (uw_out pc acc RC).
Proof.
  induction m as [|m IH]; intros regs M M0 rom this pc bp top lo size acc RC Hm H10 H11 H12 H13 H14 H15 H8 H9 Hsz Hpc Hthis Hthis' Hbp Htop Hbp8 Hlo Etop W CH AG0 TW.
  { exfalso. lia. }
  pose proof TW as (Esz & CSZ & TRC).
  assert (Hlen : Z.of_nat (length acc) = size) by (symmetry; exact Esz).
  destruct (Z.le_gt_cases 30 size) as [Full|Room].
  {
    rewrite (uw_out_full pc acc RC) by (clear - Full Hlen; Lia.lia). rewrite Hlen.
    eexists _, M. split; [|split; [|split; [apply mem_grows_refl | split; [intros; reflexivity | exact TW]]]].
    - zbtk F_9bb6c D_9bb6c. apply mst_refl.
    - intros; reflexivity. }
  assert (V : HAR.fvalid ar lo bp) by (unfold HAR.fvalid; rewrite Etop; repeat split; [exact Hlo | exact Hbp | exact Hbp8]).
  inversion CH as [lo' fp' NV | lo' fp' pc1 V' C1i P1 | lo' fp' ra fpn RC' V' C1i R1 C2i R2 CH']; subst lo' fp'; [contradiction| |].
  {
    subst RC. rewrite uw_out_nil. rewrite Hlen.
    assert (C1 : cellA M (bp - 8) 8 pc1).
    { apply (cell_agree M0 M); [intros x Hx; apply AG0; cbn in Hx; lia | lia | cbn; lia | apply cell_of_is; exact C1i]. }
    eexists _, M. split; [|split; [|split; [apply mem_grows_refl | split; [intros; reflexivity | exact TW]]]].
    - zbft F_9bb6c D_9bb6c. zld F_9bb70 D_9bb70 (bp - 8) C1. zbtk F_9bb74 D_9bb74. apply mst_refl.
    - intros; kept_solve. }
  subst RC.
  assert (C1 : cellA M (bp - 8) 8 ra).
  { apply (cell_agree M0 M); [intros x Hx; apply AG0; cbn in Hx; lia | lia | cbn; lia | apply cell_of_is; exact C1i]. }
  assert (C2 : cellA M (bp - 16) 8 fpn).
  { apply (cell_agree M0 M); [intros x Hx; apply AG0; cbn in Hx; lia | lia | cbn; lia | apply cell_of_is; exact C2i]. }

  assert (STEP : exists regs1 M1 size1 acc1,
      msteps ASEGS (mkst regs (0x9bbbc : word) M rom) (mkst regs1 (0x9bbe0 : word) M1 rom)
      /\ getr regs1 10 = Z_to_bv 64 this /\ getr regs1 11 = Z_to_bv 64 pc /\ getr regs1 12 = Z_to_bv 64 bp /\ getr regs1 13 = Z_to_bv 64 4096
      /\ getr regs1 14 = Z_to_bv 64 (this + 16) /\ getr regs1 15 = Z_to_bv 64 size1
      /\ getr regs1 8 = Z_to_bv 64 30 /\ getr regs1 9 = Z_to_bv 64 (top - 16)
      /\ (forall r : reg, r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs1 r = getr regs r)
      /\ mem_grows M M1 /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> M1 x = M x)
      /\ wrA M1 this 256 /\ size <= size1 <= size + 1 /\ trace_ws M1 this size1 acc1 /\ uw_out pc acc (ra :: RC') = uw_out pc acc1 RC').
  { destruct (Z.eq_dec ra pc) as [Same|Diff].
    - eexists _, M, size, acc. split.
      { zbft F_9bb6c D_9bb6c. zld F_9bb70 D_9bb70 (bp - 8) C1. zbft F_9bb74 D_9bb74. zbtk F_9bb78 D_9bb78. apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]).
      split. { intros; kept_solve. }
      split; [apply mem_grows_refl|]. split; [intros; reflexivity|]. split; [assumption|]. split; [lia|]. split; [exact TW|].
      rewrite Same. apply uw_out_skip.
    - eexists _, _, (size + 1), (acc ++ [ra]). split.
      { zbft F_9bb6c D_9bb6c. zld F_9bb70 D_9bb70 (bp - 8) C1. zbft F_9bb74 D_9bb74. zbft F_9bb78 D_9bb78.
        zstep F_9bb7c D_9bb7c. zstep F_9bb80 D_9bb80. zstep F_9bb84 D_9bb84.
        zsw F_9bb88 D_9bb88 (this + 8) (size + 1) ltac:(rewok W).
        zsd F_9bb8c D_9bb8c (this + 16 + size * 8) ra ltac:(rewok W).
        apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]).
      split. { intros; kept_solve. }
      split. { eapply mem_grows_trans; apply Wn_grows. }
      split. { intros x Hx Hx'. rewrite !Wn_outside by (cbn; lia). reflexivity. }
      split. { zwr. }
      split; [lia|].
      split.
      { split; [rewrite length_app; cbn [length]; clear - Esz; Lia.lia|]. split.
        { apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; cbn; lia. }
        intros i Hi. destruct (Z.eq_dec i size) as [->|Hne].
        + replace (nth (Z.to_nat size) (acc ++ [ra]) 0) with ra.
          2:{ rewrite app_nth2 by (clear - Esz Hsz; Lia.lia). replace (Z.to_nat size - length acc)%nat with 0%nat by (clear - Esz Hsz; Lia.lia). reflexivity. }
          replace (this + 16 + 8 * size) with (this + 16 + size * 8) by lia. apply cell_Wn_hit; cbn; lia.
        + rewrite app_nth1 by (clear - Esz Hsz Hi Hne; Lia.lia).
          pose proof (TRC i ltac:(lia)) as Cw.
          apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. exact Cw. }
      apply uw_out_store; [exact Diff | clear - Esz Room; Lia.lia]. }
  destruct STEP as (regs1 & M1 & size1 & acc1 & RUN1 & P10 & P11 & P12 & P13 & P14 & P15 & P8 & P9 & K1 & G1 & A1 & W1 & Hs1 & TW1 & EO).
  rewrite EO.
  pose proof TW1 as (Esz1 & CS1 & TRC1).
  assert (Hlen1 : Z.of_nat (length acc1) = size1) by (symmetry; exact Esz1).
  assert (C2' : cellA M1 (bp - 16) 8 fpn).
  { apply (cell_agree M M1); [|lia|cbn; lia|exact C2]. intros x Hx. apply A1; cbn in Hx; lia. }

  destruct (Z.le_gt_cases fpn bp) as [Back|Fwd].
  { rewrite (rchain_invalid L ar _ _ _ _ CH') by (unfold HAR.fvalid; clear - Back; Lia.lia). rewrite uw_out_nil, Hlen1.
    eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exact TW1]]]].
    - eapply msteps_trans; [exact RUN1|]. zld F_9bb90 D_9bb90 (bp - 16) C2'. zbtk F_9bb94 D_9bb94. apply mst_refl.
    - intros; rewrite <- (K1 r) by assumption; kept_solve. }
  destruct (Z.le_gt_cases (top - 16) fpn) as [High|Inr].
  { rewrite (rchain_invalid L ar _ _ _ _ CH') by (unfold HAR.fvalid; rewrite Etop; clear - High; Lia.lia). rewrite uw_out_nil, Hlen1.
    eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exact TW1]]]].
    - eapply msteps_trans; [exact RUN1|]. zld F_9bb90 D_9bb90 (bp - 16) C2'. zbft F_9bb94 D_9bb94. zbtk F_9bb98 D_9bb98. apply mst_refl.
    - intros; rewrite <- (K1 r) by assumption; kept_solve. }
  destruct (Z.eq_dec (fpn mod 8) 0) as [Al|Nal].
  -
    assert (Hland : Z.land fpn 7 = 0). { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Al. }
    assert (RUNm : exists regs2, msteps ASEGS (mkst regs1 (0x9bbe0 : word) M1 rom) (mkst regs2 (0x9bbbc : word) M1 rom)
              /\ getr regs2 10 = Z_to_bv 64 this /\ getr regs2 11 = Z_to_bv 64 pc /\ getr regs2 12 = Z_to_bv 64 fpn /\ getr regs2 13 = Z_to_bv 64 4096
              /\ getr regs2 14 = Z_to_bv 64 (this + 16) /\ getr regs2 15 = Z_to_bv 64 size1 /\ getr regs2 8 = Z_to_bv 64 30 /\ getr regs2 9 = Z_to_bv 64 (top - 16)
              /\ (forall r : reg, r <> 12%bv -> r <> 16%bv -> r <> 17%bv -> getr regs2 r = getr regs1 r)).
    { eexists. split.
      { zld F_9bb90 D_9bb90 (bp - 16) C2'. zbft F_9bb94 D_9bb94. zbft F_9bb98 D_9bb98.
        stepn F_9bb9c D_9bb9c. rwH. rewrite art_zb_andi by lia. rewrite Hland.
        zstep F_9bba0 D_9bba0. zbtk F_9bba4 D_9bba4. apply mst_refl. }
      repeat (split; [gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]|]). intros; kept_solve. }
    destruct RUNm as (regs2 & RUNm & T10 & T11 & T12 & T13 & T14 & T15 & T8 & T9 & Km).
    destruct (IH regs2 M1 M0 rom this pc fpn top bp size1 acc1 RC' ltac:(lia) T10 T11 T12 T13 T14 T15 T8 T9
                ltac:(lia) Hpc Hthis ltac:(lia) ltac:(lia) Htop Al ltac:(lia) Etop W1 CH'
                ltac:(intros x Hx; rewrite A1 by lia; apply AG0; lia) TW1) as (regs' & M' & RUN2 & K2 & G2 & A2 & SZ2).
    exists regs', M'. split; [|split; [|split; [|split]]].
    + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNm|]. exact RUN2.
    + intros r N12 N15 N16 N17. rewrite K2 by assumption. rewrite Km by assumption. apply K1; assumption.
    + eapply mem_grows_trans; [exact G1 | exact G2].
    + intros x Hx Hx'. rewrite A2 by assumption. apply A1; assumption.
    + exact SZ2.
  -
    rewrite (rchain_invalid L ar _ _ _ _ CH') by (unfold HAR.fvalid; clear - Nal; tauto). rewrite uw_out_nil, Hlen1.
    assert (Hland : Z.land fpn 7 <> 0). { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact Nal. }
    pose proof (Z_land_upper_7 fpn ltac:(lia)) as Lu. pose proof (proj2 (Z.land_nonneg fpn 7) ltac:(left; lia)) as Ln.
    eexists _, M1. split; [|split; [|split; [exact G1 | split; [exact A1 | exact TW1]]]].
    + eapply msteps_trans; [exact RUN1|]. zld F_9bb90 D_9bb90 (bp - 16) C2'. zbft F_9bb94 D_9bb94. zbft F_9bb98 D_9bb98.
      stepn F_9bb9c D_9bb9c. rwH. rewrite art_zb_andi by lia.
      zstep F_9bba0 D_9bba0.
      stepb_ft F_9bba4 D_9bba4 ltac:(rwH; rewrite art_c_eq_zb by lia; apply Z.eqb_neq; exact Hland).
      apply mst_refl.
    + intros; rewrite <- (K1 r) by assumption; kept_solve.
Qed.

Lemma art_unwind_fast_run_fn : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z) (RC : list Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 2064 <= bp - 16 -> 0 <= bot -> bot < bp -> bp < top - 16 -> top < 2 ^ 63 -> bp mod 8 = 0 -> 0 <= pc < 2 ^ 64 ->
  0x69c000 + 64 <= sp ->
  HeapIfaceA.ar_stack_top ar = top -> HAR.rchain L ar M bot bp RC ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x9bafc : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> ~ (sp - 64 <= U x < sp) -> M' x = M x)
    /\ trace_is M' this (HAR.akey pc RC).
Proof.
  intros regs M rom raw sp this pc bp top bot RC H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbot' Hbp Htop Hbp8 Hpc IMG Etop CH W Wt Cg Cps.
  assert (PRE : exists regs1 M1, msteps ASEGS (mkst regs (0x9bafc : word) M rom) (mkst regs1 (0x9bbbc : word) M1 rom)
     /\ getr regs1 10 = Z_to_bv 64 this /\ getr regs1 11 = Z_to_bv 64 pc /\ getr regs1 12 = Z_to_bv 64 bp /\ getr regs1 13 = Z_to_bv 64 4096
     /\ getr regs1 14 = Z_to_bv 64 (this + 16) /\ getr regs1 15 = Z_to_bv 64 1 /\ getr regs1 8 = Z_to_bv 64 30 /\ getr regs1 9 = Z_to_bv 64 (top - 16)
     /\ getr regs1 2 = Z_to_bv 64 (sp - 64)
     /\ (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs1 r = getr regs r)
     /\ M1 = Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
               (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (this + 8) 1) (this + 16) pc).
  { eexists _, _. split.
    - zstep F_9baac D_9baac.
      zsd F_9bab0 D_9bab0 (sp - 8) (U raw) ltac:(rewok W). zsd F_9bab4 D_9bab4 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_9bab8 D_9bab8 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_9babc D_9babc (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_9bac0 D_9bac0 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_9bac4 D_9bac4 (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zsd F_9bac8 D_9bac8 (sp - 56) (U (getr regs 21)) ltac:(rewok W). zsd F_9bacc D_9bacc (sp - 64) (U (getr regs 22)) ltac:(rewok W).
      zstep F_9bad0 D_9bad0. zstep F_9bad4 D_9bad4. zstep F_9bad8 D_9bad8. zstep F_9badc D_9badc.
      zbft F_9bae0 D_9bae0.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg' : cellA X 0x13d8a8 8 0x1d5ba0) by (recell Cg); assert (Cps' : cellA X 0x1d5ba0 8 4096) by (recell Cps) end.
      zstep F_9bae4 D_9bae4. zld F_9bae8 D_9bae8 0x13d8a8 Cg'. zld F_9baec D_9baec 0x1d5ba0 Cps'.
      zbft F_9baf0 D_9baf0.
      zstep F_9baf4 D_9baf4.
      stepn F_9baf8 D_9baf8. rwH. rewrite art_zb_srli by lia.
      zsw F_9bafc D_9bafc (this + 8) 1 ltac:(rewok Wt).
      zsd F_9bb00 D_9bb00 (this + 16) pc ltac:(rewok Wt).
      assert (Htop12 : 1 <= top / 2 ^ 12) by (apply Z.div_le_lower_bound; lia). assert (Htop12' : top / 2 ^ 12 < 2 ^ 52) by (apply Z.div_lt_upper_bound; lia). pose proof (art_u_lit top ltac:(lia)).
      zbtk F_9bb04 D_9bb04.
      zbft F_9bb4c D_9bb4c. zbft F_9bb50 D_9bb50.
      zstep F_9bb54 D_9bb54.
      zbft F_9bb58 D_9bb58.
      stepn F_9bb5c D_9bb5c. rwH. rewrite art_zb_andi by lia. replace (Z.land bp 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
      zbft F_9bb60 D_9bb60.
      zstep F_9bb64 D_9bb64. zstep F_9bb68 D_9bb68.
      apply mst_refl.
    - repeat (split; [gres; rwH; first [reflexivity | f_equal; lia]|]).
      split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; gres; reflexivity. } reflexivity. }
  destruct PRE as (regs1 & M1 & RUN1 & P10 & P11 & P12 & P13 & P14 & P15 & P8 & P9 & P2 & PK & EM1).
  assert (W1 : wrA M1 this 256) by (rewrite EM1; zwr).
  assert (AG1 : forall x : word, bp - 16 <= U x < top -> M1 x = M x).
  { intros x Hx. rewrite EM1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  assert (TW1 : trace_ws M1 this 1 [pc]).
  { split; [reflexivity|]. split; [rewrite EM1; zcell|].
    intros i Hi. replace i with 0 by lia. cbn [Z.to_nat nth]. replace (this + 16 + 8 * 0) with (this + 16) by lia. rewrite EM1; zcell. }
  destruct (art_uwf_loop_fn (Z.to_nat (top - bp)) regs1 M1 M rom this pc bp top bot 1 [pc] RC ltac:(lia) P10 P11 P12 P13 P14 P15 P8 P9
              ltac:(lia) Hpc ltac:(lia) ltac:(lia) Hbp Htop Hbp8 Hbot' Etop W1 CH AG1 TW1) as (regs2 & M2 & RUN2 & K2 & G2 & A2 & SZ2).
  rewrite <- akey_uw_out in SZ2. apply trace_ws_is in SZ2.

  assert (FR : forall off v, 0 <= off <= 56 -> cellA M1 (sp - 64 + off) 8 v -> cellA M2 (sp - 64 + off) 8 v).
  { intros off v Hoff C. apply (cell_agree M1 M2); [|lia|cbn; lia|exact C]. intros x Hx. apply A2; cbn in Hx; lia. }
  assert (C56 : cellA M2 (sp - 64 + 56) 8 (U raw)) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 56) with (sp - 8) by lia; zcell).
  assert (C48 : cellA M2 (sp - 64 + 48) 8 (U (getr regs 8))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 48) with (sp - 16) by lia; zcell).
  assert (C40 : cellA M2 (sp - 64 + 40) 8 (U (getr regs 9))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 40) with (sp - 24) by lia; zcell).
  assert (C32 : cellA M2 (sp - 64 + 32) 8 (U (getr regs 18))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 32) with (sp - 32) by lia; zcell).
  assert (C24 : cellA M2 (sp - 64 + 24) 8 (U (getr regs 19))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 24) with (sp - 40) by lia; zcell).
  assert (C16 : cellA M2 (sp - 64 + 16) 8 (U (getr regs 20))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 16) with (sp - 48) by lia; zcell).
  assert (C08 : cellA M2 (sp - 64 + 8) 8 (U (getr regs 21))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 8) with (sp - 56) by lia; zcell).
  assert (C00 : cellA M2 (sp - 64 + 0) 8 (U (getr regs 22))) by (apply FR; [lia|]; rewrite EM1; replace (sp - 64 + 0) with (sp - 64) by lia; zcell).
  assert (Q2 : getr regs2 2 = Z_to_bv 64 (sp - 64)) by (rewrite K2 by discriminate; exact P2).
  eexists _, M2. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
    zld F_9bba8 D_9bba8 (sp - 64 + 56) C56. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbac D_9bbac (sp - 64 + 48) C48. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbb0 D_9bbb0 (sp - 64 + 40) C40. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbb4 D_9bbb4 (sp - 64 + 32) C32. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbb8 D_9bbb8 (sp - 64 + 24) C24. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbbc D_9bbbc (sp - 64 + 16) C16. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbc0 D_9bbc0 (sp - 64 + 8) C08. rewrite Z_to_bv_bv_unsigned.
    zld F_9bbc4 D_9bbc4 (sp - 64 + 0) C00. rewrite Z_to_bv_bv_unsigned.
    zstep F_9bbc8 D_9bbc8.
    stepret F_9bbcc D_9bbcc raw ltac:(rwH; reflexivity).
    apply mst_refl. }
  split. { gres. f_equal. lia. }
  split. { gres. reflexivity. }
  split. { intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
           first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | rewrite K2 by discriminate; apply PK; cbn; tauto]. }
  split. { eapply mem_grows_trans; [|exact G2]. rewrite EM1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
  split. { intros x N1 N2 N3. rewrite A2 by assumption. rewrite EM1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  exact SZ2.
Qed.

Ltac uwf_prefix W Wt Cg Cps sp raw regs this pc top :=
  zstep F_9baac D_9baac;
  zsd F_9bab0 D_9bab0 (sp - 8) (U raw) ltac:(rewok W); zsd F_9bab4 D_9bab4 (sp - 16) (U (getr regs 8)) ltac:(rewok W);
  zsd F_9bab8 D_9bab8 (sp - 24) (U (getr regs 9)) ltac:(rewok W); zsd F_9babc D_9babc (sp - 32) (U (getr regs 18)) ltac:(rewok W);
  zsd F_9bac0 D_9bac0 (sp - 40) (U (getr regs 19)) ltac:(rewok W); zsd F_9bac4 D_9bac4 (sp - 48) (U (getr regs 20)) ltac:(rewok W);
  zsd F_9bac8 D_9bac8 (sp - 56) (U (getr regs 21)) ltac:(rewok W); zsd F_9bacc D_9bacc (sp - 64) (U (getr regs 22)) ltac:(rewok W);
  zstep F_9bad0 D_9bad0; zstep F_9bad4 D_9bad4; zstep F_9bad8 D_9bad8; zstep F_9badc D_9badc;
  zbft F_9bae0 D_9bae0;
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    let Cg' := fresh "Cg'" in let Cps' := fresh "Cps'" in
    assert (Cg' : cellA X 0x13d8a8 8 0x1d5ba0) by (recell Cg); assert (Cps' : cellA X 0x1d5ba0 8 4096) by (recell Cps);
    zstep F_9bae4 D_9bae4; zld F_9bae8 D_9bae8 0x13d8a8 Cg'; zld F_9baec D_9baec 0x1d5ba0 Cps' end;
  zbft F_9baf0 D_9baf0;
  zstep F_9baf4 D_9baf4;
  stepn F_9baf8 D_9baf8; rwH; rewrite art_zb_srli by lia;
  zsw F_9bafc D_9bafc (this + 8) 1 ltac:(rewok Wt);
  zsd F_9bb00 D_9bb00 (this + 16) pc ltac:(rewok Wt).

Ltac uwf_epilogue sp raw regs :=
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    let C56 := fresh "C56" in let C48 := fresh "C48" in let C40 := fresh "C40" in let C32 := fresh "C32" in
    let C24 := fresh "C24" in let C16 := fresh "C16" in let C08 := fresh "C08" in let C00 := fresh "C00" in
    assert (C56 : cellA X (sp - 64 + 56) 8 (U raw)) by (replace (sp - 64 + 56) with (sp - 8) by lia; zcell);
    assert (C48 : cellA X (sp - 64 + 48) 8 (U (getr regs 8))) by (replace (sp - 64 + 48) with (sp - 16) by lia; zcell);
    assert (C40 : cellA X (sp - 64 + 40) 8 (U (getr regs 9))) by (replace (sp - 64 + 40) with (sp - 24) by lia; zcell);
    assert (C32 : cellA X (sp - 64 + 32) 8 (U (getr regs 18))) by (replace (sp - 64 + 32) with (sp - 32) by lia; zcell);
    assert (C24 : cellA X (sp - 64 + 24) 8 (U (getr regs 19))) by (replace (sp - 64 + 24) with (sp - 40) by lia; zcell);
    assert (C16 : cellA X (sp - 64 + 16) 8 (U (getr regs 20))) by (replace (sp - 64 + 16) with (sp - 48) by lia; zcell);
    assert (C08 : cellA X (sp - 64 + 8) 8 (U (getr regs 21))) by (replace (sp - 64 + 8) with (sp - 56) by lia; zcell);
    assert (C00 : cellA X (sp - 64 + 0) 8 (U (getr regs 22))) by (replace (sp - 64 + 0) with (sp - 64) by lia; zcell);
    zld F_9bba8 D_9bba8 (sp - 64 + 56) C56; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbac D_9bbac (sp - 64 + 48) C48; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbb0 D_9bbb0 (sp - 64 + 40) C40; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbb4 D_9bbb4 (sp - 64 + 32) C32; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbb8 D_9bbb8 (sp - 64 + 24) C24; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbbc D_9bbbc (sp - 64 + 16) C16; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbc0 D_9bbc0 (sp - 64 + 8) C08; rewrite Z_to_bv_bv_unsigned;
    zld F_9bbc4 D_9bbc4 (sp - 64 + 0) C00; rewrite Z_to_bv_bv_unsigned
  end;
  zstep F_9bbc8 D_9bbc8;
  stepret F_9bbcc D_9bbcc raw ltac:(rwH; reflexivity);
  apply mst_refl.

Lemma art_unwind_fast_exit_fn : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 256 < 2 ^ 63 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> 0 <= bp < 2 ^ 63 ->
  (bp <= bot \/ top - 16 <= bp) -> 0 <= pc < 2 ^ 64 -> 0x69c000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x9bafc : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> ~ (sp - 64 <= U x < sp) -> M' x = M x)
    /\ trace_is M' this [pc].
Proof.
  intros regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbt Htop4 Htop Hbp EXIT Hpc IMG W Wt Cg Cps.
  set (M1 := Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
               (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (this + 8) 1) (this + 16) pc).
  assert (Htop12 : 1 <= top / 2 ^ 12) by (apply Z.div_le_lower_bound; lia). assert (Htop12' : top / 2 ^ 12 < 2 ^ 52) by (apply Z.div_lt_upper_bound; lia).
  pose proof (art_u_lit top ltac:(lia)) as Utop.
  assert (RUN : exists regs', msteps ASEGS (mkst regs (0x9bafc : word) M rom) (mkst regs' raw M1 rom)
                 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
                 /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)).
  { destruct (Z_le_gt_dec bp bot) as [E1|E1].
    - eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_9bb04 D_9bb04. zbft F_9bb4c D_9bb4c. zbtk F_9bb50 D_9bb50.
        uwf_epilogue sp raw regs.
      + split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
          first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity].
    - assert (E2 : top - 16 <= bp) by lia.
      eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_9bb04 D_9bb04. zbft F_9bb4c D_9bb4c. zbft F_9bb50 D_9bb50. zstep F_9bb54 D_9bb54. zbtk F_9bb58 D_9bb58.
        uwf_epilogue sp raw regs.
      + split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
          first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]. }
  destruct RUN as (regs' & RUN & P2 & P1 & PK).
  exists regs', M1. split; [exact RUN|]. split; [exact P2|]. split; [exact P1|]. split; [exact PK|].
  split. { unfold M1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
  split. { intros x N1 N2 N3. unfold M1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  split; [change (Z.of_nat (length [pc])) with 1; unfold M1; zcell|].
  intros i Hi. cbn [length] in Hi. replace i with 0%nat by (clear - Hi; Lia.lia). change (nth 0 [pc] 0) with pc. change (Z.of_nat 0) with 0.
  replace (this + 16 + 8 * 0) with (this + 16) by lia. unfold M1. zcell.
Qed.

Theorem art_unwind_fast_fn : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z) (RC : list Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 2064 <= bp - 16 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> bp < 2 ^ 63 -> bp mod 8 = 0 -> 0 <= pc < 2 ^ 64 ->
  0x69c000 + 64 <= sp ->
  HeapIfaceA.ar_stack_top ar = top -> HAR.rchain L ar M bot bp RC ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x9bafc : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> ~ (sp - 64 <= U x < sp) -> M' x = M x)
    /\ trace_is M' this (HAR.akey pc RC).
Proof.
  intros regs M rom raw sp this pc bp top bot RC H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbt Htop4 Htop Hbp Hbp8 Hpc IMG Etop CH W Wt Cg Cps.
  destruct (Z_lt_ge_dec bot bp) as [E1|E1]; [destruct (Z_lt_ge_dec bp (top - 16)) as [E2|E2]|].
  - apply (art_unwind_fast_run_fn regs M rom raw sp this pc bp top bot RC H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot E1 E2 Htop Hbp8 Hpc IMG Etop CH W Wt Cg Cps).
  - rewrite (rchain_invalid L ar _ _ _ _ CH) by (unfold HAR.fvalid; rewrite Etop; clear - E2; Lia.lia).
    apply (art_unwind_fast_exit_fn regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) ltac:(right; lia) Hpc IMG W Wt Cg Cps).
  - rewrite (rchain_invalid L ar _ _ _ _ CH) by (unfold HAR.fvalid; clear - E1; Lia.lia).
    apply (art_unwind_fast_exit_fn regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) ltac:(left; lia) Hpc IMG W Wt Cg Cps).
Qed.

End UNW.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
