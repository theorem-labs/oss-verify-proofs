(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HCatExec HCatSim HSeqExec HStoreOk HShapeAlg HNodes HFrame HAgentLib HFileSim HSymExec2 HSymExec2Sound HSymRun HSymDrive HSymDriveX HMemSplit HSpec HLibTail HRefPrintfLib HRefMemcpyLib SReach RegsEquivM MainEqv HeapCeil MainMem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HArr HStep HLFrame HMState HSysStep HExec CellsX TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0 AsPrintfFirst AsHdrErr AsRefused AsExitDefs AsDrvDefs AsDrvMem.
Import ListNotations.
Import HSymExec2.SX2. Import HSymExec2Sound.SX2S.
Import HPropExec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).

Lemma aerrno_rw_any : forall m, exists e : word, rw_cells asegs m AERRNO [C4 e].
Proof.
  intros m. unfold AERRNO, ATP. change (0x6c3f18 - 0xa4) with 0x6c3e74.
  assert (RD : forall i, 0 <= i < 4 -> exists b, mrd asegs m (wa (0x6c3e74 + i)) = Some b).
  { intros i Hi. unfold mrd. destruct (m (wa (0x6c3e74 + i))) as [b|]; [exists b; reflexivity|].
    rewrite seg_rom_same. change asegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; eexists; reflexivity. }
  destruct (RD 0 ltac:(lia)) as [b0 H0]. destruct (RD 1 ltac:(lia)) as [b1 H1].
  destruct (RD 2 ltac:(lia)) as [b2 H2]. destruct (RD 3 ltac:(lia)) as [b3 H3].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split.
  - split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app].
    change (le4 ?v) with (word_to_le_bytes 4 v). rewrite word_to_le_bytes_of_lez by (reflexivity || (cbn; lia)).
    rewrite app_nil_r. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; [ | | | | lia].
    + rewrite Z.add_0_r in H0. exact H0. + exact H1. + exact H2. + exact H3.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    unfold wview. destruct (m (wa (0x6c3e74 + i))) as [b|]; [discriminate|].
    change asegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; discriminate.
Qed.

Lemma outside_of_Forall : forall (W : list (Z * Z)) x,
  Forall (fun iv => x < fst iv \/ snd iv <= x) W -> outside W x.
Proof.
  induction W as [|[l h] W IH]; intros x HF; [exact I|]. inversion HF as [|y l' Hy Hl]; subst.
  cbn [fst snd] in Hy. cbn. split; [lia | apply IH; exact Hl].
Qed.
Lemma disjoint_of_Forall : forall (W : list (Z * Z)) a n,
  Forall (fun iv => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[l h] W IH]; intros a n HF; [exact I|]. inversion HF as [|y l' Hy Hl]; subst.
  cbn [fst snd] in Hy. cbn. split; [lia | apply IH; exact Hl].
Qed.

Lemma rdn_munchW : forall W m m' (a : Z) n bs,
  munch W m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> outside W x) ->
  rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
Proof.
  intros W m m' a n bs MU HD Ha Hn HO.
  destruct n as [|n']; [cbn in *; exact HD|].
  rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
  apply MU. apply HO. exact Hx.
Qed.

Lemma cells_ok_munchW : forall W m m' cs,
  forallb cell_wf_b cs = true -> cells_ok m cs -> munch W m m' ->
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => disjoint_from W a (Z.of_nat w) end) cs ->
  cells_ok m' cs.
Proof.
  intros W m m' cs Hwf Hc MU Hd. unfold cells_ok in *.
  induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_ok in *. eapply rdn_munchW; [exact MU | exact Hok | lia | lia |]. intros y Hy. eapply disjoint_outside; [exact Hx | lia].
Qed.

Section Apres.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Lemma rdn_apresW : forall LB1 SP m m' (a : Z) n bs,
    apres H LB1 SP m m' -> rdn RSEGS m (Z_to_bv 64 a) n = Some bs -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall x, a <= x < a + Z.of_nat n -> aclient_addr H LB1 SP x) ->
    rdn RSEGS m' (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros LB1 SP m m' a n bs HP HD Ha Hn HC.
    destruct n as [|n']; [cbn in *; exact HD|].
    rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) (HC _ Hx))).
  Qed.

  Lemma cells_ok_apresW : forall LB1 SP m m' cs,
    forallb cell_wf_b cs = true -> cells_ok m cs -> apres H LB1 SP m m' ->
    Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) cs ->
    cells_ok m' cs.
  Proof.
    intros LB1 SP m m' cs Hwf Hc HP Hd. unfold cells_ok in *.
    induction cs as [|[[a w] v] cs IH]; [constructor|].
    cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
    inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
    unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    unfold cell_ok in *. eapply rdn_apresW; [exact HP | exact Hok | lia | lia |]. intros y Hy. right; left. apply Hx. exact Hy.
  Qed.
End Apres.

Lemma adrv_cells_client :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) adrv_cells.
Proof. unfold adrv_cells, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.
Lemma astdout0_client :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) astdout0.
Proof. unfold astdout0, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.

Lemma adrv_cells_wf : forallb cell_wf_b adrv_cells = true. Proof. vm_compute. reflexivity. Qed.
Lemma adrv_cells_range :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
    (0x185580 <= a /\ a + Z.of_nat w <= 0x187ff4) \/ (a = 0x18c090 /\ w = 1%nat) \/ (0x6e3f68 <= a /\ a + Z.of_nat w <= 0x6e41ac) \/ (a = 0x6e4720 /\ w = 8%nat)
    \/ (a = 0x6c3ee8 /\ w = 8%nat) \/ (0x6c1ff8 <= a /\ a + Z.of_nat w <= 0x6c2c18)
    \/ (0x6c1d50 <= a /\ a + Z.of_nat w <= 0x6c1d58)
    end) adrv_cells.
Proof. unfold adrv_cells, aios_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
Lemma astdout0_wf : forallb cell_wf_b astdout0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma astdout0_range : Forall (fun c : Z * nat * Z => match c with (a, w, _) => 0x188140 <= a /\ a + Z.of_nat w <= 0x1881d4 end) astdout0.
Proof. unfold astdout0. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

Lemma cells_ok_In : forall m cs c, cells_ok m cs -> In c cs -> cell_ok m c.
Proof. intros m cs c CO IN. exact (proj1 (Forall_forall _ _) CO _ IN). Qed.

Lemma rw_rdn : forall m a cs, rw_cells asegs m a cs -> rdn RSEGS m (Z_to_bv 64 a) (cells_size cs) = Some (cells_bytes cs).
Proof.
  intros m a cs [[WF BA] _].
  assert (L : length (cells_bytes cs) = cells_size cs) by (apply cells_bytes_length; exact WF).
  pose proof (bytes_at_rdn asegs m a (cells_bytes cs) 0 (cells_size cs) BA ltac:(lia)) as R.
  rewrite drop_0, take_ge in R by lia. rewrite Nat2Z.inj_0, Z.add_0_r in R. exact R.
Qed.
Lemma cell_of_C8 : forall m a v, rw_cells asegs m a [C8 (TacX.wz v)] -> cell_ok m (a, 8%nat, v).
Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
Lemma cell_of_C4 : forall m a v, rw_cells asegs m a [C4 (TacX.wz v)] -> cell_ok m (a, 4%nat, v).
Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
Lemma cells_of_C8C8 : forall m a v1 v2, rw_cells asegs m a [C8 (TacX.wz v1); C8 (TacX.wz v2)] -> 0 <= a -> a + 16 < 2 ^ 64 ->
  cell_ok m (a, 8%nat, v1) /\ cell_ok m (a + 8, 8%nat, v2).
Proof.
  intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. unfold cell_ok. split.
  - pose proof (rdn_firstn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R1. rewrite R1. cbn [cells_bytes cbytes app].
    rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite length_le8; lia). reflexivity.
  - pose proof (rdn_skipn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R2. unfold nat_to_word in R2.
    change (16 - 8)%nat with 8%nat in R2. replace (Z.of_nat 8) with 8 in R2 by reflexivity. rewrite lit_add_lit in R2.
    rewrite R2. cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (drop_app_length' _ _ 8) by (rewrite length_le8; reflexivity). reflexivity.
Qed.
Lemma cells_of_C1C1 : forall m a v1 v2, rw_cells asegs m a [C1 (TacX.b8 v1); C1 (TacX.b8 v2)] -> 0 <= a -> a + 2 < 2 ^ 64 ->
  rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v1] /\ rdn RSEGS m (Z_to_bv 64 (a + 1)) 1 = Some [Z_to_bv 8 v2].
Proof.
  intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. split.
  - pose proof (rdn_firstn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R1. rewrite R1. reflexivity.
  - pose proof (rdn_skipn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R2. unfold nat_to_word in R2.
    change (2 - 1)%nat with 1%nat in R2. replace (Z.of_nat 1) with 1 in R2 by reflexivity. rewrite lit_add_lit in R2.
    rewrite R2. reflexivity.
Qed.
Lemma cell_of_C1 : forall m a v, rw_cells asegs m a [C1 (TacX.b8 v)] -> rdn RSEGS m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. rewrite R. reflexivity. Qed.

Ltac acells AC :=
  let R := fresh "R" in let F := fresh "F" in let W := fresh "W" in
  pose proof (ACONST_drv_reals _ AC) as R; pose proof (ACONST_drv_flags _ AC) as F; pose proof (ACONST_drv_shwords _ AC) as W;
  decompose [and] R; decompose [and] F; decompose [and] W; clear R F W.

Lemma hf_cells_of : forall m, ACONST m -> cells_ok m adrv_cells -> cells_ok m hf_cells.
Proof.
  intros m AC CE. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2] end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_SHORT _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_SHORT 0 0 X ltac:(unfold ASHW_MSG_SHORT; lia) ltac:(unfold ASHW_MSG_SHORT; lia)) as [S1 S2];
    change (ASHW_MSG_SHORT + 8) with 2147468576 in S2 end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_USAGE _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_USAGE 0 0 X ltac:(unfold ASHW_MSG_USAGE; lia) ltac:(unfold ASHW_MSG_USAGE; lia)) as [U1 U2];
    change (ASHW_MSG_USAGE + 8) with 2147462264 in U2 end.
  unfold hf_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact S1 | exact S2 | exact U1 | exact U2
          | unfold cell_ok; first [exact I1 | exact I2]
          | eapply (cells_ok_In m adrv_cells); [exact CE | solve [in_solve]] ].
Qed.

Lemma rf_cells_of : forall m, ACONST m -> cells_ok m adrv_cells -> cells_ok m rf_cells.
Proof.
  intros m AC CE. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2];
    change (AINITED_CELL + 1) with 1639385 in I2 end.
  lazymatch goal with X : rw_cells asegs m ACF_CHKPRINTF_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_REFUSED _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_REFUSED 0 0 X ltac:(unfold ASHW_MSG_REFUSED; lia) ltac:(unfold ASHW_MSG_REFUSED; lia)) as [S1 S2];
    change (ASHW_MSG_REFUSED + 8) with 2147464680 in S2 end.
  unfold rf_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact S1 | exact S2
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3]
          | eapply (cells_ok_In m adrv_cells); [exact CE | solve [in_solve]] ].
Qed.

Definition xdrv_cells : list (Z * nat * Z) :=
  [(0x6e4188, 4%nat, 0); (0x6e41ab, 1%nat, 0); (0x6e3f6c, 4%nat, 0); (0x6e3f70, 4%nat, 3); (0x6e3f78, 8%nat, 0x6e3f80);
   (0x6e3f80, 8%nat, 0); (0x6e3f88, 8%nat, 0x163a80); (0x6e4088, 8%nat, 0xd820c); (0x18c090, 1%nat, 0); (0x185580, 8%nat, 0x185580);
   (0x6e4720, 8%nat, 0); (0x6e3f90, 8%nat, 0x1252fc); (0x6e3f98, 8%nat, 0xae744); (0x6e4090, 8%nat, 0x6c1fb8); (0x6e4098, 8%nat, 0)]%Z.

Section Q.
  Context {HCEIL : HeapCeil}.
  Lemma stack0_qsh0 : forall m lo hi (sp' : Z),
    stack0 m lo hi -> lo + 4104 <= sp' -> sp' <= hi ->
    forall a, ASHADOW_BASE + (sp' - 4096) / 8 <= a < ASHADOW_BASE + sp' / 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
  Proof.
    intros m lo hi sp' ST Hlo Hhi a Ha. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb. rewrite ASHADOW_BASE_val in Ha.
    set (x := 8 * (a - 0x7fff8000)).
    assert (Hx : lo <= x /\ x + 1 <= hi) by (subst x; Z.div_mod_to_equations; lia).
    assert (Ex : wa (sh x) = Z_to_bv 64 a).
    { unfold wa, sh. rewrite ASHADOW_BASE_val. f_equal. subst x. Z.div_mod_to_equations. lia. }
    pose proof (stack0_read0 m lo hi x 1 (Z_to_bv 64 a) ST ltac:(lia) ltac:(lia) ltac:(lia) ltac:(symmetry; exact Ex)) as RD.
    rewrite ov_rdn in RD. cbn [rdn HLPropExec.rdn] in RD. unfold mrd in RD.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    - cbn in RD. unfold TacX.b8 in RD. congruence.
    - exfalso. change asegs with RSEGS in RD. rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|].
      rewrite u_small; [lia | unfold AAPP_HI in *; lia].
  Qed.
End Q.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
