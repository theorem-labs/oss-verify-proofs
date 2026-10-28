(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Frame AgentLib FileSim
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit Spec LibTail RefPrintfLib RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil MainMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0
  AsPrintfFirst AsHdrErr AsRefused AsExitDefs AsDrvDefs AsDrvMem.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aerrno_rw_any : forall m, exists e : word, rw_cells asegs m AERRNO [C4 e].
Proof.
  intros m. unfold AERRNO, ATP. change (0xbe1c90 - 0xa4) with 0xbe1bec.
  assert (RD : forall i, 0 <= i < 4 -> exists b, mrd asegs m (wa (0xbe1bec + i)) = Some b).
  { intros i Hi. unfold mrd. destruct (m (wa (0xbe1bec + i))) as [b|]; [exists b; reflexivity|].
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
    unfold wview. destruct (m (wa (0xbe1bec + i))) as [b|]; [discriminate|].
    change asegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; discriminate.
Qed.

(* [comment removed for export] *)
Lemma alatch_any : forall m, exists ib : byte, rdn RSEGS m (Z_to_bv 64 0xbdcf50) 1 = Some [ib].
Proof.
  intros m. change (rdn RSEGS) with (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn asegs).
  rewrite rdn_unfold.
  assert (E : exists b, mrd asegs m (Z_to_bv 64 0xbdcf50) = Some b).
  { unfold mrd. destruct (m (Z_to_bv 64 0xbdcf50)) as [b|]; [exists b; reflexivity|].
    exists (Z_to_bv 8 0). rewrite seg_rom_same. vm_compute. reflexivity. }
  destruct E as [b E]. rewrite E. exists b. reflexivity.
Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma adrv_cells_wf : forallb cell_wf_b adrv_cells = true. Proof. vm_compute. reflexivity. Qed.
Lemma adrv_cells_range :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
    (0x5ea840 <= a /\ a + Z.of_nat w <= 0x5edd3c) \/ (a = 0x6a7290 /\ w = 1%nat) \/ (0xc01ce0 <= a /\ a + Z.of_nat w <= 0xc01f24) \/ (a = 0xc02388 /\ w = 8%nat) end) adrv_cells.   (* [comment removed for export] *)
Proof. unfold adrv_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
Lemma astdout0_wf : forallb cell_wf_b astdout0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma astdout0_range : Forall (fun c : Z * nat * Z => match c with (a, w, _) => 0x5ede88 <= a /\ a + Z.of_nat w <= 0x5edf1c end) astdout0.
Proof. unfold astdout0. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

Lemma cells_ok_In : forall m cs c, cells_ok m cs -> In c cs -> cell_ok m c.
Proof. intros m cs c CO IN. exact (proj1 (Forall_forall _ _) CO _ IN). Qed.
Lemma cells_ok_incl : forall m c1 c2, cells_ok m c2 -> incl c1 c2 -> cells_ok m c1.
Proof. intros m c1 c2 H2 HI. apply Forall_forall. intros c Hc. exact (cells_ok_In _ _ _ H2 (HI _ Hc)). Qed.
Lemma cells_ok_app : forall m c1 c2, cells_ok m c1 -> cells_ok m c2 -> cells_ok m (c1 ++ c2).
Proof. intros m c1 c2 H1 H2. unfold cells_ok in *. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_rdn : forall m a cs, rw_cells asegs m a cs -> rdn RSEGS m (Z_to_bv 64 a) (cells_size cs) = Some (cells_bytes cs).
Proof.
  intros m a cs [[WF BA] _].
  pose proof (bytes_at_rdn asegs m a (cells_bytes cs) 0 (cells_size cs) BA) as R.
  rewrite Z.add_0_r, firstn_all2 in R; [| cbn [skipn]; rewrite cells_bytes_length by exact WF; lia].
  apply R. cbn [skipn]. rewrite cells_bytes_length by exact WF. lia.
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
Lemma cells_of_C8C8C8 : forall m a v1 v2 v3, rw_cells asegs m a [C8 (TacX.wz v1); C8 (TacX.wz v2); C8 (TacX.wz v3)] -> 0 <= a -> a + 24 < 2 ^ 64 ->
  cell_ok m (a, 8%nat, v1) /\ cell_ok m (a + 8, 8%nat, v2) /\ cell_ok m (a + 16, 8%nat, v3).
Proof.
  intros m a v1 v2 v3 RC Ha Ha2.
  apply (proj1 (rw_cells_app asegs m a [C8 (TacX.wz v1)] [C8 (TacX.wz v2); C8 (TacX.wz v3)])) in RC. destruct RC as [R1 R2].
  change (Z.of_nat (cells_size [C8 (TacX.wz v1)])) with 8 in R2.
  destruct (cells_of_C8C8 m (a + 8) v2 v3 R2 ltac:(lia) ltac:(lia)) as [C2 C3].
  split; [exact (cell_of_C8 m a v1 R1)|]. split; [exact C2|]. replace (a + 16) with (a + 8 + 8) by lia. exact C3.
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

(* [comment removed for export] *)
Ltac acells AC :=
  let R := fresh "R" in let F := fresh "F" in let W := fresh "W" in
  pose proof (ACONST_drv_reals _ AC) as R; pose proof (ACONST_drv_flags _ AC) as F; pose proof (ACONST_drv_shwords _ AC) as W;
  decompose [and] R; decompose [and] F; decompose [and] W; clear R F W.

(* [comment removed for export] *)
Lemma hf_cells_of : forall m, ACONST m -> cells_ok m adrv_cells -> cells_ok m hf_cells.
Proof.
  intros m AC CE. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2] end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_SHORT _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_SHORT 0 0 X ltac:(unfold ASHW_MSG_SHORT; lia) ltac:(unfold ASHW_MSG_SHORT; lia)) as [S1 S2];
    change (ASHW_MSG_SHORT + 8) with 2147485936 in S2 end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_USAGE _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_USAGE 0 0 X ltac:(unfold ASHW_MSG_USAGE; lia) ltac:(unfold ASHW_MSG_USAGE; lia)) as [U1 U2];
    change (ASHW_MSG_USAGE + 8) with 2147467816 in U2 end.
  unfold hf_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact S1 | exact S2 | exact U1 | exact U2
          | unfold cell_ok; first [exact I1 | exact I2]
          | eapply (cells_ok_In m adrv_cells); [exact CE | solve [in_solve]] ].
Qed.


(* [comment removed for export] *)
Lemma rf_cells_of : forall m, ACONST m -> cells_ok m adrv_cells -> cells_ok m rf_cells.
Proof.
  intros m AC CE. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2];
    change (AINITED_CELL + 1) with 6993369 in I2 end.
  lazymatch goal with X : rw_cells asegs m ACF_CHKPRINTF_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  lazymatch goal with X : rw_cells asegs m ASHW_MSG_REFUSED _ |- _ =>
    pose proof (cells_of_C8C8 m ASHW_MSG_REFUSED 0 0 X ltac:(unfold ASHW_MSG_REFUSED; lia) ltac:(unfold ASHW_MSG_REFUSED; lia)) as [S1 S2];
    change (ASHW_MSG_REFUSED + 8) with 2147474960 in S2 end.
  unfold rf_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact S1 | exact S2
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3]
          | eapply (cells_ok_In m adrv_cells); [exact CE | solve [in_solve]] ].
Qed.

(* [comment removed for export] *)
Definition xdrv_cells : list (Z * nat * Z) :=
  [(0xc01f00, 4%nat, 0); (0xc01f23, 1%nat, 0); (0xc01ce4, 4%nat, 0); (0xc01cf0, 8%nat, 0xc01cf8);
   (0xc01cf8, 8%nat, 0); (0xc01d00, 8%nat, 0x55e508); (0xc01e00, 8%nat, 0x1de71c); (0x6a7290, 1%nat, 0); (0x5ea840, 8%nat, 0x5ea840);
   (0xc02388, 8%nat, 0)]%Z.
Lemma xdrv_cells_wf : forallb cell_wf_b xdrv_cells = true. Proof. vm_compute. reflexivity. Qed.
Lemma xdrv_of_adrv : forall m, cells_ok m adrv_cells -> cells_ok m xdrv_cells.
Proof. intros m CE. eapply cells_ok_incl; [exact CE|]. intros c Hc. unfold xdrv_cells in Hc. cbn [In] in Hc. decompose [or] Hc; subst; try contradiction; in_solve. Qed.
Lemma xdrv_cells_range :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) =>
    (a = 0x5ea840 /\ w = 8%nat) \/ (a = 0x6a7290 /\ w = 1%nat) \/ (0xc01ce4 <= a /\ a + Z.of_nat w <= 0xc01f24) \/ (a = 0xc02388 /\ w = 8%nat) end) xdrv_cells.
Proof. unfold xdrv_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
Lemma xdrv_cells_client :
  Forall (fun c : Z * nat * Z => match c with (a, w, _) => forall x, a <= x < a + Z.of_nat w -> aimg_client x end) xdrv_cells.
Proof. unfold xdrv_cells, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.

(* [comment removed for export] *)
Lemma ax_lit_cells_of : forall m, ACONST m -> cells_ok m xdrv_cells ->
  cell_ok m (0x5edd34, 4%nat, 0xffffffff) -> cell_ok m (0x5edf14, 4%nat, 0xffffffff) -> cell_ok m (0xbdd440, 1%nat, 0) -> cells_ok m ax_lit_cells.
Proof.
  intros m AC CE L2 L1 CL. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2] end.
  lazymatch goal with X : rw_cells asegs m ACOVFLAG_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I3 end.
  lazymatch goal with X : rw_cells asegs m ACANPOISON_CELL _ |- _ => pose proof (cell_of_C1 m _ _ X) as I4 end.
  unfold ax_lit_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | apply cell_of_C4; assumption
          | exact L1 | exact L2
          | exact CL
          | unfold cell_ok; first [exact I1 | exact I3 | exact I4]
          | eapply (cells_ok_In m xdrv_cells); [exact CE | solve [in_solve]] ].
Qed.

(* [comment removed for export] *)
Lemma ax_atexit_cells_of_pre : forall m, cells_ok m aatexit_pre_cells -> cells_ok m (ax_atexit_cells false).
Proof. intros m CE. eapply cells_ok_incl; [exact CE|]. intros c Hc. cbn [ax_atexit_cells In] in Hc. decompose [or] Hc; subst; try contradiction; in_solve. Qed.
Lemma ax_atexit_cells_of_reg : forall m, cells_ok m aatexit_reg_cells -> cells_ok m (ax_atexit_cells true).
Proof. intros m CE. exact CE. Qed.

(* [comment removed for export] *)
Lemma ax_flush_cells_of : forall m k, astdout_after m k -> cells_ok m ax_flush_cells.
Proof.
  intros m k ST. destruct ST. unfold ax_flush_cells, cells_ok. repeat apply Forall_cons; try apply Forall_nil; unfold cell_ok; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
    rewrite ov_rdn in RD. cbn [rdn Lib.PropExec.rdn] in RD. unfold mrd in RD.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    - cbn in RD. unfold TacX.b8 in RD. congruence.
    - exfalso. change asegs with RSEGS in RD. rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|].
      rewrite u_small; [lia | unfold AAPP_HI in *; lia].
  Qed.
End Q.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
