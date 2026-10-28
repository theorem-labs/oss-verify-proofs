From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_ContStmt LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRepFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BllocRep BG_Free6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBP LbB_PmExit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DiagStmt LbB_WoDiagP LbB_WoKit2 LbB_WoDiagF LbB_PmMagW LbB_PmHTK.
Import ListNotations.


Open Scope Z_scope.

Definition D4L : list nat := [14; 16; 20; 21]%nat.
Definition D4BS : list byte := map (Z_to_bv 8) (wo_sh D4L).
Definition d4_sl (a b : nat) : list byte := firstn (b - a) (skipn a D4BS).

Section D4ShD.
  Context {HCEIL : HeapCeil}.

  Definition d4_U (ff : Z) (m : mem) : Prop :=
    u8arr asegs m (sh ff) (d4_sl 0 76) /\ u8arr asegs m (sh ff + 79) (d4_sl 79 84)
    /\ u8arr asegs m (sh ff + 87) (d4_sl 87 92) /\ u8arr asegs m (sh ff + 95) (d4_sl 95 286)
    /\ u8arr asegs m (sh ff + 336) (d4_sl 336 476).
  Definition d4_seg (m : mem) (A n v : Z) : Prop := u8arr asegs m A (repeat (Z_to_bv 8 v) (Z.to_nat n)).
  Definition d4_U_free (ff : Z) (iv : Z * Z) : Prop :=
    snd iv <= sh ff \/ sh ff + 476 <= fst iv \/ (sh ff + 76 <= fst iv /\ snd iv <= sh ff + 79)
    \/ (sh ff + 84 <= fst iv /\ snd iv <= sh ff + 87) \/ (sh ff + 92 <= fst iv /\ snd iv <= sh ff + 95)
    \/ (sh ff + 286 <= fst iv /\ snd iv <= sh ff + 336).
End D4ShD.

Section D4ShL.
  Context {HCEIL : HeapCeil}.

  Lemma d4a_len476 : length D4BS = 476%nat.
  Proof. vm_compute. reflexivity. Qed.

  Lemma d4a_sl_len : forall a b, (a <= b <= 476)%nat -> length (d4_sl a b) = (b - a)%nat.
  Proof. intros a b Hab. unfold d4_sl. rewrite length_firstn, length_skipn, d4a_len476. lia. Qed.

  Lemma d4a_split : D4BS = d4_sl 0 76 ++ d4_sl 76 79 ++ d4_sl 79 84 ++ d4_sl 84 87 ++ d4_sl 87 92
    ++ d4_sl 92 95 ++ d4_sl 95 286 ++ d4_sl 286 336 ++ d4_sl 336 476.
  Proof. vm_compute. reflexivity. Qed.

  Lemma d4a_app : forall m A l1 l2,
    u8arr asegs m A (l1 ++ l2) <-> u8arr asegs m A l1 /\ u8arr asegs m (A + Z.of_nat (length l1)) l2.
  Proof.
    intros m A l1 l2. unfold u8arr. rewrite length_app, Nat2Z.inj_add, bytes_at_app, wr_at_app by lia. tauto.
  Qed.

  Lemma d4a_at : forall m A A' l, A = A' -> u8arr asegs m A l -> u8arr asegs m A' l.
  Proof. intros m A A' l E U. subst A'. exact U. Qed.

  Lemma d4_U_of_shad : forall ff m, bp_shad ff D4L m -> d4_U ff m.
  Proof.
    intros ff m HS. unfold bp_shad in HS. change (map (Z_to_bv 8) (wo_sh D4L)) with D4BS in HS.
    rewrite d4a_split in HS.
    apply d4a_app in HS. destruct HS as [U0 HS].
    apply d4a_app in HS. destruct HS as [_ HS].
    apply d4a_app in HS. destruct HS as [U79 HS].
    apply d4a_app in HS. destruct HS as [_ HS].
    apply d4a_app in HS. destruct HS as [U87 HS].
    apply d4a_app in HS. destruct HS as [_ HS].
    apply d4a_app in HS. destruct HS as [U95 HS].
    apply d4a_app in HS. destruct HS as [_ U336].
    rewrite !d4a_sl_len in * by lia.
    unfold d4_U. split; [exact U0|].
    split; [revert U79; apply d4a_at; lia|].
    split; [revert U87; apply d4a_at; lia|].
    split; [revert U95; apply d4a_at; lia|].
    revert U336; apply d4a_at; lia.
  Qed.

End D4ShL.

Section D4ShL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma d4_seg_xpres : forall LB SP X m m' A n v, xpres H LB SP X m m' ->
    (forall a, A <= a < A + n -> xclient H LB SP X a) -> d4_seg m A n v -> d4_seg m' A n v.
  Proof.
    intros LB SP X m m' A n v XP XC S. unfold d4_seg, u8arr, bytes_at, wr_at in *.
    rewrite repeat_length in *. destruct S as [(B0 & B1 & B) (W0 & W1 & W)].
    split; [split; [exact B0|split; [exact B1|]] | split; [exact W0|split; [exact W1|]]].
    - intros i Hi. rewrite <- (B i Hi). unfold mrd.
      destruct (XP (A + Z.of_nat i) ltac:(lia) (XC (A + Z.of_nat i) ltac:(lia))) as [E _]. rewrite E. reflexivity.
    - intros i Hi. destruct (XP (A + i) ltac:(lia) (XC (A + i) ltac:(lia))) as [_ Wv]. apply Wv, W, Hi.
  Qed.

  Lemma d4b_u8arr_xpres : forall LB SP X m m' A bs, xpres H LB SP X m m' ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> xclient H LB SP X a) -> u8arr asegs m A bs -> u8arr asegs m' A bs.
  Proof.
    intros LB SP X m m' A bs XP XC S. unfold u8arr, bytes_at, wr_at in *. destruct S as [(B0 & B1 & B) (W0 & W1 & W)].
    split; [split; [exact B0|split; [exact B1|]] | split; [exact W0|split; [exact W1|]]].
    - intros i Hi. rewrite <- (B i Hi). unfold mrd.
      destruct (XP (A + Z.of_nat i) ltac:(lia) (XC (A + Z.of_nat i) ltac:(lia))) as [E _]. rewrite E. reflexivity.
    - intros i Hi. destruct (XP (A + i) ltac:(lia) (XC (A + i) ltac:(lia))) as [_ Wv]. apply Wv, W, Hi.
  Qed.

  Lemma d4b_sl_len : Z.of_nat (length (d4_sl 0 76)) = 76 /\ Z.of_nat (length (d4_sl 79 84)) = 5
    /\ Z.of_nat (length (d4_sl 87 92)) = 5 /\ Z.of_nat (length (d4_sl 95 286)) = 191
    /\ Z.of_nat (length (d4_sl 336 476)) = 140.
  Proof. vm_compute. repeat split; reflexivity. Qed.

  Lemma d4_U_xpres : forall LB SP X m m' ff, xpres H LB SP X m m' ->
    (forall a, sh ff <= a < sh ff + 476 -> xclient H LB SP X a) -> d4_U ff m -> d4_U ff m'.
  Proof.
    intros LB SP X m m' ff XP XC (U1 & U2 & U3 & U4 & U5). destruct d4b_sl_len as (N1 & N2 & N3 & N4 & N5).
    unfold d4_U. repeat split; (eapply d4b_u8arr_xpres; [exact XP | | eassumption]); intros a Ha; apply XC;
      rewrite ?N1, ?N2, ?N3, ?N4, ?N5 in Ha; lia.
  Qed.

  Lemma d4b_disj : forall ff W A n, Forall (d4_U_free ff) W ->
    (forall lo hi, d4_U_free ff (lo, hi) -> A + n <= lo \/ hi <= A) -> disjoint_from W A n.
  Proof.
    intros ff W. induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros A n FW K; [exact I|].
    split; [apply K; exact (Forall_inv FW) | apply IH; [exact (Forall_inv_tail FW) | exact K]].
  Qed.

  Lemma d4_U_munch : forall ff m m' W, d4_U ff m -> munch W m m' -> wmono asegs m m' ->
    Forall (d4_U_free ff) W -> d4_U ff m'.
  Proof.
    intros ff m m' W (U1 & U2 & U3 & U4 & U5) MU WM FW. destruct d4b_sl_len as (N1 & N2 & N3 & N4 & N5).
    unfold d4_U. repeat split; (eapply u8arr_transport; [eassumption | exact MU | exact WM |]);
      (eapply d4b_disj; [exact FW |]); intros lo hi K; unfold d4_U_free in K; cbn [fst snd] in K;
      rewrite ?N1, ?N2, ?N3, ?N4, ?N5; lia.
  Qed.

End D4ShL.

Section D4ShL.
  Context {HCEIL : HeapCeil}.

  Lemma d4c_u8arr_app : forall m A l1 l2,
    u8arr asegs m A (l1 ++ l2) <-> u8arr asegs m A l1 /\ u8arr asegs m (A + Z.of_nat (length l1)) l2.
  Proof.
    intros m A l1 l2. unfold u8arr. rewrite length_app, Nat2Z.inj_add, bytes_at_app, wr_at_app by lia. tauto.
  Qed.

  Lemma d4c_seg_addr : forall m A k n, 0 <= A -> A mod 8 = 0 -> 0 <= n -> n mod 8 = 0 -> n <= 8 * k ->
    d4_seg m (sh A) k 0 -> addressable m A n.
  Proof.
    intros m A k n HA HA8 Hn Hn8 Hk S. unfold addressable, SHAD.
    split; [exact Hn|]. split; [exact HA|]. split; [exact HA8|].
    rewrite shadow_of_mult8 by assumption.
    unfold d4_seg in S.
    assert (E : Z.to_nat k = (Z.to_nat (n / 8) + (Z.to_nat k - Z.to_nat (n / 8)))%nat)
      by (Z.div_mod_to_equations; lia).
    rewrite E, repeat_app in S. apply d4c_u8arr_app in S. destruct S as [S _]. exact S.
  Qed.

  Lemma d4c_seg_addr_off : forall ff m o k n, 0 <= ff -> ff mod 8 = 0 -> 0 <= o -> 0 <= n -> n mod 8 = 0 ->
    n <= 8 * k -> d4_seg m (sh ff + o) k 0 -> addressable m (ff + 8 * o) n.
  Proof.
    intros ff m o k n H0 H8 Ho Hn Hn8 Hk S. apply (d4c_seg_addr m (ff + 8 * o) k n).
    - lia.
    - Z.div_mod_to_equations. lia.
    - exact Hn.
    - exact Hn8.
    - exact Hk.
    - replace (sh (ff + 8 * o)) with (sh ff + o); [exact S|].
      unfold sh. Z.div_mod_to_equations. lia.
  Qed.

  Lemma d4_addr9 : forall ff m, 0 <= ff -> ff mod 8 = 0 -> ff + 4096 <= 2 ^ 47 ->
    d4_seg m (sh ff + 76) 3 0 -> addressable m (ff + 608) 24.
  Proof.
    intros ff m H0 H8 HT S. replace (ff + 608) with (ff + 8 * 76) by lia.
    apply (d4c_seg_addr_off ff m 76 3 24); [exact H0|exact H8|lia|lia|reflexivity|lia|exact S].
  Qed.

  Lemma d4_addr9_16 : forall ff m, 0 <= ff -> ff mod 8 = 0 -> ff + 4096 <= 2 ^ 47 ->
    d4_seg m (sh ff + 76) 3 0 -> addressable m (ff + 608) 16.
  Proof.
    intros ff m H0 H8 HT S. replace (ff + 608) with (ff + 8 * 76) by lia.
    apply (d4c_seg_addr_off ff m 76 3 16); [exact H0|exact H8|lia|lia|reflexivity|lia|exact S].
  Qed.

  Lemma d4_addr10 : forall ff m, 0 <= ff -> ff mod 8 = 0 -> ff + 4096 <= 2 ^ 47 ->
    d4_seg m (sh ff + 84) 3 0 -> addressable m (ff + 672) 24.
  Proof.
    intros ff m H0 H8 HT S. replace (ff + 672) with (ff + 8 * 84) by lia.
    apply (d4c_seg_addr_off ff m 84 3 24); [exact H0|exact H8|lia|lia|reflexivity|lia|exact S].
  Qed.

  Lemma d4_addr11 : forall ff m, 0 <= ff -> ff mod 8 = 0 -> ff + 4096 <= 2 ^ 47 ->
    d4_seg m (sh ff + 92) 3 0 -> addressable m (ff + 736) 24.
  Proof.
    intros ff m H0 H8 HT S. replace (ff + 736) with (ff + 8 * 92) by lia.
    apply (d4c_seg_addr_off ff m 92 3 24); [exact H0|exact H8|lia|lia|reflexivity|lia|exact S].
  Qed.

End D4ShL.

Section D4ShO.
Context {HCEIL : HeapCeil}.

Lemma d4s_b1 : forall v, word_to_le_bytes 1 (Z_to_bv 64 v) = [Z_to_bv 8 (v mod 256)].
Proof.
  intros v. transitivity [Z_to_bv 8 v].
  - unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. discriminate.
  - f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma d4_seg_of_flds : forall m A n v, 0 <= A -> 0 <= n -> A + n <= 2 ^ 64 -> wr_at asegs m A n ->
    (forall i, 0 <= i < n -> fldA m (A + i) 1 v) -> d4_seg m A n (v mod 256).
Proof.
  intros m A n v HA Hn HAn WR HF.
  unfold d4_seg, u8arr. rewrite repeat_length, Z2Nat.id by exact Hn.
  split; [|exact WR].
  unfold bytes_at. rewrite repeat_length. split; [exact HA|]. split; [lia|].
  intros i Hi. rewrite nth_error_repeat by exact Hi.
  pose proof (HF (Z.of_nat i) ltac:(lia)) as Fi. unfold fldA, CRep.fld in Fi. rewrite d4s_b1 in Fi.
  lazymatch goal with |- ?s = _ =>
    change (match s with Some b => Some [b] | None => None end = Some [Z_to_bv 8 (v mod 256)]) in Fi;
    revert Fi; destruct s; intros Fi; inversion Fi; reflexivity end.
Qed.
Lemma d4_shad_of : forall ff m, 0 <= ff -> ff mod 8 = 0 -> d4_U ff m -> d4_seg m (sh ff + 76) 3 248 ->
    d4_seg m (sh ff + 84) 3 248 -> d4_seg m (sh ff + 92) 3 248 -> d4_seg m (sh ff + 286) 50 248 -> bp_shad ff D4L m.
Proof.
  intros ff m Hff H8 HU S76 S84 S92 S286.
  unfold d4_U in HU. destruct HU as (U0 & U79 & U87 & U95 & U336).
  unfold d4_seg in S76, S84, S92, S286.
  assert (E76 : d4_sl 76 79 = repeat (Z_to_bv 8 248) (Z.to_nat 3)) by (vm_compute; reflexivity).
  assert (E84 : d4_sl 84 87 = repeat (Z_to_bv 8 248) (Z.to_nat 3)) by (vm_compute; reflexivity).
  assert (E92 : d4_sl 92 95 = repeat (Z_to_bv 8 248) (Z.to_nat 3)) by (vm_compute; reflexivity).
  assert (E286 : d4_sl 286 336 = repeat (Z_to_bv 8 248) (Z.to_nat 50)) by (vm_compute; reflexivity).
  rewrite <- E76 in S76. rewrite <- E84 in S84. rewrite <- E92 in S92. rewrite <- E286 in S286.
  unfold bp_shad. change (map (Z_to_bv 8) (wo_sh D4L)) with D4BS. rewrite d4a_split.
  rewrite !d4a_app, !d4a_sl_len by lia.
  split; [exact U0|].
  split; [revert S76; apply d4a_at; lia|].
  split; [revert U79; apply d4a_at; lia|].
  split; [revert S84; apply d4a_at; lia|].
  split; [revert U87; apply d4a_at; lia|].
  split; [revert S92; apply d4a_at; lia|].
  split; [revert U95; apply d4a_at; lia|].
  split; [revert S286; apply d4a_at; lia|].
  revert U336; apply d4a_at; lia.
Qed.
Lemma d4o_seg_addr : forall m A k n, 0 <= A -> A mod 8 = 0 -> 0 <= n -> n mod 8 = 0 -> n <= 8 * k ->
  d4_seg m (sh A) k 0 -> addressable m A n.
Proof.
  intros m A k n HA HA8 Hn Hn8 Hk S. unfold addressable, SHAD.
  split; [exact Hn|]. split; [exact HA|]. split; [exact HA8|].
  rewrite shadow_of_mult8 by assumption.
  unfold d4_seg in S.
  assert (E : Z.to_nat k = (Z.to_nat (n / 8) + (Z.to_nat k - Z.to_nat (n / 8)))%nat)
    by (Z.div_mod_to_equations; lia).
  rewrite E, repeat_app in S. apply d4a_app in S. destruct S as [S _]. exact S.
Qed.

Lemma d4o_seg_addr_off : forall ff m o k n, 0 <= ff -> ff mod 8 = 0 -> 0 <= o -> 0 <= n -> n mod 8 = 0 ->
  n <= 8 * k -> d4_seg m (sh ff + o) k 0 -> addressable m (ff + 8 * o) n.
Proof.
  intros ff m o k n H0 H8 Ho Hn Hn8 Hk S. apply (d4o_seg_addr m (ff + 8 * o) k n).
  - lia.
  - Z.div_mod_to_equations. lia.
  - exact Hn.
  - exact Hn8.
  - exact Hk.
  - replace (sh (ff + 8 * o)) with (sh ff + o); [exact S|].
    unfold sh. Z.div_mod_to_equations. lia.
Qed.
Lemma d4_addr17 : forall ff m, 0 <= ff -> ff mod 8 = 0 -> ff + 4096 <= 2 ^ 47 -> d4_seg m (sh ff + 286) 50 0 -> addressable m (ff + 2288) 392.
Proof.
  intros ff m H0 H8 _ S. replace (ff + 2288) with (ff + 8 * 286) by lia.
  apply (d4o_seg_addr_off ff m 286 50 392 H0 H8); [lia | lia | reflexivity | lia | exact S].
Qed.
Lemma d4o_cons_split : d4_sl 336 476 = d4_sl 336 422 ++ repeat (Z_to_bv 8 0) 6 ++ d4_sl 428 476.
Proof. vm_compute. reflexivity. Qed.
Lemma d4_addr_cons : forall ff m, 0 <= ff -> ff mod 8 = 0 -> ff + 4096 <= 2 ^ 47 -> d4_U ff m -> addressable m (ff + 3376) 48.
Proof.
  intros ff m H0 H8 Htop U. unfold d4_U in U. destruct U as [_ [_ [_ [_ U]]]].
  rewrite d4o_cons_split in U. apply d4a_app in U. destruct U as [_ U].
  apply d4a_app in U. destruct U as [U _].
  rewrite d4a_sl_len in U by lia.
  replace (ff + 3376) with (ff + 8 * 422) by lia.
  apply (d4o_seg_addr_off ff m 422 6 48); [lia|lia|lia|lia|reflexivity|lia|].
  unfold d4_seg. change (Z.to_nat 6) with 6%nat.
  revert U. apply d4a_at. lia.
Qed.

End D4ShO.
