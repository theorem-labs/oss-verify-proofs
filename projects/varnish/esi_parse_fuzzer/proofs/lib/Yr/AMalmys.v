(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMallocH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AInvWfp.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_ro_C8 : forall (m : mem) a (w : word), bytes_at rsegs m a (le8 w) -> ro_cells rsegs m a [C8 w].
Proof. intros m a w B. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B. Qed.
Lemma bytes_ro_C4 : forall (m : mem) a (w : word), bytes_at rsegs m a (le4 w) -> ro_cells rsegs m a [C4 w].
Proof. intros m a w B. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B. Qed.
Lemma bytes_ro_C1 : forall (m : mem) a (b : byte), bytes_at rsegs m a [b] -> ro_cells rsegs m a [C1 b].
Proof. intros m a b B. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. exact B. Qed.
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma u64_ro : forall (m : mem) a v, u64_at rsegs m a v -> ro_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof. intros m a v B. apply bytes_ro_C8. exact B. Qed.
Lemma u32_ro : forall (m : mem) a v, u32_at rsegs m a v -> ro_cells rsegs m a [C4 (Z_to_bv 64 v)].
Proof. intros m a v B. apply bytes_ro_C4. exact B. Qed.
Lemma u8_ro : forall (m : mem) a v, u8_at rsegs m a v -> ro_cells rsegs m a [C1 (Z_to_bv 8 v)].
Proof. intros m a v B. apply bytes_ro_C1. exact B. Qed.

End CEIL.

(* [comment removed for export] *)
Lemma mapped_wr_at : forall (m : mem) a n, mapped m a n -> 0 <= a -> a + n <= 2^64 -> wr_at rsegs m a n.
Proof.
  intros m a n M Ha Hn. split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
  destruct (m (Z_to_bv 64 (a + i))) eqn:E; [discriminate|]. exfalso. exact (M i Hi E).
Qed.
Lemma ro_rw : forall (m : mem) a cs, ro_cells rsegs m a cs -> mapped m a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m a cs.
Proof.
  intros m a cs R M. pose proof (bytes_at_bound _ _ _ _ (proj2 R)) as B. destruct R as [WF0 BA].
  rewrite (cells_bytes_length cs WF0) in B. split; [exact (conj WF0 BA)| apply mapped_wr_at; [exact M| lia| lia]].
Qed.
(* [comment removed for export] *)
Definition byte_at (m : mem) (a : Z) : byte := match m (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint rdbytes (m : mem) (a : Z) (n : nat) : list byte :=
  match n with O => [] | S n' => byte_at m a :: rdbytes m (a + 1) n' end.
Lemma rdbytes_length : forall m n a, length (rdbytes m a n) = n.
Proof. intros m n. induction n; intros a; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
Lemma rdbytes_nth : forall m n a i, (i < n)%nat -> nth_error (rdbytes m a n) i = Some (byte_at m (a + Z.of_nat i)).
Proof.
  intros m n. induction n as [|n IH]; intros a i Hi; [lia|].
  destruct i as [|i]; cbn [rdbytes nth_error]. { rewrite Z.add_0_r. reflexivity. }
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.
Lemma rdbytes_bytes_at : forall (m : mem) a n, mapped m a (Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 2^64 ->
  bytes_at rsegs m a (rdbytes m a n).
Proof.
  intros m a n M Ha Hn. split; [lia|]. rewrite rdbytes_length. split; [lia|].
  intros i Hi. rewrite rdbytes_nth by exact Hi. unfold mrd, wa, byte_at.
  destruct (m (Z_to_bv 64 (a + Z.of_nat i))) eqn:E; [reflexivity|]. exfalso. exact (M (Z.of_nat i) ltac:(lia) E).
Qed.
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range : forall bs : list byte, 0 <= bytes_le_to_Z bs < 2 ^ (8 * Z.of_nat (length bs)).
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  rewrite lor_shiftl8_add by lia. rewrite Nat2Z.inj_succ. rewrite Z.mul_succ_r. rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.
Lemma Z_to_le_bytes_le_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; cbn [Z_to_le_bytes bytes_le_to_Z length]; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. pose proof (bytes_le_to_Z_range bs) as Hr.
  rewrite lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8). change (2^8) with 256.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
    replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs); [exact IH|].
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range bs) as R. rewrite L in R. change (2 ^ (8 * Z.of_nat 8)) with (bv_modulus 64) in R.
  rewrite bv_wrap_small by exact R. rewrite <- L. apply Z_to_le_bytes_le_to_Z.
Qed.
Lemma le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range bs) as R. rewrite L in R. change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite <- L. apply Z_to_le_bytes_le_to_Z.
Qed.
Lemma le2_of_bytes : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range bs) as R. rewrite L in R. change (2 ^ (8 * Z.of_nat 2)) with (2^16) in R.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite <- L. apply Z_to_le_bytes_le_to_Z.
Qed.
Lemma le4_word_small : forall bs : list byte, length bs = 4%nat -> bv_unsigned (le_bytes_to_word bs) < 2^32.
Proof.
  intros bs L. unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_range bs) as R. rewrite L in R.
  change (2 ^ (8 * Z.of_nat 4)) with (2^32) in R. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
(* [comment removed for export] *)
Fixpoint words8 (bs : list byte) (n : nat) : list word :=
  match n with O => [] | S n' => le_bytes_to_word (firstn 8 bs) :: words8 (skipn 8 bs) n' end.
Fixpoint words4 (bs : list byte) (n : nat) : list word :=
  match n with O => [] | S n' => le_bytes_to_word (firstn 4 bs) :: words4 (skipn 4 bs) n' end.
Lemma words8_length : forall bs n, length (words8 bs n) = n.
Proof. intros bs n. revert bs. induction n; intros bs; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma words4_length : forall bs n, length (words4 bs n) = n.
Proof. intros bs n. revert bs. induction n; intros bs; cbn; [reflexivity| now rewrite IHn]. Qed.
Lemma u64s_words8 : forall n bs, length bs = (8 * n)%nat -> u64s (words8 bs n) = bs.
Proof.
  induction n as [|n IH]; intros bs L; cbn [words8 u64s].
  - destruct bs; [reflexivity| cbn in L; lia].
  - rewrite le8_of_bytes by (rewrite firstn_length; lia). rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.
Lemma u32s_words4 : forall n bs, length bs = (4 * n)%nat -> u32s (words4 bs n) = bs.
Proof.
  induction n as [|n IH]; intros bs L; cbn [words4 u32s].
  - destruct bs; [reflexivity| cbn in L; lia].
  - rewrite le4_of_bytes by (rewrite firstn_length; lia). rewrite IH by (rewrite skipn_length; lia). apply firstn_skipn.
Qed.
Lemma words4_small : forall n bs, Forall (fun w => bv_unsigned w < 2^32) (words4 bs n).
Proof.
  induction n as [|n IH]; intros bs; cbn; constructor; [| apply IH].
  destruct (Nat.le_gt_cases 4 (length bs)).
  - apply le4_word_small. rewrite firstn_length. lia.
  - unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. pose proof (bytes_le_to_Z_range (firstn 4 bs)) as R.
    rewrite firstn_length in R. replace (Nat.min 4 (length bs)) with (length bs) in R by lia.
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2^24) by (apply Z.pow_le_mono_r; lia).
    rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma consts_cell : forall (m : mem) a bs, Forall (fun c => bytes_at rsegs m (fst c) (snd c)) (cl_consts LPA) ->
  find (fun c => Z.eqb (fst c) a) (cl_consts LPA) = Some (a, bs) -> bytes_at rsegs m a bs.
Proof.
  intros m a bs F E. apply find_some in E as [Hin _]. exact (proj1 (Forall_forall _ _) F _ Hin).
Qed.
(* [comment removed for export] *)
Lemma bytes_at_mid : forall (m : mem) a bs i n, bytes_at rsegs m a bs -> (i + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
  intros m a bs i n B L. rewrite <- (firstn_skipn i bs) in B. apply bytes_at_app in B as [_ B].
  rewrite firstn_length_le in B by lia.
  rewrite <- (firstn_skipn n (skipn i bs)) in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

(* [comment removed for export] *)
Ltac byteseq := cbn; repeat (first [reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]).
Lemma bytes_at_as : forall (m : mem) a bs bs', bytes_at rsegs m a bs -> bs = bs' -> bytes_at rsegs m a bs'.
Proof. intros; subst; assumption. Qed.

Section Consts.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : pa_ainv A m md.
  Let v := aview_of (pa_hull A) m.

  Let CF : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))). Qed.
  (* [comment removed for export] *)
  Ltac cell H a bs := pose proof (consts_cell v a bs CF eq_refl) as H.

  Let CR : consts_repr_ LPA AL_pasan (a_pl A) v.
  Proof. exact (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.

  #[using="CF AI md DR"] Lemma hit_INI : ro_cells rsegs v 0xb6098 [C1 (Z_to_bv 8 1)].
  Proof. cell H 0xb6098 [Z_to_bv 8 1]. apply bytes_ro_C1. exact H. Qed.
  #[using="CR AI md DR"] Lemma hit_RSS : ro_cells rsegs v 0x137622 [C1 (Z_to_bv 8 0)].
  Proof. pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. apply u8_ro. cbn [al_rss_limit_exceeded AL_pasan] in C. tauto. Qed.
  #[using="CR AI md DR"] Lemma hit_RZm : ro_cells rsegs v 0xb2b80 [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X1 : u16_at rsegs v (728408 + off_min_redzone) kMinRedzone) by tauto.
    assert (X2 : u16_at rsegs v (728408 + off_max_redzone) kMaxRedzone) by tauto.
    unfold u16_at, off_min_redzone, off_max_redzone, kMinRedzone, kMaxRedzone in X1, X2. cbn [Z.add] in X1, X2.
    split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [exact X1| rewrite length_le2; exact X2].
  Qed.
  #[using="CR AI md DR"] Lemma hit_MUM : ro_cells rsegs v 0xb2b78 [C8 (Z_to_bv 64 (2^40))].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_max_user_malloc) kMaxUserDefinedMallocSize) by tauto.
    apply u64_ro. exact X.
  Qed.
  #[using="CR AI md DR"] Lemma hit_SBc : ro_cells rsegs v 0xb1d78 [C8 (Z_to_bv 64 (a_sb A))].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_SpaceBeg) (p_sb (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.
  #[using="CR AI md DR"] Lemma hit_CMCS : ro_cells rsegs v 0xb60bc [C4 (Z_to_bv 64 30)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_malloc_context_size AL_pasan] in C.
    assert (X : u32_at rsegs v 745660 kMallocContextSize) by tauto. apply u32_ro. exact X.
  Qed.
  #[using="CR AI md DR"] Lemma hit_HK : ro_cells rsegs v 0x146e80 [C8 (Z_to_bv 64 0)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_malloc_hooks AL_pasan] in C.
    assert (X : fill_at rsegs v 1339008 80 0) by tauto. unfold fill_at in X.
    change (repeat (b8 0) (Z.to_nat 80)) with (le8 (Z_to_bv 64 0) ++ repeat (b8 0) 72) in X.
    apply bytes_at_app in X as [X _]. apply bytes_ro_C8. exact X.
  Qed.
  (* [comment removed for export] *)
  #[using="CF AI md DR"] Lemma hit_CFU : ro_cells rsegs v (0x146ee8 + 34) [C1 (Z_to_bv 8 1)].
  Proof.
    cell H 0x146ee8 pa_common_flags_bytes. apply bytes_ro_C1.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 34 1 H ltac:(cbn; lia))). byteseq.
  Qed.
  #[using="CF AI md DR"] Lemma hit_CFT : ro_cells rsegs v (0x146ee8 + 120) [C8 (Z_to_bv 64 18446744073709551615)].   (* [comment removed for export] *)
  Proof.
    cell H 0x146ee8 pa_common_flags_bytes. apply bytes_ro_C8.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0x146ee8 pa_common_flags_bytes 120 8 H ltac:(cbn; lia))). byteseq.
  Qed.
  #[using="CF AI md DR"] Lemma hit_AF2 : ro_cells rsegs v 0xb2c0d [C1 (Z_to_bv 8 1)].
  Proof.
    cell H 0xb2bb8 pa_asan_flags_bytes. apply bytes_ro_C1.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0xb2bb8 pa_asan_flags_bytes 85 1 H ltac:(cbn; lia))). byteseq.
  Qed.
  #[using="CF AI md DR"] Lemma hit_AF44 : ro_cells rsegs v 0xb2be4 [C4 (Z_to_bv 64 4096)].
  Proof.
    cell H 0xb2bb8 pa_asan_flags_bytes. apply bytes_ro_C4.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0xb2bb8 pa_asan_flags_bytes 44 4 H ltac:(cbn; lia))). byteseq.
  Qed.
  #[using="CF AI md DR"] Lemma hit_AF52 : ro_cells rsegs v 0xb2bec [C4 (Z_to_bv 64 kMallocFillByte)].
  Proof.
    cell H 0xb2bb8 pa_asan_flags_bytes. apply bytes_ro_C4.
    apply (bytes_at_as v _ _ _ (bytes_at_mid v 0xb2bb8 pa_asan_flags_bytes 52 4 H ltac:(cbn; lia))). byteseq.
  Qed.
  (* [comment removed for export] *)
  #[using="CF AI md DR"] Lemma hit_AF1 : ro_cells rsegs v 0xa9188 [C8 (Z_to_bv 64 0xb2bb8)].
  Proof. cell H 0xa9188 (le8 (Z_to_bv 64 0xb2bb8)). apply bytes_ro_C8. exact H. Qed.
  #[using="CF AI md DR"] Lemma hit_LS1 : ro_cells rsegs v 0xa9df0 [C8 (Z_to_bv 64 0x10)].   (* [comment removed for export] *)
  Proof. cell H 0xa9df0 (le8 (Z_to_bv 64 0x10)). apply bytes_ro_C8. exact H. Qed.
  #[using="CF AI md DR"] Lemma hit_LS2 : ro_cells rsegs v (bv_unsigned (cl_tp LPA) + 16) [C4 (Z_to_bv 64 0)].   (* [comment removed for export] *)
  Proof. cbn [cl_tp LPA]. rewrite unsigned_lit by lia. cell H 0x5e83e8 (le4 (Z_to_bv 64 0)). apply bytes_ro_C4. exact H. Qed.
  #[using="CR CF AI md DR"] Lemma hit_PCo : poison_consts v.
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var AL_pasan] in C.
    unfold poison_consts.
    cell H1 0xb4c1c [Z_to_bv 8 1]. cell H2 0xa9180 (le8 (Z_to_bv 64 0x146ee8)). cell H3 0xa9190 (le8 (Z_to_bv 64 0xb53b8)).
    cell H4 0xb53b8 (le8 (Z_to_bv 64 kShadowOffset)). cell H5 0xa9198 (le8 (Z_to_bv 64 0xb60a8)). cell H6 0xa91a0 (le8 (Z_to_bv 64 0xb60b0)).
    cell H7 0xa91a8 (le8 (Z_to_bv 64 0xb60a0)). cell H8 0xa91b0 (le8 (Z_to_bv 64 0xab038)). cell H9 0xab038 (le8 (Z_to_bv 64 0xa25c8)).
    cell H10 0xa9170 (le8 (Z_to_bv 64 0x144e60)). cell H11 0x144e60 (le8 (Z_to_bv 64 4096)).
    assert (K1 : u64_at rsegs v 745632 kHighMemEnd) by tauto. assert (K2 : u64_at rsegs v 745640 0) by tauto. assert (K3 : u64_at rsegs v 745648 0) by tauto.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try (apply bytes_ro_C8; assumption); try (apply bytes_ro_C1; assumption).
    - exact hit_CFT.
    - split; [exact (conj I (conj I (conj I I)))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. split; [exact K1|]. rewrite length_le8. apply bytes_at_app. split; [exact K2|]. rewrite length_le8. exact K3.
  Qed.
End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_inj : forall (m : mem) a bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
  (intros m a bs1 bs2; (first [ intro dR_48; dand3 dR_48 as _ _ B1 | intros (_ & _ & B1) ]); (first [ intro dR_49; dand3 dR_49 as _ _ B2 | intros (_ & _ & B2) ]); intros L). apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite <- (B1 i Hi), <- (B2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
Qed.
Lemma le8_wz_inj : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> le8 (Z_to_bv 64 a) = le8 (Z_to_bv 64 b) -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E. apply wz_inj; assumption.
Qed.

Definition pa_tsd : Z := 0x609780.

Section Thread.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : pa_ainv A m md.
  Let v := aview_of (pa_hull A) m.
  Let P := a_pl A.
  Let CF : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))). Qed.
  Let CR : consts_repr_ LPA AL_pasan (a_pl A) v.
  Proof. exact (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Ltac cell H a bs := pose proof (consts_cell v a bs CF eq_refl) as H.
  Ltac crtac := pose proof CR as C; unfold consts_repr_ in C; cbv zeta in C;
    cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory
         al_page_size_cache al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan cl_tp cl_shared cl_consts cl_segs LPA] in C;
    rewrite ?unsigned_lit in C by lia;
    unfold off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in C.

  #[using="CR CF AI md DR"] Lemma hit_tsd : u64_at rsegs v (0x5e83d8 - 88) pa_tsd /\ u64_at rsegs v pa_tsd (p_ctx P).
  Proof.
    crtac. destruct C as (_ & C). do 30 apply proj2 in C.
    lazymatch type of C with context [exists tsd, _] => idtac end.
    repeat match type of C with | (exists t, _) /\ _ => idtac | _ /\ _ => apply proj2 in C end.
    destruct C as ((tsd & T1 & _ & T2) & _).
    cell H 0x5e8380 (le8 (Z_to_bv 64 0x609780)). change (0x5e83d8 - 88) with 0x5e8380 in *.
    pose proof (bytes_at_bound _ _ _ _ T2) as B. rewrite length_le8 in B.
    assert (E : tsd = pa_tsd).
    { apply le8_wz_inj; [lia| unfold pa_tsd; lia|]. apply (bytes_at_inj v 0x5e8380); [exact T1| exact H| rewrite !length_le8; reflexivity]. }
    subst tsd. split; [exact T1| exact T2].
  Qed.

  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  (* [comment removed for export] *)
  #[using="W AI md m DR"] Lemma hit_place : aobj (p_thr P) 4096 /\ p_thr P + 4096 <= alloc_ceiling /\ p_thr P mod 16 = 0 /\
                    aobj (p_ctx P) 0x10000 /\ p_ctx P + 0x10000 <= alloc_ceiling /\
                    0 <= p_stk_top P < 2^64 /\ 0 <= p_stk_bot P < 2^64.
  Proof.
    (first [ pose proof ((place_facts A W)) as dR_1; dand14 dR_1 as Pthr Pctx _ _ _ _ _ _ _ _ _ _ _ Ptb | pose proof (place_facts A W) as (Pthr & Pctx & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ptb) ]). cbv zeta in Pthr, Pctx, Ptb.
    pose proof alloc_ceiling_val as CE. subst P.
    (first [ dand3 Pthr as Pthr1 Pthr2 Pthr3 | destruct Pthr as (Pthr1 & Pthr2 & Pthr3) ]). (first [ dand3 Pctx as Pctx1 Pctx2 Pctx3 | destruct Pctx as (Pctx1 & Pctx2 & Pctx3) ]).
    apply (proj1 (aobj_app_rangeA _ _)) in Pthr1. apply (proj1 (aobj_app_rangeA _ _)) in Pctx1.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia | apply (mod0_down _ 4096 16); [exists 256; reflexivity| assumption]].
  Qed.

  #[using="W CR CF AI md DR"] Lemma hit_TC : thread_cells v (cl_tp LPA) pa_tsd (p_ctx P) (p_thr P).
  Proof.
    destruct hit_tsd as [T1 T2]. crtac. pose proof hit_place as PL. pose proof alloc_ceiling_val as CE.
    cell H1 0xb4c20 [Z_to_bv 8 1]. cell H2 0xb4c24 (le4 (Z_to_bv 64 0)).
    assert (T3 : u64_at rsegs v (p_ctx P + 152) (p_thr P)) by (subst P; tauto).
    unfold thread_cells. cbn [cl_tp LPA]. rewrite unsigned_lit by lia.
    split; [apply bytes_ro_C1; exact H1|]. split; [apply bytes_ro_C4; exact H2|].
    split; [apply u64_ro; exact T1|]. split; [apply u64_ro; exact T2|]. split; [apply u64_ro; exact T3|].
    (first [ dand6 PL as PL1 PL2 PL3 PL4 PL5 _ | destruct PL as (PL1 & PL2 & PL3 & PL4 & PL5 & _) ]). pose proof (aobj_facts _ _ PL1) as F1. pose proof (aobj_facts _ _ PL4) as F4.
    unfold pa_tsd in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | lia].
  Qed.
  #[using="CR AI md DR"] Lemma hit_TH0 : ro_cells rsegs v (p_thr P) [C8 (Z_to_bv 64 (p_ctx P))].
  Proof. crtac. apply u64_ro. assert (X : u64_at rsegs v (p_thr (a_pl A) + 0) (p_ctx (a_pl A))) by tauto. rewrite Z.add_0_r in X. exact X. Qed.
  #[using="CR AI md DR"] Lemma hit_CT8 : ro_cells rsegs v (p_ctx P + 8) [C4 (Z_to_bv 64 0)].
  Proof. crtac. apply u32_ro. assert (X : u32_at rsegs v (p_ctx (a_pl A) + 8) kMainTid) by tauto. exact X. Qed.
  #[using="CR AI md DR"] Lemma hit_TDT : ro_cells rsegs v (p_thr P + 40) [C1 (Z_to_bv 8 0)].
  Proof. crtac. apply u8_ro. subst P; tauto. Qed.
  (* [comment removed for export] *)
  Let TM : mapped v (p_thr P) 4096.
  Proof. pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. subst P. tauto. Qed.
  #[using="TM CR AI md DR"] Lemma hit_TTB : rw_cells rsegs v (p_thr P + 8) [C8 (Z_to_bv 64 (p_stk_top P)); C8 (Z_to_bv 64 (p_stk_bot P))].
  Proof.
    crtac. assert (X1 : u64_at rsegs v (p_thr (a_pl A) + 8) (p_stk_top (a_pl A))) by tauto.
    assert (X2 : u64_at rsegs v (p_thr (a_pl A) + 16) (p_stk_bot (a_pl A))) by tauto. subst P.
    apply ro_rw.
    - split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact X1|].
      rewrite length_le8. replace (p_thr (a_pl A) + 8 + Z.of_nat 8) with (p_thr (a_pl A) + 16) by lia. exact X2.
    - cbn [cells_size csize Nat.add]. intros i Hi. replace (p_thr (a_pl A) + 8 + i) with (p_thr (a_pl A) + (8 + i)) by lia. apply TM. lia.
  Qed.
  #[using="TM CR AI md DR"] Lemma hit_TUNW : rw_cells rsegs v (p_thr P + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Proof.
    crtac. assert (X : u8_at rsegs v (p_thr (a_pl A) + 3168) 0) by tauto. subst P. unfold off_th_unwinding.
    apply ro_rw; [apply u8_ro; exact X|]. cbn. intros i Hi. replace (p_thr (a_pl A) + 3168 + i) with (p_thr (a_pl A) + (3168 + i)) by lia. apply TM. lia.
  Qed.
End Thread.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u32s_of_entries : forall (m : mem) (f : Z -> Z) ks a,
  (forall i k, nth_error ks i = Some k -> u32_at rsegs m (a + 4 * Z.of_nat i) (f k)) -> 0 <= a -> a + 4 * Z.of_nat (length ks) <= 2^64 ->
  bytes_at rsegs m a (u32s (map (fun k => Z_to_bv 64 (f k)) ks)).
Proof.
  intros m f ks. induction ks as [|k ks IH]; intros a H Ha Hn; cbn [map u32s length] in *.
  - apply bytes_at_nil. lia.
  - apply bytes_at_app. split.
    + pose proof (H 0%nat k eq_refl) as X. rewrite Z.mul_0_r, Z.add_0_r in X. exact X.
    + rewrite length_le4. apply IH; [| lia| lia]. intros i k' Hk'. replace (a + Z.of_nat 4 + 4 * Z.of_nat i) with (a + 4 * Z.of_nat (S i)) by lia.
      apply H. exact Hk'.
Qed.

Section Cache.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (n : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Let v := aview_of (pa_hull A) m.
  Let P := a_pl A.
  (* [comment removed for export] *)
  Local Notation c := (class_of n).
  Local Notation ks' := (pk_chunks (a_cache A (class_of n))).
  Hypothesis NE : ks' <> [].
  Local Notation cnt := (Z.of_nat (length ks')).
  Local Notation kidx := (nth (length ks' - 1) ks' 0).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let TM : mapped v (p_thr P) 4096.
  Proof. pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. subst P. tauto. Qed.

  #[using="NR"] Lemma hit_class : 1 <= c <= 30 /\ c = size_class (needed_size n) /\ needed_size n <= class_size c /\ 32 <= class_size c <= kMaxSize /\
                    class_size c mod 32 = 0.
  Proof.
    assert (NSB : 1 <= needed_size n <= kMaxSize).
    { pose proof (rounded_size_ge n). pose proof (rz_size_range n).
      assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity. split; [lia|].
      apply needed_size_primary_le. apply (proj2 (from_primary_iff n)). lia. }
    pose proof (size_class_range _ NSB) as CR. pose proof (size_class_ge _ NSB) as GE. pose proof (class_size_range _ CR). pose proof (class_size_mod32 _ CR).
    unfold class_of. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [lia | assumption].
  Qed.
  #[using="W NE NR AI n md m DR Clg"] Lemma hit_ci : a_cache_inited A = true.
  Proof.
    destruct (wfC A W) as (C1 & _). destruct hit_class as (CR & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_5; dand4 dR_5 as _ _ _ CI | destruct (C1 c ltac:(lia)) as (_ & _ & _ & CI) ]). cbv zeta in CI.
    destruct (a_cache_inited A); [reflexivity|]. exfalso. apply NE. exact (CI eq_refl).
  Qed.
  #[using="W NE NR AI md m DR Clg"] Lemma hit_kidx : nth_error ks' (Z.to_nat (cnt - 1)) = Some kidx /\ In kidx ks' /\ 0 <= kidx < carved_count A c /\ 1 <= cnt <= 16.
  Proof.
    destruct (wfC A W) as (C1 & _). destruct hit_class as (CR & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_6; dand4 dR_6 as L1 _ B _ | destruct (C1 c ltac:(lia)) as (L1 & _ & B & _) ]). cbv zeta in L1, B.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. destruct C as (C & _).
    destruct (C c ltac:(lia)) as (L16 & _).
    assert (LP : (0 < length ks')%nat) by (destruct ks'; [exfalso; apply NE; reflexivity| cbn; lia]).
    assert (E : nth_error ks' (Z.to_nat (cnt - 1)) = Some kidx).
    { replace (Z.to_nat (Z.of_nat (length ks') - 1)) with (length ks' - 1)%nat by lia. apply nth_error_nth'. lia. }
    pose proof (nth_error_In _ _ E) as IN. split; [exact E|]. split; [exact IN|]. split; [exact (B _ IN)|].
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="TM W NE NR AI md DR"] Lemma hit_PC : exists ks, length ks = 16%nat /\
    nth_error ks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (kidx * class_size c / kCompactPtrScale)) /\
    Forall (fun w => bv_unsigned w < 2^32) ks /\
    firstn (length ks') ks = map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks' /\
    rw_cells rsegs v (p_thr P + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Proof.
    (first [ dand5 hit_class as CR _ _ CSR _ | destruct hit_class as (CR & _ & _ & CSR & _) ]). (first [ dand4 hit_kidx as KE KIN KB CB16 | destruct hit_kidx as (KE & KIN & KB & CB16) ]). pose proof hit_ci as CI.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. destruct C as (C & _).
    (first [ pose proof ((C c ltac:(lia))) as dR_9; dand5 dR_9 as L16 Hcnt Hmax Hent Hjunk | destruct (C c ltac:(lia)) as (L16 & Hcnt & Hmax & Hent & Hjunk) ]). rewrite CI in Hmax. cbn [andb negb] in Hmax.
    destruct (Z.eqb_spec c 0); [lia|]. destruct Hmax as [Hmax Hsz]. (first [ dex1 Hjunk as jb; destruct Hjunk as [Ljb Bjb] | dand3 Hjunk as jb Ljb Bjb | destruct Hjunk as (jb & Ljb & Bjb) ]).
    pose proof (place_facts A W) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE.
    (first [ dand3 Pthr as Pthr PthrC PthrM | destruct Pthr as (Pthr & PthrC & PthrM) ]). apply app_facts in Pthr.
    unfold off_th_per_class, off_th_alloc_cache, off_pc_count, off_pc_max_count, off_pc_class_size, off_pc_chunk, kPerClassSize in *.
    set (e := p_thr P + 208 + 80 * c). replace (p_thr (a_pl A) + (208 + 80 * c)) with e in * by (subst e P; lia).
    set (ks := map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks' ++ words4 jb (16 - length ks')).
    (* [comment removed for export] *)
    assert (SMALL : forall k, In k ks' -> 0 <= k * class_size c / kCompactPtrScale < 2^32).
    { intros k Hk. destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_12; dand4 dR_12 as _ _ B _ | destruct (C1 c ltac:(lia)) as (_ & _ & B & _) ]). cbv zeta in B. specialize (B k Hk).
      (first [ pose proof ((carved_chunk_bounds A c k W CR B)) as dR_13; dand3 dR_13 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W CR B) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      unfold chunk_addr, kCompactPtrScale, kFreeArrayOffset in *.
      split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    exists ks. assert (LK : length ks = 16%nat).
    { subst ks. rewrite app_length, map_length, words4_length. lia. }
    split; [exact LK|]. split.
    { subst ks. rewrite nth_error_app1 by (rewrite map_length; lia). rewrite nth_error_map, KE. reflexivity. }
    split.
    { subst ks. apply Forall_app. split; [| apply words4_small]. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (k & <- & Hk).
      pose proof (SMALL k Hk). rewrite unsigned_lit by lia. lia. }
    split.
    { subst ks. rewrite firstn_app, map_length, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by (rewrite map_length; lia). reflexivity. }
    apply ro_rw.
    - split; [cbn; rewrite u32s_length, LK; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I || reflexivity|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. split; [rewrite Z.add_0_r in Hcnt; exact Hcnt|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4) with (e + 4) by lia; exact Hmax|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4 + Z.of_nat 4) with (e + 8) by lia; exact Hsz|]. rewrite length_le8.
      replace (e + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8) with (e + 16) by lia.
      subst ks. rewrite u32s_app. apply bytes_at_app. split.
      + apply u32s_of_entries; [| | ].
        2:{ subst e P. lia. }
        2:{ subst e P. lia. }
        intros i k Hk. replace (e + 16 + 4 * Z.of_nat i) with (e + (16 + 4 * Z.of_nat i)) by lia. apply Hent. exact Hk.
      + rewrite u32s_length, map_length. rewrite u32s_words4 by lia.
        replace (e + 16 + Z.of_nat (4 * length ks')) with (e + (16 + 4 * Z.of_nat (length ks'))) by lia. exact Bjb.
    - cbn [cells_size csize Nat.add]. intros i Hi. subst e P. replace (p_thr (a_pl A) + 208 + 80 * c + i) with (p_thr (a_pl A) + (208 + 80 * c + i)) by lia.
      apply TM. lia.
  Qed.
  (* [comment removed for export] *)
  #[using="TM W NR AI n md DR"] Lemma hit_stats : exists (statv v0 v1 v2 : word) (vs : list word),
    rw_cells rsegs v (p_thr P + 208 + 2576) [C8 statv] /\
    rw_cells rsegs v (p_thr P + 2800) [C8 v0; C8 v1; C8 v2] /\
    u64arr rsegs v (p_thr P + 2912) vs /\ length vs = 32%nat.
  Proof.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand4 C as _ J1 J2 _ | destruct C as (_ & J1 & J2 & _) ]).
    unfold off_th_cache_stats, off_th_stats in J1, J2. (first [ dex1 J1 as b1; destruct J1 as [L1 B1] | dand3 J1 as b1 L1 B1 | destruct J1 as (b1 & L1 & B1) ]). (first [ dex1 J2 as b2; destruct J2 as [L2 B2] | dand3 J2 as b2 L2 B2 | destruct J2 as (b2 & L2 & B2) ]).
    pose proof (place_facts A W) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE. (first [ dand3 Pthr as Pthr PthrC PthrM | destruct Pthr as (Pthr & PthrC & PthrM) ]). apply app_facts in Pthr. subst P.
    assert (TMi : forall a k, p_thr (a_pl A) <= a -> a + k <= p_thr (a_pl A) + 4096 -> mapped v a k).
    { intros a k H1 H2 i Hi. replace (a + i) with (p_thr (a_pl A) + (a - p_thr (a_pl A) + i)) by lia. apply TM. lia. }
    (* [comment removed for export] *)
    assert (X1 : bytes_at rsegs v (p_thr (a_pl A) + 208 + 2576) (u64s (words8 (firstn 8 (skipn 16 b1)) 1))).
    { rewrite u64s_words8 by (rewrite firstn_length, skipn_length; lia).
      replace (p_thr (a_pl A) + 208 + 2576) with (p_thr (a_pl A) + 2768 + Z.of_nat 16) by lia. apply bytes_at_mid; [exact B1| lia]. }
    assert (X2 : bytes_at rsegs v (p_thr (a_pl A) + 2800) (u64s (words8 (firstn 24 b2) 3))).
    { rewrite u64s_words8 by (rewrite firstn_length; lia).
      replace (p_thr (a_pl A) + 2800) with (p_thr (a_pl A) + 2800 + Z.of_nat 0) by lia.
      exact (bytes_at_mid v _ b2 0 24 B2 ltac:(lia)). }
    assert (X3 : bytes_at rsegs v (p_thr (a_pl A) + 2912) (u64s (words8 (firstn 256 (skipn 112 b2)) 32))).
    { rewrite u64s_words8 by (rewrite firstn_length, skipn_length; lia).
      replace (p_thr (a_pl A) + 2912) with (p_thr (a_pl A) + 2800 + Z.of_nat 112) by lia. apply bytes_at_mid; [exact B2| lia]. }
    cbn [words8] in X1, X2.
    eexists _, _, _, _, (words8 (firstn 256 (skipn 112 b2)) 32).
    split; [|split; [|split; [| apply words8_length]]].
    - apply ro_rw; [| apply TMi; cbn; lia]. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. exact X1.
    - apply ro_rw; [| apply TMi; cbn; lia]. split; [exact (conj I (conj I (conj I I)))|]. cbn [cells_bytes cbytes]. exact X2.
    - split; [exact X3|]. rewrite words8_length. apply mapped_wr_at; [apply TMi; lia| lia| lia].
  Qed.
End Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_mapped_high : forall (m : mem) a bs, bytes_at rsegs m a bs -> 0x60a000 <= a -> mapped m a (Z.of_nat (length bs)).
Proof.
  (intros m a bs; (first [ intro dR_50; dand3 dR_50 as Ha Hn B | intros (Ha & Hn & B) ]); intros LO i Hi E). specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  unfold mrd, wa in B. rewrite E in B. rewrite pa_rom_high in B by (rewrite unsigned_lit by lia; lia).
  destruct (nth_error bs (Z.to_nat i)) eqn:N; [discriminate|]. apply nth_error_None in N. lia.
Qed.
(* [comment removed for export] *)
Lemma bytes_at_mapped_gen : forall (m : mem) a bs, bytes_at rsegs m a bs -> 0 <= a ->
  (a + Z.of_nat (length bs) <= 0x10000 \/ 0x60a000 <= a) -> mapped m a (Z.of_nat (length bs)).
Proof.
  (intros m a bs; (first [ intro dR_51; dand3 dR_51 as Ha Hn B | intros (Ha & Hn & B) ]); intros NNa LO i Hi E). specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
  unfold mrd, wa in B. rewrite E in B. rewrite pa_seg_rom_none in B by (rewrite unsigned_lit by lia; lia).
  destruct (nth_error bs (Z.to_nat i)) eqn:N; [discriminate|]. apply nth_error_None in N. lia.
Qed.
Lemma skipn_repeat' : forall {X} (x : X) i n, skipn i (repeat x n) = repeat x (n - i).
Proof. intros X x i. induction i as [|i IH]; intros [|n]; cbn; try reflexivity. apply IH. Qed.
Lemma firstn_repeat' : forall {X} (x : X) k n, (k <= n)%nat -> firstn k (repeat x n) = repeat x k.
Proof. intros X x k. induction k as [|k IH]; intros [|n] H; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. Qed.
Lemma repeat_mid : forall {X} (x : X) n i k, (i + k <= n)%nat -> firstn k (skipn i (repeat x n)) = repeat x k.
Proof. intros X x n i k H. rewrite skipn_repeat', firstn_repeat' by lia. reflexivity. Qed.

Section Chunk.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (n kidx : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Let v := aview_of (pa_hull A) m.
  Local Notation c := (class_of n).
  (* [comment removed for export] *)
  Hypothesis KIN : In kidx (pk_chunks (a_cache A (class_of n))).
  Local Notation AB := (chunk_addr (a_sb A) (class_of n) kidx).
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  (* [comment removed for export] *)
  Ltac glia := unfold region_beg, kRegionSize, kHighMemBeg, kMaxSize, kShadowOffset in *; change (2^32)%Z with 4294967296%Z in *;
               change (2^37)%Z with 137438953472%Z in *; lia.

  #[using="W KIN NR AI md m DR"] Lemma hit_geom :
    AB = a_sb A + c * 2^32 + 16 * (kidx * class_size c / kCompactPtrScale) /\ AB mod 32 = 0 /\ AB = 8 * (AB / 8) /\
    a_sb A <= AB /\ AB + class_size c <= a_sb A + 2^37 /\ rz_size n = 8 * (rz_size n / 8) /\
    kHighMemBeg <= a_sb A /\ a_sb A + 2^37 <= alloc_ceiling /\
    region_beg (a_sb A) c <= AB /\ AB + class_size c <= region_beg (a_sb A) c + rg_mapped_user (a_reg A c) /\
    rz_size n + n <= class_size c /\ needed_size n <= class_size c /\ 1 <= c <= 30 /\ 0 <= kidx < carved_count A c /\
    0 <= kidx * class_size c / kCompactPtrScale < 2^32.
  Proof.
    (first [ pose proof ((hit_class n NR)) as dR_18; dand5 dR_18 as CR HC FIT CSR M32 | destruct (hit_class n NR) as (CR & HC & FIT & CSR & M32) ]).
    assert (KB : 0 <= kidx < carved_count A c).
    { destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_19; dand4 dR_19 as _ _ B _ | destruct (C1 c ltac:(lia)) as (_ & _ & B & _) ]). cbv zeta in B. exact (B kidx KIN). }
    (first [ pose proof ((carved_chunk_bounds A c kidx W CR KB)) as dR_20; dand4 dR_20 as B1 B2 B3 _ | pose proof (carved_chunk_bounds A c kidx W CR KB) as (B1 & B2 & B3 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
    (first [ pose proof ((sb_facts A W)) as dR_21; dand5 dR_21 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    pose proof (rz_size_range n) as RZR. pose proof (rounded_size_ge n) as RG.
    assert (NS : rounded_size n + rz_size n = needed_size n) by reflexivity.
    assert (SM : 0 <= kidx * class_size c / kCompactPtrScale < 2^32).
    { unfold chunk_addr, kCompactPtrScale, kFreeArrayOffset in *. split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. clear - KB B1 B2 B3 RB CR; nia. }
    assert (M16 : (kidx * class_size c) mod 16 = 0).
    { apply (mod0_down _ 32 16); [exists 2; reflexivity|]. rewrite Z.mul_mod, M32, Z.mul_0_r by lia. reflexivity. }
    pose proof (Z_div_exact_full_2 (kidx * class_size c) 16 ltac:(lia) M16) as E16.
    pose proof (Z_div_mod_eq_full AB 8). pose proof (mod0_down AB 32 8 ltac:(exists 4; reflexivity) B3).
    pose proof (Z_div_mod_eq_full (rz_size n) 8). pose proof (mod0_down (rz_size n) 16 8 ltac:(exists 2; reflexivity) (rz_size_mod16 n)).
    unfold chunk_addr, region_beg, kCompactPtrScale, kRegionSize, kSpaceSize, kFreeArrayOffset, kHighMemBeg in *.
    change (2^32)%Z with 4294967296%Z in *. change (2^37)%Z with 137438953472%Z in *.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try assumption.
  Qed.
  Let RM : mapped v (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)).
  Proof. (first [ dand14 hit_geom as _ _ _ _ _ _ _ _ _ _ _ _ CR _ | destruct hit_geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _) ]). pose proof (ar_regions _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) c CR) as R. unfold region_repr_ in R. cbv zeta in R. tauto. Qed.
  Let CM : forall a k, region_beg (a_sb A) c <= a -> a + k <= region_beg (a_sb A) c + rg_mapped_user (a_reg A c) -> mapped v a k.
  Proof. intros a k H1 H2 i Hi. replace (a + i) with (region_beg (a_sb A) c + (a - region_beg (a_sb A) c + i)) by lia. apply RM. lia. Qed.

  #[using="CM RM W KIN NR AI md DR"] Lemma hit_HDR : exists (b0 b1 : byte) (h2 w4 d8 : word), rw_cells rsegs v (AB + rz_size n + -16) [C1 b0; C1 b1; C2 h2; C4 w4; C8 d8].
  Proof.
    (first [ dand14 hit_geom as _ _ _ _ U1 _ HB U2 R1 R2 FIT _ CR _ | destruct hit_geom as (_ & _ & _ & _ & U1 & _ & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]). pose proof alloc_ceiling_val as CE. pose proof (rz_size_range n).
    set (a := AB + rz_size n + -16).
    assert (M16 : mapped v a 16) by (apply CM; subst a; glia).
    pose proof (rdbytes_bytes_at v a 16 M16 ltac:(subst a; glia) ltac:(subst a; glia)) as B.
    set (bs := rdbytes v a 16) in B.
    assert (L : length bs = 16%nat) by (subst bs; apply rdbytes_length).
    exists (nth 0 bs (Z_to_bv 8 0)), (nth 1 bs (Z_to_bv 8 0)), (le_bytes_to_word (firstn 2 (skipn 2 bs))), (le_bytes_to_word (firstn 4 (skipn 4 bs))),
           (le_bytes_to_word (skipn 8 bs)).
    apply ro_rw; [| exact M16]. split; [exact (conj I (conj I (conj I (conj I (conj I I)))))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite le2_of_bytes by (rewrite firstn_length, skipn_length; lia). rewrite le4_of_bytes by (rewrite firstn_length, skipn_length; lia).
    rewrite le8_of_bytes by (rewrite skipn_length; lia).
    apply (bytes_at_as v _ _ _ B). destruct bs as [|x0 [|x1 bs']]; cbn in L; try lia. cbn [nth skipn app].
    f_equal. f_equal. rewrite <- (firstn_skipn 2 bs') at 1. f_equal. rewrite <- (firstn_skipn 4 (skipn 2 bs')) at 1. rewrite skipn_skipn. f_equal.
  Qed.
  #[using="CM RM W KIN NR AI md DR"] Lemma hit_ABH : exists (j0 j1 : word), rw_cells rsegs v AB [C8 j0; C8 j1].
  Proof.
    (first [ dand14 hit_geom as _ _ _ _ U1 _ HB U2 R1 R2 FIT _ CR _ | destruct hit_geom as (_ & _ & _ & _ & U1 & _ & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]). pose proof alloc_ceiling_val as CE. (first [ pose proof ((hit_class n NR)) as dR_25; dand5 dR_25 as _ _ _ CSR _ | destruct (hit_class n NR) as (_ & _ & _ & CSR & _) ]).
    assert (M16 : mapped v AB 16) by (apply CM; glia).
    pose proof (rdbytes_bytes_at v AB 16 M16 ltac:(glia) ltac:(glia)) as B.
    set (bs := rdbytes v AB 16) in B. assert (L : length bs = 16%nat) by (subst bs; apply rdbytes_length).
    exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (skipn 8 bs)).
    apply ro_rw; [| exact M16]. split; [exact (conj I (conj I I))|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite !le8_of_bytes by (rewrite ?firstn_length, ?skipn_length; lia). rewrite firstn_skipn. exact B.
  Qed.
  #[using="CM RM W KIN NR AI md DR"] Lemma hit_USR : exists uj, rw_cells rsegs v (AB + rz_size n) [CB (Z.to_nat (Z.min n 4096)) uj].
  Proof.
    (first [ dand14 hit_geom as _ _ _ _ U1 _ HB U2 R1 R2 FIT _ CR _ | destruct hit_geom as (_ & _ & _ & _ & U1 & _ & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]). pose proof alloc_ceiling_val as CE. pose proof (rz_size_range n).
    assert (MU : mapped v (AB + rz_size n) (Z.min n 4096)) by (apply CM; lia).
    exists (rdbytes v (AB + rz_size n) (Z.to_nat (Z.min n 4096))).
    apply ro_rw; [| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; exact MU].
    split; [cbn; rewrite rdbytes_length; exact (conj eq_refl I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply rdbytes_bytes_at; [rewrite Z2Nat.id by lia; exact MU| glia|].
    rewrite Z2Nat.id by lia. glia.
  Qed.

  (* [comment removed for export] *)
  #[using="W KIN NR AI md DR"] Lemma hit_shadow : bytes_at rsegs v (sh AB) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (class_size c / 8))).
  Proof.
    (first [ dand14 hit_geom as _ _ _ _ _ _ _ _ _ _ _ _ CR _ | destruct hit_geom as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR & _) ]).
    pose proof (ar_shadow _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as S. destruct S as (S1 & _).
    exact (S1 c kidx CR (or_intror (or_introl KIN))).
  Qed.
  #[using="W KIN NR AI md DR"] Lemma hit_SH : forall d e, n = 8 * d + e -> 0 <= e < 8 -> exists olds oldp,
    ro_cells rsegs v (AB / 8 + kShadowOffset) [C1 (Z_to_bv 8 kAsanHeapLeftRedzoneMagic)] /\
    u8arr rsegs v (AB / 8 + rz_size n / 8 + kShadowOffset) olds /\ length olds = Z.to_nat d /\
    (e <> 0 -> rw_cells rsegs v (AB / 8 + rz_size n / 8 + d + kShadowOffset) [C1 oldp]).
  Proof.
    intros d e NDE ER. pose proof hit_shadow as S. pose proof alloc_ceiling_val as CE. (first [ dand14 hit_geom as _ _ Q8 _ U1 R8 HB U2 R1 R2 FIT _ CR _ | destruct hit_geom as (_ & _ & Q8 & _ & U1 & R8 & HB & U2 & R1 & R2 & FIT & _ & CR & _) ]).
    (first [ pose proof ((hit_class n NR)) as dR_29; dand5 dR_29 as _ _ _ CSR M32 | destruct (hit_class n NR) as (_ & _ & _ & CSR & M32) ]). pose proof (rz_size_range n) as RZR.
    pose proof (Z_div_mod_eq_full (class_size c) 8) as C8E. pose proof (mod0_down (class_size c) 32 8 ltac:(exists 4; reflexivity) M32) as C8M.
    assert (SHB : sh AB = AB / 8 + kShadowOffset) by reflexivity.
    assert (HI : 0x60a000 <= sh AB).
    { rewrite SHB. unfold kShadowOffset. pose proof (Z.div_le_mono 0x10007fff8000 AB 8 ltac:(lia) ltac:(glia)) as DL.
      change (0x10007fff8000 / 8) with 0x2000ffff000 in DL. lia. }
    pose proof (bytes_at_mapped_high v (sh AB) _ S HI) as SM. rewrite repeat_length, Z2Nat.id in SM by lia.
    set (fa := Z_to_bv 8 kAsanHeapLeftRedzoneMagic) in *.
    (* [comment removed for export] *)
    assert (PIECE : forall i k, 0 <= i -> 0 <= k -> i + k <= class_size c / 8 -> bytes_at rsegs v (sh AB + i) (repeat fa (Z.to_nat k))).
    { intros i k Hi Hk Hik. replace (sh AB + i) with (sh AB + Z.of_nat (Z.to_nat i)) by lia.
      rewrite <- (repeat_mid fa (Z.to_nat (class_size c / 8)) (Z.to_nat i) (Z.to_nat k)) by lia.
      apply bytes_at_mid; [exact S| rewrite repeat_length; lia]. }
    exists (repeat fa (Z.to_nat d)), fa. split; [|split; [|split]].
    - rewrite <- SHB. apply bytes_ro_C1. replace (sh AB) with (sh AB + 0) by lia. apply (PIECE 0 1); lia.
    - split.
      + replace (AB / 8 + rz_size n / 8 + kShadowOffset) with (sh AB + rz_size n / 8) by (rewrite SHB; lia). apply PIECE; lia.
      + rewrite repeat_length, Z2Nat.id by lia. apply mapped_wr_at; [| rewrite SHB in HI; lia| glia].
        intros i Hi. replace (AB / 8 + rz_size n / 8 + kShadowOffset + i) with (sh AB + (rz_size n / 8 + i)) by (rewrite SHB; lia). apply SM. lia.
    - apply repeat_length.
    - intros NE0. apply ro_rw.
      + apply bytes_ro_C1. replace (AB / 8 + rz_size n / 8 + d + kShadowOffset) with (sh AB + (rz_size n / 8 + d)) by (rewrite SHB; lia).
        apply (PIECE (rz_size n / 8 + d) 1); lia.
      + cbn. intros i Hi. replace (AB / 8 + rz_size n / 8 + d + kShadowOffset + i) with (sh AB + (rz_size n / 8 + d + i)) by (rewrite SHB; lia). apply SM. lia.
  Qed.
End Chunk.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sep.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : pa_ainv A m md.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let P := a_pl A.

  #[using="W AI md m DR"] Lemma hit_sep :
    apart (p_thr P) 4096 (a_sb A) (2^37) /\ apart (p_ctx P) 0x10000 (a_sb A) (2^37) /\ apart (p_ctx P) 0x10000 (p_thr P) 4096 /\
    apart (p_nodes0 P) kDepotNodesBlock (a_sb A) (2^37) /\ apart (p_frames0 P) kStackStoreBlockBytes (a_sb A) (2^37) /\
    apart (p_nodes0 P) kDepotNodesBlock (p_thr P) 4096 /\ apart (p_frames0 P) kStackStoreBlockBytes (p_thr P) 4096 /\
    apart (p_nodes0 P) kDepotNodesBlock (p_ctx P) 0x10000 /\ apart (p_frames0 P) kStackStoreBlockBytes (p_ctx P) 0x10000 /\
    aobj (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\
    aobj (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling.   (* [comment removed for export] *)
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_30; dand10 dR_30 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    (first [ pose proof ((sb_facts A W)) as dR_31; dand5 dR_31 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). (first [ pose proof ((place_facts A W)) as dR_32; dand5 dR_32 as _ _ Pn0 Pf0 _ | pose proof (place_facts A W) as (_ & _ & Pn0 & Pf0 & _) ]). cbv zeta in Pn0, Pf0.
    pose proof alloc_ceiling_val as CE. subst P. unfold a_thr, a_ctx, a_nodes0, a_frames0, a_b6, a_sb in *.
    assert (B6 : forall i b s, i <> 0%nat -> nth_error (big_maps A) i = Some (b, s) -> apart b s (p_sb (a_pl A)) (2^37)).
    { intros i b s Hi Hn. destruct (bm_sep A i 0 _ _ _ _ W Hn E0 Hi); unfold apart, kSpaceReserve in *; lia. }
    assert (SW : forall a s b t, apart a s b t -> apart b t a s) by (intros a s b t; unfold apart; lia).
    split; [exact (B6 4%nat _ _ ltac:(lia) E4)|]. split; [exact (B6 5%nat _ _ ltac:(lia) E5)|].
    split; [exact (bm_sep A 5 4 _ _ _ _ W E5 E4 ltac:(lia))|].
    split; [exact (B6 7%nat _ _ ltac:(lia) E7)|]. split; [exact (B6 8%nat _ _ ltac:(lia) E8)|].
    split; [exact (bm_sep A 7 4 _ _ _ _ W E7 E4 ltac:(lia))|]. split; [exact (bm_sep A 8 4 _ _ _ _ W E8 E4 ltac:(lia))|].
    split; [exact (bm_sep A 7 5 _ _ _ _ W E7 E5 ltac:(lia))|]. split; [exact (bm_sep A 8 5 _ _ _ _ W E8 E5 ltac:(lia))|].
    (first [ dand3 Pn0 as Pn01 Pn02 _ | destruct Pn0 as (Pn01 & Pn02 & _) ]). (first [ dand3 Pf0 as Pf01 Pf02 _ | destruct Pf0 as (Pf01 & Pf02 & _) ]).
    apply (proj1 (aobj_app_rangeA _ _)) in Pn01. apply (proj1 (aobj_app_rangeA _ _)) in Pf01.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
End Sep.

(* [comment removed for export] *)
#[global] Instance DepotRepL : DepotRep := {| depot_rep := depot_repL; depot_rep_agree := depot_repL_agree |}.

Section Depot.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let P := a_pl A.
  Let v := aview_of (pa_hull A) m.

  #[using="AI md"] Lemma hit_DR : depot_repL AL_pasan rsegs (a_depot A) (p_nodes0 P) (p_frames0 P) v.
  Proof. exact (ar_depot _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)). Qed.

  #[using="W AI md m Clg"] Lemma hit_depot_wf : NoDup (map depot_hashC (a_depot A)) /\ Z.of_nat (length (a_depot A)) + 1 < 65535 /\
    depot_total (a_depot A) + 3 < kStackStoreBlockFrames /\
    (forall ra, In ra (cl_sites LPA) -> In [0x58c14; ra] (p_dkeys P) /\ In [0x58c14] (p_dkeys P)) /\
    Forall (fun k => In k (p_dkeys P)) (a_depot A) /\ NoDup (a_depot A) /\ a_depot A <> [].
  Proof.
    (first [ pose proof ((wfD A W)) as dR_35; dand3 dR_35 as INC ND NN | destruct (wfD A W) as (INC & ND & NN) ]). pose proof (wfP A W) as PL. pose proof (wf_place_dkeys _ _ PL) as DK.
    (first [ dand3 DK as DK1 DK2 DK3 | destruct DK as (DK1 & DK2 & DK3) ]). clear PL.
    assert (INC' : incl (a_depot A) (p_dkeys (a_pl A))) by (intros k Hk; exact (proj1 (Forall_forall _ _) INC k Hk)).
    (first [ pose proof ((depot_universe_bounds _ _ DK1 DK3 ND INC')) as dR_37; dand3 dR_37 as L1 _ L3 | pose proof (depot_universe_bounds _ _ DK1 DK3 ND INC') as (L1 & _ & L3) ]).
    (first [ pose proof ((place_extra A m md AI)) as dR_38; dand6 dR_38 as _ _ _ _ SK _ | destruct (place_extra A m md AI) as (_ & _ & _ & _ & SK & _) ]). subst P.
    split; [exact (nodup_map_of_incl depot_hashC _ _ DK2 INC' ND)|]. split; [lia|]. split; [unfold kStackStoreBlockFrames; lia|].
    split; [| exact (conj INC (conj ND NN))]. intros ra Hra. apply (SK 0x58c14 ra); [cbn; tauto| exact Hra].
  Qed.
End Depot.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma hull_hi_bound : forall {DR : DepotRep} A m md lo hi, pa_ainv A m md -> In (lo, hi) (pa_hull A) -> hi <= 2^47.
Proof.
  intros DR A m md lo hi AI Hin. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  unfold pa_hull, ahull_of, ahull_of_ in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
  - unfold hull_of in Hin. apply in_map_iff in Hin as ([b s] & E & Hbs). cbn in E. injection E as <- <-.
    (* [comment removed for export] *)
    assert (SHA : forall b' s', b' mod 8 = 0 -> 0 < s' ->
              ((4096 <= b' /\ b' + s' <= kLowShadowMapBeg) \/ (kHighMemBeg <= b' /\ b' + s' <= 2^47)) ->
              (b, s) = shadow_region b' s' -> b + s <= 2^47).
    { intros b' s' Q1 Q2 Q3 Q4.
      destruct (Z_lt_le_dec 0 s) as [POS|NP].
      - pose proof (shadow_region_strict b' s' (b + s - 1) Q1 Q2 Q3) as ST. rewrite <- Q4 in ST. cbn [fst snd] in ST.
        specialize (ST ltac:(lia)). unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in ST. lia.
      - pose proof (shadow_region_len_nonneg b' s' Q2) as NN. rewrite <- Q4 in NN. cbn [snd] in NN.
        unfold shadow_region in Q4. injection Q4 as E1 E2.
        pose proof (round_down_le (sh b') 8 ltac:(lia)).
        destruct Q3 as [Q3|Q3]; [pose proof (sh_lowapp_range b' ltac:(lia)); unfold kLowShadowMapBeg in *; lia
                                | pose proof (sh_high_range b' ltac:(lia)); unfold kHighShadowMapBeg, kHighMemBeg in *; lia]. }
    unfold aregions_ in Hbs. apply in_app_iff in Hbs as [Hbs|Hbs]; [|apply in_app_iff in Hbs as [Hbs|Hbs]].
    + (* [comment removed for export] *)
      (first [ pose proof ((place_facts A W)) as dR_39; dand14 dR_39 as Pthr Pctx Pn0 Pf0 Pfs Pitab Pm64k Pgvec Pdvec Pm11 Pdtls Ppa Psp0 _ | pose proof (place_facts A W) as (Pthr & Pctx & Pn0 & Pf0 & Pfs & Pitab & Pm64k & Pgvec & Pdvec & Pm11 & Pdtls & Ppa & Psp0 & _) ]).
      cbv zeta in Pthr, Pctx, Pn0, Pf0, Pfs, Pitab, Pm64k, Pgvec, Pdvec, Pm11, Pdtls, Ppa, Psp0.
      pose proof (wfP A W) as PL. apply wf_place_cheap in PL.
      assert (SPAN : p_sp0 (a_pl A) + p_stk_span (a_pl A) <= 2^47) by tauto. clear PL.
      (first [ pose proof ((sb_facts A W)) as dR_40; dand5 dR_40 as _ SBM HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBM & HB6 & RSB & SCE) ]). unfold a_sb, a_b6 in *.
      (* [comment removed for export] *)
      assert (SHP : forall p k, app_rangeA AL_pasan p k /\ p + k <= alloc_ceiling /\ p mod 4096 = 0 -> 0 < k ->
                (b, s) = shadow_region p k -> b + s <= 2^47).
      { (intros p k; (first [ intro dR_52; dand3 dR_52 as X1 X2 X3 | intros (X1 & X2 & X3) ]); intros Xk Q4). apply app_facts in X1.
        eapply (SHA p k); [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact X3] | exact Xk | | exact Q4].
        clear - X1 X2 CE. unfold kLowShadowMapBeg, kHighMemBeg in *. lia. }
      assert (APE : forall p k k', app_rangeA AL_pasan p k /\ p + k <= alloc_ceiling /\ p mod 4096 = 0 -> k' <= k -> p + k' <= 2^47).
      { (intros p k k'; (first [ intro dR_53; dand3 dR_53 as X1 X2 X3 | intros (X1 & X2 & X3) ]); intros Xk). clear - X2 Xk CE. lia. }
      pose proof alloc_ceiling_al as ACAL. assert (AC8 : alloc_ceiling mod 8 = 0) by (apply (mod0_down _ 16 8); [exists 2; reflexivity| exact ACAL]).
      assert (RI8 : p_ri (a_pl A) mod 8 = 0).
      { unfold p_ri. apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity|]. unfold kSpaceSize. rewrite <- Zplus_mod_idemp_l, SBM. reflexivity. }
      assert (RIR : kHighMemBeg <= p_ri (a_pl A) /\ p_ri (a_pl A) + 4096 <= 2^47) by (unfold p_ri, kSpaceSize, kHighMemBeg in *; lia).
      cbn -[shadow_region Z.add Z.sub Z.mul] in Hbs. cbn [al_image_lo al_image_hi AL_pasan] in Hbs.
      destruct Hbs as [Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[Q|[]]]]]]]]]]]]]]]]]]]]]]]]]];
        (* [comment removed for export] *)
        lazymatch type of Q with
        | shadow_region ?p ?k = _ =>
            first [ eapply (SHP p k); [eassumption | reflexivity | exact (eq_sym Q)]
                  | eapply (SHA p k); [ first [exact AC8 | exact RI8 | reflexivity] | reflexivity || (clear - CE; lia)
                                      | first [right; clear - CE RIR; unfold kHighMemBeg in *; lia | left; clear - CE; unfold kLowShadowMapBeg; lia] | exact (eq_sym Q)] ]
        | stack_shadow_iv = _ => (first [ pose proof (stack_shadow_iv_facts) as dR_41; dand4 dR_41 as _ _ SSF _ | pose proof stack_shadow_iv_facts as (_ & _ & SSF & _) ]); rewrite Q in SSF; cbn [fst snd] in SSF;
                                 clear - SSF; unfold kHighMemBeg in SSF; lia
        | (p_sp0 _ - _, _) = _ => injection Q as <- <-; clear - SPAN Psp0 CE; lia
        | (p_ri _, _) = _ => injection Q as <- <-; clear - RIR CE; unfold kHighMemBeg in RIR; lia
        | _ => injection Q as <- <-;
               eapply APE; [eassumption | clear - CE; unfold kChunksBlockCount, kPtrArrayReserve, kDepotNodesBlock, kStackStoreBlockBytes, kFakeStackBytes; lia]
        end.
    + (first [ pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_42; dex1 dR_42 as c; destruct dR_42 as [Hc Hr] | pose proof ((classes_regions_inv _ _ _ _ Hbs)) as dR_42; dand3 dR_42 as c Hc Hr | destruct (classes_regions_inv _ _ _ _ Hbs) as (c & Hc & Hr) ]). (first [ pose proof ((wfR A W)) as dR_43; dand3 dR_43 as WR1 WR2 _ | destruct (wfR A W) as (WR1 & WR2 & _) ]).
      destruct (Z.eq_dec c 31) as [->|N31]. { rewrite (WR2 31) in Hr by lia. cbn in Hr. destruct Hr. }
      pose proof (region_piece_bounds A c W ltac:(lia)) as RB. cbv zeta in RB. unfold a_sb in RB.
      unfold kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *.
      assert (SHI : forall b' s', 17594333495296 <= b' -> b' + s' <= 2^47 -> 0 < s' -> (b, s) = shadow_region b' s' -> b + s <= 2^47).
      { intros b' s' Q1 Q2 Q3 Q4. pose proof (shadow_region_high b' s' Q1 Q2 Q3) as SH. rewrite <- Q4 in SH. cbn [fst snd] in SH.
        unfold kHighMemBeg in SH. lia. }
      destruct (class_regions_inv _ _ _ _ Hr) as [[Q NZ]|[[Q NZ]|[[Q NZ]|[Q NZ]]]];
        first [ injection Q as -> ->; unfold kFreeArrayOffset; lia | eapply SHI; [| | | exact Q]; unfold kFreeArrayOffset; lia ].
    + unfold sec_regions_ in Hbs. apply in_flat_map in Hbs as (sc & Hsc & Hr).
      (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_44; dand5 dR_44 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_room (cs_n sc)).
      pose proof (rounded_size_ge (cs_n sc)) as RG. rewrite needed_size2_secondary in B5 by lia.
      apply app_facts in B3.   (* [comment removed for export] *)
      destruct Hr as [Q|[Q|[]]]; [injection Q as <- <-; clear - B4 CE; lia
        | eapply (SHA (cs_map sc) (map_size (cs_n sc))); [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2] | lia
                     | clear - B3 B4 CE; unfold kLowShadowMapBeg, kHighMemBeg in *; lia | exact (eq_sym Q)]].
  - apply in_app_iff in Hin as [Hin|Hin].
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      (first [ pose proof ((wfE A W)) as dR_45; dand4 dR_45 as _ DF _ _ | destruct (wfE A W) as (_ & DF & _ & _) ]). (first [ pose proof ((proj1 (Forall_forall _ _) DF _ Hin)) as dR_46; dand4 dR_46 as B _ _ _ | pose proof (proj1 (Forall_forall _ _) DF _ Hin) as (B & _ & _ & _) ]). cbn [fst snd] in B.
      clear - B. unfold kHighShadowMapBeg, kHighMemBeg, kLowShadowBeg, kShadowGapBeg in B. lia.
    + destruct (place_extra A m md AI) as (WX1 & _). pose proof (proj1 (Forall_forall _ _) WX1 _ Hin) as B. cbn [fst snd] in B. lia.
Qed.

End CEIL2.

Section Stack.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (sp : word).
  Hypothesis AI : pa_ainv A m md.
  Let v := aview_of (pa_hull A) m.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
  Hypothesis SM : mapped v (bv_unsigned sp - ASTK) ASTK.

  #[using="SM CEIL"] Lemma hit_stk : stk rsegs v (bv_unsigned sp - ASTK) (bv_unsigned sp).
  Proof.
    pose proof (zr_word sp) as R; unfold inr64 in R. pose proof alloc_ceiling_val as CE.
    split; [lia|]. split; [lia|]. intros a Ha.
    assert (X : v (Z_to_bv 64 a) <> None).
    { replace a with (bv_unsigned sp - ASTK + (a - (bv_unsigned sp - ASTK))) by lia. apply SM. lia. }
    unfold wview, mrd, wa. destruct (v (Z_to_bv 64 a)) as [b|] eqn:E; [| exfalso; exact (X eq_refl)]. split; [discriminate| exists b; reflexivity].
  Qed.
  #[using="SM CEIL v AI md m A DR Clg"] Lemma hit_sp47 : bv_unsigned sp <= 2^47.
  Proof.
    pose proof (zr_word sp) as R; unfold inr64 in R. pose proof alloc_ceiling_val as CE. unfold ASTK in *.
    assert (X : v (Z_to_bv 64 (bv_unsigned sp - 1)) <> None).
    { replace (bv_unsigned sp - 1) with (bv_unsigned sp - 8192 + 8191) by lia. apply SM. lia. }
    pose proof (view_some_visible _ _ _ X) as VS.
    (first [ pose proof ((visible_in_hull (pa_hull A) (bv_unsigned sp - 1) VS ltac:(lia))) as dR_47; dex2 dR_47 as lo hi; destruct dR_47 as [Hin Ra] | pose proof ((visible_in_hull (pa_hull A) (bv_unsigned sp - 1) VS ltac:(lia))) as dR_47; dand4 dR_47 as lo hi Hin Ra | destruct (visible_in_hull (pa_hull A) (bv_unsigned sp - 1) VS ltac:(lia)) as (lo & hi & Hin & Ra) ]).
    pose proof (hull_hi_bound A m md lo hi AI Hin). lia.
  Qed.
End Stack.
