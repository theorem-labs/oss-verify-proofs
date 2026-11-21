(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Arr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Fixpoint u16s (ws : list word) : list byte :=
  match ws with [] => [] | w :: r => le2 w ++ u16s r end.

Lemma u16s_length : forall ws, length (u16s ws) = (2 * length ws)%nat.
Proof. induction ws as [|w r IH]; [reflexivity|]. cbn [u16s length]. rewrite length_app, length_le2, IH. lia. Qed.

Lemma u16s_app : forall a b, u16s (a ++ b) = u16s a ++ u16s b.
Proof. induction a as [|w a IH]; intros b; [reflexivity|]. cbn [u16s app]. rewrite IH, app_assoc. reflexivity. Qed.

Lemma u16s_split : forall ws i w, nth_error ws i = Some w ->
  exists pre post, ws = pre ++ w :: post /\ length pre = i /\
    u16s ws = u16s pre ++ le2 w ++ u16s post /\ length (u16s pre) = (2 * i)%nat.
Proof.
  intros ws i w H. destruct (nth_error_split _ _ _ H) as (pre & post & -> & Hlen).
  exists pre, post. rewrite u16s_app. cbn -[le2]. rewrite u16s_length. repeat split; lia.
Qed.

Section U16.
Variable segs : list Segment.

Definition u16arr (m : word -> option byte) (A : Z) (ws : list word) : Prop := u8arr segs m A (u16s ws).

Lemma u16arr_read : forall m A ws (i : Z) w a,
  u16arr m A ws -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 2 * i) ->
  ov_read_bytes segs m a 2 = Some (le2 w).
Proof.
  intros m A ws i w a [Hb _] Hn Hi ->.
  destruct (u16s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (2 * i)%Z with (Z.of_nat (2 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read segs m A (u16s ws) (2 * Z.to_nat i) 2 Hb).
  2:{ rewrite Eu, !length_app, length_le2, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le2; lia).
  rewrite length_le2, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Lemma u16arr_store_ok : forall m A ws (i : Z) a,
  u16arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z -> a = wa (A + 2 * i) ->
  store_ok segs m a 2 = true.
Proof. intros m A ws i a [_ Hw] Hi ->. rewrite u16s_length in Hw. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma u16arr_write : forall m A ws (i : Z) (v : word),
  u16arr m A ws -> (0 <= i < Z.of_nat (length ws))%Z ->
  u16arr (write_to_mem m (wa (A + 2 * i)) (le2 v)) A (upd ws (Z.to_nat i) v).
Proof.
  intros m A ws i v [Hb Hw] Hi.
  destruct (upd_app_split ws (Z.to_nat i) v ltac:(lia)) as (pre & y & post & E & Hlen & Hupd).
  split.
  - eapply bytes_at_ext.
    { apply (bytes_at_write_inside segs m A (u16s ws) (2 * i) (le2 v) Hb); [lia|].
      rewrite length_le2, u16s_length. lia. }
    rewrite Hupd, E, !u16s_app. cbn [u16s].
    replace (Z.to_nat (2 * i)) with (length (u16s pre)) by (rewrite u16s_length; lia).
    apply upd_bytes_mid. rewrite !length_le2. reflexivity.
  - rewrite u16s_length, upd_length. rewrite u16s_length in Hw. apply wr_at_write. exact Hw.
Qed.
End U16.

(* [comment removed for export] *)
Definition zw16 (l : list Z) : list word := map (Z_to_bv 64) l.

(* [comment removed for export] *)
Lemma zx16_small : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. f_equal. rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  apply Z.mod_small. lia.
Qed.
