From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Instr Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_cb_bytes : forall m A cs k n bs,
  rw_cells rsegs m A cs -> cell_at cs k = Some (CB n bs) -> bytes_at rsegs m (A + Z.of_nat k) bs.
Proof.
  intros m A cs k n bs [[Hwf Hb] _] Hc.
  destruct (cell_at_split _ _ _ (CB n bs) Hc) as (pre & post & Ecs & Hsz & _).
  rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
  rewrite cells_bytes_app in Hb. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hwpre. rewrite Hsz in Hb.
  apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

Lemma bytes_at_sub : forall m a bs (k n : nat), bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hl.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_cb_split2 : forall m A (n1 n2 : nat) junk,
  rw_cells rsegs m A [CB (n1 + n2) junk] ->
  rw_cells rsegs m A [CB n1 (firstn n1 junk)] /\ rw_cells rsegs m (A + Z.of_nat n1) [CB n2 (skipn n1 junk)].
Proof.
  intros m A n1 n2 junk [[[Hl _] Hb] (Ha & Hn & Hw)].
  cbn [cell_wf] in Hl. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hn, Hw.
  rewrite <- (firstn_skipn n1 junk) in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite firstn_length_le in B2 by lia.
  split; (split; [split|]).
  - cbn. split; [apply firstn_length_le; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B1.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - cbn. split; [rewrite length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B2.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat n1 + i) with (A + (Z.of_nat n1 + i)) by lia. apply Hw. lia.
Qed.

Lemma rw_cells_CB_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma firstn_add_skipn : forall {X} (l : list X) (c t : nat), firstn (c + t) l = firstn c l ++ firstn t (skipn c l).
Proof.
  intros X l c. revert l. induction c as [|c IH]; intros l t; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct t; reflexivity|]. f_equal. apply IH.
Qed.

Lemma fs_comm : forall {X} (b a : nat) (l : list X), firstn a (skipn b l) = skipn b (firstn (b + a) l).
Proof.
  intros X b. induction b as [|b IH]; intros a l; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct a; reflexivity| apply IH].
Qed.

Lemma sk_sk : forall {X} (y x : nat) (l : list X), skipn x (skipn y l) = skipn (y + x) l.
Proof.
  intros X y. induction y as [|y IH]; intros x l; [reflexivity|].
  destruct l as [|a l]; cbn; [destruct x; reflexivity| apply IH].
Qed.

Lemma len_take : forall (Fc : list byte) p c, 0 <= p -> 0 <= c -> p + c <= Z.of_nat (length Fc) ->
  Z.of_nat (length (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc))) = c.
Proof. intros. rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. Qed.

Lemma bytes_at_join : forall m a (Fc : list byte) p c t,
  0 <= p -> 0 <= c -> 0 <= t -> p + c <= Z.of_nat (length Fc) ->
  bytes_at rsegs m a (firstn (Z.to_nat c) (skipn (Z.to_nat p) Fc)) ->
  bytes_at rsegs m (a + c) (firstn (Z.to_nat t) (skipn (Z.to_nat (p + c)) Fc)) ->
  bytes_at rsegs m a (firstn (Z.to_nat (c + t)) (skipn (Z.to_nat p) Fc)).
Proof.
  intros m a Fc p c t Hp Hc Ht Hl B1 B2.
  rewrite Z2Nat.inj_add by lia. rewrite firstn_add_skipn. apply bytes_at_app. split; [exact B1|].
  rewrite firstn_length_le by (rewrite length_skipn; lia).
  rewrite Z2Nat.id by lia. rewrite sk_sk.
  replace (Z.to_nat p + Z.to_nat c)%nat with (Z.to_nat (p + c)) by lia. exact B2.
Qed.

Lemma buf_take : forall (buf Fc : list byte) i e q c,
  0 <= c <= e - i ->
  firstn (Z.to_nat (e - i)) (skipn (Z.to_nat i) buf) = firstn (Z.to_nat (e - i)) (skipn (Z.to_nat (q - (e - i))) Fc) ->
  firstn (Z.to_nat c) (skipn (Z.to_nat i) buf) = firstn (Z.to_nat c) (skipn (Z.to_nat (q - (e - i))) Fc).
Proof.
  intros buf Fc i e q c Hc H.
  replace (Z.to_nat c) with (Nat.min (Z.to_nat c) (Z.to_nat (e - i))) by lia.
  rewrite <- !firstn_firstn. rewrite H. reflexivity.
Qed.

Lemma buf_drop : forall (buf Fc : list byte) i e q c,
  0 <= i -> 0 <= c <= e - i -> e - i <= q ->
  firstn (Z.to_nat (e - i)) (skipn (Z.to_nat i) buf) = firstn (Z.to_nat (e - i)) (skipn (Z.to_nat (q - (e - i))) Fc) ->
  firstn (Z.to_nat (e - (i + c))) (skipn (Z.to_nat (i + c)) buf) =
  firstn (Z.to_nat (e - (i + c))) (skipn (Z.to_nat (q - (e - (i + c)))) Fc).
Proof.
  intros buf Fc i e q c Hi Hc Hq H.
  replace (Z.to_nat (i + c)) with (Z.to_nat i + Z.to_nat c)%nat by lia.
  replace (Z.to_nat (q - (e - (i + c)))) with (Z.to_nat (q - (e - i)) + Z.to_nat c)%nat by lia.
  rewrite <- !sk_sk. rewrite !(fs_comm (Z.to_nat c)).
  replace (Z.to_nat c + Z.to_nat (e - (i + c)))%nat with (Z.to_nat (e - i)) by lia.
  rewrite H. reflexivity.
Qed.

Lemma mfile_buf : forall m h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf,
  rw_cells rsegs m h (mfile_cells h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf) ->
  bytes_at rsegs m (h + 280) buf.
Proof.
  intros m h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf HC.
  change (h + 280) with (h + Z.of_nat 280).
  apply (rw_cells_cb_bytes m h _ 280 1024 buf HC). reflexivity.
Qed.

Lemma mfile_cells_md : forall m h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf,
  rw_cells rsegs m h (mfile_cells h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf) ->
  le4 md = le4 (wz 4294967295) ->
  rw_cells rsegs m h (mfile_cells h b n fl pad0 rpos rend prev next (wz 4294967295) pad1 pos pad2 ung buf).
Proof.
  intros m h b n fl pad0 rpos rend prev next md pad1 pos pad2 ung buf [[Hwf Hb] Hw] E.
  split; [split|].
  - exact Hwf.
  - unfold mfile_cells in *. cbn [cells_bytes cbytes] in *. rewrite E in Hb. exact Hb.
  - exact Hw.
Qed.

Lemma mfile_pack : forall m h b (Fc : list byte) fl pad0 pad1 pad2 ung buf md q rb pv nx,
  rw_cells rsegs m h (mfile_cells h b (Z.of_nat (length Fc)) fl pad0 (rpos_of h rb) (rend_of h rb) pv nx md pad1 (wz q) pad2 ung buf) ->
  length ung = 8%nat -> length buf = 1024%nat -> 0 < h -> h mod 16 = 0 ->
  0 <= q <= Z.of_nat (length Fc) ->
  match rb with
  | None => True
  | Some (i, e) =>
      0 <= i <= e /\ e <= 1024 /\ e - i <= q /\
      firstn (Z.to_nat (e - i)) (skipn (Z.to_nat i) buf) = firstn (Z.to_nat (e - i)) (skipn (Z.to_nat (q - (e - i))) Fc)
  end ->
  bytes_at rsegs m b Fc -> 0 < b -> (h + 1304 <= b \/ b + Z.of_nat (length Fc) <= h) ->
  mfile m h b Fc fl md q rb pv nx.
Proof.
  intros. unfold mfile. exists buf. split; [exists pad0, pad1, pad2, ung; tauto | tauto].
Qed.

Lemma mstl_of : forall m h b Fc fl md q rb pv nx p,
  mfile m h b Fc fl md q rb pv nx -> (fl = wz 8 \/ fl = wz 24) -> (md = wz 0 \/ md = wz 4294967295) ->
  p = q - rlen rb -> (fl = wz 24 -> p = Z.of_nat (length Fc)) -> mstl m h b Fc p pv nx.
Proof. intros. exists fl, md, q, rb. tauto. Qed.

Lemma rlen_zero : forall h q (Fc buf : list byte) (rb : option (Z * Z)),
  0 <= h -> h + 1304 < 2^64 ->
  match rb with
  | None => True
  | Some (i, e) =>
      0 <= i <= e /\ e <= 1024 /\ e - i <= q /\
      firstn (Z.to_nat (e - i)) (skipn (Z.to_nat i) buf) = firstn (Z.to_nat (e - i)) (skipn (Z.to_nat (q - (e - i))) Fc)
  end ->
  bv_eqb (rpos_of h rb) (rend_of h rb) = true -> rlen rb = 0.
Proof.
  intros h q Fc buf [[i e]|] Hh Hl Hb E; cbn [rlen]; [|reflexivity].
  destruct Hb as (Hi & He & _).
  cbn [rpos_of rend_of] in E. unfold wz, bv_eqb in E. apply Z.eqb_eq in E.
  rewrite !unsigned_lit in E by lia. lia.
Qed.

Lemma wz_8_24 : wz 8 = wz 24 -> False.
Proof. intros E. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate. Qed.

Lemma divu_one : forall x : word, Sem.mul_div Instr.M_DIVU x (Z_to_bv 64 1) = x.
Proof.
  intros x.
  change (Sem.mul_div Instr.M_DIVU x (Z_to_bv 64 1))
    with (if (bv_unsigned (Z_to_bv 64 1) =? 0)%Z then Z_to_bv 64 (-1) else bv_divu x (Z_to_bv 64 1)).
  change (bv_unsigned (Z_to_bv 64 1) =? 0)%Z with false. cbv iota.
  apply bv_eq. rewrite bv_divu_unsigned. change (bv_unsigned (Z_to_bv 64 1)) with 1. apply Z.div_1_r.
Qed.

Lemma land_ones_k : forall x, 0 <= x < 2^64 -> Z.land ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) x = x.
Proof.
  intros x Hx. change ((Z.b2z (1 <? 1) + -1) mod 18446744073709551616) with (Z.ones 64).
  rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma le4_eq : forall v v' : word, bv_unsigned v mod 2^32 = bv_unsigned v' mod 2^32 -> le4 v = le4 v'.
Proof.
  intros v v' H. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned v') 32) by lia.
  rewrite H. reflexivity.
Qed.
