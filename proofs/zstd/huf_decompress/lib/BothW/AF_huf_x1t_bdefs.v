(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXSound.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXMem KXBridge.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Definition u32q (x : Z) : list Z := [x mod 256; (x / 256) mod 256; (x / 65536) mod 256; (x / 16777216) mod 256].
Fixpoint u32b (ws : list Z) : list Z := match ws with [] => [] | x :: t => u32q x ++ u32b t end.
Definition shspan (A n : Z) : Z := (A + n + 7) / 8 - A / 8.

Definition zle4 (v : Z) : list Z := [v mod 256; (v / 256) mod 256; (v / 65536) mod 256; (v / 16777216) mod 256].

Section HK_u8arr_app.
Variable segs : list Segment.
Import KXSound.KXS.
Lemma u8arr_app : forall m A b1 b2,
  u8arr segs m A (b1 ++ b2) <-> u8arr segs m A b1 /\ u8arr segs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add. split.
  - intros ((H1 & H2) & (W0 & W1 & W)). split; (split; [assumption|]).
    + split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (length b1) + i) with (A + (Z.of_nat (length b1) + i)) by lia. apply W. lia.
  - intros ((H1 & (W0 & W1 & W)) & (H2 & (V0 & V1 & V))). split; [split; assumption|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (Z.of_nat (length b1))) as [L|L]; [apply W; lia|].
    replace (A + i) with (A + Z.of_nat (length b1) + (i - Z.of_nat (length b1))) by lia. apply V. lia.
Qed.
End HK_u8arr_app.

Section HK_firstn1_skipn.
Variable segs : list Segment.
Import KXSound.KXS.
Lemma firstn1_skipn : forall (k : nat) (bs : list byte) b, nth_error bs k = Some b -> firstn 1 (skipn k bs) = [b].
Proof.
  induction k as [|k IH]; intros [|x bs] b H; cbn in H; try discriminate H.
  - injection H as ->. reflexivity.
  - cbn [skipn]. exact (IH bs b H).
Qed.
End HK_firstn1_skipn.

Lemma le4_Z : forall x v, x mod 2^32 = v mod 2^32 -> le4 (Z_to_bv 64 x) = map (Z_to_bv 8) (zle4 v).
Proof.
  intros x v E. unfold le4, zle4. cbn [Z_to_le_bytes map]. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia. cbn [Z.add Pos.add Pos.succ].
  change (2^8) with 256 in *. change (2^16) with 65536 in *. change (2^24) with 16777216 in *. change (2^32) with 4294967296 in *.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; lia.
Qed.

Section HK1.
Variable segs : list Segment.
Import KXSound.KXS.
Lemma rdval_bytes_at : forall m A bs (k : Z) n sx,
  bytes_at segs m A bs -> 0 <= k -> (Z.to_nat k + n <= length bs)%nat ->
  rdval segs m (wa (A + k)) n sx = Z_to_bv 64 (extz sx n (bytes_le_to_Z (firstn n (skipn (Z.to_nat k) bs)))).
Proof.
  intros m A bs k n sx Hb Hk Hn. unfold rdval.
  pose proof (bytes_at_rdn segs m A bs (Z.to_nat k) n Hb Hn) as H. rewrite Z2Nat.id in H by lia. rewrite H. reflexivity.
Qed.
End HK1.

Lemma firstn4_skipn : forall {X} (d : X) (l : list X) (i : nat), (i + 4 <= length l)%nat ->
  firstn 4 (skipn i l) = [nth i l d; nth (i + 1) l d; nth (i + 2) l d; nth (i + 3) l d].
Proof.
  intros X d l i. revert l. induction i as [|i IH]; intros l H.
  - destruct l as [|a [|b [|c [|e t]]]]; cbn [length] in H; try lia. reflexivity.
  - destruct l as [|a t]; cbn [length] in H; [lia|]. cbn [skipn]. rewrite (IH t) by lia. reflexivity.
Qed.

Lemma stk_open : forall segs m lo hi a (n : nat),
  stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists j, rw_cells segs m a [CB n j] /\ stk segs m lo a /\ stk segs m (a + Z.of_nat n) hi.
Proof.
  intros segs m lo hi a n S La Lh.
  destruct (stk_split segs m lo (a + Z.of_nat n) hi S ltac:(lia)) as [S1 S3].
  destruct (stk_carve segs m lo (a + Z.of_nat n) n S1 ltac:(lia)) as [S0 [j C]].
  replace (a + Z.of_nat n - Z.of_nat n) with a in * by lia.
  exists j. split; [exact C|]. split; [exact S0| exact S3].
Qed.

Section HK2.
Variable segs : list Segment.
Import KXSound.KXS.
Lemma rdval_u32Zb : forall m A (buf : list Z) i az,
  u8arr segs m A (map (Z_to_bv 8) buf) -> az = A + i -> 0 <= i -> i + 4 <= Z.of_nat (length buf) ->
  Forall (fun v : Z => 0 <= v < 256) buf ->
  rdval segs m (wa az) 4 false = Z_to_bv 64 (Znth i buf + 256 * Znth (i + 1) buf + 65536 * Znth (i + 2) buf + 16777216 * Znth (i + 3) buf).
Proof.
  intros m A buf i az [HB _] -> Hi Hl HF.
  rewrite (rdval_bytes_at segs m A _ i 4 false HB); [| lia| rewrite length_map; lia].
  f_equal. rewrite (firstn4_skipn (Z_to_bv 8 0)) by (rewrite length_map; lia).
  pose proof (Forall_Znth _ buf i HF ltac:(lia)) as B0. pose proof (Forall_Znth _ buf (i + 1) HF ltac:(lia)) as B1.
  pose proof (Forall_Znth _ buf (i + 2) HF ltac:(lia)) as B2. pose proof (Forall_Znth _ buf (i + 3) HF ltac:(lia)) as B3. cbv beta in *.
  assert (N : forall k, 0 <= k -> k < Z.of_nat (length buf) -> nth (Z.to_nat k) (map (Z_to_bv 8) buf) (Z_to_bv 8 0) = Z_to_bv 8 (Znth k buf)).
  { intros k Hk Hk2. unfold Znth. change (Z_to_bv 8 0) with ((Z_to_bv 8) 0). rewrite map_nth. reflexivity. }
  replace (Z.to_nat i + 1)%nat with (Z.to_nat (i + 1)) by lia. replace (Z.to_nat i + 2)%nat with (Z.to_nat (i + 2)) by lia.
  replace (Z.to_nat i + 3)%nat with (Z.to_nat (i + 3)) by lia.
  rewrite !N by lia.
  unfold extz. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite !byte_lit by lia.
  lia.
Qed.
End HK2.

Lemma u32b_app : forall a b, u32b (a ++ b) = u32b a ++ u32b b.
Proof. induction a as [|x a IH]; intros b; [reflexivity|]. cbn [u32b app]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma u32b_length : forall ws, length (u32b ws) = (4 * length ws)%nat.
Proof. induction ws as [|x t IH]; [reflexivity|]. cbn [u32b]. rewrite length_app, IH. cbn [length u32q]. lia. Qed.
Lemma u32b_length2 : forall ws, zlen (u32b ws) = 4 * zlen ws.
Proof. intros. rewrite u32b_length. lia. Qed.
Lemma u32b_bytes : forall ws, Forall isbyte (u32b ws).
Proof.
  induction ws as [|x t IH]; [constructor|]. cbn [u32b]. apply Forall_app. split; [| exact IH].
  unfold u32q. repeat constructor; Z.div_mod_to_equations; lia.
Qed.
Lemma Zupd_app_l' : forall i v (a b : list Z), 0 <= i < zlen a -> Zupd i v (a ++ b) = Zupd i v a ++ b.
Proof.
  intros i v a b Hi. unfold Zupd. remember (Z.to_nat i) as n. assert (Hn : (n < length a)%nat) by lia. clear Heqn Hi.
  revert n Hn. induction a as [|x a IH]; intros [|n] Hn; cbn [length] in Hn; try lia; cbn; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.
Lemma Zupd_app_r' : forall i v (a b : list Z), zlen a <= i -> Zupd i v (a ++ b) = a ++ Zupd (i - zlen a) v b.
Proof.
  intros i v a b Hi. unfold Zupd. replace (Z.to_nat (i - zlen a)) with (Z.to_nat i - length a)%nat by lia.
  remember (Z.to_nat i) as n. assert (Hn : (length a <= n)%nat) by lia. clear Heqn Hi.
  revert n Hn. induction a as [|x a IH]; intros n Hn; cbn [length] in Hn; [cbn; rewrite Nat.sub_0_r; reflexivity|].
  destruct n as [|n]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.
Lemma u32b_upd4 : forall ws i x, 0 <= i < zlen ws ->
  Zupd (4 * i + 3) ((x / 16777216) mod 256) (Zupd (4 * i + 2) ((x / 65536) mod 256) (Zupd (4 * i + 1) ((x / 256) mod 256) (Zupd (4 * i) (x mod 256) (u32b ws))))
  = u32b (Zupd i x ws).
Proof.
  intros ws i x Hi.
  destruct (nth_error_split (map (fun z : Z => z) ws) (Z.to_nat i) (Znth i ws) (nth_error_map_Znth (fun z : Z => z) ws i Hi)) as (pre & post & E & Hlen).
  rewrite map_id in E. rewrite E.
  unfold Zupd at 5. rewrite <- Hlen.
  assert (UPD : forall (a b : list Z) y v, upd_nat (length a) v (a ++ y :: b) = a ++ v :: b).
  { intros a. induction a as [|h a IH]; intros b y v; cbn; [reflexivity|]. rewrite IH. reflexivity. }
  rewrite UPD. rewrite !u32b_app. cbn [u32b]. pose proof (u32b_length2 pre) as L.
  rewrite !Zupd_app_r' by (rewrite ?Zupd_length2; lia).
  replace (4 * i - zlen (u32b pre)) with 0 by lia. replace (4 * i + 1 - zlen (u32b pre)) with 1 by lia.
  replace (4 * i + 2 - zlen (u32b pre)) with 2 by lia. replace (4 * i + 3 - zlen (u32b pre)) with 3 by lia.
  reflexivity.
Qed.
Lemma Znth_app_r' : forall (a b : list Z) k, 0 <= k -> Znth (zlen a + k) (a ++ b) = Znth k b.
Proof. intros a b k Hk. unfold Znth. rewrite app_nth2 by lia. f_equal. lia. Qed.
Lemma u32b_read : forall ws i, 0 <= i < zlen ws ->
  Znth (4 * i) (u32b ws) + 256 * Znth (4 * i + 1) (u32b ws) + 65536 * Znth (4 * i + 2) (u32b ws) + 16777216 * Znth (4 * i + 3) (u32b ws)
  = Znth i ws mod 4294967296.
Proof.
  intros ws i Hi.
  destruct (nth_error_split (map (fun z : Z => z) ws) (Z.to_nat i) (Znth i ws) (nth_error_map_Znth (fun z : Z => z) ws i Hi)) as (pre & post & E & Hlen).
  rewrite map_id in E. rewrite E at 1 2 3 4. rewrite !u32b_app. pose proof (u32b_length2 pre) as L.
  replace (4 * i) with (zlen (u32b pre) + 0) by lia.
  replace (zlen (u32b pre) + 0 + 1) with (zlen (u32b pre) + 1) by lia.
  replace (zlen (u32b pre) + 0 + 2) with (zlen (u32b pre) + 2) by lia.
  replace (zlen (u32b pre) + 0 + 3) with (zlen (u32b pre) + 3) by lia.
  rewrite !Znth_app_r' by lia. set (x := Znth i ws). unfold Znth.
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 1) with 1%nat. change (Z.to_nat 2) with 2%nat. change (Z.to_nat 3) with 3%nat.
  cbn [nth u32b u32q app]. Z.div_mod_to_equations. lia.
Qed.

Lemma u32s_u32b : forall l, u32s (map (Z_to_bv 64) l) = map (Z_to_bv 8) (u32b l).
Proof.
  induction l as [|x t IH]; [reflexivity|]. cbn [map u32s u32b]. rewrite map_app, <- IH.
  change (u32s (Z_to_bv 64 x :: map (Z_to_bv 64) t)) with (le4 (Z_to_bv 64 x) ++ u32s (map (Z_to_bv 64) t)).
  rewrite (le4_Z x x eq_refl). reflexivity.
Qed.
Lemma u32arr_u32b : forall segs m A l, u32arr segs m A (map (Z_to_bv 64) l) -> u8arr segs m A (map (Z_to_bv 8) (u32b l)).
Proof.
  intros segs m A l [HB HW]. split; [rewrite <- u32s_u32b; exact HB|].
  rewrite length_map, u32b_length. rewrite length_map in HW. replace (Z.of_nat (4 * length l)) with (4 * zlen l) by lia. exact HW.
Qed.

Section MEM.
Variable segs : list Segment.
Import KXSound.KXS.
Lemma rdval_u32b : forall m A (ws : list Z) i az sx,
  u8arr segs m A (map (Z_to_bv 8) (u32b ws)) -> az = A + 4 * i -> 0 <= i < zlen ws -> 0 <= Znth i ws < 2147483648 ->
  rdval segs m (wa az) 4 sx = Z_to_bv 64 (Znth i ws).
Proof.
  intros m A ws i az sx H -> Hi Hv. pose proof (u32b_length2 ws) as L.
  destruct sx.
  - destruct H as [HB _]. rewrite (rdval_bytes_at segs m A _ (4 * i) 4 true HB); [| lia| rewrite length_map; lia].
    rewrite (firstn4_skipn (Z_to_bv 8 0)) by (rewrite length_map; lia).
    assert (N : forall k, 0 <= k -> k < zlen (u32b ws) -> nth (Z.to_nat k) (map (Z_to_bv 8) (u32b ws)) (Z_to_bv 8 0) = Z_to_bv 8 (Znth k (u32b ws))).
    { intros k Hk Hk2. unfold Znth. change (Z_to_bv 8 0) with ((Z_to_bv 8) 0). rewrite map_nth. reflexivity. }
    replace (Z.to_nat (4 * i) + 1)%nat with (Z.to_nat (4 * i + 1)) by lia. replace (Z.to_nat (4 * i) + 2)%nat with (Z.to_nat (4 * i + 2)) by lia.
    replace (Z.to_nat (4 * i) + 3)%nat with (Z.to_nat (4 * i + 3)) by lia.
    rewrite !N by lia.
    pose proof (u32b_bytes ws) as BY.
    pose proof (Forall_Znth _ _ (4 * i) BY ltac:(lia)) as B0. pose proof (Forall_Znth _ _ (4 * i + 1) BY ltac:(lia)) as B1.
    pose proof (Forall_Znth _ _ (4 * i + 2) BY ltac:(lia)) as B2. pose proof (Forall_Znth _ _ (4 * i + 3) BY ltac:(lia)) as B3. cbv beta in B0, B1, B2, B3.
    pose proof (u32b_read ws i Hi) as RDX. rewrite (Z.mod_small (Znth i ws) 4294967296) in RDX by lia.
    unfold extz. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite !byte_lit by lia.
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N (8 * N.of_nat 4)) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616.
    Z.div_mod_to_equations. lia.
  - rewrite (rdval_u32Zb segs m A (u32b ws) (4 * i) _ H eq_refl ltac:(lia) ltac:(lia) (u32b_bytes ws)). f_equal.
    rewrite (u32b_read ws i Hi). apply Z.mod_small. lia.
Qed.
Lemma u32b_of_stk : forall m A (k : nat), stk segs m A (A + 4 * Z.of_nat k) -> 0 <= A -> A + 4 * Z.of_nat k < 2^64 ->
  exists ws : list Z, u8arr segs m A (map (Z_to_bv 8) (u32b ws)) /\ length ws = k /\ Forall (fun v => 0 <= v < 4294967296) ws.
Proof.
  intros m A k ST HA HH.
  destruct (stk_open segs m A (A + 4 * Z.of_nat k) A (4 * k)%nat ST ltac:(lia) ltac:(lia)) as (bs & C & _ & _).
  assert (BL : length bs = (4 * k)%nat) by (destruct C as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
  apply u8arr_of_rw_cells in C. clear ST. revert A bs HA HH C BL. induction k as [|k IH]; intros A bs HA HH C BL.
  - exists []. destruct bs; [| cbn in BL; lia]. split; [exact C|]. split; [reflexivity| constructor].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 t]]]]; cbn [length] in BL; try lia.
    destruct (proj1 (u8arr_app segs m A [b0; b1; b2; b3] t) C) as [C1 C2]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in C2.
    destruct (IH (A + 4) t ltac:(lia) ltac:(lia) C2 ltac:(lia)) as (ws & W1 & W2 & W3).
    exists ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) :: ws).
    pose proof (bv_unsigned_in_range _ b0) as R0. pose proof (bv_unsigned_in_range _ b1) as R1.
    pose proof (bv_unsigned_in_range _ b2) as R2. pose proof (bv_unsigned_in_range _ b3) as R3.
    unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
    split; [| split; [cbn [length]; lia| constructor; [lia| exact W3]]].
    cbn [u32b app]. change (map (Z_to_bv 8) (u32q _ ++ u32b ws)) with (map (Z_to_bv 8) (u32q (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)) ++ map (Z_to_bv 8) (u32b ws)).
    apply (proj2 (u8arr_app segs m A _ _)). split; [| rewrite length_map; cbn [length u32q Z.of_nat Pos.of_succ_nat Pos.succ]; exact W1].
    unfold u32q. cbn [map].
    replace ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) mod 256) with (bv_unsigned b0) by (Z.div_mod_to_equations; lia).
    replace ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) / 256 mod 256) with (bv_unsigned b1) by (Z.div_mod_to_equations; lia).
    replace ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) / 65536 mod 256) with (bv_unsigned b2) by (Z.div_mod_to_equations; lia).
    replace ((bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3) / 16777216 mod 256) with (bv_unsigned b3) by (Z.div_mod_to_equations; lia).
    rewrite !byte_of_unsigned. exact C1.
Qed.
Lemma rdn_u8Z : forall m A (buf : list Z) i,
  u8arr segs m A (map (Z_to_bv 8) buf) -> 0 <= i < zlen buf -> 0 <= Znth i buf < 256 ->
  rdn segs m (wa (A + i)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 (Znth i buf))).
Proof.
  intros m A buf i [HB _] Hi Hv.
  replace i with (Z.of_nat (Z.to_nat i)) at 1 by lia.
  rewrite (bytes_at_rdn segs m A _ (Z.to_nat i) 1 HB) by (rewrite length_map; lia).
  rewrite (firstn1_skipn (Z.to_nat i) (map (Z_to_bv 8) buf) (Z_to_bv 8 (Znth i buf))) by (apply nth_error_map_Znth; lia).
  change (word_to_le_bytes 1 (Z_to_bv 64 (Znth i buf))) with (le1 (Z_to_bv 64 (Znth i buf))).
  f_equal. unfold le1. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with 18446744073709551616. Z.div_mod_to_equations. lia.
Qed.
Lemma rdn_u32b : forall m A (ws : list Z) i,
  u8arr segs m A (map (Z_to_bv 8) (u32b ws)) -> 0 <= i < zlen ws -> 0 <= Znth i ws < 4294967296 ->
  rdn segs m (wa (A + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (Znth i ws))).
Proof.
  intros m A ws i [HB _] Hi Hv. pose proof (u32b_length2 ws) as L.
  replace (4 * i) with (Z.of_nat (Z.to_nat (4 * i))) at 1 by lia.
  rewrite (bytes_at_rdn segs m A _ (Z.to_nat (4 * i)) 4 HB) by (rewrite length_map; lia).
  change (word_to_le_bytes 4 (Z_to_bv 64 (Znth i ws))) with (le4 (Z_to_bv 64 (Znth i ws))).
  rewrite (le4_Z (Znth i ws) (Znth i ws) eq_refl). f_equal.
  destruct (nth_error_split (map (fun z : Z => z) ws) (Z.to_nat i) (Znth i ws) (nth_error_map_Znth (fun z : Z => z) ws i Hi)) as (pre & post & E & Hlen).
  rewrite map_id in E. rewrite E at 1. rewrite u32b_app, map_app. cbn [u32b]. rewrite map_app.
  replace (Z.to_nat (4 * i)) with (length (map (Z_to_bv 8) (u32b pre))) by (rewrite length_map, u32b_length; lia).
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [app skipn]. unfold u32q. cbn [map firstn]. reflexivity.
Qed.
End MEM.

Section CANSEC1. Context {rc : runConstT}.

Definition x1A_hyps (RNG : footprint) (SPV SPA lo DT DTB WK wksz FF : Z) : Prop :=
  4096 <= DT
  /\ DT + DTB <= 2^47
  /\ DT mod 4 = 0
  /\ 4096 <= WK
  /\ WK + wksz < 2^47
  /\ WK mod 4 = 0
  /\ 1492 <= wksz < 2^32
  /\ KHIGH <= lo
  /\ ATOP + 4096 <= lo
  /\ lo <= SPV - 5936
  /\ SPV + 16 <= 2^47
  /\ SPV mod 16 = 0
  /\ SPV - 336 <= SPA <= SPV - 320
  /\ SPA mod 32 = 0
  /\ (DT + DTB <= lo \/ SPV <= DT)
  /\ (WK + wksz <= lo \/ SPV <= WK)
  /\ (DT + DTB <= WK \/ WK + wksz <= DT)
  /\ FF mod 64 = 0
  /\ 4096 <= FF
  /\ FF + 64 <= ATOP
  /\ ablk FF (FF + 64)
  /\ (DT + DTB <= FF \/ FF + 64 <= DT)
  /\ (WK + wksz <= FF \/ FF + 64 <= WK)
  /\ ablk DT (DT + DTB)
  /\ rng RNG DT DTB
  /\ rng RNG (shad DT) (shspan DT DTB)
  /\ ablk WK (WK + wksz)
  /\ rng RNG WK wksz
  /\ rng RNG (shad WK) (shspan WK wksz)
  /\ rng RNG FF 64
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG.

Definition X1FRB (DT WK FF r tl : Z) (k176 : word) (jA jA2 jC jD jB jE : list byte) : list cell :=
  [CB 8 jA; C8 (Z_to_bv 64 r); CB 8 jA2; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); CB 16 jC; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DT);
   C8 (Z_to_bv 64 (tl + 1)); CB 16 jD; C8 (Z_to_bv 64 WK); CB 72 jB; C8 k176; C8 (Z_to_bv 64 (DT + 4)); CB 16 jE; C8 (Z_to_bv 64 FF)].

Definition XB (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z) (hw rank : list Z) (tl : Z) (k176 : word) (jA jA2 jC jD jB jE : list byte) (dt rst : list Z) (syb : list byte) (m1 : amem) : Prop :=
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
  /\ zlen dt = DTB
  /\ Forall isbyte dt
  /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw)
  /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank))
  /\ u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst))
  /\ zlen rst = 13
  /\ Forall (fun v : Z => 0 <= v) rst
  /\ stk bsegs m1 (WK + 104) (WK + 980)
  /\ u8arr bsegs m1 (WK + 980) syb
  /\ zlen syb = 256
  /\ stk bsegs m1 (WK + 1492) (WK + wksz)
  /\ stk bsegs m1 lo SPA
  /\ mem_inv bsegs m1
  /\ munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1
  /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X1FRB DT WK FF r tl k176 jA jA2 jC jD jB jE).
End CANSEC1.

Section CANSEC2. Context {rc : runConstT}.
Definition X1_KM32 : Z := 18446744071562067967.
Definition X1FR1 (DT WK FF r tl : Z) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 X1_KM32); C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 (tl + 1));
   C8 (Z_to_bv 64 (18446744073709551615 - WK)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1))].
Definition XFR2 (SPA WK rsacc sym : Z) (m : amem) : Prop :=
  exists k104 k112 k120 k128 k136 k144 k152 : word,
    rw_cells bsegs m (SPA + 80) [C8 (Z_to_bv 64 rsacc); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); C8 k104; C8 k112; C8 k120; C8 k128; C8 k136; C8 k144; C8 k152].
Definition X1FR4 (DT WK FF : Z) (j192 : list byte) : list cell :=
  [C8 (Z_to_bv 64 281479271743489); C8 (Z_to_bv 64 (18446744073709551615 - (WK + 980))); C8 (Z_to_bv 64 (WK + 980)); C8 (Z_to_bv 64 (DT + 4)); CB 16 j192; C8 (Z_to_bv 64 FF)].

Definition XF (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z) (hw rank : list Z) (tl : Z) (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z) (m1 : amem) : Prop :=
  4 + 2 * 2 ^ tl <= DTB /\
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
  /\ zlen dt = DTB
  /\ Forall isbyte dt
  /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw)
  /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank))
  /\ u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst))
  /\ zlen rst = 13
  /\ stk bsegs m1 (WK + 104) (WK + 980)
  /\ u8arr bsegs m1 (WK + 980) syb
  /\ zlen syb = 256
  /\ stk bsegs m1 (WK + 1492) (WK + wksz)
  /\ stk bsegs m1 lo SPA
  /\ mem_inv bsegs m1
  /\ munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1
  /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0)
  /\ XFR2 SPA WK rsacc sym m1
  /\ rw_cells bsegs m1 (SPA + 160) (X1FR4 DT WK FF j192).
End CANSEC2.

Section CANSEC3. Context {rc : runConstT}.

Lemma x1_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.

Lemma x1_art_transport : forall W m m', artcells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W -> artcells m'.
Proof.
  intros W m m' ART MU WM HW. unfold artcells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split;
    (eapply rw_cells_transport; [eassumption| exact MU| exact WM|
       eapply x1_disjoint_from_above; [exact HW| cbn; unfold AIMG_HI; lia]]).
Qed.

Section G.
  Variables (RNG : footprint) (m5 : amem) (SPV SPA lo DT DTB WK wksz FF : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + DTB).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : artcells m5.

  Lemma x1_bands : (DT + DTB + 8 <= KLOW \/ KHIGH <= DT) /\ (WK + wksz + 8 <= KLOW \/ KHIGH <= WK)
                   /\ KHIGH + 5600 <= SPA /\ SPA + 336 <= 2^47 /\ AIMG_HI <= DT /\ AIMG_HI <= WK
                   /\ FF + 64 + 4096 <= lo /\ (FF + 64 + 8 <= KLOW \/ KHIGH <= FF) /\ AIMG_HI <= FF.
  Proof.
    pose proof HY as H. unfold x1A_hyps in H.
    destruct H as (DTL & DTH & DT4 & WKL & WKH & WK4 & WSZ & KLO & BOT & LOS & SPT & SP16 & SPA1 & SPA32 & DSTK & WSTK
                   & DTWK & FF64 & FFL & FFT & ABF & DFD & DFW & ABD & RD & RSD & ABW & RW & RSW & RF & RSTK & RI).
    pose proof atop_range as ATR.
    unfold ablk in ABF, ABD, ABW. unfold AIMG_HI, KLS, KHIGH, KLOW in *.
    split; [clear - ABD ATR; lia|]. split; [clear - ABW ATR; lia|].
    split; [clear - KLO LOS SPA1; lia|]. split; [clear - SPA1 SPT; lia|].
    split; [clear - ABD ATR; lia|]. split; [clear - ABW ATR; lia|].
    split; [clear - FFT BOT; lia|]. split; [clear - ABF ATR; lia|]. clear - ABF ATR; lia.
  Qed.

  Lemma x1_unp_dtM : forall m1, munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
    unpoisoned m1 DT (DT + DTB).
  Proof.
    intros m1 MU. pose proof HY as H. unfold x1A_hyps in H.
    destruct H as (DTL & DTH & DT4 & WKL & WKH & WK4 & WSZ & KLO & BOT & LOS & SPT & SP16 & SPA1 & SPA32 & DSTK & WSTK
                   & DTWK & FF64 & FFL & FFT & ABF & DFD & DFW & ABD & RD & RSD & ABW & RW & RSW & RF & RSTK & RI).
    pose proof x1_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    clear DSTK WSTK DTWK DFD DFW ABF ABD ABW RD RSD RW RSW RF RSTK RI.
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, AIMG_HI in *.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Lemma x1_unp_wkM : forall m1, munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
    unpoisoned m1 WK (WK + wksz).
  Proof.
    intros m1 MU. pose proof HY as H. unfold x1A_hyps in H.
    destruct H as (DTL & DTH & DT4 & WKL & WKH & WK4 & WSZ & KLO & BOT & LOS & SPT & SP16 & SPA1 & SPA32 & DSTK & WSTK
                   & DTWK & FF64 & FFL & FFT & ABF & DFD & DFW & ABD & RD & RSD & ABW & RW & RSW & RF & RSTK & RI).
    pose proof x1_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    clear DSTK WSTK DTWK DFD DFW ABF ABD ABW RD RSD RW RSW RF RSTK RI.
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KLOW, KHIGH, AIMG_HI in *.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Lemma x1_artM : forall m1, munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
    wmono bsegs m5 m1 -> artcells m1.
  Proof.
    intros m1 MU WM. pose proof x1_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
    eapply x1_art_transport; [exact ART0| exact MU| exact WM|].
    pose proof HY as H. unfold x1A_hyps in H. destruct H as (_ & _ & _ & _ & _ & _ & _ & KLO & _ & LOS & _ & _ & SPA1 & _).
    unfold KHIGH, AIMG_HI in *. repeat constructor; cbn [fst]; lia.
  Qed.
End G.

End CANSEC3.
