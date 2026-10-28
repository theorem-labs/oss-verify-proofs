(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_x1_seg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u32q (x : Z) : list Z := [x mod 256; (x / 256) mod 256; (x / 65536) mod 256; (x / 16777216) mod 256].
Fixpoint u32b (ws : list Z) : list Z := match ws with [] => [] | x :: t => u32q x ++ u32b t end.

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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition x1A_hyps (RNG : footprint) (SPV SPA lo DT WK wksz FF : Z) : Prop :=
  4096 <= DT
  /\ DT + 16388 <= 2^47
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
  /\ SPV - 448 <= SPA <= SPV - 416
  /\ SPA mod 32 = 0
  /\ (DT + 16388 <= lo \/ SPV <= DT)
  /\ (WK + wksz <= lo \/ SPV <= WK)
  /\ (DT + 16388 <= WK \/ WK + wksz <= DT)
  /\ FF mod 64 = 0
  /\ 4096 <= FF
  /\ FF + 64 <= ATOP
  /\ ablk FF (FF + 64)
  /\ (DT + 16388 <= FF \/ FF + 64 <= DT)
  /\ (WK + wksz <= FF \/ FF + 64 <= WK)
  /\ ablk DT (DT + 16388)
  /\ rng RNG DT 16388
  /\ rng RNG (shad DT) (shspan DT 16388)
  /\ ablk WK (WK + wksz)
  /\ rng RNG WK wksz
  /\ rng RNG (shad WK) (shspan WK wksz)
  /\ rng RNG FF 64
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG.

Lemma x1A_open : forall RNG SPV SPA lo DT WK wksz FF, x1A_hyps RNG SPV SPA lo DT WK wksz FF ->
  forall G : Prop, (4096 <= DT ->
    DT + 16388 <= 2^47 ->
    DT mod 4 = 0 ->
    4096 <= WK ->
    WK + wksz < 2^47 ->
    WK mod 4 = 0 ->
    1492 <= wksz < 2^32 ->
    KHIGH <= lo ->
    ATOP + 4096 <= lo ->
    lo <= SPV - 5936 ->
    SPV + 16 <= 2^47 ->
    SPV mod 16 = 0 ->
    SPV - 448 <= SPA <= SPV - 416 ->
    SPA mod 32 = 0 ->
    (DT + 16388 <= lo \/ SPV <= DT) ->
    (WK + wksz <= lo \/ SPV <= WK) ->
    (DT + 16388 <= WK \/ WK + wksz <= DT) ->
    FF mod 64 = 0 ->
    4096 <= FF ->
    FF + 64 <= ATOP ->
    ablk FF (FF + 64) ->
    (DT + 16388 <= FF \/ FF + 64 <= DT) ->
    (WK + wksz <= FF \/ FF + 64 <= WK) ->
    ablk DT (DT + 16388) ->
    rng RNG DT 16388 ->
    rng RNG (shad DT) (shspan DT 16388) ->
    ablk WK (WK + wksz) ->
    rng RNG WK wksz ->
    rng RNG (shad WK) (shspan WK wksz) ->
    rng RNG FF 64 ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG -> G) -> G.
Proof. intros until FF. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31). eapply K; eassumption. Qed.
Ltac open_hx HY := apply (x1A_open _ _ _ _ _ _ _ _ HY); intros DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.

(* [comment removed for export] *)
Definition X1FRB (DT WK FF r tl : Z) (k176 : word) (jA jA2 jC jD jB jE : list byte) : list cell :=
  [CB 56 jA; C8 (Z_to_bv 64 r); CB 16 jA2; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
   CB 8 jC; C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK); CB 64 jD; CB 80 jB; CB 24 jE; C8 (Z_to_bv 64 FF)].

(* [comment removed for export] *)
Definition XB (m5 : amem) (SPV SPA lo DT WK wksz FF r : Z) (hw rank : list Z) (tl : Z) (k176 : word) (jA jA2 jC jD jB jE : list byte) (dt rst : list Z) (syb : list byte) (m1 : amem) : Prop :=
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
  /\ zlen dt = 16388
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
  /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1
  /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X1FRB DT WK FF r tl k176 jA jA2 jC jD jB jE).

Lemma XB_open : forall m5 SPV SPA lo DT WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1,
  XB m5 SPV SPA lo DT WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 ->
  forall G : Prop, (u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
    zlen dt = 16388 ->
    Forall isbyte dt ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
    u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
    zlen rst = 13 ->
    Forall (fun v : Z => 0 <= v) rst ->
    stk bsegs m1 (WK + 104) (WK + 980) ->
    u8arr bsegs m1 (WK + 980) syb ->
    zlen syb = 256 ->
    stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 ->
    wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X1FRB DT WK FF r tl k176 jA jA2 jC jD jB jE) -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & FR). eapply K; eassumption. Qed.
Ltac open_xb I := apply (XB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR; unfold X1FRB in FR.
Lemma XB_close : forall m5 SPV SPA lo DT WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1,
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
  zlen dt = 16388 ->
  Forall isbyte dt ->
  u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
  u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
  u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
  zlen rst = 13 ->
  Forall (fun v : Z => 0 <= v) rst ->
  stk bsegs m1 (WK + 104) (WK + 980) ->
  u8arr bsegs m1 (WK + 980) syb ->
  zlen syb = 256 ->
  stk bsegs m1 (WK + 1492) (WK + wksz) ->
  stk bsegs m1 lo SPA ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 ->
  wmono bsegs m5 m1 ->
  rw_cells bsegs m1 SPA (X1FRB DT WK FF r tl k176 jA jA2 jC jD jB jE) ->
  XB m5 SPV SPA lo DT WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1.
Proof. intros. unfold XB. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_xb := unfold X1FRB; eapply XB_close; try eassumption.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?u32b_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

(* [comment removed for export] *)
Lemma x1_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma x1_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply x1_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply x1_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section G.
  Variables (RNG : footprint) (m5 : amem) (SPV SPA lo DT WK wksz FF : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.

  (* [comment removed for export] *)
  Lemma x1_bands : (DT + 16388 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (WK + wksz + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= WK)
                   /\ 0x10007fff8000 + 5488 <= SPA /\ SPA + 432 <= 2^47 /\ 0x625000 <= DT /\ 0x625000 <= WK
                   /\ FF + 64 + 4096 <= lo /\ (FF + 64 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= FF).
  Proof.
    open_hx HY. clear SDS SWS DTWK DFD DFW.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABD, ABW, ABF. unfold KHIGH in KLO.
    repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_unp_dtM : forall m1, munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 -> unpoisoned m1 DT (DT + 16388).
  Proof.
    intros m1 MU. open_hx HY. clear SDS SWS DTWK DFD DFW. pose proof x1_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear ABD ABW ABF. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x1_unp_wkM : forall m1, munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 -> unpoisoned m1 WK (WK + wksz).
  Proof.
    intros m1 MU. open_hx HY. clear SDS SWS DTWK DFD DFW. pose proof x1_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear ABD ABW ABF. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x1_artM : forall m1, munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 -> art m1.
  Proof.
    intros m1 MU WM. pose proof x1_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply x1_art_transport; [exact ART0| exact MU| exact WM|]. open_hx HY. unfold ablk, AIMG_HI in ABF. repeat constructor; cbn [fst]; lia.
  Qed.
End G.
End CANSEC1.

(* [comment removed for export] *)

Ltac open_hx HY := apply (x1A_open _ _ _ _ _ _ _ _ HY); intros DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.
Ltac open_xb I := apply (XB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR; unfold X1FRB in FR.
Ltac close_xb := unfold X1FRB; eapply XB_close; try eassumption.
Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?u32b_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition X1_KM32 : Z := 18446744071562067967.   (* [comment removed for export] *)
Definition X1FR1 (DT WK FF r tl : Z) (j0 : list byte) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 (DT + 27)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 19)); C8 (Z_to_bv 64 (DT + 35));
   C8 (Z_to_bv 64 (DT + 28)); C8 (Z_to_bv 64 (DT + 11)); C8 (Z_to_bv 64 r); C8 (Z_to_bv 64 (DT + 12)); C8 (Z_to_bv 64 (DT + 4));
   C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 (tl + 1));
   C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK)].
Definition XFR2 (SPA WK rsacc sym : Z) (m : amem) : Prop :=
  exists k136 k144 k160 k184 k192 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 : word,
    rw_cells bsegs m (SPA + 136) [C8 k136; C8 k144; C8 (Z_to_bv 64 rsacc); C8 k160; C8 (Z_to_bv 64 (WK + 980)); C8 (Z_to_bv 64 sym);
                                  C8 k184; C8 k192; C8 (Z_to_bv 64 281479271743489); C8 k208; C8 k216; C8 k224; C8 k232; C8 k240;
                                  C8 k248; C8 k256; C8 k264; C8 k272; C8 k280; C8 k288].
Definition X1FR4 (DT WK FF : Z) (j192 : list byte) : list cell :=
  [CB 8 j192; C8 (Z_to_bv 64 FF)].

Definition XF (m5 : amem) (SPV SPA lo DT WK wksz FF r : Z) (hw rank : list Z) (tl : Z) (j0 j192 : list byte) (dt rst : list Z) (syb : list byte) (rsacc sym : Z) (m1 : amem) : Prop :=
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
  /\ zlen dt = 16388
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
  /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1
  /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0)
  /\ XFR2 SPA WK rsacc sym m1
  /\ rw_cells bsegs m1 (SPA + 296) (X1FR4 DT WK FF j192).

Lemma XF_open : forall m5 SPV SPA lo DT WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1,
  XF m5 SPV SPA lo DT WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1 ->
  forall G : Prop, (u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
    zlen dt = 16388 ->
    Forall isbyte dt ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
    u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
    zlen rst = 13 ->
    stk bsegs m1 (WK + 104) (WK + 980) ->
    u8arr bsegs m1 (WK + 980) syb ->
    zlen syb = 256 ->
    stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 ->
    wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0) ->
    XFR2 SPA WK rsacc sym m1 ->
    rw_cells bsegs m1 (SPA + 296) (X1FR4 DT WK FF j192) -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & HL). eapply K; eassumption. Qed.
Ltac open_xf I := apply (XF_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RST RSTLEN STS SYC SYLEN WKR STK MI MU WM FR1 F2 FR4; unfold X1FR1 in FR1; unfold X1FR4 in FR4;
  destruct F2 as (k136 & k144 & k160 & k184 & k192 & k208 & k216 & k224 & k232 & k240 & k248 & k256 & k264 & k272 & k280 & k288 & FR2).
Lemma XF_close : forall m5 SPV SPA lo DT WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1,
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
  zlen dt = 16388 ->
  Forall isbyte dt ->
  u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
  u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
  u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
  zlen rst = 13 ->
  stk bsegs m1 (WK + 104) (WK + 980) ->
  u8arr bsegs m1 (WK + 980) syb ->
  zlen syb = 256 ->
  stk bsegs m1 (WK + 1492) (WK + wksz) ->
  stk bsegs m1 lo SPA ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 5520, SPA + 312); (FF + 32, FF + 36)] m5 m1 ->
  wmono bsegs m5 m1 ->
  rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0) ->
  XFR2 SPA WK rsacc sym m1 ->
  rw_cells bsegs m1 (SPA + 296) (X1FR4 DT WK FF j192) ->
  XF m5 SPV SPA lo DT WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1.
Proof. intros. unfold XF. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_xf := unfold X1FR1, X1FR4; eapply XF_close; try eassumption; try (unfold XFR2; do 16 eexists; eassumption); try eassumption.
End CANSEC2.
Ltac open_xf I := apply (XF_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RST RSTLEN STS SYC SYLEN WKR STK MI MU WM FR1 F2 FR4; unfold X1FR1 in FR1; unfold X1FR4 in FR4;
  destruct F2 as (k136 & k144 & k160 & k184 & k192 & k208 & k216 & k224 & k232 & k240 & k248 & k256 & k264 & k272 & k280 & k288 & FR2).
Ltac close_xf := unfold X1FR1, X1FR4; eapply XF_close; try eassumption; try (unfold XFR2; do 16 eexists; eassumption); try eassumption.
