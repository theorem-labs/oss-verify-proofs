(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs F_sscanf H_scanner_get_token H_vfmatch_A H_match H_map_str_to_int H_str_alloc
     H_parse_uri_A H_presp_B H_phdr_B.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation FMT09 := 0x10331%Z.
Notation FMTREQ := 0x10423%Z.
Notation MTAB := 0x2a8c0%Z.
Notation FMT_VER := 0x10365%Z.
Notation HEAD := 0x155c0%Z.
Ltac sstep := step; fix_lit_store.

Lemma zx32_lit : forall x, (0 <= x < 2^32)%Z -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. f_equal. rewrite unsigned_lit by lia. apply Z.mod_small. lia. Qed.

Lemma rw_cells_C44_C8 : forall m X (a b : word),
  rw_cells rsegs m X [C4 a; C4 b] -> rw_cells rsegs m X [C8 (le_bytes_to_word (le4 a ++ le4 b))].
Proof.
  intros m X a b H. pose proof (rw_cells_merge rsegs m X [] [C4 a; C4 b] [] ltac:(rewrite app_nil_r; exact H)) as M.
  cbn [app cells_size csize cells_bytes cbytes Nat.add] in M. rewrite app_nil_r in M.
  exact (rw_cells_CB_C8 rsegs m X [] _ [] M).
Qed.

Lemma rw_cells_C8_C44 : forall m X (w : word),
  rw_cells rsegs m X [C8 w] -> exists a b : word, rw_cells rsegs m X [C4 a; C4 b].
Proof.
  intros m X w H.
  pose proof (rw_cells_split_CB rsegs m X [] 8 (le8 w) [] [4; 4]%nat) as SP. cbn [app mk_CB_cells] in SP.
  assert (H8 : rw_cells rsegs m X [CB 8 (le8 w)]).
  { destruct H as [[W B] R]. split; [split; [cbn; split; [reflexivity| exact I]| exact B]| exact R]. }
  specialize (SP H8 eq_refl).
  pose proof (rw_cells_CB_C4 rsegs m X [] (firstn 4 (le8 w)) [CB 4 (firstn 4 (skipn 4 (le8 w)))] SP) as S1. cbn [app] in S1.
  pose proof (rw_cells_CB_C4 rsegs m X [C4 (le_bytes_to_word (firstn 4 (le8 w)))] (firstn 4 (skipn 4 (le8 w))) [] S1) as S2. cbn [app] in S2.
  eexists _, _. exact S2.
Qed.

Lemma tokm1 : forall ty, (0 <= ty <= 5)%Z ->
  (ty = 0 /\ Z.land (bv_swrap 32 (ty + -1)) 18446744073709551615 = 2^64 - 1)%Z
  \/ (1 <= ty /\ Z.land (bv_swrap 32 (ty + -1)) 18446744073709551615 = ty - 1)%Z.
Proof.
  intros ty H. rewrite swrap32_id by lia. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.eq_dec ty 0) as [->|NE]; [left; split; [reflexivity| reflexivity] | right]. split; [lia|]. apply Z.mod_small. lia.
Qed.

Lemma land64_neg : forall x, (-2^63 <= x < 0)%Z -> Z.land x 18446744073709551615 = (x + 2^64)%Z.
Proof.
  intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite <- (Z.mod_add x 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma land64_nonneg : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac sgn K x := first [ rewrite (land64_neg x) in K by lia | rewrite (land64_nonneg x) in K by lia ].

Lemma u64arr_transport : forall W m m' A ws,
  u64arr rsegs m A ws -> munch W m m' -> wmono rsegs m m' -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr rsegs m' A ws.
Proof.
  intros W m m' A ws [B Wr] MU WM D. split.
  - eapply bytes_at_transport; [exact B| exact MU|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws))%Z by lia. exact D.
  - eapply wr_at_transport; [| exact WM]. exact Wr.
Qed.

Section SEGS.
Context {HCEIL : HasCeiling}.
  Variables (P q lo : Z).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo <= q)%Z.
  Hypothesis LO0 : (0x5c000 <= lo)%Z.
  Hypothesis QP : (q + 192 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^63)%Z.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s8v s9v t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz 3) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v s8v s9v (wz 1) (wz 4) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  Notation S7 := (wz (P + 8)). Notation S8 := (wz (P + 276)). Notation S9 := (wz (P + 280)).

  Variable ws : list word.
  Hypothesis WSL : length ws = 22%nat.
  Hypothesis MID : forall i, (0 <= i < 11)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.

  #[using="Type"] Lemma rq_blank : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS sgt_entry (wz 0x155f0) t0 t1 t2 (wz S) (wz (q + 72)) (wz (q + 56)) a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x155e0 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. unfold sgt_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="QP PHI"] Lemma rq_tok : forall (r ty tl cur' : Z) (tb tyw : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m (jt : word),
    mem_inv rsegs m -> rw_cells rsegs m (q + 56) [C4 tyw; C4 jt] -> rw_cells rsegs m (q + 72) [C8 tb; C8 (wz tl)] ->
    rw_cells rsegs m S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    (0 <= r <= 5)%Z -> (r = 4 -> tyw = wz ty /\ 0 <= ty <= 5)%Z -> (r = 4 -> 0 <= tl <= cur')%Z -> (0 <= cur' < 2^62)%Z ->
    evt rsegs (fun ms' => exists m' (a0' : word),
        ( (r <> 4 /\ ms' = PRS HEAD x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
       \/ (r = 4 /\ (ty = 1 \/ ty = 2) /\ ms' = PRS 0x155e0 x1 t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
       \/ (r = 4 /\ ty <> 1 /\ ty <> 2
           /\ ms' = PRS match_entry (wz 0x15624) t0 t1 t2 (wz S) (wz FMT09) (wz (q + 72)) (wz (q + 40)) a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
           /\ munch [(P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
           /\ rw_cells rsegs m' (q + 56) [C4 tyw; C4 jt] /\ rw_cells rsegs m' (q + 72) [C8 tb; C8 (wz tl)]
           /\ rw_cells rsegs m' S [C8 (wz MB); C8 (wz (cur' - tl)); C4 (wz 0)]) ))
      (PRS 0x155f0 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until jt. intros MI TYC TOK SC RR TYR0 TL CUR. unfold match_entry.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K0; zify_cond K0; condn K0.
    { pose proof (munch_refl [] m) as MU. apply evt_done. do 2 eexists. left. split; [lia|]. split; [reflexivity| reflexivity]. }
    destruct (TYR0 ltac:(lia)) as [Ety TYR]. rewrite Ety in TYC |- *.
    zstep. rewrite (sx32_lit ty) by lia. zstep. zstep. if_cases K1; zify_cond K1.
    -
      pose proof (munch_refl [] m) as MU.
      assert (T12 : (ty = 1 \/ ty = 2)%Z) by (destruct (tokm1 ty TYR) as [[-> E]|[T1 E]]; rewrite E in K1; lia).
      apply evt_done. do 2 eexists. right; left. split; [lia|]. split; [exact T12|]. split; [reflexivity| reflexivity].
    - assert (TN : (ty <> 1 /\ ty <> 2)%Z) by (destruct (tokm1 ty TYR) as [[-> E]|[T1 E]]; rewrite E in K1; lia).
      pose proof (munch_refl [(P + 488, P + 496)]%Z m) as MU. specialize (TL ltac:(lia)).
      zstep. zstep. zstep. sstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. do 2 eexists. right; right. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. repeat (split; [eassumption|]). eassumption.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="Type"] Lemma rq_m09 : forall (r : Z) (mb ml : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 72) [C8 mb; C8 ml] -> rw_cells rsegs m (q + 32) [C8 (wz FMTREQ)] -> (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' =>
        ( r = 4 /\ ms' = PRS map_str_to_int_entry (wz 0x15640) t0 t1 t2 mb ml (wz MTAB) (wz 11) (wz 1) a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m)
     \/ ( r <> 4 /\ ms' = PRS match_entry (wz 0x156d4) t0 t1 t2 (wz S) (wz FMTREQ) (wz (q + 72)) (wz (q + 40)) (wz (q + 56)) a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x15624 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros MI TOK F32 RR. unfold match_entry, map_str_to_int_entry.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. right. split; [lia| reflexivity].
    - zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done. left. split; [lia| reflexivity].
  Qed.

  #[using="Type"] Lemma cb_read1 : forall m A n bs (i : Z) b,
    rw_cells rsegs m A [CB n bs] -> nth_error bs (Z.to_nat i) = Some b -> (0 <= i)%Z ->
    ov_read_bytes rsegs m (wa (A + i)) 1 = Some [b].
  Proof. clear WSL MID. intros m A n bs i b BLK Hn Hi. eapply (u8arr_read rsegs); [eapply u8arr_of_rw_cells; exact BLK| exact Hn| exact Hi| reflexivity]. Qed.

  #[using="lo QLO LO0 QP PHI WSL MID"] Lemma rq_msi09 : forall (r meth err ub ul : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u64arr rsegs m MTAB ws -> rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> rw_cells rsegs m (P + 440) [C4 (wz err)] ->
    rw_cells rsegs m (q + 40) [C8 (wz ub); C8 (wz ul)] ->
    (r = -1 \/ 0 <= r < 11)%Z -> (0 <= ub < 2^64)%Z -> (0 <= ul < 2^64)%Z -> (0 <= meth < 2^32)%Z -> (0 <= err < 2^32)%Z ->
    evt rsegs (fun ms' => exists m' (meth' err' : Z) a0' a1' a2' pc,
        ms' = PRS pc x1 t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 4, P + 8); (P + 440, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ u64arr rsegs m' MTAB ws /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')] /\ rw_cells rsegs m' (P + 440) [C4 (wz err')]
        /\ rw_cells rsegs m' (q + 40) [C8 (wz ub); C8 (wz ul)]
        /\ ( (pc = HEAD /\ a0' = wz 3 /\ meth' = meth /\ (err' = 501 \/ err' = 400))
           \/ (pc = 0x15664 /\ a0' = wz ub /\ a2' = wz ul /\ meth' = 12 /\ err' = err
               /\ exists id, 0 <= r /\ nth_error ws (Z.to_nat (2 * r + 1)) = Some (wz id) /\ id = 2) )%Z)
      (PRS 0x15640 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TAB MC EC UC RR UB UL MR ER.
    pose proof (munch_refl [(P + 4, P + 8); (P + 440, P + 444)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K0; zify_cond K0.
    {   zstep. zstep. sstep. zstep. zstep.
      apply evt_done. eexists m0, meth, 501. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). left. repeat split; try reflexivity. left; reflexivity. }
    assert (R0 : (0 <= r < 11)%Z). { destruct RR as [->|RR']; [exfalso| exact RR']. cbv in K0. first [lia| discriminate| exact (K0 eq_refl)]. }
    destruct (MID r R0) as (id & HN & IDR).
    pose proof (u64arr_read4 m MTAB ws (2 * r + 1) (wz id) (Z_to_bv 64 (MTAB + Z.shiftl r 4 + 8)) TAB HN ltac:(lia)
                  ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    zstep. zstep. zstep. rewrite (sx32_lit id) by lia. zstep. if_cases K1; zify_cond K1.
    {   zstep. zstep. sstep. zstep. zstep.
      apply evt_done. eexists _, meth, 400. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). left. repeat split; try reflexivity. right; reflexivity. }
    zstep. zstep. zstep. sstep.
    apply evt_done. eexists _, 12, err. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    repeat (split; [eassumption|]). right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists id. split; [lia|]. split; [exact HN| lia].
    Unshelve. all: try exact (wz 0); try exact m; try exact 0%Z.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash_body1 : forall (k : nat) (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a4 a5 a6 a7 s7v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 40) [C8 (wz (A + o)); C8 (wz l)] ->
    (l < Z.of_nat k)%Z -> (0 <= o)%Z -> (2 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x1569c \/ ra' = 0x15830)
        /\ munch [(q + 40, q + 56)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 40) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x1566c x1 t0 t1 t2 (wz (A + o)) a1 (wz l) (wz (A + o + 1)) a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry.
    induction k as [|k IH]; intros until m; intros MI BLK Q40 HK O0 L2 OL A0 AHI; [lia|].
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 40, q + 56)]%Z m) as MU.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    destruct (nth_error bs (Z.to_nat o)) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
    destruct (nth_error bs (Z.to_nat (o + 1))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
    pose proof (byte_range b0) as BR0. pose proof (byte_range b1) as BR1.
    pose proof (cb_read1 m A n bs o b0 BLK Hb0 ltac:(lia)) as RD0.
    pose proof (cb_read1 m A n bs (o + 1) b1 BLK Hb1 ltac:(lia)) as RD1.
    replace (wa (A + o)) with (wa (A + o + 1 + -1)) in RD0 by (unfold wa; f_equal; lia).
    replace (wa (A + (o + 1))) with (wa (A + o + 1 + 0)) in RD1 by (unfold wa; f_equal; lia).
    zstep. zstep. if_cases K0; zify_cond K0.
    {
      zstep. zstep. zstep. replace (A + o + 1 + -1)%Z with (A + o)%Z by lia.
      apply evt_done. eexists m, o, l, _. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. zstep. if_cases K1; zify_cond K1.
    { zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. zstep. zstep. sstep. sstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      replace (A + o + 1 + 1)%Z with (A + (o + 1) + 1)%Z by lia. replace (A + o + 2)%Z with (A + (o + 1) + 1)%Z by lia.
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with BLK' : rw_cells rsegs mm A _, Q40' : rw_cells rsegs mm (q + 40) _, MI' : mem_inv rsegs mm |- _ =>
          eapply evt_mono; [eapply (IH A (o + 1)%Z (l - 1)%Z n bs); first [exact MI'| exact BLK'| exact Q40'| lia]|] end end.
      cbv beta. intros ms' (m' & o' & l' & ra' & a1' & a3' & -> & HRA & MU' & WM' & MI' & BLK' & Q40' & OL' & _).
      eexists m', o', l', ra'. do 2 eexists. split; [reflexivity|]. split; [exact HRA|].
      split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
      split; [exact BLK'|]. split; [exact Q40'|]. split; [lia| reflexivity].
    -
      zstep.
      assert (L1 : (l - 1 = 1)%Z) by (revert K2; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia).
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      replace (wz 1) with (wz (l - 1)) by (f_equal; lia).
      apply evt_done. eexists _, (o + 1)%Z, (l - 1)%Z, _. do 2 eexists. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [lia| reflexivity].
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash1 : forall (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 40) [C8 (wz (A + o)); C8 (wz l)] ->
    (0 <= o)%Z -> (1 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x1569c \/ ra' = 0x15830)
        /\ munch [(q + 40, q + 56)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 40) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x15664 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) a3 a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry. intros until m; intros MI BLK Q40 O0 L1 OL A0 AHI.
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 40, q + 56)]%Z m) as MU.
    zstep. if_cases K; zify_cond K.
    -   zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity].
    - zstep. eapply (rq_slash_body1 (Datatypes.S (Z.to_nat l))); try eassumption; try LiaTuning.alia.
      all: revert K; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash_body2 : forall (k : nat) (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a4 a5 a6 a7 s7v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 40) [C8 (wz (A + o)); C8 (wz l)] ->
    (l < Z.of_nat k)%Z -> (0 <= o)%Z -> (2 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x15718 \/ ra' = 0x15740)
        /\ munch [(q + 40, q + 56)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 40) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x156e8 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) (wz (A + o + 1)) a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry.
    induction k as [|k IH]; intros until m; intros MI BLK Q40 HK O0 L2 OL A0 AHI; [lia|].
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 40, q + 56)]%Z m) as MU.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    destruct (nth_error bs (Z.to_nat o)) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
    destruct (nth_error bs (Z.to_nat (o + 1))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
    pose proof (byte_range b0) as BR0. pose proof (byte_range b1) as BR1.
    pose proof (cb_read1 m A n bs o b0 BLK Hb0 ltac:(lia)) as RD0.
    pose proof (cb_read1 m A n bs (o + 1) b1 BLK Hb1 ltac:(lia)) as RD1.
    replace (wa (A + o)) with (wa (A + o + 1 + -1)) in RD0 by (unfold wa; f_equal; lia).
    replace (wa (A + (o + 1))) with (wa (A + o + 1 + 0)) in RD1 by (unfold wa; f_equal; lia).
    zstep. zstep. if_cases K0; zify_cond K0.
    {
      zstep. zstep. zstep. replace (A + o + 1 + -1)%Z with (A + o)%Z by lia.
      apply evt_done. eexists m, o, l, _. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. zstep. if_cases K1; zify_cond K1.
    { zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. zstep. zstep. sstep. sstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      replace (A + o + 1 + 1)%Z with (A + (o + 1) + 1)%Z by lia. replace (A + o + 2)%Z with (A + (o + 1) + 1)%Z by lia.
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with BLK' : rw_cells rsegs mm A _, Q40' : rw_cells rsegs mm (q + 40) _, MI' : mem_inv rsegs mm |- _ =>
          eapply evt_mono; [eapply (IH A (o + 1)%Z (l - 1)%Z n bs); first [exact MI'| exact BLK'| exact Q40'| lia]|] end end.
      cbv beta. intros ms' (m' & o' & l' & ra' & a1' & a3' & -> & HRA & MU' & WM' & MI' & BLK' & Q40' & OL' & _).
      eexists m', o', l', ra'. do 2 eexists. split; [reflexivity|]. split; [exact HRA|].
      split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
      split; [exact BLK'|]. split; [exact Q40'|]. split; [lia| reflexivity].
    -
      zstep.
      assert (L1 : (l - 1 = 1)%Z) by (revert K2; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia).
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      replace (wz 1) with (wz (l - 1)) by (f_equal; lia).
      apply evt_done. eexists _, (o + 1)%Z, (l - 1)%Z, _. do 2 eexists. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [lia| reflexivity].
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash2 : forall (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 40) [C8 (wz (A + o)); C8 (wz l)] ->
    (0 <= o)%Z -> (1 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x15718 \/ ra' = 0x15740)
        /\ munch [(q + 40, q + 56)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 40) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x156e0 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) a3 a4 a5 a6 a7 s7v S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry. intros until m; intros MI BLK Q40 O0 L1 OL A0 AHI.
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 40, q + 56)]%Z m) as MU.
    zstep. if_cases K; zify_cond K.
    -   zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity].
    - zstep. eapply (rq_slash_body2 (Datatypes.S (Z.to_nat l))); try eassumption; try LiaTuning.alia.
      all: revert K; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QP PHI"] Lemma rq_sa09 : forall (pc U ul : Z) (ubw errw ubuf : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (pc = 0x1569c \/ pc = 0x15830) ->
    mem_inv rsegs m -> rw_cells rsegs m (P + 432) [C8 ubw] -> rw_cells rsegs m (P + 440) [C4 errw] ->
    rw_cells rsegs m (q + 40) [C8 ubuf; C8 (wz ul)] -> (0 <= U < 2^64)%Z -> (0 <= ul < 2^64)%Z ->
    evt rsegs (fun ms' => exists m' (errw' : word) a0' a1' a2' x1' pc',
        ms' = PRS pc' x1' t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 432, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (P + 432) [C8 (wz U)] /\ rw_cells rsegs m' (P + 440) [C4 errw'] /\ rw_cells rsegs m' (q + 40) [C8 ubuf; C8 (wz ul)]
        /\ ( (U = 0 /\ pc' = HEAD /\ x1' = x1 /\ a0' = wz 3 /\ errw' = wz 500)
           \/ (U <> 0 /\ pc' = parse_uri_entry /\ x1' = wz 0x15844 /\ a0' = wz U /\ a1' = wz ul /\ a2' = S7 /\ errw' = errw) )%Z)
      (PRS pc x1 t0 t1 t2 (wz U) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros PC MI UBC EC UC UR ULR. unfold parse_uri_entry.
    pose proof (munch_refl [(P + 432, P + 444)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct PC as [-> | ->].
    - sstep. zstep. if_cases K; zify_cond K; condn K.
      +   zstep. zstep. zstep.
        apply evt_done. eexists _, errw. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity. lia.
      + zstep. zstep. sstep. zstep. zstep.
        apply evt_done. eexists _, (wz 500). do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). left. repeat split; try reflexivity. lia.
    - sstep. zstep. if_cases K; zify_cond K; condn K.
      +   zstep. sstep. zstep. zstep.
        apply evt_done. eexists _, (wz 500). do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). left. repeat split; try reflexivity. lia.
      + zstep. zstep. zstep.
        apply evt_done. eexists _, errw. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity. lia.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QP PHI"] Lemma rq_sa : forall (pc U ul : Z) (ubw errw ubuf : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (pc = 0x15718 \/ pc = 0x15740) ->
    mem_inv rsegs m -> rw_cells rsegs m (P + 432) [C8 ubw] -> rw_cells rsegs m (P + 440) [C4 errw] ->
    rw_cells rsegs m (q + 40) [C8 ubuf; C8 (wz ul)] -> (0 <= U < 2^64)%Z -> (0 <= ul < 2^64)%Z ->
    evt rsegs (fun ms' => exists m' (errw' : word) a0' a1' a2' x1' pc',
        ms' = PRS pc' x1' t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 432, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (P + 432) [C8 (wz U)] /\ rw_cells rsegs m' (P + 440) [C4 errw'] /\ rw_cells rsegs m' (q + 40) [C8 ubuf; C8 (wz ul)]
        /\ ( (U = 0 /\ pc' = HEAD /\ x1' = x1 /\ a0' = wz 3 /\ errw' = wz 500)
           \/ (U <> 0 /\ pc' = parse_uri_entry /\ x1' = wz 0x15754 /\ a0' = wz U /\ a1' = wz ul /\ a2' = S7 /\ errw' = errw) )%Z)
      (PRS pc x1 t0 t1 t2 (wz U) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros PC MI UBC EC UC UR ULR. unfold parse_uri_entry.
    pose proof (munch_refl [(P + 432, P + 444)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    destruct PC as [-> | ->].
    - sstep. zstep. if_cases K; zify_cond K; condn K.
      +   zstep. zstep. zstep.
        apply evt_done. eexists _, errw. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity. lia.
      + zstep. zstep. sstep. zstep. zstep.
        apply evt_done. eexists _, (wz 500). do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). left. repeat split; try reflexivity. lia.
    - sstep. zstep. if_cases K; zify_cond K; condn K.
      +   zstep. sstep. zstep. zstep.
        apply evt_done. eexists _, (wz 500). do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). left. repeat split; try reflexivity. lia.
      + zstep. zstep. zstep.
        apply evt_done. eexists _, errw. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
        repeat (split; [eassumption|]). right. repeat split; try reflexivity. lia.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  Definition ctl8 (err hack pos entp clen csz esp : Z) : list cell :=
    [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)].

  #[using="PHI"] Lemma rq_pu09 : forall (r err hack pos entp clen csz esp : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (P + 440) (ctl8 err hack pos entp clen csz esp) -> (0 <= r < 2^64)%Z ->
    evt rsegs (fun ms' => exists m' (ra0 pos' : Z),
        ms' = PRS HEAD x1 t0 t1 t2 (wz ra0) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 448, P + 452)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (P + 440) (ctl8 err hack pos' entp clen csz esp)
        /\ ( (r <> 1 /\ ra0 = 3 /\ pos' = pos /\ m' = m) \/ (r = 1 /\ ra0 = 0 /\ pos' = 4) )%Z)
      (PRS 0x15844 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros MI CTL RR. unfold ctl8 in *.
    pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - zstep. zstep. apply evt_done. eexists m, 3, pos. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split; [exact CTL|]. left. repeat split; lia.
    - zstep. sstep. zstep. apply evt_done. eexists _, 0, 4. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [eassumption|]. right. repeat split; lia.
  Qed.

  #[using="Type"] Lemma rq_pu : forall (r : Z) (mb ml j8 j16 j24 : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 72) [C8 mb; C8 ml] -> rw_cells rsegs m (q + 8) [C8 j8; C8 j16; C8 j24] -> (0 <= r < 2^64)%Z ->
    evt rsegs (fun ms' => exists m',
        ( (r <> 1)%Z /\ ms' = PRS HEAD x1 t0 t1 t2 (wz 3) (wz r) a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m' /\ m' = m )
     \/ ( r = 1 /\ ms' = PRS map_str_to_int_entry (wz 0x15788) t0 t1 t2 mb ml (wz MTAB) (wz 11) (wz 1) a5 a6 a7 S7 (wz MTAB) S9 t3 t4 t5 t6 gp tp F fc m'
          /\ munch [(q + 16, q + 32)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
          /\ rw_cells rsegs m' (q + 72) [C8 mb; C8 ml] /\ rw_cells rsegs m' (q + 8) [C8 j8; C8 S9; C8 S8] ))
      (PRS 0x15754 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros MI MC Q8 RR. unfold map_str_to_int_entry.
    pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. if_cases K; zify_cond K; condn K.
    - pose proof (munch_refl [] m) as MU. apply evt_done. exists m. left. split; [lia|]. split; [reflexivity| reflexivity].
    - pose proof (munch_refl [(q + 16, q + 32)]%Z m) as MU.
      sstep. sstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists. right. split; [lia|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; eassumption.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_msi : forall (r err A o l : Z) (n : nat) (bs : list byte) (j8 : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (P + 440) [C4 (wz err)] ->
    rw_cells rsegs m (q + 8) [C8 j8; C8 S9; C8 S8] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m A [CB n bs] ->
    (r = -1 \/ 0 <= r < 11)%Z -> (0 <= err < 2^32)%Z ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l + 1 < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m',
        ( r = -1 /\ ms' = PRS HEAD x1 t0 t1 t2 (wz 3) a1 a2 a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
          /\ munch [(P + 440, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
          /\ rw_cells rsegs m' (P + 440) [C4 (wz 501)] /\ rw_cells rsegs m' (q + 8) [C8 j8; C8 S9; C8 S8]
          /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o)); C8 (wz l)] /\ rw_cells rsegs m' A [CB n bs] )
     \/ ( exists b : byte, (0 <= r)%Z /\ nth_error bs (Z.to_nat (o + l)) = Some b
          /\ ms' = PRS SSCANF (wz 0x157c0) t0 t1 t2 (wz (A + o)) (wz FMT_VER) S8 S9 a4 a5 a6 a7 (wz (bv_unsigned b)) (wz MTAB) (wz r) t3 t4 t5 t6 gp tp F fc m'
          /\ munch [(q + 8, q + 16); (A + (o + l), A + (o + l) + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
          /\ rw_cells rsegs m' (P + 440) [C4 (wz err)] /\ rw_cells rsegs m' (q + 8) [C8 S7; C8 S9; C8 S8]
          /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o)); C8 (wz l)]
          /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (o + l) + 1) bs)] ))
      (PRS 0x15788 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 S7 (wz MTAB) S9 t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros MI EC Q8 Q56 BLK RR ER O0 L0 KN A0 AHI. unfold SSCANF.
    pose proof (wmono_refl rsegs m) as WM.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    zstep. if_cases K0; zify_cond K0.
    {
      pose proof (munch_refl [(P + 440, P + 444)]%Z m) as MU.
      assert (R1 : r = -1) by (destruct RR as [E|RR']; [exact E| exfalso; sgn K0 r; lia]).
      zstep. sstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists. left. split; [exact R1|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      repeat (split; [eassumption|]). eassumption. }
    assert (R0 : (0 <= r < 11)%Z) by (destruct RR as [->|RR']; [exfalso; cbv in K0; first [lia| discriminate| exact (K0 eq_refl)]| exact RR']).
    pose proof (munch_refl [(q + 8, q + 16); (A + (o + l), A + (o + l) + 1)]%Z m) as MU.
    destruct (nth_error bs (Z.to_nat (o + l))) as [b|] eqn:Hb. 2:{ exfalso. apply nth_error_None in Hb. lia. }

    apply (rw_cells_split_CB rsegs m A [] n bs [] [Z.to_nat (o + l); 1%nat; Z.to_nat (Z.of_nat n - (o + l) - 1)]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app rsegs m A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
    assert (E1 : firstn 1 (skipn (Z.to_nat (o + l)) bs) = [b]).
    { destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen). rewrite E at 1. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity. }
    rewrite E1 in BLK23.
    zstep. sstep. zstep. zstep. zstep.
    remember (A + (o + l))%Z as V eqn:EV.
    replace (wz (A + o + l)) with (wz V) by (f_equal; lia).
    zstep. sstep. subst V.
    zstep. zstep. zstep. zstep. zstep. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BLK : rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [Z_to_bv 8 0] ++ skipn (Z.to_nat (o + l) + 1) bs)]) end.
    { lazymatch type of BLK23 with rw_cells _ ?mm _ [?c2; ?c3] =>
        pose proof (proj2 (rw_cells_app rsegs mm A [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs)] [c2; c3])) as J;
        cbn [cells_size csize Nat.add] in J; rewrite Nat.add_0_r, Z2Nat.id in J by lia;
        specialize (J (conj BLK1 BLK23)); cbn [app] in J;
        pose proof (rw_cells_merge rsegs mm A [] [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs); c2; c3] []) as M
      end.
      rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      replace (Z.to_nat (o + l) + Datatypes.S (Z.to_nat (Z.of_nat n - (o + l) - 1) + 0))%nat with n in M by lia.
      replace (firstn (Z.to_nat (Z.of_nat n - (o + l) - 1)) (skipn 1 (skipn (Z.to_nat (o + l)) bs))) with (skipn (Z.to_nat (o + l) + 1) bs) in *.
      2:{ rewrite skipn_skipn. replace (1 + Z.to_nat (o + l))%nat with (Z.to_nat (o + l) + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
      pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ. }
    clear BLK1 BLK23.
    apply evt_done. eexists. right. exists b. split; [lia|]. split; [first [exact Hb| reflexivity]|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. repeat (split; [eassumption|]). exact BLK.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO LO0 QP PHI WSL"] Lemma rq_ver : forall (r idx id A o l maj min err meth pos : Z) (n : nat) (bs : list byte) (b : byte) (hack entp clen csz esp : Z)
      gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u64arr rsegs m MTAB ws -> nth_error ws (Z.to_nat (2 * idx + 1)) = Some (wz id) -> (0 <= idx < 11)%Z -> (0 <= id < 64)%Z ->
    rw_cells rsegs m (q + 8) [C8 S7; C8 S9; C8 S8] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m A [CB n bs] ->
    rw_cells rsegs m (P + 276) [C4 (wz maj)] -> rw_cells rsegs m (P + 280) [C4 (wz min)] ->
    rw_cells rsegs m (P + 440) (ctl8 err hack pos entp clen csz esp) -> rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] ->
    (- 2^31 <= maj < 2^31)%Z -> (- 2^31 <= min < 2^31)%Z -> (r = -1 \/ 0 <= r <= 2)%Z -> (0 <= err < 2^32)%Z -> (0 <= meth < 2^32)%Z -> (0 <= pos < 2^32)%Z ->
    (0 <= o)%Z -> (0 <= l)%Z -> (o + l + 1 < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    (A + Z.of_nat n <= 0x29000 \/ 0x5c000 <= A)%Z ->
    evt rsegs (fun ms' => exists m' (ra0 err' meth' pos' : Z) a0' a1' a2',
        ms' = PRS HEAD x1 t0 t1 t2 (wz ra0) a1' a2' a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 8) [C8 S7; C8 S9; C8 S8] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o)); C8 (wz l)]
        /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj)] /\ rw_cells rsegs m' (P + 280) [C4 (wz min)]
        /\ rw_cells rsegs m' (P + 440) (ctl8 err' hack pos' entp clen csz esp) /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')]
        /\ u64arr rsegs m' MTAB ws
        /\ ( (ra0 = 3 /\ err' = 505 /\ meth' = meth /\ pos' = pos)
           \/ (ra0 = 4 /\ err' = err /\ meth' = id /\ pos' = 2 /\ r = 2 /\ 0 <= maj) )%Z /\ (a0' : word) = a0')
      (PRS 0x157c0 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 (wz (bv_unsigned b)) (wz MTAB) (wz idx) t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TAB HN IR IDR Q8 Q56 BLK C1c C2c CTL MC MR NR RR ER METR PR O0 L0 KN A0 AHI AW. unfold ctl8 in *.
    pose proof (munch_refl [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    apply (rw_cells_split_CB rsegs m A [] n bs [] [Z.to_nat (o + l); 1%nat; Z.to_nat (Z.of_nat n - (o + l) - 1)]) in BLK; [| cbn; lia].
    cbn [app mk_CB_cells] in BLK.
    lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
      destruct (proj1 (rw_cells_app rsegs m A [c1] [c2; c3]) BLK) as [BLK1 BLK23] end. clear BLK.
    cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r, Z2Nat.id in BLK23 by lia.
    zstep. zstep. zstep.
    remember (A + (o + l))%Z as V eqn:EV.
    replace (wz (A + o + l)) with (wz V) by (f_equal; lia).
    step. change (Z_to_bv 64 (bv_unsigned b)) with (zxb b). rewrite le1_zxb. mem_after_store. subst V.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (BLK : rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]) end.
    { lazymatch type of BLK23 with rw_cells _ ?mm _ [?c2; ?c3] =>
        pose proof (proj2 (rw_cells_app rsegs mm A [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs)] [c2; c3])) as J;
        cbn [cells_size csize Nat.add] in J; rewrite Nat.add_0_r, Z2Nat.id in J by lia;
        specialize (J (conj BLK1 BLK23)); cbn [app] in J;
        pose proof (rw_cells_merge rsegs mm A [] [CB (Z.to_nat (o + l)) (firstn (Z.to_nat (o + l)) bs); c2; c3] []) as M
      end.
      rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
      replace (Z.to_nat (o + l) + Datatypes.S (Z.to_nat (Z.of_nat n - (o + l) - 1) + 0))%nat with n in M by lia.
      replace (firstn (Z.to_nat (Z.of_nat n - (o + l) - 1)) (skipn 1 (skipn (Z.to_nat (o + l)) bs))) with (skipn (Z.to_nat (o + l) + 1) bs) in *.
      2:{ rewrite skipn_skipn. replace (1 + Z.to_nat (o + l))%nat with (Z.to_nat (o + l) + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
      pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ. }
    clear BLK1 BLK23. unfold zxb.

    assert (FAIL : forall (s9v a0v a1v a2v : word) mm, munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
      rw_cells rsegs mm (q + 8) [C8 S7; C8 S9; C8 S8] -> rw_cells rsegs mm (q + 56) [C8 (wz (A + o)); C8 (wz l)] ->
      rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)] ->
      rw_cells rsegs mm (P + 276) [C4 (wz maj)] -> rw_cells rsegs mm (P + 280) [C4 (wz min)] ->
      rw_cells rsegs mm (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] ->
      rw_cells rsegs mm P [C4 (wz 1); C4 (wz meth)] -> u64arr rsegs mm MTAB ws ->
      evt rsegs (fun ms' => exists m' (ra0 err' meth' pos' : Z) a0' a1' a2',
        ms' = PRS HEAD x1 t0 t1 t2 (wz ra0) a1' a2' a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 8) [C8 S7; C8 S9; C8 S8] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o)); C8 (wz l)]
        /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj)] /\ rw_cells rsegs m' (P + 280) [C4 (wz min)]
        /\ rw_cells rsegs m' (P + 440) [C4 (wz err'); C4 (wz hack); C4 (wz pos'); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')]
        /\ u64arr rsegs m' MTAB ws
        /\ ( (ra0 = 3 /\ err' = 505 /\ meth' = meth /\ pos' = pos)
           \/ (ra0 = 4 /\ err' = err /\ meth' = id /\ pos' = 2 /\ r = 2 /\ 0 <= maj) )%Z /\ (a0' : word) = a0')
       (PRS 0x15804 x1 t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 (wz (bv_unsigned b)) (wz MTAB) s9v t3 t4 t5 t6 gp tp F fc mm)).
    { intros s9v a0v a1v a2v mm MU' WM' MI' Q8' Q56' BLK' C1' C2' CTL' MC' TAB'.
      clear MU WM MI Q8 Q56 BLK C1c C2c CTL MC TAB.
      zstep. sstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists _, 3, 505, meth, pos. do 3 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [eassumption|].
      repeat (split; [eassumption|]). split; [left; repeat split; reflexivity| reflexivity]. }
    zstep. if_cases K; zify_cond K; condn K.
    { eapply FAIL; eassumption. }
    assert (R2 : r = 2).
    { change 18446744073709551615%Z with (Z.ones 64) in K. rewrite Z.land_ones in K by lia.
      destruct RR as [->|RR']; [cbv in K; lia|]. rewrite Z.mod_small in K by lia. exact K. }
    subst r.
    zstep. zstep. rewrite (sx32_lit maj) by lia. zstep. if_cases K1; zify_cond K1.
    { eapply FAIL; eassumption. }
    assert (MJ0 : (0 <= maj)%Z) by (destruct (Z.lt_ge_cases maj 0); [sgn K1 maj; lia| lia]).
    pose proof (u64arr_read4 _ MTAB ws (2 * idx + 1) (wz id) (Z_to_bv 64 (MTAB + Z.shiftl idx 4 + 8)) TAB HN ltac:(lia)
                  ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.

    assert (OK : forall (a0v a1v a2v : word) mm, munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m mm -> wmono rsegs m mm -> mem_inv rsegs mm ->
      rw_cells rsegs mm (q + 8) [C8 S7; C8 S9; C8 S8] -> rw_cells rsegs mm (q + 56) [C8 (wz (A + o)); C8 (wz l)] ->
      rw_cells rsegs mm A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)] ->
      rw_cells rsegs mm (P + 276) [C4 (wz maj)] -> rw_cells rsegs mm (P + 280) [C4 (wz min)] ->
      rw_cells rsegs mm (P + 440) [C4 (wz err); C4 (wz hack); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] ->
      rw_cells rsegs mm P [C4 (wz 1); C4 (wz meth)] -> u64arr rsegs mm MTAB ws ->
      evt rsegs (fun ms' => exists m' (ra0 err' meth' pos' : Z) a0' a1' a2',
        ms' = PRS HEAD x1 t0 t1 t2 (wz ra0) a1' a2' a3 a4 a5 a6 a7 S7 S8 S9 t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(A + (o + l), A + (o + l) + 1); (P + 440, P + 444); (P + 448, P + 452); (P + 4, P + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (q + 8) [C8 S7; C8 S9; C8 S8] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o)); C8 (wz l)]
        /\ rw_cells rsegs m' A [CB n (firstn (Z.to_nat (o + l)) bs ++ [b] ++ skipn (Z.to_nat (o + l) + 1) bs)]
        /\ rw_cells rsegs m' (P + 276) [C4 (wz maj)] /\ rw_cells rsegs m' (P + 280) [C4 (wz min)]
        /\ rw_cells rsegs m' (P + 440) [C4 (wz err'); C4 (wz hack); C4 (wz pos'); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz esp)] /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')]
        /\ u64arr rsegs m' MTAB ws
        /\ ( (ra0 = 3 /\ err' = 505 /\ meth' = meth /\ pos' = pos)
           \/ (ra0 = 4 /\ err' = err /\ meth' = id /\ pos' = 2 /\ 2 = 2 /\ 0 <= maj) )%Z /\ (a0' : word) = a0')
       (PRS 0x15864 x1 t0 t1 t2 a0v a1v a2v a3 a4 a5 a6 a7 (wz (bv_unsigned b)) (wz MTAB) (wz (Z.shiftl idx 4)) t3 t4 t5 t6 gp tp F fc mm)).
    { intros a0v a1v a2v mm MU' WM' MI' Q8' Q56' BLK' C1' C2' CTL' MC' TAB'.
      clear MU WM MI Q8 Q56 BLK C1c C2c CTL MC TAB K K1.
      pose proof (u64arr_read4 mm MTAB ws (2 * idx + 1) (wz id) (Z_to_bv 64 (MTAB + Z.shiftl idx 4 + 8)) TAB' HN ltac:(lia)
                    ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD'.
      zstep. zstep. rewrite (sx32_lit id) by lia. sstep. sstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. eexists _, 4, err, id, 2. do 3 eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [eassumption|].
      repeat (split; [eassumption|]). split; [right; repeat split; try reflexivity; lia| reflexivity]. }
    zstep. zstep. if_cases K2; zify_cond K2; condn K2.
    { eapply OK; eassumption. }
    zstep. zstep. rewrite (sx32_lit min) by lia. zstep. if_cases K3; zify_cond K3.
    { eapply OK; eassumption. }
    zstep. zstep. rewrite (sx32_lit id) by lia. zstep. zstep. if_cases K4; zify_cond K4; condn K4.
    { eapply OK; eassumption. }
    eapply FAIL; eassumption.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.
End SEGS.
