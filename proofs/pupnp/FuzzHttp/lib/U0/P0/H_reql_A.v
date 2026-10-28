(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_sscanf H_scanner_get_token H_vfmatch_A H_match H_map_str_to_int H_str_alloc
     H_parse_uri_A H_presp_B H_phdr_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation FMT09 := 0x10331%Z.
Notation FMTREQ := 0x10423%Z.
Notation MTAB := 0x2b3b8%Z.
Notation FMT_VER := 0x10365%Z.
Notation HEAD := 0x15c98%Z.
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
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis QP : (q + 208 <= P)%Z.
  Hypothesis PHI : (P + 504 < 2^63)%Z.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz (-1)) (wz 47) (wz 2) (wz FMT09) (wz MTAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).
  Notation S7 := (wz (P + 8)). Notation S8 := (wz (P + 276)). Notation S9 := (wz (P + 280)).
  Notation FXC := [C8 S9; C8 S8; C8 S7; C8 (wz (2^64 - 1 - MTAB)); C8 (wz FMTREQ)].

  Variable ws : list word.
  Hypothesis WSL : length ws = 22%nat.
  Hypothesis MID : forall i, (0 <= i < 11)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.

  #[using="Type"] Lemma rq_blank : forall gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    evt rsegs (fun ms' => ms' = PRS sgt_entry (wz 0x15cc8) t0 t1 t2 (wz S) (wz (q + 88)) (wz (q + 72)) a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m)
      (PRS 0x15cb8 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. unfold sgt_entry. pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. zstep. apply evt_done. reflexivity.
  Qed.

  #[using="QP PHI"] Lemma rq_tok : forall (r ty tl cur' : Z) (tb tyw : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m (jt : word),
    mem_inv rsegs m -> rw_cells rsegs m (q + 72) [C4 tyw; C4 jt] -> rw_cells rsegs m (q + 88) [C8 tb; C8 (wz tl)] ->
    rw_cells rsegs m S [C8 (wz MB); C8 (wz cur'); C4 (wz 0)] ->
    (0 <= r <= 5)%Z -> (r = 4 -> tyw = wz ty /\ 0 <= ty <= 5)%Z -> (r = 4 -> 0 <= tl <= cur')%Z -> (0 <= cur' < 2^62)%Z ->
    evt rsegs (fun ms' => exists m' (a0' : word),
        ( (r <> 4 /\ ms' = PRS HEAD x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
       \/ (r = 4 /\ (ty = 1 \/ ty = 2) /\ ms' = PRS 0x15cb8 x1 t0 t1 t2 a0' a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m' /\ m' = m)
       \/ (r = 4 /\ ty <> 1 /\ ty <> 2
           /\ ms' = PRS match_entry (wz 0x15cfc) t0 t1 t2 (wz S) (wz FMT09) (wz (q + 88)) (wz (q + 56)) a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
           /\ munch [(P + 488, P + 496)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
           /\ rw_cells rsegs m' (q + 72) [C4 tyw; C4 jt] /\ rw_cells rsegs m' (q + 88) [C8 tb; C8 (wz tl)]
           /\ rw_cells rsegs m' S [C8 (wz MB); C8 (wz (cur' - tl)); C4 (wz 0)]) ))
      (PRS 0x15cc8 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
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

  #[using="Type"] Lemma rq_m09 : forall (r : Z) (mb ml : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 88) [C8 mb; C8 ml] -> rw_cells rsegs m (q + 16) FXC -> (0 <= r <= 5)%Z ->
    evt rsegs (fun ms' =>
        ( r = 4 /\ ms' = PRS map_str_to_int_entry (wz 0x15d18) t0 t1 t2 mb ml (wz MTAB) (wz 11) (wz 1) a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m)
     \/ ( r <> 4 /\ ms' = PRS match_entry (wz 0x15dcc) t0 t1 t2 (wz S) (wz FMTREQ) (wz (q + 88)) (wz (q + 56)) (wz (q + 72)) a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m))
      (PRS 0x15cfc x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
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

  #[using="lo QLO LO0 QP PHI WSL MID"] Lemma rq_msi09 : forall (r meth err ub ul : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> u64arr rsegs m MTAB ws -> rw_cells rsegs m P [C4 (wz 1); C4 (wz meth)] -> rw_cells rsegs m (P + 440) [C4 (wz err)] ->
    rw_cells rsegs m (q + 56) [C8 (wz ub); C8 (wz ul)] -> rw_cells rsegs m (q + 16) FXC ->
    (r = -1 \/ 0 <= r < 11)%Z -> (0 <= ub < 2^64)%Z -> (0 <= ul < 2^64)%Z -> (0 <= meth < 2^32)%Z -> (0 <= err < 2^32)%Z ->
    evt rsegs (fun ms' => exists m' (meth' err' : Z) a0' a1' a2' pc,
        ms' = PRS pc x1 t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 4, P + 8); (P + 440, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ u64arr rsegs m' MTAB ws /\ rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth')] /\ rw_cells rsegs m' (P + 440) [C4 (wz err')]
        /\ rw_cells rsegs m' (q + 56) [C8 (wz ub); C8 (wz ul)]
        /\ ( (pc = HEAD /\ a0' = wz 3 /\ meth' = meth /\ (err' = 501 \/ err' = 400))
           \/ (pc = 0x15d50 /\ a0' = wz ub /\ a2' = wz ul /\ meth' = 12 /\ err' = err
               /\ exists id, 0 <= r /\ nth_error ws (Z.to_nat (2 * r + 1)) = Some (wz id) /\ id = 2) )%Z)
      (PRS 0x15d18 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof.
    intros until m. intros MI TAB MC EC UC MTC RR UB UL MR ER.
    pose proof (munch_refl [(P + 4, P + 8); (P + 440, P + 444)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K0; zify_cond K0.
    {   zstep. zstep. sstep. zstep. zstep.
      apply evt_done. eexists m0, meth, 501. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      repeat (split; [eassumption|]). left. repeat split; try reflexivity. left; reflexivity. }
    assert (R0 : (0 <= r < 11)%Z). { destruct RR as [->|RR']; [exfalso| exact RR']. cbv in K0. first [lia| discriminate| exact (K0 eq_refl)]. }
    destruct (MID r R0) as (id & HN & IDR).
    pose proof (u64arr_read4 m MTAB ws (2 * r + 1) (wz id) (Z_to_bv 64 (MTAB + Z.shiftl r 4 + 8)) TAB HN ltac:(lia)
                  ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    zstep. zstep. ubr. zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 r 4) by lia. ubr.
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

  #[using="QLO QP PHI"] Lemma rq_slash_body1 : forall (k : nat) (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o)); C8 (wz l)] ->
    (l < Z.of_nat k)%Z -> (0 <= o)%Z -> (2 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3' a4',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4' a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x15d94 \/ ra' = 0x15f68)
        /\ munch [(q + 56, q + 72)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x15d58 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) (wz (A + o + 1)) a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry.
    induction k as [|k IH]; intros until m; intros MI BLK Q40 HK O0 L2 OL A0 AHI; [lia|].
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 56, q + 72)]%Z m) as MU.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    destruct (nth_error bs (Z.to_nat o)) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
    destruct (nth_error bs (Z.to_nat (o + 1))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
    pose proof (byte_range b0) as BR0. pose proof (byte_range b1) as BR1.
    pose proof (cb_read1 m A n bs o b0 BLK Hb0 ltac:(lia)) as RD0.
    pose proof (cb_read1 m A n bs (o + 1) b1 BLK Hb1 ltac:(lia)) as RD1.
    replace (wa (A + o)) with (wa (A + o + 1 + -1)) in RD0 by (unfold wa; f_equal; lia).
    replace (wa (A + (o + 1))) with (wa (A + o + 1 + 0)) in RD1 by (unfold wa; f_equal; lia).
    zstep. zstep. ubr. zstep. zstep. if_cases K0; zify_cond K0.
    {
      zstep. zstep. zstep. replace (A + o + 1 + -1)%Z with (A + o)%Z by lia.
      apply evt_done. eexists m, o, l, _. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. ubr. zstep. zstep. if_cases K1; zify_cond K1.
    { zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. zstep. zstep. sstep. sstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      replace (A + o + 1 + 1)%Z with (A + (o + 1) + 1)%Z by lia. replace (A + o + 2)%Z with (A + (o + 1) + 1)%Z by lia.
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with BLK' : rw_cells rsegs mm A _, Q40' : rw_cells rsegs mm (q + 56) _, MI' : mem_inv rsegs mm |- _ =>
          eapply evt_mono; [eapply (IH A (o + 1)%Z (l - 1)%Z n bs); first [exact MI'| exact BLK'| exact Q40'| lia]|] end end.
      cbv beta. intros ms' (m' & o' & l' & ra' & a1' & a3' & a4' & -> & HRA & MU' & WM' & MI' & BLK' & Q40' & OL' & _).
      eexists m', o', l', ra'. do 3 eexists. split; [reflexivity|]. split; [exact HRA|].
      split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
      split; [exact BLK'|]. split; [exact Q40'|]. split; [lia| reflexivity].
    -
      zstep.
      assert (L1 : (l - 1 = 1)%Z) by (revert K2; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia).
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      replace (wz 1) with (wz (l - 1)) by (f_equal; lia).
      apply evt_done. eexists _, (o + 1)%Z, (l - 1)%Z, _. do 3 eexists. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [lia| reflexivity].
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash1 : forall (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o)); C8 (wz l)] ->
    (0 <= o)%Z -> (1 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3' a4',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4' a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x15d94 \/ ra' = 0x15f68)
        /\ munch [(q + 56, q + 72)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x15d50 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry. intros until m; intros MI BLK Q40 O0 L1 OL A0 AHI.
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 56, q + 72)]%Z m) as MU.
    zstep. if_cases K; zify_cond K.
    -   zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity].
    - zstep. eapply (rq_slash_body1 (Datatypes.S (Z.to_nat l))); try eassumption; try LiaTuning.alia.
      all: revert K; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash_body2 : forall (k : nat) (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o)); C8 (wz l)] ->
    (l < Z.of_nat k)%Z -> (0 <= o)%Z -> (2 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3' a4',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4' a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x15e1c \/ ra' = 0x15e3c)
        /\ munch [(q + 56, q + 72)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x15de0 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) (wz (A + o + 1)) a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry.
    induction k as [|k IH]; intros until m; intros MI BLK Q40 HK O0 L2 OL A0 AHI; [lia|].
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 56, q + 72)]%Z m) as MU.
    assert (LBS : length bs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
    destruct (nth_error bs (Z.to_nat o)) as [b0|] eqn:Hb0. 2:{ exfalso. apply nth_error_None in Hb0. lia. }
    destruct (nth_error bs (Z.to_nat (o + 1))) as [b1|] eqn:Hb1. 2:{ exfalso. apply nth_error_None in Hb1. lia. }
    pose proof (byte_range b0) as BR0. pose proof (byte_range b1) as BR1.
    pose proof (cb_read1 m A n bs o b0 BLK Hb0 ltac:(lia)) as RD0.
    pose proof (cb_read1 m A n bs (o + 1) b1 BLK Hb1 ltac:(lia)) as RD1.
    replace (wa (A + o)) with (wa (A + o + 1 + -1)) in RD0 by (unfold wa; f_equal; lia).
    replace (wa (A + (o + 1))) with (wa (A + o + 1 + 0)) in RD1 by (unfold wa; f_equal; lia).
    zstep. zstep. ubr. zstep. zstep. if_cases K0; zify_cond K0.
    {
      zstep. zstep. zstep. replace (A + o + 1 + -1)%Z with (A + o)%Z by lia.
      apply evt_done. eexists m, o, l, _. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. ubr. zstep. zstep. if_cases K1; zify_cond K1.
    { zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity]. }
    zstep. zstep. zstep. sstep. sstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      replace (A + o + 1 + 1)%Z with (A + (o + 1) + 1)%Z by lia. replace (A + o + 2)%Z with (A + (o + 1) + 1)%Z by lia.
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch goal with BLK' : rw_cells rsegs mm A _, Q40' : rw_cells rsegs mm (q + 56) _, MI' : mem_inv rsegs mm |- _ =>
          eapply evt_mono; [eapply (IH A (o + 1)%Z (l - 1)%Z n bs); first [exact MI'| exact BLK'| exact Q40'| lia]|] end end.
      cbv beta. intros ms' (m' & o' & l' & ra' & a1' & a3' & a4' & -> & HRA & MU' & WM' & MI' & BLK' & Q40' & OL' & _).
      eexists m', o', l', ra'. do 3 eexists. split; [reflexivity|]. split; [exact HRA|].
      split; [eapply munch_trans; [exact MU| exact MU']|]. split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|].
      split; [exact BLK'|]. split; [exact Q40'|]. split; [lia| reflexivity].
    -
      zstep.
      assert (L1 : (l - 1 = 1)%Z) by (revert K2; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia).
      replace (A + o + 1)%Z with (A + (o + 1))%Z in * by lia. replace (l + -1)%Z with (l - 1)%Z in * by lia.
      replace (wz 1) with (wz (l - 1)) by (f_equal; lia).
      apply evt_done. eexists _, (o + 1)%Z, (l - 1)%Z, _. do 3 eexists. split; [reflexivity|]. split; [left; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [lia| reflexivity].
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QLO QP PHI"] Lemma rq_slash2 : forall (A o l : Z) (n : nat) (bs : list byte) gp tp t0 t1 t2 a1 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m A [CB n bs] -> rw_cells rsegs m (q + 56) [C8 (wz (A + o)); C8 (wz l)] ->
    (0 <= o)%Z -> (1 <= l)%Z -> (o + l < Z.of_nat n)%Z -> (0 < A)%Z -> (A + Z.of_nat n <= lo)%Z ->
    evt rsegs (fun ms' => exists m' (o' l' ra' : Z) a1' a3' a4',
        ms' = PRS str_alloc_entry (wz ra') t0 t1 t2 (wz (A + o')) (wz l') (wz l') a3' a4' a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ (ra' = 0x15e1c \/ ra' = 0x15e3c)
        /\ munch [(q + 56, q + 72)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' A [CB n bs] /\ rw_cells rsegs m' (q + 56) [C8 (wz (A + o')); C8 (wz l')]
        /\ (o <= o' /\ o' + l' = o + l /\ 1 <= l')%Z /\ (a1' : word) = a1')
      (PRS 0x15dd8 x1 t0 t1 t2 (wz (A + o)) a1 (wz l) a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    unfold str_alloc_entry. intros until m; intros MI BLK Q40 O0 L1 OL A0 AHI.
    pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(q + 56, q + 72)]%Z m) as MU.
    zstep. if_cases K; zify_cond K.
    -   zstep. zstep.
      apply evt_done. eexists m, o, l, _. do 3 eexists. split; [reflexivity|]. split; [right; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BLK|]. split; [exact Q40|]. split; [lia| reflexivity].
    - zstep. eapply (rq_slash_body2 (Datatypes.S (Z.to_nat l))); try eassumption; try LiaTuning.alia.
      all: revert K; change 18446744073709551615%Z with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia; lia.
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.

  #[using="QP PHI"] Lemma rq_sa09 : forall (pc U ul : Z) (ubw errw ubuf : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (pc = 0x15d94 \/ pc = 0x15f68) ->
    mem_inv rsegs m -> rw_cells rsegs m (P + 432) [C8 ubw] -> rw_cells rsegs m (P + 440) [C4 errw] ->
    rw_cells rsegs m (q + 56) [C8 ubuf; C8 (wz ul)] -> rw_cells rsegs m (q + 16) FXC -> (0 <= U < 2^64)%Z -> (0 <= ul < 2^64)%Z ->
    evt rsegs (fun ms' => exists m' (errw' : word) a0' a1' a2' x1' pc',
        ms' = PRS pc' x1' t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 432, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (P + 432) [C8 (wz U)] /\ rw_cells rsegs m' (P + 440) [C4 errw'] /\ rw_cells rsegs m' (q + 56) [C8 ubuf; C8 (wz ul)]
        /\ ( (U = 0 /\ pc' = HEAD /\ x1' = x1 /\ a0' = wz 3 /\ errw' = wz 500)
           \/ (U <> 0 /\ pc' = parse_uri_entry /\ x1' = wz 0x15f7c /\ a0' = wz U /\ a1' = wz ul /\ a2' = S7 /\ errw' = errw) )%Z)
      (PRS pc x1 t0 t1 t2 (wz U) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros PC MI UBC EC UC S7C UR ULR. unfold parse_uri_entry.
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

  #[using="QP PHI"] Lemma rq_sa : forall (pc U ul : Z) (ubw errw ubuf : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    (pc = 0x15e1c \/ pc = 0x15e3c) ->
    mem_inv rsegs m -> rw_cells rsegs m (P + 432) [C8 ubw] -> rw_cells rsegs m (P + 440) [C4 errw] ->
    rw_cells rsegs m (q + 56) [C8 ubuf; C8 (wz ul)] -> rw_cells rsegs m (q + 16) FXC -> (0 <= U < 2^64)%Z -> (0 <= ul < 2^64)%Z ->
    evt rsegs (fun ms' => exists m' (errw' : word) a0' a1' a2' x1' pc',
        ms' = PRS pc' x1' t0 t1 t2 a0' a1' a2' a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 432, P + 444)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (P + 432) [C8 (wz U)] /\ rw_cells rsegs m' (P + 440) [C4 errw'] /\ rw_cells rsegs m' (q + 56) [C8 ubuf; C8 (wz ul)]
        /\ ( (U = 0 /\ pc' = HEAD /\ x1' = x1 /\ a0' = wz 3 /\ errw' = wz 500)
           \/ (U <> 0 /\ pc' = parse_uri_entry /\ x1' = wz 0x15e50 /\ a0' = wz U /\ a1' = wz ul /\ a2' = S7 /\ errw' = errw) )%Z)
      (PRS pc x1 t0 t1 t2 (wz U) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros PC MI UBC EC UC S7C UR ULR. unfold parse_uri_entry.
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

  #[using="PHI"] Lemma rq_pu09 : forall (r err hack pos entp clen csz esp : Z) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (P + 440) (ctl8 err hack pos entp clen csz esp) -> (0 <= r < 2^64)%Z ->
    evt rsegs (fun ms' => exists m' (ra0 pos' : Z),
        ms' = PRS HEAD x1 t0 t1 t2 (wz ra0) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m'
        /\ munch [(P + 448, P + 452)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (P + 440) (ctl8 err hack pos' entp clen csz esp)
        /\ ( (r <> 1 /\ ra0 = 3 /\ pos' = pos /\ m' = m) \/ (r = 1 /\ ra0 = 0 /\ pos' = 4) )%Z)
      (PRS 0x15f7c x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros MI CTL RR. unfold ctl8 in *.
    pose proof (munch_refl [(P + 448, P + 452)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. if_cases K; zify_cond K; condn K.
    - zstep. zstep. apply evt_done. eexists m, 3, pos. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split; [exact CTL|]. left. repeat split; lia.
    - zstep. sstep. zstep. apply evt_done. eexists _, 0, 4. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
      split; [eassumption|]. right. repeat split; lia.
  Qed.

  #[using="Type"] Lemma rq_pu : forall (r : Z) (mb ml : word) gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 x1 (F : bvmap 5 word) fc m,
    mem_inv rsegs m -> rw_cells rsegs m (q + 88) [C8 mb; C8 ml] -> (0 <= r < 2^64)%Z ->
    evt rsegs (fun ms' =>
        ( (r <> 1)%Z /\ ms' = PRS HEAD x1 t0 t1 t2 (wz 3) (wz r) a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m )
     \/ ( r = 1 /\ ms' = PRS map_str_to_int_entry (wz 0x15e7c) t0 t1 t2 mb ml (wz MTAB) (wz 11) (wz 1) a5 a6 a7 (wz MTAB) s9v t3 t4 t5 t6 gp tp F fc m ))
      (PRS 0x15e50 x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp tp F fc m).
  Proof. clear WSL MID.
    intros until m. intros MI MC RR. unfold map_str_to_int_entry.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    zstep. zstep. zstep. if_cases K; zify_cond K; condn K.
    - apply evt_done. left. split; [lia| reflexivity].
    - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      apply evt_done. right. split; [lia| reflexivity].
    Unshelve. all: try exact (wz 0); try exact m.
  Qed.
End SEGS.
