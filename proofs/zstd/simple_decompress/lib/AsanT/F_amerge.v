(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ AKitR ARep ARepKit ARepFrame ARepQ ARepQP.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma firstn_S_snoc : forall {X} (l : list X) i x, nth_error l i = Some x -> firstn (Datatypes.S i) l = firstn i l ++ [x].
Proof.
  intros X l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH i x H). reflexivity.
Qed.

Definition amerge_entry : Z := 0x35898.
Definition amerge_loop : Z := 0x358d0.     (* [comment removed for export] *)
Definition amerge_copy : Z := 0x35908.     (* [comment removed for export] *)
Definition amerge_copied : Z := 0x3591c.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mcopy_loop_spec : forall RNG (d : nat) (i n SRC DST : Z) (src ws0 : list word)
    ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (n - i) ->
  0 <= i < n -> length src = Z.to_nat n -> (n <= Z.of_nat (length ws0))%Z ->
  u64arr bsegs m SRC src ->
  u64arr bsegs m DST (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) ->
  mem_inv bsegs m ->
  0 <= SRC -> SRC + 8 * n < 2^47 -> 0 <= DST -> DST + 8 * Z.of_nat (length ws0) < 2^47 ->
  (SRC + 8 * n <= DST \/ DST + 8 * Z.of_nat (length ws0) <= SRC) ->
  rng RNG SRC (8 * n) -> rng RNG DST (8 * n) ->
  evtF bsegs RNG (fun ms' => exists t5' m',
      ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (SRC + 8 * n)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + 8 * n)) (Z_to_bv 64 (SRC + 8 * n)) t5' t6) F (Z_to_bv 64 amerge_copied) fc None m' (seg_rom bsegs)
      /\ munch [(DST, DST + 8 * n)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ u64arr bsegs m' SRC src /\ u64arr bsegs m' DST (src ++ skipn (Z.to_nat n) ws0))
    (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (SRC + 8 * i)) s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (DST + 8 * i)) (Z_to_bv 64 (SRC + 8 * n)) t5 t6) F (Z_to_bv 64 amerge_copy) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I LS LW SRCA DSTA MI S0 S1 D0 D1 DJ RS RD; [lia|].
  unfold amerge_copy, amerge_copied in *.
  pose proof (munch_refl [(DST, DST + 8 * n)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (nth_error src (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; lia].
  assert (LD : length (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) = length ws0) by (rewrite length_app, length_firstn, length_skipn; lia).
  pose proof (u64arr_read bsegs _ _ src i w (wa (SRC + 8 * i)) SRCA NTH ltac:(lia) eq_refl) as RDV.
  assert (RS1 : rng RNG (SRC + 8 * i) 8) by (eapply rng_sub'; [exact RS| lia]).
  assert (RD1 : rng RNG (DST + 8 * i) 8) by (eapply rng_sub'; [exact RD| lia]).
  step. clear RDV RS1.                                   (* [comment removed for export] *)
  zstep.                                                 (* [comment removed for export] *)
  setreg 7 (Z_to_bv 64 (SRC + 8 * (i + 1))) ltac:(f_equal; clear; lia).
  pose proof (u64arr_store_ok bsegs m DST _ i (wa (DST + 8 * i)) DSTA ltac:(rewrite LD; lia) eq_refl) as SOK.
  step.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?a (le8 ?v)) _) =>
    let E := lazymatch a with wa ?E => E | Z_to_bv _ ?E => E end in
    pose proof (u64arr_write bsegs m DST _ i v DSTA ltac:(rewrite LD; lia)) as DST2;
    replace (DST + 8 * i)%Z with E in DST2 by lia
  end.
  replace (upd (firstn (Z.to_nat i) src ++ skipn (Z.to_nat i) ws0) (Z.to_nat i) w)
     with (firstn (Z.to_nat (i + 1)) src ++ skipn (Z.to_nat (i + 1)) ws0) in DST2.
  2:{ rewrite upd_firstn_skipn by (rewrite LD; lia).
      rewrite firstn_app, firstn_firstn, Nat.min_id, length_firstn.
      replace (Z.to_nat i - Nat.min (Z.to_nat i) (length src))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite skipn_app, length_firstn. replace (Datatypes.S (Z.to_nat i) - Nat.min (Z.to_nat i) (length src))%nat with 1%nat by lia.
      rewrite skipn_skipn. replace (1 + Z.to_nat i)%nat with (Z.to_nat (i + 1)) by lia.
      replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) at 1 by lia.
      rewrite (firstn_S_snoc _ _ _ NTH), (skipn_all2 (firstn (Z.to_nat i) src)) by (rewrite length_firstn; lia).
      rewrite <- app_assoc. reflexivity. }
  assert (SRC2 : u64arr bsegs (write_to_mem m (wa (DST + 8 * i)) (le8 w)) SRC src).
  { apply Arr.u64arr_frame; [exact SRCA| lia| rewrite length_le8; lia| rewrite length_le8; lia]. }
  clear DSTA SRCA. store_done. try clear SOK. clear RD1.
  zstep.                                                 (* [comment removed for export] *)
  setreg 28 (Z_to_bv 64 (DST + 8 * (i + 1))) ltac:(f_equal; clear; lia).
  step. if_cases K; zify_cond K.                         (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia.
    eapply evtF_mono.
    { eapply (IH (i + 1) n SRC DST src ws0); try eassumption; try lia. }
    cbv beta. intros ms' (t5' & m' & -> & MU2 & WM2 & MI2 & SR3 & DS3).
    exists t5', m'. split; [reflexivity|].
    split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
    split; [exact MI2|]. split; [exact SR3| exact DS3].
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in K by lia. assert (EI : i + 1 = n) by lia.
    apply evtF_done. rewrite EI in DST2 |- *. eexists _, _. split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact SRC2|].
    rewrite firstn_all2 in DST2 by lia. exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u64arr_app2 : forall m A ws1 ws2,
  u64arr bsegs m A ws1 -> u64arr bsegs m (A + 8 * Z.of_nat (length ws1)) ws2 -> u64arr bsegs m A (ws1 ++ ws2).
Proof.
  intros m A ws1 ws2 [HB HW] [HB2 HW2]. split.
  - rewrite u64s_app. apply bytes_at_app. split; [exact HB|]. rewrite u64s_length.
    replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) by lia. exact HB2.
  - rewrite length_app. destruct HW as (H0 & H1 & HW). destruct HW2 as (H2 & H3 & HW2).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_le_dec i (8 * Z.of_nat (length ws1))); [apply HW; lia|].
    replace (A + i) with (A + 8 * Z.of_nat (length ws1) + (i - 8 * Z.of_nat (length ws1))) by lia. apply HW2. lia.
Qed.

(* [comment removed for export] *)

Lemma junk_of_u64arr : forall m A ws, u64arr bsegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W]. exists (u64s ws). split; [split|].
  - cbn. split; [rewrite u64s_length; lia| exact I].
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. replace (Z.of_nat (Z.to_nat (8 * Z.of_nat (length ws)) + 0)) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Lemma u64arr_of_junk : forall m A n, junk_at m A (8 * n) -> 0 <= n ->
  exists ws, u64arr bsegs m A ws /\ length ws = Z.to_nat n.
Proof.
  intros m A n [bs H] Hn. replace (Z.to_nat (8 * n)) with (8 * Z.to_nat n)%nat in H by lia.
  destruct (u64arr_of_CB m A (Z.to_nat n) bs H) as [U L]. exists (words_of_bytes bs). split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mcore_post (ra sp gp tp s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (CUR NXT LST nxn szc szn cc cn ls : Z) (ec en : list word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 m',
    ms' = MS (mkR ra sp gp tp (Z_to_bv 64 NXT) (Z_to_bv 64 (cc + cn)) t2 s0 s1 (Z_to_bv 64 LST) a1 a2 (Z_to_bv 64 ls) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3593c) fc None m' (seg_rom bsegs)
    /\ munch [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 (szc + szn - Q_BATCH_BYTES)); C8 (Z_to_bv 64 (cc + cn))]
    /\ u64arr bsegs m' (CUR + 24) (ec ++ en)
    /\ junk_at m' (CUR + 24 + 8 * (cc + cn)) (Q_BATCH_BYTES - 24 - 8 * (cc + cn))
    /\ rw_cells bsegs m' NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 Q_BATCH_BYTES); C8 (Z_to_bv 64 0)]
    /\ junk_at m' (NXT + 24) (Q_BATCH_BYTES - 24).

Lemma mcore_spec : forall RNG ra sp gp tp t2 s0 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 (F : bvmap 5 word) fc (m : amem)
    (CUR NXT LST nxn szc szn cc cn ls lf ll lb : Z) (ec en : list word),
  mem_inv bsegs m ->
  rw_cells bsegs m CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)] ->
  u64arr bsegs m (CUR + 24) ec -> length ec = Z.to_nat cc ->
  junk_at m (CUR + 24 + 8 * cc) (Q_BATCH_BYTES - 24 - 8 * cc) ->
  rw_cells bsegs m NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)] ->
  u64arr bsegs m (NXT + 24) en -> length en = Z.to_nat cn ->
  junk_at m (NXT + 24 + 8 * cn) (Q_BATCH_BYTES - 24 - 8 * cn) ->
  rw_cells bsegs m LST [C8 (Z_to_bv 64 ls); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 ll); C8 (Z_to_bv 64 lb)] ->
  Q_BATCH_BYTES <= szc < 2^63 -> 0 <= szn < 2^63 -> 0 <= cc -> 0 <= cn -> cc + cn <= Q_BATCH -> 0 <= nxn < 2^64 -> 0 <= ls < 2^64 ->
  AIMG_HI <= CUR -> CUR + Q_BATCH_BYTES <= ATOP -> AIMG_HI <= NXT -> NXT + Q_BATCH_BYTES <= ATOP ->
  (CUR + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= CUR) ->
  (LST + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= LST) -> (LST + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= LST) -> 0 <= LST -> LST + 32 <= ATOP ->
  a6 = Z_to_bv 64 (2^64 - Q_BATCH_BYTES) -> a7 = Z_to_bv 64 Q_BATCH_BYTES ->
  rng RNG CUR Q_BATCH_BYTES -> rng RNG NXT Q_BATCH_BYTES -> rng RNG LST 32 ->
  evtF bsegs RNG (mcore_post ra sp gp tp s0 s1 a1 a2 (Z_to_bv 64 CUR) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc CUR NXT LST nxn szc szn cc cn ls ec en m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 NXT) (Z_to_bv 64 (cn + cc)) t2 s0 s1 (Z_to_bv 64 LST) a1 a2 a3 (Z_to_bv 64 CUR) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cn) (Z_to_bv 64 cc) t5 t6) F (Z_to_bv 64 0x358e0) fc None m (seg_rom bsegs)).
Proof.
  intros until en. intros MI CC EC LEC JC CN EN LEN JN LS SZC SZN C0 N0 FIT NXN LSR C1 C2 N1 N2 DCN DLC DLN L1 L2 -> -> RC RN RL.
  unfold AIMG_HI, Q_BATCH_BYTES, Q_BATCH in *.
  pose proof (munch_refl [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  step.                                                   (* [comment removed for export] *)
  zstep.                                                  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.                        (* [comment removed for export] *)
  { exfalso. revert K0 SZC. clear. intros K0 SZC. rewrite ?unsigned_lit in K0 by lia. rewrite Z.shiftr_div_pow2 in K0 by lia.
    rewrite ?unsigned_lit in K0 by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
  clear K0.
  step. if_cases KZ; zify_cond KZ.                        (* [comment removed for export] *)
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KZ by lia.
    assert (cn = 0) by lia. subst cn.
    assert (en = []) by (destruct en; [reflexivity| cbn in LEN; lia]). subst en.
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (szc + szn - 8192)) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow_pos Pos.iter Z.mul]; 
                                                    clear -SZC SZN; Z.div_mod_to_equations; lia).
    destruct JC as [jc JC]. destruct JN as [jn JN].
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    apply evtF_done. unfold mcore_post, Q_BATCH_BYTES. rewrite !Z.add_0_r. replace (cc + 0) with cc in MU by lia.
    replace (0 + cc) with cc in * by lia.
    replace (NXT + 24 + 8 * 0) with (NXT + 24) in JN by lia. replace (8192 - 24 - 8 * 0) with (8192 - 24) in JN by lia.
    do 4 eexists. exists m1. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact CC|].
    split; [rewrite app_nil_r; exact EC|]. split; [exists jc; exact JC|]. split; [exact CN|]. exists jn; exact JN.
  - (* [comment removed for export] *)
    rewrite ?unsigned_lit in KZ by lia.
    do 6 zstep.                                           (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (NXT + 24 + 8 * 0)) ltac:(f_equal; clear; lia).
    setreg 28 (Z_to_bv 64 (CUR + 24 + 8 * cc + 8 * 0)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -C0; lia).
    setreg 29 (Z_to_bv 64 (NXT + 24 + 8 * cn)) ltac:(rewrite ?Z.shiftl_mul_pow2 by (clear; lia); f_equal; clear -N0; lia).
    replace (8192 - 24 - 8 * cc) with (8 * cn + (8192 - 24 - 8 * cc - 8 * cn)) in JC by lia.
    destruct (junk_split m _ _ _ JC ltac:(lia) ltac:(lia)) as [J1 J2]. clear JC.
    destruct (u64arr_of_junk m _ cn J1 ltac:(lia)) as (ws0 & WS0 & LWS0). clear J1.
    destruct J2 as [jc J2]. destruct JN as [jn JN].
    eapply evtF_cut.
    { eapply (mcopy_loop_spec RNG _ 0 cn (NXT + 24) (CUR + 24 + 8 * cc) en ws0); try reflexivity.
      - lia.
      - exact LEN.
      - rewrite LWS0. lia.
      - exact EN.
      - cbn [Z.to_nat firstn skipn app]. exact WS0.
      - exact MI.
      - lia. - lia. - lia.
      - rewrite LWS0. lia.
      - rewrite LWS0. destruct DCN; [right| left]; lia.
      - eapply rng_sub'; [exact RN| lia].
      - eapply rng_sub'; [exact RC| lia]. }
    cbv beta. intros ms' (t5' & m3 & -> & MU3 & WM3 & MI3 & SR3 & DS3).
    xport CC MU3 WM3 ltac:(clear -C0 N0; lia).
    xport CN MU3 WM3 ltac:(clear -C0 N0 FIT DCN; lia).
    xport LS MU3 WM3 ltac:(clear -C0 N0 FIT DLC; lia).
    xport EC MU3 WM3 ltac:(rewrite ?LEC; clear -C0 N0; lia).
    xport J2 MU3 WM3 ltac:(clear -C0 N0 FIT; lia).
    xport JN MU3 WM3 ltac:(clear -C0 N0 FIT DCN; lia).
    clear MI WS0 MU WM. box MU3.
    rewrite skipn_all2 in DS3 by (rewrite LWS0; lia). rewrite app_nil_r in DS3. box DS3. box SR3.
    snapshot [(CUR + 8, CUR + 24); (NXT + 8, NXT + 24)]%Z MUs WMs.
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    zstep.                                                (* [comment removed for export] *)
    setreg 7 (Z_to_bv 64 (szc + szn - 8192)) ltac:(apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.pow_pos Pos.iter Z.mul];
                                                    clear -SZC SZN; Z.div_mod_to_equations; lia).
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    step.                                                 (* [comment removed for export] *)
    apply evtF_done. unfold mcore_post, Q_BATCH_BYTES. unbox MU3.
    unbox DS3. xport DS3 MUs WMs ltac:(rewrite ?LEN; clear -C0 N0 DCN FIT; lia).
    unbox SR3. xport SR3 MUs WMs ltac:(rewrite ?LEN; clear -C0 N0 DCN FIT; lia).
    replace (cn + cc) with (cc + cn) in * by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] =>
      assert (MUF : munch [(CUR + 8, CUR + 24); (CUR + 24 + 8 * cc, CUR + 24 + 8 * (cc + cn)); (NXT + 8, NXT + 24)]%Z m mx)
        by (eapply (munch_trans_w _ _ _ _ _ _ MU3 MUs); solve_sub_fpw ltac:(clear -C0 N0; lia)) end.
    do 4 eexists. eexists. split; [reflexivity|].
    split; [exact MUF|]. split; [first [exact WM3 | eapply wmono_trans; [exact WM3| exact WMs]]|]. split; [assumption|]. split; [exact CC|].
    split. { apply u64arr_app2; [exact EC|]. rewrite LEC, Z2Nat.id by lia. exact DS3. }
    split. { exists jc. replace (CUR + 24 + 8 * (cc + cn)) with (CUR + 24 + 8 * cc + 8 * cn) by lia.
             replace (8192 - 24 - 8 * (cc + cn)) with (8192 - 24 - 8 * cc - 8 * cn) by lia. exact J2. }
    split; [exact CN|].
    replace (8192 - 24) with (8 * cn + (8192 - 24 - 8 * cn)) by lia. apply junk_merge; [| | lia| lia].
    + replace (8 * cn) with (8 * Z.of_nat (length en)) by (rewrite LEN; lia). apply junk_of_u64arr. exact SR3.
    + exists jn. exact JN.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition munlink_post (tfull : bool) (ra sp gp tp t0 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tb ex : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 (ex + Q_BATCH_BYTES)) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x359ac) fc None m' (seg_rom bsegs)
    /\ munch ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ (if tfull then [(TL, TL + 8)] else []))%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ rw_cells bsegs m' CUR [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)]
    /\ rw_cells bsegs m' NXT [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)]
    /\ rw_cells bsegs m' LST [C8 (Z_to_bv 64 (ls - 1)); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (if ll =? NXT then CUR else ll)); C8 (Z_to_bv 64 lb)]
    /\ rw_cells bsegs m' TMP [C8 (Z_to_bv 64 (tn + 1)); C8 (Z_to_bv 64 (if tfull then tf else NXT)); C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES))]
    /\ (if tfull then rw_cells bsegs m' TL [C8 (Z_to_bv 64 NXT)] else True).

Lemma munlink_spec : forall (tfull : bool) RNG ra sp gp tp t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem)
    (CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tl tb ex tlx : Z),
  mem_inv bsegs m ->
  rw_cells bsegs m CUR [C8 (Z_to_bv 64 NXT); C8 (Z_to_bv 64 szc); C8 (Z_to_bv 64 cc)] ->
  rw_cells bsegs m NXT [C8 (Z_to_bv 64 nxn); C8 (Z_to_bv 64 szn); C8 (Z_to_bv 64 cn)] ->
  rw_cells bsegs m LST [C8 (Z_to_bv 64 ls); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 ll); C8 (Z_to_bv 64 lb)] ->
  rw_cells bsegs m TMP [C8 (Z_to_bv 64 tn); C8 (Z_to_bv 64 tf); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 tb)] ->
  (if tfull then tl = TL else True) -> 0 <= tl < 2^64 ->
  0 < ls < 2^63 -> 0 <= ll < 2^64 -> 0 <= nxn < 2^64 -> 0 <= tn < 2^63 -> 0 <= tf < 2^64 -> 0 <= tb -> tb + Q_BATCH_BYTES < 2^63 ->
  0 <= ex -> ex + Q_BATCH_BYTES < 2^63 ->
  AIMG_HI <= CUR -> CUR + Q_BATCH_BYTES <= ATOP -> AIMG_HI <= NXT -> NXT + Q_BATCH_BYTES <= ATOP ->
  0 <= LST -> LST + 32 <= ATOP -> 0 <= TMP -> TMP + 32 <= 2^47 ->
  (CUR + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= CUR) ->
  (LST + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= LST) -> (LST + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= LST) ->
  (TMP + 32 <= CUR \/ CUR + Q_BATCH_BYTES <= TMP) -> (TMP + 32 <= NXT \/ NXT + Q_BATCH_BYTES <= TMP) ->
  (TMP + 32 <= LST \/ LST + 32 <= TMP) ->
  (if tfull then 0 < tn /\ rw_cells bsegs m TL [C8 (Z_to_bv 64 tlx)] /\ AIMG_HI <= TL /\ TL + Q_BATCH_BYTES <= ATOP
                 /\ (TL + Q_BATCH_BYTES <= CUR \/ CUR + Q_BATCH_BYTES <= TL) /\ (TL + Q_BATCH_BYTES <= NXT \/ NXT + Q_BATCH_BYTES <= TL)
                 /\ (LST + 32 <= TL \/ TL + Q_BATCH_BYTES <= LST) /\ (TMP + 32 <= TL \/ TL + Q_BATCH_BYTES <= TMP) /\ rng RNG TL 8
   else tn = 0) ->
  a7 = Z_to_bv 64 Q_BATCH_BYTES ->
  rng RNG CUR Q_BATCH_BYTES -> rng RNG NXT Q_BATCH_BYTES -> rng RNG LST 32 -> rng RNG TMP 32 ->
  evtF bsegs RNG (munlink_post tfull ra sp gp tp (Z_to_bv 64 NXT) s0 s1 (Z_to_bv 64 CUR) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                     CUR NXT LST TMP TL nxn szc cc szn cn ls lf ll lb tn tf tb ex m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 NXT) t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 ex) (Z_to_bv 64 ls) (Z_to_bv 64 CUR) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3593c) fc None m (seg_rom bsegs)).
Proof.
  intros until tlx. intros MI CC CN LS TM TLE TLR LSR LLR NXN TN TF TB TB2 EX EX2 C1 C2 N1 N2 L1 L2 T1 T2 DCN DLC DLN DTC DTN DTL TFULL -> RC RN RL RT.
  unfold AIMG_HI, Q_BATCH_BYTES in *.
  destruct tfull.
  - destruct TFULL as (TN1 & TLC & TL1 & TL2 & DTLC & DTLN & DTLL & DTLT & RTL). subst tl.
    pose proof (munch_refl ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ [(TL, TL + 8)])%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM. cbn [app] in MU.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.   (* [comment removed for export] *)
    step. step. step.                                     (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.                      (* [comment removed for export] *)
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      step. zstep. step. step. step.                      (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; lia]. clear KT.   (* [comment removed for export] *)
      step. step. zstep. step.                            (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact TLC].
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in KL by lia.
      zstep. step. step. step.                            (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|]. clear KT.   (* [comment removed for export] *)
      step. step. zstep. step.                            (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact TLC].
  - subst tn. clear TLE.
    pose proof (munch_refl ([(CUR, CUR + 8); (NXT, NXT + 8); (LST, LST + 24); (TMP, TMP + 32)] ++ [])%Z m) as MU.
    pose proof (wmono_refl bsegs m) as WM. cbn [app] in MU.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.   (* [comment removed for export] *)
    step. step. step.                                     (* [comment removed for export] *)
    step. if_cases KL; zify_cond KL.                      (* [comment removed for export] *)
    + rewrite ?unsigned_lit in KL by lia.
      step. zstep. step. step. step.                      (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|]. clear KT.   (* [comment removed for export] *)
      step. zstep.                                        (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with true by (symmetry; apply Z.eqb_eq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia. change (0 + 1) with 1.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact I].
    + rewrite ?unsigned_lit in KL by lia.
      zstep. step. step. step.                            (* [comment removed for export] *)
      step. if_cases KT; zify_cond KT; [| exfalso; rewrite ?unsigned_lit in KT by lia; lia]. clear KT.   (* [comment removed for export] *)
      step. zstep.                                        (* [comment removed for export] *)
      step. step. step. zstep. zstep. step.               (* [comment removed for export] *)
      apply evtF_done. unfold munlink_post. cbn [app].
      replace (ll =? NXT) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (ls + -1) with (ls - 1) in LS by lia. change (0 + 1) with 1.
      do 3 eexists. eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact CC|]. split; [exact CN|]. split; [exact LS|]. split; [exact TM| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bq := (abatch * qbatchc)%type.
Definition baddr (L : alayout) (x : bq) : Z := abatch_addr L (qb_slot (snd x)).
(* [comment removed for export] *)
Definition bq_merge (cur nx : bq) : bq :=
  (mkABatch (b_count (fst cur) + b_count (fst nx)) (b_size (fst cur) + (b_size (fst nx) - Q_BATCH_BYTES)) (b_chunks (fst nx) ++ b_chunks (fst cur)),
   mkQB (qb_slot (snd cur)) (qb_ks (snd nx) ++ qb_ks (snd cur))).
Definition bq_empty (nx : bq) : bq := (mkABatch 0 Q_BATCH_BYTES [], mkQB (qb_slot (snd nx)) []).

Fixpoint merge_bq (cur : bq) (rest : list bq) {struct rest} : list bq * list bq :=
  match rest with
  | [] => ([cur], [])
  | nx :: rest' =>
      if b_count (fst cur) + b_count (fst nx) <=? Q_BATCH then
        let '(l, ex) := merge_bq (bq_merge cur nx) rest' in (l, bq_empty nx :: ex)
      else
        let '(l, ex) := merge_bq nx rest' in (cur :: l, ex)
  end.

Lemma merge_bq_fst : forall rest cur,
  let '(l, ex, exb) := merge_batches (fst cur) (map fst rest) in
  map fst (fst (merge_bq cur rest)) = l /\ map fst (snd (merge_bq cur rest)) = ex /\ exb = Q_BATCH_BYTES * Z.of_nat (length (snd (merge_bq cur rest))).
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn [merge_batches merge_bq map fst snd length].
  - cbn. repeat split; reflexivity.
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH) eqn:E.
    + specialize (IH (bq_merge cur nx)). cbn [bq_merge fst] in IH.
      destruct (merge_batches _ (map fst rest)) as [[l ex] exb]. destruct (merge_bq _ rest) as [l2 ex2]. cbn [fst snd map length] in *.
      destruct IH as (A & B & C). rewrite A, B. repeat split; try reflexivity. lia.
    + specialize (IH nx). destruct (merge_batches (fst nx) (map fst rest)) as [[l ex] exb]. destruct (merge_bq nx rest) as [l2 ex2].
      cbn [fst snd map length] in *. destruct IH as (A & B & C). rewrite A, B. repeat split; try reflexivity. exact C.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tfirst (L : alayout) (T : list bq) (tf0 : Z) : Z := match T with [] => tf0 | x :: _ => baddr L x end.
Definition tlast (L : alayout) (T : list bq) (tl0 : Z) : Z := List.last (map (baddr L) T) tl0.

Lemma tlast_app1 : forall L T x tl0, tlast L (T ++ [x]) tl0 = baddr L x.
Proof. intros. unfold tlast. rewrite map_app. cbn. rewrite last_last. reflexivity. Qed.
Lemma tfirst_app : forall L T U tf0, T <> [] -> tfirst L (T ++ U) tf0 = tfirst L T tf0.
Proof. intros L [|x T] U tf0 H; [congruence| reflexivity]. Qed.
Lemma tlast_cons_ne : forall L x T tl0, T <> [] -> tlast L (x :: T) tl0 = tlast L T tl0.
Proof. intros L x [|y T] tl0 H; [congruence|]. unfold tlast. cbn [map]. destruct (map (baddr L) T); reflexivity. Qed.

Lemma merge_bq_ne : forall rest cur, fst (merge_bq cur rest) <> [].
Proof.
  induction rest as [|nx rest IH]; intros cur; cbn; [congruence|].
  destruct (_ <=? _); [specialize (IH (bq_merge cur nx)); destruct (merge_bq _ rest) | specialize (IH nx); destruct (merge_bq nx rest)]; cbn in *; congruence.
Qed.
Lemma merge_bq_first : forall L rest cur tf0, tfirst L (fst (merge_bq cur rest)) tf0 = baddr L cur.
Proof.
  induction rest as [|nx rest IH]; intros cur tf0; cbn; [reflexivity|].
  destruct (_ <=? _).
  - specialize (IH (bq_merge cur nx) tf0). destruct (merge_bq _ rest). cbn in *. rewrite IH. reflexivity.
  - destruct (merge_bq nx rest). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bgeom (L : alayout) (LST TMP : Z) (x : bq) : Prop :=
  AIMG_HI <= baddr L x /\ baddr L x + Q_BATCH_BYTES <= ATOP
  /\ (LST + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= LST)
  /\ (TMP + 32 <= baddr L x \/ baddr L x + Q_BATCH_BYTES <= TMP).

Lemma baddr_disj : forall L x y, qb_slot (snd x) <> qb_slot (snd y) -> 0 <= qb_slot (snd x) -> 0 <= qb_slot (snd y) ->
  baddr L x + Q_BATCH_BYTES <= baddr L y \/ baddr L y + Q_BATCH_BYTES <= baddr L x.
Proof.
  intros L x y NE X Y. unfold baddr, abatch_addr, aslot_addr, Q_BATCH_BYTES. rewrite size_of_class_24.
  destruct (Z.lt_ge_cases (qb_slot (snd x)) (qb_slot (snd y))); [left| right]; nia.
Qed.

Section Loop.
  Variables (L : alayout) (RNG : footprint) (LST TMP lf lb tf0 tl0 : Z).
  Variables (ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).

  Definition chain (m : amem) (X : list bq) (nxt : Z) : Prop := abatches_to L m (map fst X) (map snd X) nxt.

  Definition mloop_post (P : list bq) (cur : bq) (R T : list bq) (tb ex : Z) (m : amem) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a3 a4 t3 t4 t5 m',
      let '(l, e) := merge_bq cur R in
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 (ex + Q_BATCH_BYTES * Z.of_nat (length e))) a3 a4
                   (Z_to_bv 64 Q_BATCH) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x359b4) fc None m' (seg_rom bsegs)
      /\ munch ([(LST, LST + 24); (TMP, TMP + 32)] ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (cur :: R ++ T))%Z m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' LST [C8 (Z_to_bv 64 (Z.of_nat (length (P ++ l)))); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (tlast L l 0)); C8 (Z_to_bv 64 lb)]
      /\ chain m' (P ++ l) 0
      /\ rw_cells bsegs m' TMP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ e)))); C8 (Z_to_bv 64 (tfirst L (T ++ e) tf0));
                               C8 (Z_to_bv 64 (tlast L (T ++ e) tl0)); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES * Z.of_nat (length e)))]
      /\ chain m' (T ++ e) 0.

(* [comment removed for export] *)
  Lemma hd_qaddrs : forall X nxt, hd nxt (qaddrs L (map snd X)) = tfirst L X nxt.
  Proof. intros [|x X] nxt; reflexivity. Qed.

  Lemma chain_app : forall m X Y nxt, chain m (X ++ Y) nxt <-> chain m X (tfirst L Y nxt) /\ chain m Y nxt.
  Proof.
    intros. unfold chain. rewrite !map_app. rewrite abatches_to_app by (rewrite !length_map; reflexivity).
    rewrite <- (hd_qaddrs Y nxt). tauto.
  Qed.
  Lemma chain_cons : forall m x Y nxt, chain m (x :: Y) nxt <-> abatch_cells L m (fst x) (snd x) (tfirst L Y nxt) /\ chain m Y nxt.
  Proof. intros. unfold chain. cbn [map abatches_to]. rewrite <- (hd_qaddrs Y nxt). tauto. Qed.
  Lemma chain_nil : forall m nxt, chain m [] nxt.
  Proof. intros. exact I. Qed.

  Lemma tfirst_pos : forall X nxt, Forall (bgeom L LST TMP) X -> X <> [] -> AIMG_HI <= tfirst L X nxt.
  Proof. intros [|x X] nxt HF NE; [congruence|]. cbn. inversion HF; subst. destruct H1 as (A & _). exact A. Qed.

  Lemma chain_frame : forall W m m' X nxt, chain m X nxt -> munch W m m' -> wmono bsegs m m' ->
    Forall (fun x => disjoint_from W (baddr L x) Q_BATCH_BYTES) X -> chain m' X nxt.
  Proof.
    intros W m m' X nxt CH MU WM HF. unfold chain in *. eapply abatches_to_frame; [exact MU| exact WM| exact CH|].
    intros q Hq. apply in_map_iff in Hq. destruct Hq as (x & <- & Hx). exact (proj1 (Forall_forall _ _) HF x Hx).
  Qed.

  (* [comment removed for export] *)
  Definition abatch_rest (m : amem) (b : abatch) (q : qbatchc) : Prop :=
    let B := abatch_addr L (qb_slot q) in
       rw_cells bsegs m (B + 8) [C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]
    /\ u64arr bsegs m (B + 24) (map (Z_to_bv 64) (qhdrs L (b_chunks b) (qb_ks q)))
    /\ junk_at m (B + 24 + 8 * b_count b) (Q_BATCH_BYTES - 24 - 8 * b_count b)
    /\ b_count b = Z.of_nat (length (b_chunks b)) /\ length (qb_ks q) = length (b_chunks b)
    /\ 0 <= b_count b <= Q_BATCH.
  Lemma abatch_cells_split : forall m b q nx,
    abatch_cells L m b q nx <-> rw_cells bsegs m (abatch_addr L (qb_slot q)) [C8 (Z_to_bv 64 nx)] /\ abatch_rest m b q.
  Proof.
    intros. unfold abatch_cells, abatch_rest. cbv zeta.
    rewrite (rw_cells_app bsegs m (abatch_addr L (qb_slot q)) [C8 (Z_to_bv 64 nx)] [C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]).
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. tauto.
  Qed.

  Lemma qhdrs_app : forall (a b : list achunk) (ka kb : list Z), length ka = length a ->
    qhdrs L (a ++ b) (ka ++ kb) = qhdrs L b kb ++ qhdrs L a ka.
  Proof.
    induction a as [|x a IH]; intros b [|k ka] kb LEN; cbn in *; try lia.
    - rewrite app_nil_r. reflexivity.
    - rewrite IH by lia. rewrite app_assoc. reflexivity.
  Qed.

(* [comment removed for export] *)

  Lemma nodup_mid : forall (f : bq -> Z) l1 a l2, NoDup (map f (l1 ++ a :: l2)) -> forall x, In x (l1 ++ l2) -> f x <> f a.
  Proof.
    intros f l1 a l2 ND x Hx E. rewrite map_app in ND. cbn [map] in ND.
    destruct (proj1 (list_relations.list.NoDup_app _ _) ND) as (_ & NI & ND2).
    destruct (proj1 (list_relations.list.NoDup_cons _ _) ND2) as [NA _].
    apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
    - refine (NI (f x) _ _). { apply list_elem_of_In. apply in_map. exact Hx. } rewrite E. left.
    - apply NA. rewrite <- E. apply list_elem_of_In. apply in_map. exact Hx.
  Qed.

  Lemma tlast_in : forall X d, X <> [] -> exists x, In x X /\ tlast L X d = baddr L x.
  Proof.
    induction X as [|x X IH]; intros d NE; [congruence|]. destruct X as [|y X'].
    - exists x. split; [left; reflexivity| reflexivity].
    - destruct (IH d ltac:(congruence)) as (z & Hz & E). exists z. split; [right; exact Hz|]. rewrite tlast_cons_ne by congruence. exact E.
  Qed.
  Lemma tfirst_in : forall X d, X <> [] -> exists x, In x X /\ tfirst L X d = baddr L x.
  Proof. intros [|x X] d NE; [congruence|]. exists x. split; [left; reflexivity| reflexivity]. Qed.

  Lemma bq_eq_dec : forall x y : bq, {x = y} + {x <> y}.
  Proof. intros. repeat (decide equality). Qed.

  Lemma sub_fp_incl : forall W W', (forall iv, In iv W -> In iv W') -> sub_fp W W'.
  Proof.
    intros W W' H. apply sub_fp_by_incl'. apply Forall_forall. intros iv Hiv. apply Exists_exists. exists iv. split; [apply H; exact Hiv| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Hypothesis A6 : a6 = Z_to_bv 64 (2^64 - Q_BATCH_BYTES).
  Hypothesis A7 : a7 = Z_to_bv 64 Q_BATCH_BYTES.
  Hypothesis L1 : 0 <= LST. Hypothesis L2 : LST + 32 <= ATOP.
  Hypothesis T1 : 0 <= TMP. Hypothesis T2 : TMP + 32 <= 2^47.
  Hypothesis DTL : TMP + 32 <= LST \/ LST + 32 <= TMP.
  Hypothesis RL : rng RNG LST 32. Hypothesis RT : rng RNG TMP 32.
  Hypothesis TF0 : 0 <= tf0 < 2^64. Hypothesis TL0 : 0 <= tl0 < 2^64. Hypothesis LF : 0 <= lf < 2^64. Hypothesis LB : 0 <= lb < 2^64.

  Lemma mloop_spec : forall (d : nat) (P : list bq) (cur : bq) (R T : list bq) (tb ex : Z) (t1 t2 a3 t3 t4 t5 : word) (m : amem),
    d = length R -> R <> [] ->
    mem_inv bsegs m ->
    rw_cells bsegs m LST [C8 (Z_to_bv 64 (Z.of_nat (length (P ++ cur :: R)))); C8 (Z_to_bv 64 lf); C8 (Z_to_bv 64 (tlast L (cur :: R) 0)); C8 (Z_to_bv 64 lb)] ->
    chain m (P ++ cur :: R) 0 ->
    rw_cells bsegs m TMP [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T tf0)); C8 (Z_to_bv 64 (tlast L T tl0)); C8 (Z_to_bv 64 tb)] ->
    chain m T 0 ->
    Forall (bgeom L LST TMP) (P ++ cur :: R ++ T) -> Forall (fun x => 0 <= qb_slot (snd x)) (P ++ cur :: R ++ T) ->
    NoDup (map (fun x => qb_slot (snd x)) (P ++ cur :: R ++ T)) ->
    Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) (cur :: R) -> batches_bytes (map fst (cur :: R)) < 2^62 ->
    Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (cur :: R ++ T) ->
    0 <= tb -> tb + Q_BATCH_BYTES * (Z.of_nat (length R) + 1) < 2^62 -> 0 <= ex -> ex + Q_BATCH_BYTES * (Z.of_nat (length R) + 1) < 2^62 ->
    Z.of_nat (length (P ++ cur :: R ++ T)) < 2^40 ->
    evtF bsegs RNG (mloop_post P cur R T tb ex m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (baddr L (hd cur R))) t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) (Z_to_bv 64 ex) a3 (Z_to_bv 64 (baddr L cur))
               (Z_to_bv 64 Q_BATCH) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 amerge_loop) fc None m (seg_rom bsegs)).
  Proof using A6 A7 L1 L2 T1 T2 DTL RL RT TF0 TL0 LF LB.   (* [comment removed for export] *)
    induction d as [|d IH]; intros until m; intros HD RNE MI LS CH TM CT GEO SL ND SZ SZS RB TB0 TB1 EX0 EX1 LEN40.
    { exfalso. destruct R; [congruence| cbn in HD; lia]. }
    destruct R as [|nx R']; [congruence|]. cbn [hd].
    pose proof CH as CH0.
    destruct (proj1 (chain_app _ _ _ _) CH) as [CHP CHR]. clear CH.
    destruct (proj1 (chain_cons _ _ _ _) CHR) as [BC CHR1]. clear CHR. destruct (proj1 (chain_cons _ _ _ _) CHR1) as [BN CHR']. clear CHR1.
    destruct BC as (CC & EC & JC & CCNT & CLEN & CRNG). destruct BN as (CN & EN & JN & NCNT & NLEN & NRNG).
    assert (GC : bgeom L LST TMP cur) by (eapply (proj1 (Forall_forall _ _) GEO); apply in_app_iff; right; left; reflexivity).
    assert (GN : bgeom L LST TMP nx) by (eapply (proj1 (Forall_forall _ _) GEO); apply in_app_iff; right; right; left; reflexivity).
    assert (RC : rng RNG (baddr L cur) Q_BATCH_BYTES) by (pose proof (Forall_inv RB) as X; exact X).
    assert (RN : rng RNG (baddr L nx) Q_BATCH_BYTES) by (pose proof (Forall_inv (Forall_inv_tail RB)) as X; exact X).
    assert (DCN : baddr L cur + Q_BATCH_BYTES <= baddr L nx \/ baddr L nx + Q_BATCH_BYTES <= baddr L cur).
    { apply (baddr_disj L cur nx).
      - intros E. rewrite map_app in ND. cbn [map] in ND. destruct (proj1 (list_relations.list.NoDup_app _ _) ND) as (_ & _ & ND2).
        destruct (proj1 (list_relations.list.NoDup_cons _ _) ND2) as [NI _]. apply NI. rewrite E. left.
      - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff; right; left; reflexivity.
      - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff; right; right; left; reflexivity. }
    pose proof (Forall_inv SZ) as SZC. pose proof (Forall_inv (Forall_inv_tail SZ)) as SZN. cbn beta in SZC, SZN.
    cbn [map] in SZS. rewrite !batches_bytes_cons in SZS.
    pose proof (batches_bytes_lb (map fst R') ltac:(rewrite Forall_map; exact (Forall_inv_tail (Forall_inv_tail SZ)))) as SZR.
    unfold bgeom, amerge_loop, AIMG_HI, Q_BATCH_BYTES, Q_BATCH in GC, GN, RC, RN, DCN, CC, EC, JC, CN, EN, JN, CRNG, NRNG, SZC, SZN, L2 |- *.
    unfold baddr in GC, GN, RC, RN, DCN, CC, CN |- *. cbn [fst snd tfirst baddr] in GC, GN, RC, RN, DCN, CC, EC, JC, CN, EN, JN, CCNT, CLEN, CRNG, NCNT, NLEN, NRNG, SZC, SZN |- *.
    set (CUR := abatch_addr L (qb_slot (snd cur))) in *. set (NXT := abatch_addr L (qb_slot (snd nx))) in *.
    destruct GC as (GC1 & GC2 & GC3 & GC4). destruct GN as (GN1 & GN2 & GN3 & GN4).
    unfold baddr in CC. cbn [fst snd] in CC. fold NXT in CC.
    (* [comment removed for export] *)
    step. step. zstep.                                    (* [comment removed for export] *)
    step. if_cases KF; zify_cond KF.                      (* [comment removed for export] *)
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KF by lia.
      zstep.                                              (* [comment removed for export] *)
      step.                                               (* [comment removed for export] *)
      step. if_cases KE; zify_cond KE.                    (* [comment removed for export] *)
      + (* [comment removed for export] *)
        assert (GR : Forall (bgeom L LST TMP) R').
        { apply Forall_app in GEO. destruct GEO as [_ G2]. do 2 apply Forall_inv_tail in G2. apply Forall_app in G2. destruct G2 as [G2 _]. exact G2. }
        assert (RNIL : R' = []).
        { destruct R' as [|r R'']; [reflexivity| exfalso].
          pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KE.
          pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. destruct Y as (Y1 & Y & Y3).
          rewrite Z.mod_small in KE by (clear -X Y; lia). clear -X KE. lia. }
        subst R'. clear GR KE.
        assert (MB : merge_bq cur [nx] = ([cur; nx], [])).
        { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [exfalso; clear -KF l; lia| reflexivity]. }
        apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat app Pos.of_succ_nat].
        rewrite !app_nil_r, Z.mul_0_r, !Z.add_0_r.
        do 8 eexists. exists m. split; [reflexivity|].
        split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
        split. { replace (length (P ++ [cur; nx])) with (length (P ++ cur :: nx :: [])) by reflexivity. exact LS. }
        split; [exact CH0|]. split; [exact TM| exact CT].
      + (* [comment removed for export] *)
        assert (RNE' : R' <> []) by (intros ->; cbn in KE; rewrite ?unsigned_lit in KE by lia; lia).
        assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
        rewrite TFE.
        eapply evtF_mono.
        { eapply (IH (P ++ [cur]) nx R' T tb ex); try eassumption.
          - cbn in HD. lia.
          - rewrite <- app_assoc. cbn [app]. rewrite tlast_cons_ne in LS by congruence. exact LS.
          - rewrite <- app_assoc. cbn [app]. exact CH0.
          - rewrite <- app_assoc. cbn [app]. exact GEO.
          - rewrite <- app_assoc. cbn [app]. exact SL.
          - rewrite <- app_assoc. cbn [app]. exact ND.
          - exact (Forall_inv_tail SZ).
          - cbn [map]. rewrite batches_bytes_cons. clear -SZS SZC. lia.
          - exact (Forall_inv_tail RB).
          - revert TB1. clear. cbn [length]. unfold Q_BATCH_BYTES. intros. lia.
          - revert EX1. clear. cbn [length]. unfold Q_BATCH_BYTES. intros. lia.
          - rewrite <- app_assoc. cbn [app]. exact LEN40. }
        cbv beta. unfold mloop_post. intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & POST).
        assert (MB : merge_bq cur (nx :: R') = (cur :: fst (merge_bq nx R'), snd (merge_bq nx R'))).
        { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [exfalso; clear -KF l; lia|].
          destruct (merge_bq nx R'); reflexivity. }
        rewrite MB. destruct (merge_bq nx R') as [l' e'] eqn:MB'. cbn [fst snd].
        destruct POST as (-> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
        do 8 eexists. exists m'. split; [reflexivity|].
        split. { eapply munch_weaken; [| exact MU']. intros x Hx. revert Hx. cbn [map app]. unfold outside. cbn. clear. tauto. }   (* [comment removed for export] *)
        split; [exact WM'|]. split; [exact MI'|].
        split. { rewrite <- app_assoc in LS'. cbn [app] in LS'. rewrite tlast_cons_ne by (pose proof (merge_bq_ne R' nx) as NE; rewrite MB' in NE; exact NE). exact LS'. }
        split. { rewrite <- app_assoc in CH'. exact CH'. }
        split; [exact TM'| exact CT'].
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in KF by lia.
      assert (GR : Forall (bgeom L LST TMP) R').
      { pose proof GEO as G. apply Forall_app in G. destruct G as [_ G2]. do 2 apply Forall_inv_tail in G2. apply Forall_app in G2. destruct G2 as [G2 _]. exact G2. }
      assert (NXN : 0 <= tfirst L R' 0 < 2^64).
      { destruct R' as [|r R'']; [cbn; lia|]. pose proof (Forall_inv GR) as Y. unfold bgeom, AIMG_HI, Q_BATCH_BYTES in Y. cbn [tfirst]. clear -Y. lia. }
      assert (LEC : length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst cur)) (qb_ks (snd cur)))) = Z.to_nat (b_count (fst cur)))
        by (rewrite length_map, qhdrs_length by exact CLEN; lia).
      assert (LEN : length (map (Z_to_bv 64) (qhdrs L (b_chunks (fst nx)) (qb_ks (snd nx)))) = Z.to_nat (b_count (fst nx)))
        by (rewrite length_map, qhdrs_length by exact NLEN; lia).
      eapply evtF_cut.
      { eapply (mcore_spec RNG) with (LST := LST) (CUR := CUR) (NXT := NXT); try reflexivity.
        all: try eassumption.
        all: clear -SZC SZN SZS SZR CRNG NRNG KF NXN LEN40 GC1 GC2 GC3 GC4 GN1 GN2 GN3 GN4 DCN L1 L2; unfold Q_BATCH, Q_BATCH_BYTES in *.
        all: try lia.
        revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
      cbv beta. intros ms1 (y2 & y3 & y4 & y5 & m1 & -> & MUc & WMc & MI1 & CC1 & EC1 & JC1 & CN1 & JN1). clear MI.
      unfold Q_BATCH_BYTES in CC1, JC1, CN1, JN1.
      (* [comment removed for export] *)
      assert (OTH : forall x, In x (P ++ R' ++ T) ->
                (baddr L x + 8192 <= CUR \/ CUR + 8192 <= baddr L x) /\ (baddr L x + 8192 <= NXT \/ NXT + 8192 <= baddr L x)
                /\ bgeom L LST TMP x /\ 0 <= qb_slot (snd x)).
      { intros x Hx.
        assert (INA : In x (P ++ cur :: (nx :: R') ++ T)).
        { apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right]. cbn [app]. right. exact Hx. }
        pose proof (proj1 (Forall_forall _ _) SL x INA) as SX. pose proof (proj1 (Forall_forall _ _) GEO x INA) as GX. cbv beta in SX.
        assert (SC : 0 <= qb_slot (snd cur)) by (eapply (proj1 (Forall_forall _ _) SL); apply in_app_iff; right; left; reflexivity).
        assert (SN : 0 <= qb_slot (snd nx)) by (eapply (proj1 (Forall_forall _ _) SL); apply in_app_iff; right; right; left; reflexivity).
        assert (N1 : qb_slot (snd x) <> qb_slot (snd cur)).
        { apply (nodup_mid (fun x => qb_slot (snd x)) P cur ((nx :: R') ++ T) ND x).
          apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; cbn [app]; right; exact Hx]. }
        assert (N2 : qb_slot (snd x) <> qb_slot (snd nx)).
        { apply (nodup_mid (fun x => qb_slot (snd x)) (P ++ [cur]) nx (R' ++ T)); [rewrite <- app_assoc; exact ND|].
          apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; apply in_app_iff; left; exact Hx| right; exact Hx]. }
        pose proof (baddr_disj L x cur N1 SX SC) as D1. pose proof (baddr_disj L x nx N2 SX SN) as D2.
        unfold baddr, Q_BATCH_BYTES in D1, D2 |- *. cbn [snd] in D1, D2. fold CUR in D1. fold NXT in D2. clear -D1 D2 GX SX; tauto. }   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (DJc : forall x, In x (P ++ R' ++ T) ->
        disjoint_from [(CUR + 8, CUR + 24); (CUR + 24 + 8 * b_count (fst cur), CUR + 24 + 8 * (b_count (fst cur) + b_count (fst nx))); (NXT + 8, NXT + 24)]%Z (baddr L x) 8192).
      { intros x Hx. destruct (OTH x Hx) as (D1 & D2 & _). cbn. clear -D1 D2 CRNG NRNG KF. lia. }
      xport LS MUc WMc ltac:(clear -GC3 GN3 CRNG NRNG KF; lia).
      xport TM MUc WMc ltac:(clear -GC4 GN4 CRNG NRNG KF; lia).
      assert (CHP1 : chain m1 P CUR).
      { eapply chain_frame; [exact CHP| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. left. exact Hx. }
      assert (CHR1 : chain m1 R' 0).
      { eapply chain_frame; [exact CHR'| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. right. apply in_app_iff. left. exact Hx. }
      assert (CT1 : chain m1 T 0).
      { eapply chain_frame; [exact CT| exact MUc| exact WMc|]. apply Forall_forall. intros x Hx. apply DJc. apply in_app_iff. right. apply in_app_iff. right. exact Hx. }
      clear CHP CHR' CT DJc.
      (* [comment removed for export] *)
      assert (GB : forall x, In x (P ++ cur :: (nx :: R') ++ T) -> 6443008 <= baddr L x /\ baddr L x + 8192 <= ATOP
                                                            /\ (LST + 32 <= baddr L x \/ baddr L x + 8192 <= LST) /\ (TMP + 32 <= baddr L x \/ baddr L x + 8192 <= TMP)).
      { intros x Hx. pose proof (proj1 (Forall_forall _ _) GEO x Hx) as G. unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. exact G. }
      assert (LLR : 0 <= tlast L (cur :: nx :: R') 0 < 2^64).
      { destruct (tlast_in (cur :: nx :: R') 0 ltac:(congruence)) as (z & Hz & ->).
        assert (INz : In z (P ++ cur :: (nx :: R') ++ T)).
        { apply in_app_iff. right. destruct Hz as [<-|[<-|Hz]]; [left; reflexivity| right; left; reflexivity| right; right; apply in_app_iff; left; exact Hz]. }
        destruct (GB z INz) as (B1 & B2 & _). clear -B1 B2. lia. }
      assert (TFR : 0 <= tfirst L T tf0 < 2^64 /\ 0 <= tlast L T tl0 < 2^64).
      { destruct T as [|t T']; [cbn; clear -TF0 TL0; lia|].
        destruct (tfirst_in (t :: T') tf0 ltac:(congruence)) as (z1 & Hz1 & ->). destruct (tlast_in (t :: T') tl0 ltac:(congruence)) as (z2 & Hz2 & ->).
        destruct (GB z1 ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hz1)) as (B1 & B2 & _).
        destruct (GB z2 ltac:(apply in_app_iff; right; right; apply in_app_iff; right; exact Hz2)) as (B3 & B4 & _). clear -B1 B2 B3 B4. lia. }
      assert (LSP : 0 < Z.of_nat (length (P ++ cur :: nx :: R')) < 2^63).
      { revert LEN40. clear. rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. intros. lia. }
      (* [comment removed for export] *)
      destruct (list_eq_dec bq_eq_dec T []) as [TNIL|TNE].
      + (* [comment removed for export] *) subst T.
        eapply evtF_cut.
        { eapply (munlink_spec false RNG) with (CUR := CUR) (NXT := NXT) (LST := LST) (TMP := TMP) (TL := 0) (tlx := 0)
            (nxn := tfirst L R' 0) (szc := b_size (fst cur) + b_size (fst nx) - 8192) (cc := b_count (fst cur) + b_count (fst nx))
            (szn := 8192) (cn := 0) (ls := Z.of_nat (length (P ++ cur :: nx :: R'))) (lf := lf) (ll := tlast L (cur :: nx :: R') 0) (lb := lb)
            (tn := 0) (tf := tf0) (tl := tl0) (tb := tb) (ex := ex);
            try reflexivity; try eassumption; try exact I.
          all: unfold Q_BATCH_BYTES; revert TB0 TB1 EX0 EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia. }
        cbv beta. intros ms2 (z1 & z2 & z3 & m2 & -> & MUu & WMu & MI2 & CC2 & CN2 & LS2 & TM2 & _). cbn [app] in MUu. clear MI1.
        step.                                             (* [comment removed for export] *)
        step. if_cases KX; zify_cond KX.                  (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (RNE' : R' <> []) by (intros ->; cbn in KX; rewrite ?unsigned_lit in KX by lia; lia).
          assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
          assert (MB : merge_bq cur (nx :: R') = (fst (merge_bq (bq_merge cur nx) R'), bq_empty nx :: snd (merge_bq (bq_merge cur nx) R'))).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [| exfalso; clear -KF n; lia].
            destruct (merge_bq (bq_merge cur nx) R'); reflexivity. }
          (* [comment removed for export] *)
          xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4; lia).
          assert (CHP2 : chain m2 P CUR).
          { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            destruct (OTH x ltac:(apply in_app_iff; left; exact Hx)) as (D1 & D2 & (G1 & G2 & G3 & G4) & _). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          assert (CHR2 : chain m2 R' 0).
          { eapply chain_frame; [exact CHR1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            destruct (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) as (D1 & D2 & (G1 & G2 & G3 & G4) & _). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          (* [comment removed for export] *)
          assert (LLN : (tlast L (cur :: nx :: R') 0 =? NXT) = false).
          { apply Z.eqb_neq. rewrite 2!tlast_cons_ne by congruence. destruct (tlast_in R' 0 RNE') as (z & Hz & ->).
            destruct (OTH z ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hz)) as (_ & D2 & _). clear -D2. lia. }
          rewrite LLN in LS2. rewrite TFE.
          replace (baddr L (hd nx R')) with (baddr L (hd (bq_merge cur nx) R')) by (destruct R'; [congruence| reflexivity]).
          setreg 14 (Z_to_bv 64 (baddr L (bq_merge cur nx))) ltac:(unfold baddr; cbn [bq_merge snd qb_slot]; reflexivity).
          unfold Q_BATCH_BYTES.
          eapply evtF_mono.
          { eapply (IH P (bq_merge cur nx) R' [bq_empty nx] (tb + 8192) (ex + 8192)).
            - cbn in HD. clear -HD. lia.
            - exact RNE'.
            - exact MI2.
            - (* [comment removed for export] *) rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
              replace (Z.of_nat (length P + S (S (length R'))) - 1) with (Z.of_nat (length P + S (length R'))) in LS2 by lia.
              rewrite tlast_cons_ne by exact RNE'. rewrite 2!tlast_cons_ne in LS2 by congruence. exact LS2.
            - (* [comment removed for export] *) apply (proj2 (chain_app _ _ _ _)). cbn [tfirst]. unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. split; [exact CHP2|].
              apply (proj2 (chain_cons _ _ _ _)). split; [| exact CHR2].
              unfold abatch_cells. cbn [fst snd bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
              replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
              split; [exact CC2|]. split; [rewrite qhdrs_app, map_app by exact NLEN; exact EC1|].
              split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia.
            - (* [comment removed for export] *) cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last]. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
              unfold Q_BATCH_BYTES. replace (0 + 1) with 1 in TM2 by lia. exact TM2.
            - (* [comment removed for export] *) apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
              unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
              split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
              split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia.
            - (* [comment removed for export] *) apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]].
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. left. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_merge snd qb_slot]. fold CUR. clear -GC1 GC2 GC3 GC4. tauto.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_empty snd qb_slot]. fold NXT. clear -GN1 GN2 GN3 GN4. tauto.
            - (* [comment removed for export] *) apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]].
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. left. exact Hx.
              + cbn [bq_merge snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. left. reflexivity.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + cbn [bq_empty snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. left. reflexivity.
            - (* [comment removed for export] *) rewrite app_nil_r in ND. revert ND. rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map bq_merge bq_empty snd qb_slot app].
              intros ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
              apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append.
            - (* [comment removed for export] *) constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZ))]. cbn [fst bq_merge b_size]. unfold Q_BATCH_BYTES in *. clear -SZC SZN. lia.
            - cbn [map fst bq_merge b_size]. rewrite batches_bytes_cons. cbn [b_size]. clear -SZS SZC SZN. unfold Q_BATCH_BYTES in *. lia.
            - (* [comment removed for export] *) rewrite app_nil_r in RB. constructor; [unfold baddr; cbn [bq_merge snd qb_slot]; fold CUR; exact RC|]. apply Forall_app. split; [exact (Forall_inv_tail (Forall_inv_tail RB))|].
              constructor; [unfold baddr; cbn [bq_empty snd qb_slot]; fold NXT; exact RN| constructor].
            - clear -TB0; lia.
            - revert TB1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - clear -EX0; lia.
            - revert EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
          cbv beta. unfold mloop_post. rewrite MB. destruct (merge_bq (bq_merge cur nx) R') as [l' e']. cbn [fst snd].
          intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
          cbn [length app] in TM' |- *. unfold Q_BATCH_BYTES in TM' |- *.
          replace (ex + 8192 * Z.of_nat (S (length e'))) with (ex + 8192 + 8192 * Z.of_nat (length e')) by lia.
          replace (tb + 8192 * Z.of_nat (S (length e'))) with (tb + 8192 + 8192 * Z.of_nat (length e')) by lia.
          do 8 eexists. exists m'. split; [reflexivity|].
          split. { (* [comment removed for export] *)
            unfold baddr. cbn [map app snd bq_merge bq_empty qb_slot] in MU' |- *. fold CUR in MU' |- *. fold NXT in MU' |- *.
            lazymatch goal with |- munch ?W _ _ =>
              assert (MU12 : munch W m m2) by (eapply (munch_trans_w _ _ _ _ _ _ MUc MUu); solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia));
              eapply (munch_trans_w _ _ _ _ _ _ MU12 MU'); apply sub_fp_incl; [intros iv Hiv; exact Hiv|] end.
            intros iv Hiv. cbn [In app] in Hiv |- *. rewrite app_nil_r. rewrite map_app in Hiv. cbn [map] in Hiv.
            destruct Hiv as [H|[H|[H|H]]]; [first [clear -H; tauto | tauto]| first [clear -H; tauto | tauto]| first [clear -H; tauto | tauto]|]. apply in_app_iff in H. destruct H as [H|[H|[]]]; [right; right; right; right; exact H| first [clear -H; tauto | tauto]]. }   (* [comment removed for export] *)
          split; [eapply wmono_trans; [exact WMc| eapply wmono_trans; [exact WMu| exact WM']]|]. split; [exact MI'|].
          split; [exact LS'|]. split; [exact CH'|]. split; [exact TM'| exact CT'].
        * (* [comment removed for export] *)
          assert (RNIL : R' = []).
          { destruct R' as [|r R'']; [reflexivity| exfalso].
            pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KX.
            pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. destruct Y as (Y1 & Y & Y3).
            rewrite ?unsigned_lit in KX by (clear -X Y; lia). clear -X KX. lia. }
          subst R'. clear GR KX.
          assert (MB : merge_bq cur [nx] = ([bq_merge cur nx], [bq_empty nx])).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [reflexivity| exfalso; clear -KF n; lia]. }
          (* [comment removed for export] *)
          xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4; lia).
          destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4; lia).
          assert (CHP2 : chain m2 P CUR).
          { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
            destruct (OTH x ltac:(apply in_app_iff; left; exact Hx)) as (D1 & D2 & (G1 & G2 & G3 & G4) & _). unfold Q_BATCH_BYTES in *. cbn. clear -D1 D2 G3 G4. lia. }
          apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat app Pos.of_succ_nat Pos.to_nat].
          rewrite !Z.mul_1_r.
          do 8 eexists. exists m2. split; [reflexivity|].
          split. { cbn [map app]. unfold baddr, Q_BATCH_BYTES. cbn [snd]. fold CUR. fold NXT. eapply (munch_trans_w _ _ _ _ _ _ MUc MUu); solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia). }
          split; [eapply wmono_trans; [exact WMc| exact WMu]|]. split; [exact MI2|].
          split. { rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
                   replace (Z.of_nat (length P + 2) - 1) with (Z.of_nat (length P + 1)) in LS2 by lia.
                   cbn [tlast map List.last] in LS2. rewrite Z.eqb_refl in LS2. exact LS2. }
          split. { apply (proj2 (chain_app _ _ _ _)). split; [exact CHP2|]. apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
                   unfold abatch_cells. cbn [fst snd tfirst bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
                   cbn [tfirst] in CC2. replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
                   split; [exact CC2|]. split.
                   - rewrite qhdrs_app, map_app by exact NLEN. exact EC1.
                   - split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia. }
          split. { unfold Q_BATCH_BYTES. replace (0 + 1) with 1 in TM2 by lia. exact TM2. }
          apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
          unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
          split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
          split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia.
      + (* [comment removed for export] *)
        destruct (exists_last TNE) as (T0 & tl & ET). rewrite ET in *. clear ET TNE.
        destruct (proj1 (chain_app _ _ _ _) CT1) as [CT0 CTL]. cbn [tfirst] in CT0.
        destruct (proj1 (chain_cons _ _ _ _) CTL) as [BTL _]. clear CTL. cbn [fst snd tfirst] in BTL.
        destruct (proj1 (abatch_cells_split _ _ _ _) BTL) as [TLN TLR]. clear BTL.
        unfold baddr in CT0. set (TL := abatch_addr L (qb_slot (snd tl))) in *.
        assert (INtl : In tl (P ++ R' ++ T0 ++ [tl])) by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
        destruct (OTH tl INtl) as (DTLC & DTLN & (GT1 & GT2 & GT3 & GT4) & STL). unfold baddr, Q_BATCH_BYTES in DTLC, DTLN, GT1, GT2, GT3, GT4. fold TL in DTLC, DTLN, GT1, GT2, GT3, GT4.
        assert (RTL : rng RNG TL 8192).
        { pose proof (proj1 (Forall_forall _ _) RB tl ltac:(right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity)) as X. unfold baddr in X. exact X. }
        assert (TLl : tlast L (T0 ++ [tl]) tl0 = TL) by (rewrite tlast_app1; reflexivity).
        eapply evtF_cut.
        { eapply (munlink_spec true RNG) with (CUR := CUR) (NXT := NXT) (LST := LST) (TMP := TMP) (TL := TL) (tlx := 0)
            (nxn := tfirst L R' 0) (szc := b_size (fst cur) + b_size (fst nx) - 8192) (cc := b_count (fst cur) + b_count (fst nx))
            (szn := 8192) (cn := 0) (ls := Z.of_nat (length (P ++ cur :: nx :: R'))) (lf := lf) (ll := tlast L (cur :: nx :: R') 0) (lb := lb)
            (tn := Z.of_nat (length (T0 ++ [tl]))) (tf := tfirst L (T0 ++ [tl]) tf0) (tl := tlast L (T0 ++ [tl]) tl0) (tb := tb) (ex := ex);
            try reflexivity; try eassumption; try exact I.
          all: try (revert TB0 TB1 EX0 EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia).
          all: try (clear -TFR; tauto).
          - revert LEN40. clear. rewrite !length_app. cbn [length]. rewrite ?length_app. cbn [length]. intros. lia.
          - (* [comment removed for export] *) unfold AIMG_HI, Q_BATCH_BYTES. split; [rewrite length_app; cbn [length]; clear; lia|]. split; [exact TLN|].
            split; [exact GT1|]. split; [exact GT2|]. split; [exact DTLC|]. split; [exact DTLN|]. split; [exact GT3|]. split; [exact GT4|].
            eapply rng_sub'; [exact RTL| clear; lia]. }
        cbv beta. intros ms2 (z1 & z2 & z3 & m2 & -> & MUu & WMu & MI2 & CC2 & CN2 & LS2 & TM2 & TL2). cbn [app] in MUu. clear MI1.
        (* [comment removed for export] *)
        assert (NTL : forall x, In x (P ++ R' ++ T0) -> qb_slot (snd x) <> qb_slot (snd tl)).
        { intros x Hx. apply (nodup_mid (fun x => qb_slot (snd x)) (P ++ cur :: nx :: R' ++ T0) tl []).
          - revert ND. clear. intros ND.
            match goal with |- NoDup ?l => match type of ND with NoDup ?l' => replace l with l'; [exact ND|] end end.
            rewrite !map_app. cbn [map]. rewrite ?map_app. cbn [map app]. repeat (rewrite <- ?app_assoc; cbn [app]). reflexivity.
          - rewrite app_nil_r. apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right; right].
            apply in_app_iff in Hx. apply in_app_iff. exact Hx. }
        assert (DSTL : forall x, In x (P ++ R' ++ T0) -> abatch_addr L (qb_slot (snd x)) + 8192 <= TL \/ TL + 8192 <= abatch_addr L (qb_slot (snd x))).
        { intros x Hx. pose proof (baddr_disj L x tl (NTL x Hx)) as D. unfold baddr, Q_BATCH_BYTES in D. apply D.
          - eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; exact Hx| right; right].
            apply in_app_iff in Hx. apply in_app_iff. destruct Hx as [Hx|Hx]; [left; right; exact Hx| right; apply in_app_iff; left; exact Hx].
          - exact STL. }
        xport EC1 MUu WMu ltac:(rewrite length_app, ?LEC, ?LEN; clear -CRNG NRNG KF DCN GC3 GC4 DTLC; lia).
        destruct JC1 as [jc JC1]. xport JC1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GC3 GC4 DTLC; lia).
        destruct JN1 as [jn JN1]. xport JN1 MUu WMu ltac:(clear -CRNG NRNG KF DCN GN3 GN4 DTLN; lia).
        assert (CHP2 : chain m2 P CUR).
        { eapply chain_frame; [exact CHP1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; left; exact Hx)) as D3.
          destruct (OTH x ltac:(apply in_app_iff; left; exact Hx)) as (D1 & D2 & (G1 & G2 & G3 & G4) & _). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        assert (CHR2 : chain m2 R' 0).
        { eapply chain_frame; [exact CHR1| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) as D3.
          destruct (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hx)) as (D1 & D2 & (G1 & G2 & G3 & G4) & _). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        assert (CT02 : chain m2 T0 TL).
        { eapply chain_frame; [exact CT0| exact MUu| exact WMu|]. apply Forall_forall. intros x Hx.
          pose proof (DSTL x ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hx)) as D3.
          destruct (OTH x ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hx)) as (D1 & D2 & (G1 & G2 & G3 & G4) & _). unfold baddr, Q_BATCH_BYTES in *. cbn. clear -D1 D2 D3 G3 G4. lia. }
        (* [comment removed for export] *)
        destruct TLR as (TLR1 & TLR2 & TLR3 & TLR4 & TLR5 & TLR6). fold TL in TLR1, TLR2, TLR3. unfold Q_BATCH_BYTES, Q_BATCH in TLR3, TLR6.
        xport TLR1 MUu WMu ltac:(clear -DTLC DTLN GT3 GT4; lia).
        xport TLR2 MUu WMu ltac:(rewrite length_map, qhdrs_length by exact TLR5; clear -DTLC DTLN GT3 GT4 TLR4 TLR6; lia).
        destruct TLR3 as [jt TLR3]. xport TLR3 MUu WMu ltac:(clear -DTLC DTLN GT3 GT4 TLR6; lia).
        assert (CT2 : chain m2 ((T0 ++ [tl]) ++ [bq_empty nx]) 0).
        { apply (proj2 (chain_app _ _ _ _)). split.
          - apply (proj2 (chain_app _ _ _ _)). cbn [tfirst app]. unfold baddr. fold TL. split; [exact CT02|].
            apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil]. cbn [tfirst]. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
            apply (proj2 (abatch_cells_split _ _ _ _)). fold TL. split; [exact TL2|]. split; [exact TLR1|]. split; [exact TLR2|].
            split; [exists jt; unfold Q_BATCH_BYTES; exact TLR3|]. unfold Q_BATCH. exact (conj TLR4 (conj TLR5 TLR6)).
          - apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
            unfold abatch_cells. cbn [fst snd tfirst bq_empty b_size b_count b_chunks qb_slot qb_ks qhdrs map length Z.of_nat]. fold NXT. unfold Q_BATCH_BYTES, Q_BATCH.
            split; [exact CN2|]. split; [apply u64arr_nil; clear -GN1 GN2; lia|].
            split; [exists jn; rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r; exact JN1|]. clear. lia. }
        clear CT0 CT02 TLR1 TLR2 TLR3 TL2 TLN.
        (* [comment removed for export] *)
        assert (MU12 : munch ([(LST, LST + 24); (TMP, TMP + 32)] ++ map (fun x => (baddr L x, baddr L x + 8192)) (cur :: (nx :: R') ++ T0 ++ [tl]))%Z m m2).
        { eapply (munch_trans_w _ _ _ _ _ _ MUc MUu).
          - unfold baddr. cbn [map app snd]. fold CUR. fold NXT. solve_sub_fpw ltac:(clear -CRNG NRNG KF; lia).
          - apply sub_fp_by_incl'. unfold baddr. cbn [map app snd]. fold CUR. fold NXT. fold TL.
            repeat (apply Forall_cons; [first [ find_ivw ltac:(clear; lia)
                                               | apply Exists_exists; exists (TL, TL + 8192)%Z; split; [| cbn; clear; lia];
                                                 right; right; right; right; rewrite map_app, in_app_iff; right; rewrite map_app, in_app_iff; right; left; reflexivity ] |]).
            apply Forall_nil. }
        step.                                             (* [comment removed for export] *)
        step. if_cases KX; zify_cond KX.                  (* [comment removed for export] *)
        * (* [comment removed for export] *)
          assert (RNE' : R' <> []) by (intros ->; cbn in KX; rewrite ?unsigned_lit in KX by lia; lia).
          assert (TFE : tfirst L R' 0 = baddr L (hd nx R')) by (destruct R'; [congruence| reflexivity]).
          assert (MB : merge_bq cur (nx :: R') = (fst (merge_bq (bq_merge cur nx) R'), bq_empty nx :: snd (merge_bq (bq_merge cur nx) R'))).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [| exfalso; clear -KF n; lia].
            destruct (merge_bq (bq_merge cur nx) R'); reflexivity. }
          assert (LLN : (tlast L (cur :: nx :: R') 0 =? NXT) = false).
          { apply Z.eqb_neq. rewrite 2!tlast_cons_ne by congruence. destruct (tlast_in R' 0 RNE') as (z & Hz & ->).
            destruct (OTH z ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hz)) as (_ & D2 & _). clear -D2. lia. }
          rewrite LLN in LS2. rewrite TFE.
          replace (baddr L (hd nx R')) with (baddr L (hd (bq_merge cur nx) R')) by (destruct R'; [congruence| reflexivity]).
          setreg 14 (Z_to_bv 64 (baddr L (bq_merge cur nx))) ltac:(unfold baddr; cbn [bq_merge snd qb_slot]; reflexivity).
          unfold Q_BATCH_BYTES.
          eapply evtF_mono.
          { eapply (IH P (bq_merge cur nx) R' ((T0 ++ [tl]) ++ [bq_empty nx]) (tb + 8192) (ex + 8192)).
            - cbn in HD. clear -HD. lia.
            - exact RNE'.
            - exact MI2.
            - rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
              replace (Z.of_nat (length P + S (S (length R'))) - 1) with (Z.of_nat (length P + S (length R'))) in LS2 by lia.
              rewrite tlast_cons_ne by exact RNE'. rewrite 2!tlast_cons_ne in LS2 by congruence. exact LS2.
            - apply (proj2 (chain_app _ _ _ _)). cbn [tfirst]. unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. split; [exact CHP2|].
              apply (proj2 (chain_cons _ _ _ _)). split; [| exact CHR2].
              unfold abatch_cells. cbn [fst snd bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
              replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
              split; [exact CC2|]. split; [rewrite qhdrs_app, map_app by exact NLEN; exact EC1|].
              split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia.
            - rewrite tfirst_app by (destruct T0; cbn; congruence). rewrite tlast_app1. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
              rewrite !length_app in TM2 |- *. cbn [length] in TM2 |- *. unfold Q_BATCH_BYTES in TM2.
              replace (Z.of_nat (length (T0 ++ [tl]) + 1)) with (Z.of_nat (length T0 + 1) + 1) by (rewrite length_app; cbn [length]; lia).
              exact TM2.
            - exact CT2.
            - apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. left. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_merge snd qb_slot]. fold CUR. clear -GC1 GC2 GC3 GC4. tauto.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) GEO). apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
              + unfold bgeom, baddr, AIMG_HI, Q_BATCH_BYTES. cbn [bq_empty snd qb_slot]. fold NXT. clear -GN1 GN2 GN3 GN4. tauto.
            - apply Forall_forall. intros x Hx. apply in_app_iff in Hx. cbn [app In] in Hx.
              destruct Hx as [Hx|[E|Hx]]; [| subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. left. exact Hx.
              + cbn [bq_merge snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. left. reflexivity.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. apply in_app_iff. right. exact Hx.
              + cbn [bq_empty snd qb_slot]. eapply (proj1 (Forall_forall _ _) SL). apply in_app_iff. right. right. left. reflexivity.
            - revert ND. rewrite !map_app. cbn [map]. rewrite !map_app. cbn [map bq_merge bq_empty snd qb_slot app]. rewrite ?map_app. cbn [map].
              intros ND. refine (proj1 (list_relations.list.NoDup_Permutation_proper _ _ _) ND).
              apply Permutation_app_head. apply perm_skip. repeat (rewrite <- ?app_assoc; cbn [app]).
              match goal with |- Permutation _ (?l1 ++ ?l2 ++ [?t; ?b]) =>
                replace (l1 ++ l2 ++ [t; b]) with ((l1 ++ l2 ++ [t]) ++ [b]) by (rewrite <- !app_assoc; reflexivity) end.
              apply Permutation_cons_append.
            - constructor; [| exact (Forall_inv_tail (Forall_inv_tail SZ))]. cbn [fst bq_merge b_size]. unfold Q_BATCH_BYTES in *. clear -SZC SZN. lia.
            - cbn [map fst bq_merge b_size]. rewrite batches_bytes_cons. cbn [b_size]. clear -SZS SZC SZN. unfold Q_BATCH_BYTES in *. lia.
            - apply Forall_forall. intros x Hx. cbn [app In] in Hx.
              destruct Hx as [E|Hx]; [subst x| apply in_app_iff in Hx; destruct Hx as [Hx|Hx]; [| apply in_app_iff in Hx; destruct Hx as [Hx|[E|F0]]; [| subst x| destruct F0]]].
              + unfold baddr. cbn [bq_merge snd qb_slot]. fold CUR. exact RC.
              + eapply (proj1 (Forall_forall _ _) RB). right. apply in_app_iff. left. right. exact Hx.
              + eapply (proj1 (Forall_forall _ _) RB). right. apply in_app_iff. right. exact Hx.
              + unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT. exact RN.
            - clear -TB0; lia.
            - revert TB1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - clear -EX0; lia.
            - revert EX1; clear; cbn [length]; unfold Q_BATCH_BYTES; intros; lia.
            - revert LEN40; clear; rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; intros; lia. }
          cbv beta. unfold mloop_post. rewrite MB. destruct (merge_bq (bq_merge cur nx) R') as [l' e']. cbn [fst snd].
          intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
          rewrite <- !app_assoc in TM', CT'. cbn [app] in TM', CT'.
          rewrite !length_app in TM' |- *. cbn [length app] in TM' |- *. unfold Q_BATCH_BYTES in TM' |- *.
          replace (ex + 8192 * Z.of_nat (S (length e'))) with (ex + 8192 + 8192 * Z.of_nat (length e')) by lia.
          replace (tb + 8192 * Z.of_nat (S (length e'))) with (tb + 8192 + 8192 * Z.of_nat (length e')) by lia.
          do 8 eexists. exists m'. split; [reflexivity|].
          split. { eapply (munch_trans_w _ _ _ _ _ _ MU12 MU'); apply sub_fp_incl; [intros iv Hiv; exact Hiv|].
                   intros iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [Hiv|Hiv].
                   { cbn [In] in Hiv. destruct Hiv as [H|[H|[]]]; [left; exact H| right; left; exact H]. }
                   apply in_map_iff in Hiv. destruct Hiv as (x & <- & Hx). right. right. apply in_map_iff.
                   destruct Hx as [<-|Hx]; [exists cur; split; [reflexivity| left; reflexivity]|].
                   apply in_app_iff in Hx. destruct Hx as [Hx|Hx]; [exists x; split; [reflexivity| right; right; apply in_app_iff; left; exact Hx]|].
                   apply in_app_iff in Hx. destruct Hx as [Hx|[<-|[]]]; [exists x; split; [reflexivity| right; right; apply in_app_iff; right; exact Hx]|].
                   exists nx; split; [reflexivity| right; left; reflexivity]. }
          split; [eapply wmono_trans; [exact WMc| eapply wmono_trans; [exact WMu| exact WM']]|]. split; [exact MI'|].
          split. { revert LS'. rewrite ?length_app. intros X; exact X. } split; [exact CH'|].
          rewrite <- !app_assoc. cbn [app]. split; [| exact CT'].
          revert TM'. rewrite ?length_app. cbn [length]. intros X.
          first [exact X| replace (length T0 + 1 + S (length e'))%nat with (length T0 + S (S (length e')))%nat by lia; exact X].
        * (* [comment removed for export] *)
          assert (RNIL : R' = []).
          { destruct R' as [|r R'']; [reflexivity| exfalso].
            pose proof (tfirst_pos (r :: R'') 0 GR ltac:(congruence)) as X. unfold AIMG_HI in X. cbn [tfirst] in X, KX.
            pose proof (Forall_inv GR) as Y. unfold bgeom, Q_BATCH_BYTES in Y. cbv beta in Y. destruct Y as (Y1 & Y & Y3).
            rewrite ?unsigned_lit in KX by (clear -X Y; lia). clear -X KX. lia. }
          subst R'. clear GR KX.
          assert (MB : merge_bq cur [nx] = ([bq_merge cur nx], [bq_empty nx])).
          { cbn [merge_bq]. unfold Q_BATCH. destruct (Z.leb_spec0 (b_count (fst cur) + b_count (fst nx)) 1021); [reflexivity| exfalso; clear -KF n; lia]. }
          apply evtF_done. unfold mloop_post. rewrite MB. cbv beta iota zeta. cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat].
          rewrite !Z.mul_1_r.
          do 8 eexists. exists m2. split; [reflexivity|].
          split. { exact MU12. }
          split; [eapply wmono_trans; [exact WMc| exact WMu]|]. split; [exact MI2|].
          split. { rewrite length_app in LS2 |- *. cbn [length] in LS2 |- *.
                   replace (Z.of_nat (length P + 2) - 1) with (Z.of_nat (length P + 1)) in LS2 by lia.
                   cbn [tlast map List.last] in LS2. rewrite Z.eqb_refl in LS2. exact LS2. }
          split. { apply (proj2 (chain_app _ _ _ _)). split; [exact CHP2|]. apply (proj2 (chain_cons _ _ _ _)). split; [| apply chain_nil].
                   unfold abatch_cells. cbn [fst snd tfirst bq_merge b_size b_count b_chunks qb_slot qb_ks]. fold CUR. unfold Q_BATCH_BYTES, Q_BATCH.
                   cbn [tfirst] in CC2. replace (b_size (fst cur) + (b_size (fst nx) - 8192)) with (b_size (fst cur) + b_size (fst nx) - 8192) by lia.
                   split; [exact CC2|]. split.
                   - rewrite qhdrs_app, map_app by exact NLEN. exact EC1.
                   - split; [exists jc; exact JC1|]. rewrite !length_app. clear -CCNT NCNT CLEN NLEN CRNG NRNG KF. lia. }
          split; [| exact CT2].
          lazymatch type of TM2 with rw_cells _ _ _ ?l2 => lazymatch goal with |- rw_cells _ _ _ ?l1 => replace l1 with l2; [exact TM2|] end end.
          rewrite (tfirst_app L (T0 ++ [tl]) [bq_empty nx] tf0) by (destruct T0; cbn; congruence). rewrite tlast_app1. unfold baddr. cbn [bq_empty snd qb_slot]. fold NXT.
          rewrite !length_app. cbn [length]. unfold Q_BATCH_BYTES.
          replace (Z.of_nat (length T0 + 1 + 1)) with (Z.of_nat (length T0 + 1) + 1) by lia. reflexivity.
  Qed.
End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation AMERGE_STACK := 16 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition amerge_fun (X : list bq) : list bq * list bq :=
  match X with [] => ([], []) | cur :: R => merge_bq cur R end.

Definition amerge_post (L : alayout) (LST TMP lb tf0 tl0 tb lo : Z) (X T : list bq)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    let '(l, e) := amerge_fun X in
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(bv_unsigned sp - AMERGE_STACK, bv_unsigned sp); (LST, LST + 32); (TMP, TMP + 32)]
              ++ map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) (X ++ T))%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' LST [C8 (Z_to_bv 64 (Z.of_nat (length l))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L l 0));
                             C8 (Z_to_bv 64 (lb - Q_BATCH_BYTES * Z.of_nat (length e)))]
    /\ chain L m' l 0
    /\ rw_cells bsegs m' TMP [C8 (Z_to_bv 64 (Z.of_nat (length (T ++ e)))); C8 (Z_to_bv 64 (tfirst L (T ++ e) tf0));
                             C8 (Z_to_bv 64 (tlast L (T ++ e) tl0)); C8 (Z_to_bv 64 (tb + Q_BATCH_BYTES * Z.of_nat (length e)))]
    /\ chain L m' (T ++ e) 0.

Lemma disj_objs_above : forall L LST TMP Y A n, Forall (bgeom L LST TMP) Y -> ATOP <= A ->
  disjoint_from (map (fun x => (baddr L x, baddr L x + Q_BATCH_BYTES)) Y) A n.
Proof.
  intros L LST TMP Y A n HF HA. apply disjoint_from_Forall. apply Forall_map. eapply Forall_impl; [| exact HF].
  intros x (G1 & G2 & _). cbn [fst snd]. left. unfold Q_BATCH_BYTES in *. lia.
Qed.

Lemma merge_bq_baddr_in : forall L R cur x, In x (fst (merge_bq cur R) ++ snd (merge_bq cur R)) ->
  exists y, In y (cur :: R) /\ baddr L y = baddr L x.
Proof.
  induction R as [|nx R IH]; intros cur x Hx; cbn [merge_bq fst snd app] in Hx.
  - destruct Hx as [<-|[]]. exists cur. split; [left; reflexivity| reflexivity].
  - destruct (b_count (fst cur) + b_count (fst nx) <=? Q_BATCH).
    + specialize (IH (bq_merge cur nx) x). destruct (merge_bq (bq_merge cur nx) R) as [l e]. cbn [fst snd] in Hx, IH.
      assert (Hx' : In x (l ++ e) \/ x = bq_empty nx).
      { apply in_app_iff in Hx. destruct Hx as [Hx|[<-|Hx]]; [left; apply in_app_iff; left; exact Hx| right; reflexivity| left; apply in_app_iff; right; exact Hx]. }
      destruct Hx' as [Hx'| ->].
      * destruct (IH Hx') as (y & Hy & EY). destruct Hy as [<-|Hy].
        -- exists cur. split; [left; reflexivity| exact EY].
        -- exists y. split; [right; right; exact Hy| exact EY].
      * exists nx. split; [right; left; reflexivity| reflexivity].
    + specialize (IH nx x). destruct (merge_bq nx R) as [l e]. cbn [fst snd] in Hx, IH.
      destruct Hx as [<-|Hx].
      * exists cur. split; [left; reflexivity| reflexivity].
      * destruct (IH Hx) as (y & Hy & EY). exists y. split; [right; exact Hy| exact EY].
Qed.

Lemma amerge_spec : forall L RNG (LST TMP lb tf0 tl0 tb lo : Z) (X T : list bq)
    ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : amem),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AMERGE_STACK ->
  mem_inv bsegs m ->
  rw_cells bsegs m LST [C8 (Z_to_bv 64 (Z.of_nat (length X))); C8 (Z_to_bv 64 (tfirst L X 0)); C8 (Z_to_bv 64 (tlast L X 0)); C8 (Z_to_bv 64 lb)] ->
  chain L m X 0 ->
  rw_cells bsegs m TMP [C8 (Z_to_bv 64 (Z.of_nat (length T))); C8 (Z_to_bv 64 (tfirst L T tf0)); C8 (Z_to_bv 64 (tlast L T tl0)); C8 (Z_to_bv 64 tb)] ->
  chain L m T 0 ->
  Forall (bgeom L LST TMP) (X ++ T) -> Forall (fun x => 0 <= qb_slot (snd x)) (X ++ T) ->
  NoDup (map (fun x => qb_slot (snd x)) (X ++ T)) ->
  Forall (fun x => Q_BATCH_BYTES <= b_size (fst x)) X -> batches_bytes (map fst X) < 2^62 ->
  0 <= LST -> LST + 32 <= ATOP -> 0 <= TMP -> TMP + 32 <= 2^47 -> (TMP + 32 <= LST \/ LST + 32 <= TMP) ->
  (bv_unsigned sp <= TMP \/ TMP + 32 <= lo) ->
  0 <= tf0 < 2^64 -> 0 <= tl0 < 2^64 -> 0 <= lb < 2^64 -> 0 <= tb -> tb + Q_BATCH_BYTES * Z.of_nat (length X) < 2^62 ->
  Z.of_nat (length (X ++ T)) < 2^40 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG LST 32 -> rng RNG TMP 32 ->
  Forall (fun x => rng RNG (baddr L x) Q_BATCH_BYTES) (X ++ T) ->
  evtF bsegs RNG (amerge_post L LST TMP lb tf0 tl0 tb lo X T ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LST) (Z_to_bv 64 TMP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 amerge_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST CEIL LO MI LS CH TM CT GEO SL ND SZ SZS L1 L2 T1 T2 DTL DTS TF0 TL0 LB TB0 TB1 LEN40 RSTK RL RT RB.
  unfold amerge_entry. atop_facts. unfold Q_BATCH_BYTES in TB1.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (LST + 24, LST + 32)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  step. step.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac chain_over CHx MUx WMx GEOx sel :=
    eapply chain_frame in CHx; [| exact MUx | exact WMx |
      apply Forall_forall; let xg := fresh "xg" in let Hxg := fresh "Hxg" in let Gx := fresh "Gx" in intros xg Hxg;
      lazymatch type of GEOx with Forall (bgeom ?L ?LST ?TMP) _ =>
        assert (Gx : bgeom L LST TMP xg) by (eapply (proj1 (Forall_forall _ _) GEOx); apply in_app_iff; sel (); exact Hxg) end;
      unfold bgeom, AIMG_HI, Q_BATCH_BYTES in Gx; unfold Q_BATCH_BYTES; cbn [disjoint_from fst snd]; lia ].
  (* [comment removed for export] *)
  Local Ltac exit2 sp MU WM ST FR CH CT GEO LS TM :=
    step; zstep;                               (* [comment removed for export] *)
    step;                                      (* [comment removed for export] *)
    step; step; step;                          (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp);
    chain_over CH MU WM GEO ltac:(fun _ => left); chain_over CT MU WM GEO ltac:(fun _ => right);
    apply evtF_done; unfold amerge_post; cbn [amerge_fun merge_bq length Z.of_nat Pos.of_succ_nat Pos.to_nat tfirst tlast map List.last];
    rewrite !app_nil_r, !Z.mul_0_r, !Z.sub_0_r, !Z.add_0_r in *;
    do 14 eexists; eexists; split; [reflexivity|];
    split; [ eapply munch_weaken; [| exact MU]; apply sub_fp_by_incl';
             constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; lia]|];
             constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; lia]|]; constructor |];
    split; [exact WM|]; split; [assumption|]; split; [exact ST|];
    split; [exact LS|]; split; [exact CH|]; split; [exact TM| exact CT].
  destruct X as [|cur R].
  - (* [comment removed for export] *)
    cbn [tfirst tlast map List.last length Z.of_nat] in LS.
    step. step. if_lit.                        (* [comment removed for export] *)
    exit2 sp MU WM ST FR CH CT GEO LS TM.
  - (* [comment removed for export] *)
    pose proof CH as CH0.
    destruct (proj1 (chain_cons _ _ _ _ _) CH) as [BC CHR]. clear CH. rename CH0 into CH.
    destruct BC as (CC & EC & JC & CCNT & CLEN & CRNG).
    assert (GC : bgeom L LST TMP cur) by (eapply (proj1 (Forall_forall _ _) GEO); left; reflexivity).
    assert (RC : rng RNG (baddr L cur) Q_BATCH_BYTES) by (pose proof (Forall_inv RB) as X; exact X).
    unfold bgeom, AIMG_HI, Q_BATCH_BYTES in GC, RC. unfold baddr in GC, RC. cbn [fst snd] in CC, GC, RC. cbn [tfirst tlast map List.last] in LS. unfold baddr in LS.
    set (CUR := abatch_addr L (qb_slot (snd cur))) in *. destruct GC as (GC1 & GC2 & GC3 & GC4).
    xport CC MU WM ltac:(clear -GC2 GC3 CEIL LO; lia).
    clear EC JC.
    step. step. if_cases KC; zify_cond KC.     (* [comment removed for export] *)
    { exfalso. rewrite ?unsigned_lit in KC by (clear -GC1 GC2; lia). clear -KC GC1. lia. }
    clear KC.
    destruct R as [|nx R'].
    + (* [comment removed for export] *)
      cbn [tfirst] in CC.
      step. step. if_lit.                      (* [comment removed for export] *)
      clear CC. exit2 sp MU WM ST FR CH CT GEO LS TM.
    + (* [comment removed for export] *)
      assert (GN : bgeom L LST TMP nx) by (eapply (proj1 (Forall_forall _ _) GEO); right; left; reflexivity).
      unfold bgeom, AIMG_HI, Q_BATCH_BYTES, baddr in GN. cbn [tfirst] in CC. unfold baddr in CC.
      set (NXT := abatch_addr L (qb_slot (snd nx))) in *. destruct GN as (GN1 & GN2 & GN3 & GN4).
      step. step. if_cases KN; zify_cond KN.   (* [comment removed for export] *)
      { exfalso. rewrite ?unsigned_lit in KN by (clear -GN1 GN2; lia). clear -KN GN1. lia. }
      clear KN.
      step. step. step. step. step.            (* [comment removed for export] *)
      chain_over CH MU WM GEO ltac:(fun _ => left). chain_over CT MU WM GEO ltac:(fun _ => right).
      clear CC CHR.
      eapply evtF_cut.
      { eapply (mloop_spec L RNG LST TMP CUR lb tf0 tl0) with (P := []) (R := nx :: R') (T := T) (tb := tb) (ex := 0) (d := length (nx :: R'));
          try eassumption; try reflexivity.
        - apply Z_to_bv_eqm. reflexivity.
        - clear -GC1 GC2. lia.
        - congruence.
        - revert TB1. clear. unfold Q_BATCH_BYTES. cbn [length]. intros; lia.
        - revert LEN40. clear. unfold Q_BATCH_BYTES. rewrite length_app. cbn [length]. intros; lia. }
      cbv beta. unfold mloop_post, amerge_post. cbn [amerge_fun].
      destruct (merge_bq cur (nx :: R')) as [l e] eqn:MB.
      intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & m' & -> & MU' & WM' & MI' & LS' & CH' & TM' & CT').
      clear LS TM MI.
      xport FR MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -CEIL LO L2; lia| split; [clear -DTS LO; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -CEIL LO; lia]]]).
      xport ST MU' WM' ltac:(cbn [app disjoint_from fst snd]; split; [clear -CEIL LO L2; lia| split; [clear -DTS LO; lia| eapply disj_objs_above; [exact GEO| atop_facts; clear -CEIL LO; lia]]]).
      box MU'.
      snapshot [(bv_unsigned sp + -16, bv_unsigned sp); (LST + 24, LST + 32)]%Z MUe WMe.
      step. zstep.                             (* [comment removed for export] *)
      setreg 11%Z (Z_to_bv 64 (lb - Q_BATCH_BYTES * Z.of_nat (length e))) ltac:(apply Z_to_bv_eqm; unfold Q_BATCH_BYTES; clear; Z.div_mod_to_equations; lia).
      step.                                    (* [comment removed for export] *)
      step. step. step.                        (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      apply evtF_done. cbn [length app] in LS'. cbn [app] in CH'.
      do 14 eexists. eexists. split; [reflexivity|].
      split. { (* [comment removed for export] *)
        unbox MU'.
        lazymatch goal with |- munch ?W m ?mf =>
          assert (S1 : sub_fp [(bv_unsigned sp + -16, bv_unsigned sp); (LST + 24, LST + 32)]%Z W);
          [ apply sub_fp_by_incl';
            constructor; [apply Exists_exists; eexists; split; [left; reflexivity| cbn; clear; lia]|];
            constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|]; constructor |] end.
        lazymatch goal with |- munch ?W m ?mf =>
          assert (MU2 : munch W m0 mf); [eapply (munch_trans_w W _ _ _ _ _ MU' MUe); [| exact S1]
                                        |eapply (munch_trans_w W _ _ _ _ _ MU MU2); [exact S1| intros z Hz; exact Hz]] end.
        apply sub_fp_by_incl'. apply Forall_app. split.
        - constructor; [apply Exists_exists; eexists; split; [right; left; reflexivity| cbn; clear; lia]|].
          constructor; [apply Exists_exists; eexists; split; [right; right; left; reflexivity| cbn; clear; lia]|]. constructor.
        - apply Forall_map. apply Forall_forall. intros x Hx. apply Exists_exists. eexists. split; [right; right; right; apply in_map; exact Hx|]. cbn; clear; lia. }
      split; [eapply wmono_trans; [exact WM| first [exact WM'| eapply wmono_trans; [exact WM'| exact WMe]]]|]. split; [assumption|]. split; [exact ST|].
      split. { cbn [tfirst]. unfold baddr. fold CUR. exact LS'. }
      split. { eapply chain_frame; [exact CH'| exact MUe| exact WMe|]. apply Forall_forall. intros x Hx.
               destruct (merge_bq_baddr_in L (nx :: R') cur x ltac:(rewrite MB; apply in_app_iff; left; exact Hx)) as (y & Hy & EY).
               rewrite <- EY. pose proof (proj1 (Forall_forall _ _) GEO y ltac:(apply in_app_iff; left; exact Hy)) as G.
               unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia. }
      split; [exact TM'|].
      eapply chain_frame; [exact CT'| exact MUe| exact WMe|]. apply Forall_app. split.
      * apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) GEO x ltac:(apply in_app_iff; right; exact Hx)) as G.
        unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia.
      * apply Forall_forall. intros x Hx.
        destruct (merge_bq_baddr_in L (nx :: R') cur x ltac:(rewrite MB; apply in_app_iff; right; exact Hx)) as (y & Hy & EY).
        rewrite <- EY. pose proof (proj1 (Forall_forall _ _) GEO y ltac:(apply in_app_iff; left; exact Hy)) as G.
        unfold bgeom, AIMG_HI, Q_BATCH_BYTES in G. unfold Q_BATCH_BYTES. cbn [disjoint_from fst snd]. clear -G CEIL LO. lia.
Qed.
End CANSEC2.
