(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol F_atoi F_htons F_memset F_memmove F_stpncpy F_strncasecmp
     F_inet_pton_A F_inet_pton_C H_parse_uric H_parse_uri_A.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Lemma memset0_call : forall (D n : Z) (junk : list byte)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  rw_cells rsegs m D [CB (Z.to_nat n) junk] -> mem_inv rsegs m -> (0 <= D /\ D + n < 2^64)%Z -> (0 <= n)%Z ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 n ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' D [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24660) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros DST MI HD HN -> -> ->.
  assert (E0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (E1 : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply (memset_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 n)); rewrite ?E0, ?E2; eauto. }
  intros ms' Q. unfold memset_post in Q. rewrite !E0, !E1, !E2 in Q. cbn [Z.modulo] in Q. exact Q.
Qed.

Lemma strncpy_call : forall (qq lo D Ss n : Z) (str slack bs : list byte)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  u8arr rsegs m D bs -> length bs = Z.to_nat n ->
  bytes_at rsegs m Ss (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((- (Ss + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  stk rsegs m lo qq -> (lo <= qq - 32)%Z -> (0 <= qq < 2^64)%Z -> (0 <= D)%Z -> (0 <= n)%Z -> (D + n < 2^64)%Z -> (0 <= Ss < 2^64)%Z ->
  (D + n <= Ss \/ Ss + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D)%Z ->
  (D + n <= lo \/ qq <= D)%Z ->
  (Ss + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= qq - 32 \/ qq <= Ss)%Z ->
  mem_inv rsegs m -> a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 Ss -> a2 = Z_to_bv 64 n ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra (Z_to_bv 64 qq) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(D, D + n); (qq - 32, qq)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo qq
    /\ u8arr rsegs m' D (stpn_result str (Z.to_nat n))
    /\ bytes_at rsegs m' Ss (str ++ Z_to_bv 8 0 :: slack))
    (MS (mkR ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24a60) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros DST LBS SRC NONUL PAD ST LO QQ D0 N0 DN SS0 SEP SEPD SEPS MI -> -> ->.
  assert (EQ : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Ss) = Ss) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strncpy_spec ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 Ss) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack bs lo);
      rewrite ?EQ, ?ED, ?ES, ?EN; eauto; try lia. }
  intros ms' P. unfold strncpy_post in P. rewrite !EQ, !ED, !ES, !EN in P. exact P.
Qed.

Lemma strncasecmp_call : forall (qq lo A B n v : Z) (ls rs : list byte)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  bytes_at rsegs m A ls -> bytes_at rsegs m B rs -> strncasecmp_model ls rs n = Some v ->
  stk rsegs m lo qq -> (lo <= qq - 48)%Z -> (0 <= qq < 2^64)%Z -> (0 <= A < 2^64)%Z -> (0 <= B < 2^64)%Z -> (0 <= n < 2^64)%Z ->
  (A + Z.of_nat (length ls) <= qq - 48 \/ qq <= A)%Z ->
  (B + Z.of_nat (length rs) <= qq - 48 \/ qq <= B)%Z ->
  mem_inv rsegs m -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 B -> a2 = Z_to_bv 64 n ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra (Z_to_bv 64 qq) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(qq - 48, qq)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo qq
    /\ bytes_at rsegs m' A ls /\ bytes_at rsegs m' B rs)
    (MS (mkR ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2493c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros LS RS HM ST LO QQ A0 B0 N0 SEPL SEPR MI -> -> ->.
  assert (EQ : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strncasecmp_spec_lo ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 B) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo);
      rewrite ?EQ, ?EA, ?EB, ?EN; eauto; try lia. }
  intros ms' P. unfold strncasecmp_post in P. rewrite !EQ, !EA, !EB in P. exact P.
Qed.

Lemma strtol10_call : forall (qq lo Ss : Z) (str : list byte) (errv canary : word)
    (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at rsegs m Ss (str ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  stk rsegs m lo qq -> mem_inv rsegs m ->
  (lo <= qq - STRTOL_DEPTH)%Z -> (ssp_guard + 8 <= lo)%Z -> (0 <= qq < 2^63)%Z ->
  (4096 + 164 <= bv_unsigned tp)%Z ->
  (4096 <= Ss)%Z -> (Ss + 2^41 <= 2^63)%Z -> (Z.of_nat (length str) + 1 <= 2^40)%Z ->
  (Ss + Z.of_nat (length str) + 1 <= qq - STRTOL_DEPTH \/ qq <= Ss)%Z ->
  (Ss + Z.of_nat (length str) + 1 <= got_ssp \/ got_ssp + 8 <= Ss)%Z -> (Ss + Z.of_nat (length str) + 1 <= ssp_guard \/ ssp_guard + 8 <= Ss)%Z ->
  (bv_unsigned tp - 164 + 4 <= lo \/ qq <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= Ss \/ Ss + Z.of_nat (length str) + 1 <= bv_unsigned tp - 164)%Z ->
  (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z -> (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z ->
  a0 = Z_to_bv 64 Ss -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 10 ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (errv' : word),
      ms' = MS (mkR ra (Z_to_bv 64 qq) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch [(qq - 528, qq); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo qq
      /\ bytes_at rsegs m' Ss (str ++ [Z_to_bv 8 0])
      /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary]
      /\ rw_cells rsegs m' (bv_unsigned tp - 164) [C4 errv'])
    (MS (mkR ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 strtol_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros STR ERR GOT CAN ST MI LO GLO QQ TP S4 SHI LEN D1 D2 D3 D4 D5 D6 D7 -> -> ->.
  assert (E0 : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strtol0_proof ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Ss str 10 errv canary lo);
      rewrite ?E0; eauto; try lia. }
  intros ms' P. unfold strtol_post0, STRTOL_DEPTH in P. rewrite !E0 in P. exact P.
Qed.

Lemma inet_pton_call : forall (qq lo af Ss A : Z) (str ojunk : list byte) (N : nat) (canary : word)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc m,
  bytes_at rsegs m Ss (str ++ [Z_to_bv 8 0]) ->
  rw_cells rsegs m A [CB N ojunk] ->
  ((af = 2 /\ 4 <= Z.of_nat N) \/ (af = 10 /\ N = 16%nat))%Z ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  stk rsegs m lo qq -> (lo <= qq - 80)%Z -> (0 <= qq < 2^64)%Z -> (0 <= Ss < 2^64)%Z -> (0 <= A < 2^64)%Z ->
  (Ss + Z.of_nat (length str) + 1 <= qq - 80 \/ qq <= Ss)%Z ->
  (A + Z.of_nat N <= qq - 80 \/ qq <= A)%Z ->
  (A + Z.of_nat N <= Ss \/ Ss + Z.of_nat (length str) + 1 <= A)%Z ->
  (got_ssp + 8 <= qq - 80)%Z -> (ssp_guard + 8 <= qq - 80)%Z ->
  (A + Z.of_nat N <= got_ssp \/ got_ssp + 8 <= A)%Z ->
  (A + Z.of_nat N <= ssp_guard \/ ssp_guard + 8 <= A)%Z ->
  mem_inv rsegs m -> a0 = Z_to_bv 64 af -> a1 = Z_to_bv 64 Ss -> a2 = Z_to_bv 64 A ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (r : Z) (outs : list byte),
    ms' = MS (mkR ra (Z_to_bv 64 qq) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(qq - 80, qq); (A, A + Z.of_nat N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo qq
    /\ bytes_at rsegs m' Ss (str ++ [Z_to_bv 8 0])
    /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary]
    /\ rw_cells rsegs m' A [CB N outs]
    /\ (r = 0 \/ r = 1)%Z)
    (MS (mkR ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a008) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros STR OC AF GOT CAN ST LO QQ S0 A0 D1 D2 D3 G1 G2 D4 D5 MI -> -> ->.
  assert (EQ : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 af) = af) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Ss) = Ss) by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (inet_pton_spec ra (Z_to_bv 64 qq) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 af) (Z_to_bv 64 Ss) (Z_to_bv 64 A) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str ojunk N canary lo);
      rewrite ?EQ, ?EF, ?ES, ?EA; eauto; try lia. }
  intros ms' P. unfold inet_pton_post in P. rewrite !EQ, !ES, !EA in P. destruct_exs P.
  destruct P as (-> & MU & WM & MI' & ST' & STR' & GOT' & CAN' & OUT' & LEN & R).
  repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
  repeat (split; [eassumption|]). split; [| exact R]. apply rw_cells_of_u8arr in OUT'. rewrite LEN in OUT'. exact OUT'.
Qed.

Lemma puri_Z_to_le_bytes_app : forall n k z, Z_to_le_bytes (n + k) z = Z_to_le_bytes n z ++ Z_to_le_bytes k (Z.shiftr z (8 * Z.of_nat n)).
Proof.
  induction n as [|n IH]; intros k z.
  - cbn [Nat.add app]. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Nat.add Z_to_le_bytes app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma puri_le8_small_split : forall v, (0 <= v < 2^32)%Z -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. unfold le8, le4, RiscvSemantics.word_to_le_bytes. rewrite !unsigned_lit by lia. rewrite (puri_Z_to_le_bytes_app 4 4 v : Z_to_le_bytes 8 v = _).
  f_equal. f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma puri_C8_C4C4 : forall m A pre v post, rw_cells rsegs m A (pre ++ C8 (Z_to_bv 64 v) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post).
Proof.
  intros m A pre v post [[W B] WR] Hv. split; [split|].
  - rewrite cells_wf_app in *. cbn in *. LiaTuning.ctauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite (puri_le8_small_split v Hv) in B. rewrite <- !app_assoc in *. cbn [app] in *. exact B.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact WR.
Qed.
Lemma puri_C4C4_C8 : forall m A pre v post, rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: post) -> (0 <= v < 2^32)%Z ->
  rw_cells rsegs m A (pre ++ C8 (Z_to_bv 64 v) :: post).
Proof.
  intros m A pre v post [[W B] WR] Hv. split; [split|].
  - rewrite cells_wf_app in *. cbn in *. LiaTuning.ctauto.
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. rewrite (puri_le8_small_split v Hv). rewrite <- !app_assoc in *. cbn [app] in *. exact B.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *.
    replace (cells_size pre + (8 + cells_size post))%nat with (cells_size pre + (4 + (4 + cells_size post)))%nat by lia. exact WR.
Qed.

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (U O ulen : Z) (ustr slack : list byte) (canary gifv : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis USL : Z.of_nat (length ustr) = ulen.
  Hypothesis ULR : (0 <= ulen < 2^31)%Z.
  Hypothesis PAD : ((- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis U4K : (4096 <= U)%Z.
  Hypothesis ULO : (U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 928)%Z.
  Hypothesis OSP : (bv_unsigned sp <= O)%Z.
  Hypothesis OHI : (O + 216 <= 2^62)%Z.
  Hypothesis OAL : oal O.
  Hypothesis SPH : (bv_unsigned sp + 2^41 <= 2^63)%Z.
  Hypothesis TP1 : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis TP2 : (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis SGLO : (ssp_guard + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GSLO : (got_ssp + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GFLO : (GIF + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis DE1 : (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE2 : (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE3 : (bv_unsigned tp - 164 + 4 <= GOT_GIF \/ GOT_GIF + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE4 : (bv_unsigned tp - 164 + 4 <= GIF \/ GIF + 4 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE5 : (bv_unsigned tp - 164 + 4 <= U \/ U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned tp - 164)%Z.

  Notation SP := (bv_unsigned sp).
  Notation q := (bv_unsigned sp + -400)%Z.
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -400)).
  Notation lo := (bv_unsigned sp - 928)%Z.
  Notation TPE := (bv_unsigned tp - 164)%Z.
  Notation W := [(bv_unsigned sp - 928, bv_unsigned sp); (O, O + 216); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.
  Notation POST := (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U O ustr slack canary gifv m0).
  Notation USTR m := (bytes_at rsegs m U (ustr ++ Z_to_bv 8 0 :: slack)).

  Notation baseP := (base U O ustr slack canary gifv sp tp m0).

  Notation FRB m := (rw_cells rsegs m (q + 296) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac open_base B :=
    let errv := fresh "errv" in
    destruct B as (USTR & [errv ERR] & GOT & CAN & GIFP & GIFV & MI & MU & WM).
  Ltac close_base :=
      split; [assumption|]; split; [eexists; eassumption|]; repeat (split; [assumption|]); assumption.

  #[using="U ulen slack ULR U4K ULO SPH"] Lemma sp_rangeB : (928 <= SP /\ SP + 2^41 <= 2^63)%Z.
  Proof. clear -ULR U4K ULO SPH. pose proof (word_lt64 sp). lia. Qed.
  #[using="U ulen ustr slack ULR U4K ULO SPH GFLO"] Lemma q_spB : bv_unsigned spw = q.
  Proof. pose proof sp_rangeB. apply unsigned_lit. lia. Qed.

  #[using="Type"] Lemma frameA_join : forall m cs wb, rw_cells rsegs m q cs -> cells_size cs = 40%nat -> u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    exists jA, rw_cells rsegs m q [CB 296 jA].
  Proof.
    intros m cs wb H L WB LW. apply rw_cells_of_u8arr in WB. rewrite LW in WB.
    assert (J : rw_cells rsegs m q (cs ++ [CB 256 wb])). { apply rw_cells_app. rewrite L. split; [exact H| exact WB]. }
    destruct (rw_cells_forget rsegs m q _ J) as [jA JA]. rewrite cells_size_app, L in JA. cbn in JA. exists jA. exact JA.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma frame5 : forall m c0 v8 c16 v24 c32,
    rw_cells rsegs m q c0 -> cells_size c0 = 8%nat -> rw_cells rsegs m (q + 8) [C8 v8] ->
    rw_cells rsegs m (q + 16) c16 -> cells_size c16 = 8%nat -> rw_cells rsegs m (q + 24) [C8 v24] ->
    rw_cells rsegs m (q + 32) c32 -> cells_size c32 = 8%nat ->
    rw_cells rsegs m q (c0 ++ [C8 v8] ++ c16 ++ [C8 v24] ++ c32) /\ cells_size (c0 ++ [C8 v8] ++ c16 ++ [C8 v24] ++ c32) = 40%nat.
  Proof.
    intros m c0 v8 c16 v24 c32 H0 L0 H8 H16 L16 H24 H32 L32.
    split; [| rewrite !cells_size_app, L0, L16, L32; reflexivity].
    apply rw_cells_app. rewrite L0. split; [exact H0|].
    apply rw_cells_app. cbn [cells_size csize Nat.add]. split; [replace (q + Z.of_nat 8)%Z with (q + 8)%Z by lia; exact H8|].
    apply rw_cells_app. rewrite L16. split; [replace (q + Z.of_nat 8 + Z.of_nat 8)%Z with (q + 16)%Z by lia; exact H16|].
    apply rw_cells_app. cbn [cells_size csize Nat.add]. split; [replace (q + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (q + 24)%Z by lia; exact H24|].
    replace (q + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8)%Z with (q + 32)%Z by lia. exact H32.
  Qed.

  #[using="Type"] Lemma out_join2 : forall m csL csH, rw_cells rsegs m O csL -> cells_size csL = 64%nat -> rw_cells rsegs m (O + 64) csH -> cells_size csH = 152%nat ->
    exists junk, rw_cells rsegs m O [CB 216 junk].
  Proof.
    intros m csL csH HL LL HH LH.
    assert (J : rw_cells rsegs m O (csL ++ csH)). { apply rw_cells_app. rewrite LL. split; [exact HL| exact HH]. }
    destruct (rw_cells_forget rsegs m O _ J) as [junk JJ]. rewrite cells_size_app, LL, LH in JJ. cbn in JJ. exists junk. exact JJ.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma hp_join : forall m h0 cs, rw_cells rsegs m (O + 64) h0 -> cells_size h0 = 16%nat -> rw_cells rsegs m (O + 80) cs ->
    rw_cells rsegs m (O + 64) (h0 ++ cs).
  Proof. intros m h0 cs H0 L0 H1. apply rw_cells_app. rewrite L0. split; [exact H0|]. replace (O + 64 + Z.of_nat 16)%Z with (O + 80)%Z by lia. exact H1. Qed.

  #[using="ulen ULR U4K ULO SPH"] Lemma fail : forall x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      m csq wb csL csH,
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 40%nat -> u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat -> rw_cells rsegs m (O + 64) csH -> cells_size csH = 152%nat ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x170dc) fc None m (seg_rom rsegs)).
  Proof.
    intros until csH. intros B FQ LQ WB LW FRBm ST OL LL OH LH. pose proof sp_rangeB as SR.
    destruct (frameA_join m csq wb FQ LQ WB LW) as [jA FRA]. destruct (out_join2 m csL csH OL LL OH LH) as [junk OUT].
    open_base B. zstep. zstep. eapply epilogue; try eassumption. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma hpend : forall (bh2 size : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x22 x23 x24 x26 x27 x28 x29 x30 x31
      m c0 c16 c32 wb csL h0 csH,
    baseP m -> rw_cells rsegs m q c0 -> cells_size c0 = 8%nat -> rw_cells rsegs m (q + 8) [C4 (Z_to_bv 64 bh2); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (q + 16) c16 -> cells_size c16 = 8%nat -> rw_cells rsegs m (q + 24) [C8 (Z_to_bv 64 (U + bh2))] ->
    rw_cells rsegs m (q + 32) c32 -> cells_size c32 = 8%nat -> u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 16 h0] -> rw_cells rsegs m (O + 80) csH -> cells_size csH = 136%nat ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 (q + 40 + size)) x22 x23 x24 (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x170a8) fc None m (seg_rom rsegs)).
  Proof.
    intros until csH. intros B F0 L0 F8 F16 L16 F24 F32 L32 WB LW FRBm ST OL LL H0 HH LH SZ BH BND. pose proof sp_rangeB as SR. pose proof q_spB as QSP.
    open_base B. replace (q + 24)%Z with (SP + -376)%Z in F24 by lia. replace (q + 8)%Z with (SP + -392)%Z in F8 by lia.
    pwalk_to 0x16d58%Z.
    replace (SP + -360 + size - (SP + -360) + bh2)%Z with (bh2 + size)%Z by lia.
    replace (SP + -392)%Z with (q + 8)%Z in F8 by lia. replace (SP + -376)%Z with (q + 24)%Z in F24 by lia.
    pose proof (puri_C4C4_C8 m (q + 8) [] bh2 [] F8 ltac:(lia)) as F8'. cbn [app] in F8'.
    destruct (frame5 m c0 _ c16 _ c32 F0 L0 F8' F16 L16 F24 F32 L32) as [FQ LQ].
    destruct (frameA_join m _ wb FQ LQ WB LW) as [jA FRA].
    pose proof (hp_join m _ csH H0 eq_refl HH) as HP.
    destruct (out_join2 m csL _ OL LL HP ltac:(rewrite cells_size_app, LH; reflexivity)) as [junk OUT].
    eapply tail; try eassumption; [close_base | lia].
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma join3 : forall m A nl csl N o csr, rw_cells rsegs m A csl -> cells_size csl = Z.to_nat nl -> (0 <= nl)%Z ->
    rw_cells rsegs m (A + nl) [CB N o] -> rw_cells rsegs m (A + nl + Z.of_nat N) csr -> rw_cells rsegs m A (csl ++ CB N o :: csr).
  Proof.
    intros m A nl csl N o csr HL LL NL HO HR. apply rw_cells_app. split; [exact HL|]. rewrite LL, Z2Nat.id by lia.
    change (CB N o :: csr) with ([CB N o] ++ csr). apply rw_cells_app. split; [exact HO|]. cbn [cells_size csize]. rewrite Nat.add_0_r. exact HR.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma inet : forall (bh2 size af srv nl : Z) (N : nat) (host oj : list byte)
      x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x19 x20 x22 x26 x27 x28 x29 x30 x31
      m c0 c32 wb csL h0 csl csr,
    baseP m -> rw_cells rsegs m q c0 -> cells_size c0 = 8%nat -> rw_cells rsegs m (q + 8) [C4 (Z_to_bv 64 bh2); C4 (Z_to_bv 64 0)] ->
    rw_cells rsegs m (q + 16) [C8 (Z_to_bv 64 (O + 64))] -> rw_cells rsegs m (q + 24) [C8 (Z_to_bv 64 (U + bh2))] ->
    rw_cells rsegs m (q + 32) c32 -> cells_size c32 = 8%nat -> u8arr rsegs m (q + 40) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 16 h0] ->
    rw_cells rsegs m (O + 80) csl -> cells_size csl = Z.to_nat nl -> (0 <= nl)%Z ->
    rw_cells rsegs m (O + 80 + nl) [CB N oj] ->
    rw_cells rsegs m (O + 80 + nl + Z.of_nat N) csr -> (nl + Z.of_nat N + Z.of_nat (cells_size csr) = 136)%Z ->
    ((af = 2 /\ 4 <= Z.of_nat N) \/ (af = 10 /\ N = 16%nat))%Z ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 40 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 296)%Z ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 (Z_to_bv 64 (16 + nl)) x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 (q + 40 + size)) x22 (Z_to_bv 64 srv) (Z_to_bv 64 af) (Z_to_bv 64 1) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x17090) fc None m (seg_rom rsegs)).
  Proof.
    intros until csr. intros B F0 L0 F8 F16 F24 F32 L32 WB LW FRBm ST OL LL H0 HL LLl NL OC HR SUM AF HOST SRV1 SRV2 SZ BH BND.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    pose proof (rw_cells_bound _ _ _ _ HR) as RB.
    replace (q + 16)%Z with (SP + -384)%Z in F16 by lia.
    pwalk_to 0x170a0%Z. step.
    callq (inet_pton_call q lo af srv (O + 80 + nl)%Z host oj N canary).
    all: side (first [exact HOST | exact OC | exact AF | exact GOT | exact CAN | exact ST | exact MI | reflexivity | (f_equal; lia) | lia]).
    match goal with H : rw_cells _ _ (O + 80 + nl)%Z [CB N ?o] |- _ => rename H into OC' end.
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    match goal with H : (?r = 0 \/ ?r = 1)%Z |- _ => rename H into R01 end.
    lazymatch type of OC' with rw_cells _ ?m' _ [CB _ ?outs] =>
      pose proof (join3 m' (O + 80)%Z nl csl N outs csr HL LLl NL OC' HR) as HH;
      assert (LH : cells_size (csl ++ CB N outs :: csr) = 136%nat) by (rewrite cells_size_app; cbn [cells_size csize]; lia) end.
    replace (SP + -384)%Z with (q + 16)%Z in F16 by lia.
    pwalk_to 0x170a8%Z. if_cases K0; zify_cond K0.
    -   pose proof (puri_C4C4_C8 _ (q + 8) [] bh2 [] F8 ltac:(lia)) as F8'. cbn [app] in F8'.
        destruct (frame5 _ c0 _ [C8 (Z_to_bv 64 (O + 64))] _ c32 F0 L0 F8' F16 eq_refl F24 F32 L32) as [FQ LQ].
        pwalk_to 0x170dc%Z.
        eapply (fail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ csL ([CB 16 h0] ++ _)); try eassumption.
      + close_base.
      + apply hp_join; [exact H0| reflexivity| exact HH].
      + cbn [cells_size csize app] in *. lia.
    -   replace (SP + -360 + size)%Z with (q + 40 + size)%Z by lia.
        eapply hpend; try eassumption; try reflexivity; try LiaTuning.alia. close_base.
  Qed.

End WALK.

