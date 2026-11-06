(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol F_atoi F_htons F_memset F_memmove F_stpncpy F_strncasecmp
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
        F (Z_to_bv 64 0x23b6c) fc None m (seg_rom rsegs)).
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
        F (Z_to_bv 64 0x23f6c) fc None m (seg_rom rsegs)).
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
        F (Z_to_bv 64 0x23e48) fc None m (seg_rom rsegs)).
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
        F (Z_to_bv 64 0x19514) fc None m (seg_rom rsegs)).
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

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (U O ulen : Z) (ustr slack : list byte) (canary gifv : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis USL : Z.of_nat (length ustr) = ulen.
  Hypothesis ULR : (0 <= ulen < 2^31)%Z.
  Hypothesis PAD : ((- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis U4K : (4096 <= U)%Z.
  Hypothesis ULO : (U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 912)%Z.
  Hypothesis OSP : (bv_unsigned sp <= O)%Z.
  Hypothesis OHI : (O + 216 <= 2^62)%Z.
  Hypothesis SPH : (bv_unsigned sp + 2^41 <= 2^63)%Z.
  Hypothesis TP1 : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis TP2 : (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 912)%Z.
  Hypothesis SGLO : (ssp_guard + 8 <= bv_unsigned sp - 912)%Z.
  Hypothesis GSLO : (got_ssp + 8 <= bv_unsigned sp - 912)%Z.
  Hypothesis GFLO : (GIF + 4 <= bv_unsigned sp - 912)%Z.
  Hypothesis DE1 : (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE2 : (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE3 : (bv_unsigned tp - 164 + 4 <= GOT_GIF \/ GOT_GIF + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE4 : (bv_unsigned tp - 164 + 4 <= GIF \/ GIF + 4 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE5 : (bv_unsigned tp - 164 + 4 <= U \/ U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned tp - 164)%Z.

  Notation SP := (bv_unsigned sp).
  Notation q := (bv_unsigned sp + -384)%Z.
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -384)).
  Notation lo := (bv_unsigned sp - 912)%Z.
  Notation TPE := (bv_unsigned tp - 164)%Z.
  Notation W := [(bv_unsigned sp - 912, bv_unsigned sp); (O, O + 216); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.
  Notation POST := (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U O ustr slack canary gifv m0).
  Notation USTR m := (bytes_at rsegs m U (ustr ++ Z_to_bv 8 0 :: slack)).

  Notation baseP := (base U O ustr slack canary gifv sp tp m0).

  Notation FRB m := (rw_cells rsegs m (q + 280) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac open_base B :=
    let errv := fresh "errv" in
    destruct B as (USTR & [errv ERR] & GOT & CAN & GIFP & GIFV & MI & MU & WM).
  Ltac close_base :=
      split; [assumption|]; split; [eexists; eassumption|]; repeat (split; [assumption|]); assumption.

  #[using="U ulen slack ULR U4K ULO SPH"] Lemma sp_rangeB : (912 <= SP /\ SP + 2^41 <= 2^63)%Z.
  Proof. clear -ULR U4K ULO SPH. pose proof (word_lt64 sp). lia. Qed.
  #[using="U ulen ustr slack ULR U4K ULO SPH GFLO"] Lemma q_spB : bv_unsigned spw = q.
  Proof. pose proof sp_rangeB. apply unsigned_lit. lia. Qed.

  #[using="Type"] Lemma frameA_join : forall m cs wb, rw_cells rsegs m q cs -> cells_size cs = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    exists jA, rw_cells rsegs m q [CB 280 jA].
  Proof.
    intros m cs wb H L WB LW. apply rw_cells_of_u8arr in WB. rewrite LW in WB.
    assert (J : rw_cells rsegs m q (cs ++ [CB 256 wb])). { apply rw_cells_app. rewrite L. split; [exact H| exact WB]. }
    destruct (rw_cells_forget rsegs m q _ J) as [jA JA]. rewrite cells_size_app, L in JA. cbn in JA. exists jA. exact JA.
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
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat -> rw_cells rsegs m (O + 64) csH -> cells_size csH = 152%nat ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16680) fc None m (seg_rom rsegs)).
  Proof.
    intros until csH. intros B FQ LQ WB LW FRBm ST OL LL OH LH. pose proof sp_rangeB as SR.
    destruct (frameA_join m csq wb FQ LQ WB LW) as [jA FRA]. destruct (out_join2 m csL csH OL LL OH LH) as [junk OUT].
    open_base B. zstep. zstep. eapply epilogue; try eassumption. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma hpend : forall (bh2 size : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x27 x28 x29 x30 x31
      m csq wb csL h0 csH,
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 16 h0] -> rw_cells rsegs m (O + 80) csH -> cells_size csH = 136%nat ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 (Z_to_bv 64 bh2) (Z_to_bv 64 size) x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16694) fc None m (seg_rom rsegs)).
  Proof.
    intros until csH. intros B FQ LQ WB LW FRBm ST OL LL H0 HH LH SZ BH BND. pose proof sp_rangeB as SR.
    destruct (frameA_join m csq wb FQ LQ WB LW) as [jA FRA]. clear FQ WB.
    open_base B.
    zstep. rewrite Z.add_0_r. rewrite (HttpTac.swrap32_id size) by lia.
    sstep. sstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. lia. }
    zstep. zstep.
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

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma inet : forall (bh2 size af srv nl : Z) (N : nat) (host oj : list byte)
      x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x19 x20 x22 x25 x26 x27 x28 x29 x30 x31
      m csq wb csL h0 csl csr,
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 16 h0] ->
    rw_cells rsegs m (O + 80) csl -> cells_size csl = Z.to_nat nl -> (0 <= nl)%Z ->
    rw_cells rsegs m (O + 80 + nl) [CB N oj] ->
    rw_cells rsegs m (O + 80 + nl + Z.of_nat N) csr -> (nl + Z.of_nat N + Z.of_nat (cells_size csr) = 136)%Z ->
    ((af = 2 /\ 4 <= Z.of_nat N) \/ (af = 10 /\ N = 16%nat))%Z ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 24 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 280)%Z ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 af) x11 (Z_to_bv 64 (O + 80 + nl)) x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 srv) x22 (Z_to_bv 64 bh2) (Z_to_bv 64 size) x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16674) fc None m (seg_rom rsegs)).
  Proof.
    intros until csr. intros B FQ LQ WB LW FRBm ST OL LL H0 HL LLl NL OC HR SUM AF HOST SRV1 SRV2 SZ BH BND.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    pose proof (rw_cells_bound _ _ _ _ HR) as RB.
    zstep. zstep.
    callq (inet_pton_call q lo af srv (O + 80 + nl)%Z host oj N canary).
    all: side (first [exact HOST | exact OC | exact AF | exact GOT | exact CAN | exact ST | exact MI | reflexivity | lia]).
    match goal with H : rw_cells _ _ (O + 80 + nl)%Z [CB N ?o] |- _ => rename H into OC' end.
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    match goal with H : (?r = 0 \/ ?r = 1)%Z |- _ => rename H into R01 end.
    lazymatch type of OC' with rw_cells _ ?m' _ [CB _ ?outs] =>
      pose proof (join3 m' (O + 80)%Z nl csl N outs csr HL LLl NL OC' HR) as HH;
      assert (LH : cells_size (csl ++ CB N outs :: csr) = 136%nat) by (rewrite cells_size_app; cbn [cells_size csize]; lia) end.
    zstep. if_cases K0; zify_cond K0.
    -   eapply hpend; try eassumption; try LiaTuning.alia. close_base.
    -   eapply (fail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ csL ([CB 16 h0] ++ _)); try eassumption.
      + close_base.
      + apply hp_join; [exact H0| reflexivity| exact HH].
      + cbn [cells_size csize app] in *. lia.
  Qed.

  #[using="Type"] Lemma split4 : forall m A l0 l1 l2 l3, rw_cells rsegs m A (l0 ++ l1 ++ l2 ++ l3) ->
    rw_cells rsegs m A l0 /\ rw_cells rsegs m (A + Z.of_nat (cells_size l0)) l1
    /\ rw_cells rsegs m (A + Z.of_nat (cells_size l0) + Z.of_nat (cells_size l1)) l2
    /\ rw_cells rsegs m (A + Z.of_nat (cells_size l0) + Z.of_nat (cells_size l1) + Z.of_nat (cells_size l2)) l3.
  Proof.
    intros m A l0 l1 l2 l3 H. apply rw_cells_app in H. destruct H as [H0 H]. apply rw_cells_app in H. destruct H as [H1 H].
    apply rw_cells_app in H. destruct H as [H2 H3]. auto.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma v6fill : forall (bh2 size srv : Z) (pw : word) (host h hr : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x25 x26 x27 x28 x29 x30 x31
      m csq wb csL,
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 144 h; C2 pw; CB 6 hr] ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 24 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 280)%Z ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 pw (Z_to_bv 64 srv) x22 (Z_to_bv 64 bh2) (Z_to_bv 64 size) x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16644) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B FQ LQ WB LW FRBm ST OL LL HP HOST SRV1 SRV2 SZ BH BND.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    pose proof (word_lt64 pw) as PW.
    zstep. sstep. zstep. zstep.
    change 65535%Z with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^16) ltac:(lia)) as P16.
    zstep. call htons_spec. all: side (rewrite ?unsigned_lit by lia; first [exact MI | lia]).
    rewrite unsigned_lit by lia.
    zstep. zstep. zstep. sstep. sstep. zstep. zstep.
    lazymatch type of HP with rw_cells _ ?m' _ [?c0; ?c1; ?c2; CB 20 ?d; ?c4; ?c5; ?c6; ?c7] =>
      pose proof (rw_cells_split_CB rsegs m' (O + 64) [c0; c1; c2] 20 d [c4; c5; c6; c7] [4; 16]%nat HP eq_refl) as HP'; clear HP;
      cbn [mk_CB_cells app] in HP';
      lazymatch type of HP' with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?cN; ?c4; ?c5; ?c6; ?c7] =>
        change (rw_cells rsegs m' (O + 64) ([c0] ++ [c1; c2; c3] ++ [cN] ++ [c4; c5; c6; c7])) in HP' end end.
    apply split4 in HP'. destruct HP' as (H0 & HL & OC & HR). cbn [cells_size csize Nat.add] in HL, OC, HR.
    change (Z.of_nat 16) with 16%Z in *. change (Z.of_nat 8) with 8%Z in *.
    replace (O + 64 + 16)%Z with (O + 80)%Z in HL by lia. replace (O + 64 + 16 + 8)%Z with (O + 80 + 8)%Z in OC by lia.
    replace (O + 64 + 16 + 8 + 16)%Z with (O + 80 + 8 + Z.of_nat 16)%Z in HR by lia.
    replace (Z_to_bv 64 (O + 88)) with (Z_to_bv 64 (O + 80 + 8)) by (f_equal; lia).
    eapply inet; try eassumption; try reflexivity; try lia. close_base.
  Qed.

  Ltac hp144_split HP :=
    lazymatch type of HP with rw_cells _ ?m' _ [CB 144 ?d; ?c1; ?c2] =>
      pose proof (rw_cells_split_CB rsegs m' (O + 64) [] 144 d [c1; c2] [16; 128]%nat HP eq_refl) as HP'; clear HP;
      cbn [mk_CB_cells app] in HP';
      lazymatch type of HP' with rw_cells _ _ _ [?c0; ?cA; ?cB; ?cC] =>
        change (rw_cells rsegs m' (O + 64) ([c0] ++ [cA; cB; cC])) in HP' end;
      apply rw_cells_app in HP'; destruct HP' as [H0 HH]; cbn [cells_size csize Nat.add] in HH; change (Z.of_nat 16) with 16%Z in HH;
      replace (O + 64 + 16)%Z with (O + 80)%Z in HH by lia end.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma afsw : forall (bh2 size srv af e8 : Z) (pw : word) (host h : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x26 x27 x28 x29 x30 x31
      m csq wb csL,
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 24 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 280)%Z ->
    (0 <= size <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + size <= ulen)%Z -> (af = 0 \/ af = 2 \/ af = 10)%Z -> (e8 = q + 24 + size)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 pw (Z_to_bv 64 srv) x22 (Z_to_bv 64 bh2) (Z_to_bv 64 e8) (Z_to_bv 64 af) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16604) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B FQ LQ WB LW FRBm ST OL LL HP HOST SRV1 SRV2 SZ BH BND AF ->.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    pose proof (word_lt64 pw) as PW.
    zstep. zstep. zstep. sstep.
    zstep. if_cases K0; zify_cond K0.
    {   replace af with 10%Z by lia. eapply v6fill; try eassumption; try LiaTuning.alia. close_base. }
    zstep. zstep. if_cases K1; zify_cond K1.
    {
      lazymatch type of HP with rw_cells _ ?m' _ [CB 144 ?d; ?c1; ?c2] =>
        pose proof (rw_cells_split_CB rsegs m' (O + 64) [] 144 d [c1; c2] [16; 128]%nat HP eq_refl) as HP'; clear HP;
        cbn [mk_CB_cells app] in HP';
        lazymatch type of HP' with rw_cells _ _ _ [?c0; ?cA; ?cB; ?cC] =>
          change (rw_cells rsegs m' (O + 64) ([c0] ++ [cA; cB; cC])) in HP' end end.
      apply rw_cells_app in HP'. destruct HP' as [H0 HH]. cbn [cells_size csize Nat.add] in HH. change (Z.of_nat 16) with 16%Z in HH.
      replace (O + 64 + 16)%Z with (O + 80)%Z in HH by lia.
      eapply hpend; try eassumption; try reflexivity; try lia. close_base. }

    replace af with 2%Z by lia.
    sstep. zstep. zstep.
    change 65535%Z with (Z.ones 16). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^16) ltac:(lia)) as P16.
    zstep. call htons_spec. all: side (rewrite ?unsigned_lit by lia; first [exact MI | lia]).
    rewrite unsigned_lit by lia.
    sstep. zstep. zstep. zstep.
    lazymatch type of HP with rw_cells _ ?m' _ [?c0; ?c1; ?c2; CB 124 ?d; ?c6; ?c7] =>
      pose proof (rw_cells_split_CB rsegs m' (O + 64) [c0; c1; c2] 124 d [c6; c7] [4; 120]%nat HP eq_refl) as HP'; clear HP;
      cbn [mk_CB_cells app] in HP';
      lazymatch type of HP' with rw_cells _ _ _ [?c0; ?c1; ?c2; ?cN; ?c4; ?c6; ?c7] =>
        change (rw_cells rsegs m' (O + 64) ([c0] ++ [c1; c2] ++ [cN] ++ [c4; c6; c7])) in HP' end end.
    apply split4 in HP'. destruct HP' as (H0 & HL & OC & HR). cbn [cells_size csize Nat.add] in HL, OC, HR.
    change (Z.of_nat 16) with 16%Z in *. change (Z.of_nat 4) with 4%Z in *.
    replace (O + 64 + 16)%Z with (O + 80)%Z in HL by lia. replace (O + 64 + 16 + 4)%Z with (O + 80 + 4)%Z in OC by lia.
    replace (O + 64 + 16 + 4 + 4)%Z with (O + 80 + 4 + Z.of_nat 4)%Z in HR by lia.
    replace (Z_to_bv 64 (O + 84)) with (Z_to_bv 64 (O + 80 + 4)) by (f_equal; lia).
    eapply inet; try eassumption; try reflexivity; try lia. close_base.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma dig_land : forall c, (0 <= c < 256 -> Z.land (c + -48) 18446744073709551615 < 10 -> 48 <= c < 58)%Z.
  Proof.
    intros c Hc H. change 18446744073709551615%Z with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
    destruct (Z.lt_ge_cases c 48).
    - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
    - rewrite Z.mod_small in H by lia. lia.
  Qed.
  #[using="U ulen ustr slack ULR"] Lemma nodig_land : forall c, (0 <= c < 256 -> ~ (Z.land (c + -48) 18446744073709551615 < 10) -> ~ (48 <= c < 58))%Z.
  Proof.
    intros c Hc H Hd. apply H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wrap_sub_lt : forall c a n, (0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
    Z.land (c + a) 18446744073709551615 < n -> - a <= c < - a + n)%Z.
  Proof.
    intros c a n Hc Ha Hn H. change 18446744073709551615%Z with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
    destruct (Z.lt_ge_cases c (- a)).
    - rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
    - rewrite Z.mod_small in H by lia. lia.
  Qed.
  #[using="U ulen ustr slack ULR"] Lemma wrap_sub_ge : forall c a n, (0 <= c < 2^32 -> - 2^32 < a <= 0 -> 0 <= n < 2^32 ->
    ~ (Z.land (c + a) 18446744073709551615 < n) -> ~ (- a <= c < - a + n))%Z.
  Proof.
    intros c a n Hc Ha Hn H Hd. apply H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
    rewrite Z.mod_small by lia. lia.
  Qed.
  #[using="Type"] Lemma is_alnum_nz : forall c, is_alnum c = true -> c <> 0%Z.
  Proof. intros c H ->. discriminate H. Qed.

  #[using="Type"] Lemma firstn_S_snoc : forall (l : list byte) n x, nth_error l n = Some x -> firstn (S n) l = firstn n l ++ [x].
  Proof.
    induction l as [|a l IH]; intros n x H; [destruct n; discriminate|].
    destruct n as [|n]; cbn in H |- *. { injection H as ->. reflexivity. } rewrite (IH n x H). reflexivity.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_string : forall m wb (a z : Z),
    u8arr rsegs m (q + 24) wb -> length wb = 256%nat -> (0 <= a <= z)%Z -> (z <= 255)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    bytes_at rsegs m (q + 24 + a) (firstn (Z.to_nat (z - a)) (skipn (Z.to_nat a) wb) ++ [Z_to_bv 8 0])
    /\ length (firstn (Z.to_nat (z - a)) (skipn (Z.to_nat a) wb)) = Z.to_nat (z - a).
  Proof.
    intros m wb a z [B _] L A Z0 NZ. split.
    - rewrite <- (firstn_S_snoc (skipn (Z.to_nat a) wb) (Z.to_nat (z - a)) (Z_to_bv 8 0)).
      2:{ rewrite nth_error_skipn. replace (Z.to_nat a + Z.to_nat (z - a))%nat with (Z.to_nat z) by lia. exact NZ. }
      rewrite <- (firstn_skipn (Z.to_nat a) wb) in B. apply bytes_at_app in B. destruct B as [_ B].
      rewrite firstn_length, Nat.min_l in B by lia. rewrite Z2Nat.id in B by lia.
      rewrite <- (firstn_skipn (S (Z.to_nat (z - a))) (skipn (Z.to_nat a) wb)) in B. apply bytes_at_app in B. destruct B as [B _]. exact B.
    - rewrite firstn_length, skipn_length, L. lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_nth : forall (wb : list byte) i, length wb = 256%nat -> (0 <= i <= 255)%Z -> exists b, nth_error wb (Z.to_nat i) = Some b.
  Proof.
    intros wb i L Hi. destruct (nth_error wb (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. lia.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma port : forall (bh2 p0 z srv af e6 : Z) (host h : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x24 x26 x27 x28 x29 x30 x31
      m csq wb csL,
    baseP m -> rw_cells rsegs m q csq -> cells_size csq = 24%nat -> u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    bytes_at rsegs m srv (host ++ [Z_to_bv 8 0]) -> (q + 24 <= srv)%Z -> (srv + Z.of_nat (length host) + 1 <= q + 280)%Z ->
    (0 <= p0 < z)%Z -> (z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (af = 0 \/ af = 2 \/ af = 10)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j b, (p0 < j < z)%Z -> nth_error wb (Z.to_nat j) = Some b -> bv_unsigned b <> 0%Z) ->
    (e6 = q + 24 + p0 + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 srv) (Z_to_bv 64 e6) (Z_to_bv 64 bh2) x24 (Z_to_bv 64 af) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x165b8) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B FQ LQ WB LW FRBm ST OL LL HP HOST SRV1 SRV2 P0 Z0 BH BND AF WZ WNZ E6.
    replace e6 with (SP + -360 + p0 + 1)%Z by lia. clear e6 E6.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    pose proof (bytes_at_bound _ _ _ _ HOST) as HB. rewrite app_length in HB. cbn [length] in HB.
    destruct (wb_string m wb (p0 + 1) z WB LW ltac:(lia) ltac:(lia) WZ) as [PSTR PL].
    set (pstr := firstn (Z.to_nat (z - (p0 + 1))) (skipn (Z.to_nat (p0 + 1)) wb)) in PSTR, PL. clearbody pstr.
    replace (q + 24 + (p0 + 1))%Z with (SP + -360 + p0 + 1)%Z in PSTR by lia.

    assert (EXIT : forall (p' e8 : Z) y11,
      (p0 + 1 <= p' <= z)%Z -> (e8 = q + 24 + p')%Z ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 10) y11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 srv) (Z_to_bv 64 (SP + -360 + p0 + 1)) (Z_to_bv 64 bh2) (Z_to_bv 64 e8) (Z_to_bv 64 af) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x165d0) fc None m (seg_rom rsegs))).
    { intros p' e8 y11 HP' E8.
      zstep. zstep. zstep. zstep.
      unfold got_ssp, ssp_guard in *.
      callq (strtol10_call q lo (SP + -360 + p0 + 1)%Z pstr errv canary).
      all: side (first [exact PSTR | exact ERR | exact GOT | exact CAN | exact ST | exact MI | reflexivity | (f_equal; lia) | (unfold got_ssp, ssp_guard, STRTOL_DEPTH in *; lia)]).
      match goal with H : rw_cells _ _ TPE _ |- _ => rename H into ERR end.
      match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      {   eapply fail; try eassumption; try reflexivity. close_base. }
      zstep. zstep. call (atoi_spec). all: side (first [eassumption | lia]).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      {   eapply fail; try eassumption; try reflexivity. close_base. }
      eapply (afsw bh2 p'); try eassumption; try LiaTuning.alia. close_base. }
    assert (LOOP : forall (k : nat) (p e8 : Z) y11, (z - p < Z.of_nat k)%Z -> (p0 <= p < z)%Z -> (e8 = q + 24 + p)%Z ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 10) y11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 (Z_to_bv 64 srv) (Z_to_bv 64 (SP + -360 + p0 + 1)) (Z_to_bv 64 bh2) (Z_to_bv 64 e8) (Z_to_bv 64 af) x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x165c0) fc None m (seg_rom rsegs))).
    { induction k as [|k IH]; intros p e8 y11 HK HPp E8; [lia|].
      destruct (wb_nth wb (p + 1) LW ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
      pose proof (u8arr_read rsegs m _ wb (p + 1) b (Z_to_bv 64 (e8 + 1)) WB Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
      -
        assert (p + 1 <> z)%Z.
        { intros E. rewrite E, WZ in Hb. injection Hb as Hb'. subst b. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z in K0. apply dig_land in K0; lia. }
        eapply (IH (p + 1)%Z); lia.
      - eapply (EXIT (p + 1)%Z); lia. }
    zstep. zstep. eapply (LOOP (S (Z.to_nat (z - p0))) p0); lia.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v4exit : forall (bh2 z j c ld e6 defport : Z) (bc : byte) (h j0 : list byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x25 x27 x28 x29 x30 x31
      m wb csL,
    baseP m -> rw_cells rsegs m q [CB 8 j0; C8 (Z_to_bv 64 defport); C8 (Z_to_bv 64 (U + bh2))] ->
    u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (0 <= j <= z)%Z -> (z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^64)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    nth_error wb (Z.to_nat j) = Some bc -> c = bv_unsigned bc ->
    (ld = 0 \/ exists d, ld = q + 24 + d /\ 0 <= d < j)%Z ->
    (e6 = q + 24 + j + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 (Z_to_bv 64 bh2) (Z_to_bv 64 ld) (Z_to_bv 64 e6) x23 (Z_to_bv 64 j) x25 (Z_to_bv 64 c) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16550) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros B FQ WB LW FRBm ST OL LL HP J Z0 BH BND DP WZ WNZ Hbc Hc LD E6.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B. pose proof (byte_range bc) as BR.
    pose proof (u8arr_store_ok rsegs _ _ _ j (Z_to_bv 64 (e6 + -1)) WB ltac:(rewrite LW; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
    replace (Z_to_bv 64 (e6 + -1)) with (wa (q + 24 + j)) by (unfold wa; f_equal; lia).
    pose proof (u8arr_write rsegs _ _ _ j (Z_to_bv 8 0) WB ltac:(rewrite LW; lia)) as WB2. clear WB. store_done.
    set (wb' := upd wb (Z.to_nat j) (Z_to_bv 8 0)) in WB2.
    assert (LW' : length wb' = 256%nat) by (subst wb'; rewrite upd_length; exact LW).
    assert (WZj : nth_error wb' (Z.to_nat j) = Some (Z_to_bv 8 0)) by (subst wb'; apply nth_error_upd_same; rewrite LW; lia).
    assert (WOTH : forall i, i <> Z.to_nat j -> nth_error wb' i = nth_error wb i) by (intros i Hi; subst wb'; apply nth_error_upd_other; lia).
    clearbody wb'.

    destruct (wb_string _ wb' 0 j WB2 LW' ltac:(lia) ltac:(lia) WZj) as [HOST HL]. rewrite Z.sub_0_r in HOST, HL.
    set (host := firstn (Z.to_nat j) (skipn (Z.to_nat 0) wb')) in HOST, HL. clearbody host.
    replace (q + 24 + 0)%Z with (SP + -360)%Z in HOST by lia.

    assert (WZ' : c <> 0%Z -> nth_error wb' (Z.to_nat z) = Some (Z_to_bv 8 0)).
    { intros Hc0. rewrite WOTH; [exact WZ|]. intros E. assert (j = z) by lia. subst j c. rewrite WZ in Hbc. injection Hbc as <-. apply Hc0. reflexivity. }
    assert (JZ : c <> 0%Z -> (j < z)%Z).
    { intros Hc0. destruct (Z.eq_dec j z); [|lia]. subst j c. rewrite WZ in Hbc. injection Hbc as <-. exfalso. apply Hc0. reflexivity. }
    assert (WNZ' : forall j' b, (j < j' < z)%Z -> nth_error wb' (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z).
    { intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
    destruct LD as [-> | (d & -> & Hd)].
    -
      zstep. if_cases K0; zify_cond K0; [| exfalso; clear -K0; cbn in K0; lia].
      zstep. zstep. zstep. if_cases K1; zify_cond K1.
      +
        zstep. sstep. zstep. hp144_split HP.
        eapply (hpend bh2 j); try eassumption; try reflexivity; try lia. close_base.
      +
        zstep. zstep. zstep.
        eapply (port bh2 j z _ 0 e6 host h); try eassumption; try reflexivity; try (rewrite ?HL; lia). all: pg. close_base. apply WZ'; lia.
    -
      zstep. if_cases K0; zify_cond K0.
      { exfalso. clear -K0 SR Hd. lia. }
      destruct (wb_nth wb' (d + 1) LW' ltac:(lia)) as [bd Hbd]. pose proof (byte_range bd) as BRd.
      pose proof (u8arr_read rsegs _ _ wb' (d + 1) bd (Z_to_bv 64 (q + 24 + d + 1)) WB2 Hbd ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. zstep.
      match goal with |- context [Z_to_bv 64 (Z.shiftl (Z.b2z ?b) 1)] =>
        set (af := Z.shiftl (Z.b2z b) 1); assert (AF : (af = 0 \/ af = 2 \/ af = 10)%Z) by (subst af; clear; destruct b; [right; left | left]; reflexivity); clearbody af end.
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      +
        zstep. eapply (port bh2 j z _ af e6 host h); try eassumption; try reflexivity; try (rewrite ?HL; lia). close_base. apply WZ'; lia.
      +
        zstep. zstep. zstep. zstep.
        eapply (afsw bh2 j _ af); try eassumption; try reflexivity; try (rewrite ?HL; lia). close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v4loop : forall (bh2 z defport : Z) (h j0 : list byte) m wb csL (k : nat) (j c ld e6 : Z) (bc : byte)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 8 j0; C8 (Z_to_bv 64 defport); C8 (Z_to_bv 64 (U + bh2))] ->
    u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^64)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    (z - j < Z.of_nat k)%Z -> (0 <= j <= z)%Z ->
    nth_error wb (Z.to_nat j) = Some bc -> c = bv_unsigned bc ->
    (ld = 0 \/ exists d, ld = q + 24 + d /\ 0 <= d < j)%Z ->
    (e6 = q + 24 + j + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 46) (Z_to_bv 64 bh2) (Z_to_bv 64 ld) (Z_to_bv 64 e6) (Z_to_bv 64 2) (Z_to_bv 64 j) (Z_to_bv 64 47) (Z_to_bv 64 c) (Z_to_bv 64 58) x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16528) fc None m (seg_rom rsegs)).
  Proof.
    intros until csL. intros k. induction k as [|k IH]; intros until x31; intros B FQ WB LW FRBm ST OL LL HP Z0 BH BND DP WZ WNZ HK J Hbc Hc LD E6; [lia|].
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. pose proof (byte_range bc) as BR.
    pose proof B as B0. open_base B.
    zstep. if_cases K0; zify_cond K0.
    {   eapply v4exit; try eassumption; try LiaTuning.alia. }
    zstep. if_cases K1; zify_cond K1.
    {   eapply v4exit; try eassumption; try LiaTuning.alia. }
    zstep. replace (Z.land c 255) with c by (subst c; change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
    zstep. call isalnum_spec. all: side (rewrite ?unsigned_lit by lia; first [exact MI | lia]).
    rewrite unsigned_lit by lia.

    assert (ADV : forall (e5 : Z) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31, (e5 = 0 \/ exists d, e5 = q + 24 + d /\ 0 <= d < j + 1)%Z -> c <> 0%Z ->
      evt rsegs POST (MS (mkR (Z_to_bv 64 91448) spw gp tp y5 y6 y7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 U) (Z_to_bv 64 46) (Z_to_bv 64 bh2) (Z_to_bv 64 e5) (Z_to_bv 64 e6) (Z_to_bv 64 2) (Z_to_bv 64 j) (Z_to_bv 64 47) (Z_to_bv 64 c) (Z_to_bv 64 58) y28 y29 y30 y31)
                        F (Z_to_bv 64 0x1651c) fc None m (seg_rom rsegs))).
    { intros until y31. intros LD' Hc0.
      assert (JZ : (j < z)%Z).
      { destruct (Z.eq_dec j z); [|lia]. subst j c. rewrite WZ in Hbc. injection Hbc as <-. exfalso. apply Hc0. reflexivity. }
      destruct (wb_nth wb (j + 1) LW ltac:(lia)) as [b' Hb']. pose proof (byte_range b') as BR'.
      pose proof (u8arr_read rsegs _ _ wb (j + 1) b' (Z_to_bv 64 e6) WB Hb' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep. zstep.
      eapply (IH (j + 1)%Z); try eassumption; try LiaTuning.alia. }

    assert (DASH : forall y10 y11, (c = 45 \/ c = 46 \/ is_alnum c = true)%Z ->
      evt rsegs POST (MS (mkR (Z_to_bv 64 91448) spw gp tp x x0 x2 (Z_to_bv 64 O) (Z_to_bv 64 ulen) y10 y11 x4 x8 x9 x18 x19 x20
                            (Z_to_bv 64 U) (Z_to_bv 64 46) (Z_to_bv 64 bh2) (Z_to_bv 64 ld) (Z_to_bv 64 e6) (Z_to_bv 64 2) (Z_to_bv 64 j) (Z_to_bv 64 47) (Z_to_bv 64 c) (Z_to_bv 64 58) x21 x22 x23 x24)
                        F (Z_to_bv 64 0x16544) fc None m (seg_rom rsegs))).
    { intros y10 y11 HC.
      assert (Hc0 : c <> 0%Z). { destruct HC as [-> | [-> | HA]]; [lia| lia| apply is_alnum_nz; exact HA]. }
      zstep. if_cases K3; zify_cond K3.
      -   eapply ADV; [| exact Hc0]. destruct LD as [-> | (d & -> & Hd)]; [left; reflexivity | right; exists d; lia].
      -   zstep. zstep. eapply ADV; [| exact Hc0]. right. exists j. lia. }
    zstep. zstep. if_cases K2; zify_cond K2.
    {   apply wrap_sub_lt in K2; [|lia|lia|lia]. apply DASH. lia. }
    zstep. if_cases K4; zify_cond K4.
    {   eapply v4exit; try eassumption; try LiaTuning.alia. }
    apply DASH. right. right. first [exact K4 | destruct (is_alnum c); [reflexivity| exfalso; first [discriminate | apply K4; reflexivity]]].
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v4 : forall (bh2 z defport c0 : Z) (b0 : byte) (h jq : list byte) m wb csL
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 24 jq] ->
    u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (0 <= z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^64)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    nth_error wb 0%nat = Some b0 -> c0 = bv_unsigned b0 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 defport) x21 x22 (Z_to_bv 64 bh2) x24 x25 (Z_to_bv 64 c0) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x164f0) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FQ WB LW FRBm ST OL LL HP Z0 BH BND DP WZ WNZ Hb0 Hc0.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. pose proof (byte_range b0) as BR. open_base B.
    sstep. sstep. do 9 zstep.
    eapply (v4loop bh2 z defport h _ _ wb csL (S (Z.to_nat z)) 0 c0 0 _ b0); try eassumption; try reflexivity; try lia. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma v6 : forall (bh2 z defport : Z) (h jq : list byte) m wb csL
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x24 x25 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 24 jq] ->
    u8arr rsegs m (q + 24) wb -> length wb = 256%nat ->
    FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O csL -> cells_size csL = 64%nat ->
    rw_cells rsegs m (O + 64) [CB 152 h] ->
    (0 <= z <= 255)%Z -> (0 <= bh2)%Z -> (bh2 + z <= ulen)%Z -> (0 <= defport < 2^64)%Z ->
    nth_error wb (Z.to_nat z) = Some (Z_to_bv 8 0) ->
    (forall j' b, (0 <= j' < z)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
    nth_error wb 0%nat = Some (Z_to_bv 8 91) ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 defport) x21 x22 (Z_to_bv 64 bh2) x24 x25 (Z_to_bv 64 91) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x164c0) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FQ WB LW FRBm ST OL LL HP Z0 BH BND DP WZ WNZ Hb0.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B.
    assert (Z1 : (1 <= z)%Z).
    { destruct (Z.eq_dec z 0); [|lia]. exfalso. subst z. change (Z.to_nat 0) with 0%nat in WZ. rewrite WZ in Hb0. injection Hb0 as E. vm_compute in E. lia. }

    assert (FOUND : forall (j e6 e8 : Z) y10 y11,
      (1 <= j < z)%Z -> (e6 = q + 24 + j + 2)%Z -> (e8 = j + 1)%Z -> nth_error wb (Z.to_nat j) = Some (Z_to_bv 8 93) ->
      (forall j' b, (0 <= j' < j)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z) ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) y10 y11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 defport) (Z_to_bv 64 (SP + -359)) (Z_to_bv 64 e6) (Z_to_bv 64 bh2) (Z_to_bv 64 e8) x25 (Z_to_bv 64 91) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16588) fc None m (seg_rom rsegs))).
    { intros j e6 e8 y10 y11 J E6 E8 Hj WNZj. subst e8.
      destruct (wb_nth wb (j + 1) LW ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
      pose proof (u8arr_read rsegs _ _ wb (j + 1) b1 (Z_to_bv 64 (e6 + -1)) WB Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep.
      pose proof (u8arr_store_ok rsegs _ _ _ j (Z_to_bv 64 (e6 + -2)) WB ltac:(rewrite LW; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
      zstep. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
      replace (Z_to_bv 64 (e6 + -2)) with (wa (q + 24 + j)) by (unfold wa; f_equal; lia).
      pose proof (u8arr_write rsegs _ _ _ j (Z_to_bv 8 0) WB ltac:(rewrite LW; lia)) as WB2. clear WB RD. store_done.
      set (wb' := upd wb (Z.to_nat j) (Z_to_bv 8 0)) in WB2.
      assert (LW' : length wb' = 256%nat) by (subst wb'; rewrite upd_length; exact LW).
      assert (WZj : nth_error wb' (Z.to_nat j) = Some (Z_to_bv 8 0)) by (subst wb'; apply nth_error_upd_same; rewrite LW; lia).
      assert (WOTH : forall i, i <> Z.to_nat j -> nth_error wb' i = nth_error wb i) by (intros i Hi; subst wb'; apply nth_error_upd_other; lia).
      clearbody wb'.
      destruct (wb_string _ wb' 1 j WB2 LW' ltac:(lia) ltac:(lia) WZj) as [HOST HL].
      set (host := firstn (Z.to_nat (j - 1)) (skipn (Z.to_nat 1) wb')) in HOST, HL. clearbody host.
      replace (q + 24 + 1)%Z with (SP + -359)%Z in HOST by lia.
      zstep. if_cases K0; zify_cond K0.
      -
        sstep. eapply (v6fill bh2 (j + 1)); try eassumption; try reflexivity; try (rewrite ?HL; lia). close_base.
      -
        assert (J1 : (j + 1 < z)%Z).
        { destruct (Z.eq_dec (j + 1) z) as [e|]; [|lia]. exfalso. rewrite <- e, Hb1 in WZ. injection WZ as ->. revert K0. clear. intros K0. vm_compute in K0. lia. }
        zstep. zstep.
        eapply (port bh2 (j + 1) z _ 10 e6 host h); try eassumption; try reflexivity; try (rewrite ?HL; lia).
        + close_base.
        + rewrite WOTH by lia. exact WZ.
        + intros j' b Hj' Hb. rewrite WOTH in Hb by lia. exact (WNZ j' b ltac:(lia) Hb). }
    assert (LOOP : forall (k : nat) (j e6 e8 c : Z) (bc : byte),
      (z - j < Z.of_nat k)%Z -> (1 <= j <= z)%Z -> nth_error wb (Z.to_nat j) = Some bc -> c = bv_unsigned bc -> c <> 0%Z -> (e6 = q + 24 + j + 2)%Z -> (e8 = j + 1)%Z ->
      evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 93) (Z_to_bv 64 c) x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) (Z_to_bv 64 (U + bh2)) (Z_to_bv 64 defport) (Z_to_bv 64 (SP + -359)) (Z_to_bv 64 e6) (Z_to_bv 64 bh2) (Z_to_bv 64 e8) x25 (Z_to_bv 64 91) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x164d8) fc None m (seg_rom rsegs))).
    { induction k as [|k IH]; intros j e6 e8 c bc HK J Hbc Hc Hc0 E6 E8; [lia|]. pose proof (byte_range bc) as BR.
      assert (JZ : (j < z)%Z).
      { destruct (Z.eq_dec j z); [|lia]. exfalso. subst j c. rewrite WZ in Hbc. injection Hbc as <-. apply Hc0. reflexivity. }
      zstep. if_cases K0; zify_cond K0.
      {   eapply (FOUND j e6 e8); try lia. { subst c. rewrite Hbc. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 93) with 93%Z. lia. }
        intros j' b Hj' Hb. exact (WNZ j' b ltac:(lia) Hb). }
      destruct (wb_nth wb (j + 1) LW ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
      pose proof (u8arr_read rsegs _ _ wb (j + 1) b1 (Z_to_bv 64 (e6 + 1 + -2)) WB Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      - eapply (IH (j + 1)%Z); try eassumption; try LiaTuning.alia.
      - zstep. eapply fail; try eassumption; try reflexivity. close_base. }
    destruct (wb_nth wb 1 LW ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
    pose proof (u8arr_read rsegs _ _ wb 1 b1 (Z_to_bv 64 (SP + -357 + -2)) WB Hb1 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases K0; zify_cond K0.
    {   eapply fail; try eassumption; try reflexivity. close_base. }
    eapply (LOOP (S (Z.to_nat z)) 1); try eassumption; try LiaTuning.alia.
  Qed.

  #[using="U ulen ustr slack canary tp m0 ULR DE1 DE2 DE3 DE4 DE5"] Lemma nul_split : forall (l1 l2 : list byte), exists s r, l1 ++ Z_to_bv 8 0 :: l2 = s ++ Z_to_bv 8 0 :: r /\ ~ In (Z_to_bv 8 0) s /\ (length s <= length l1)%nat.
  Proof.
    induction l1 as [|a l1 IH]; intros l2.
    - exists [], l2. cbn. repeat split; [LiaTuning.ctauto| lia].
    - destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
      + exists [], (l1 ++ Z_to_bv 8 0 :: l2). assert (a = Z_to_bv 8 0) as -> by (apply bv_eq; rewrite E; reflexivity).
        cbn. repeat split; [LiaTuning.ctauto| lia].
      + destruct (IH l2) as (s & r & E & NI & L). exists (a :: s), r. cbn. rewrite E. repeat split; [| cbn in *; lia].
        intros [H|H]; [| exact (NI H)]. apply NE. subst a. reflexivity.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma mod8_shift : forall x d, 0 <= d -> (x + d) mod 8 <= x mod 8 + d.
  Proof.
    intros x d Hd. rewrite <- Z.add_mod_idemp_l by lia. apply Z.mod_le; [| lia]. pose proof (Z.mod_pos_bound x 8). lia.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_nth_lt : forall (str : list byte) j, (j < stpn_k str 255)%nat -> nth_error (stpn_result str 255 ++ [Z_to_bv 8 0]) j = nth_error str j.
  Proof.
    intros str j Hj. unfold stpn_result. pose proof (Nat.le_min_l (length str) 255). unfold stpn_k in *.
    rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
    rewrite nth_error_app1 by (rewrite firstn_length; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec0 j (Nat.min (length str) 255)); [reflexivity| lia].
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma wb_nth_z : forall (str : list byte), nth_error (stpn_result str 255 ++ [Z_to_bv 8 0]) (stpn_k str 255) = Some (Z_to_bv 8 0).
  Proof.
    intros str. unfold stpn_result. pose proof (Nat.le_min_l (length str) 255). pose proof (Nat.le_min_r (length str) 255). unfold stpn_k in *.
    set (k := Nat.min (length str) 255) in *.
    destruct (Nat.eq_dec k 255).
    - rewrite nth_error_app2. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
      rewrite length_app, firstn_length, repeat_length. replace (k - (Nat.min k (length str) + (255 - k)))%nat with 0%nat by lia. reflexivity.
    - rewrite nth_error_app1. 2:{ rewrite length_app, firstn_length, repeat_length. lia. }
      rewrite nth_error_app2 by (rewrite firstn_length; lia). rewrite firstn_length.
      replace (k - Nat.min k (length str))%nat with 0%nat by lia.
      destruct (255 - k)%nat eqn:E; [lia|]. reflexivity.
  Qed.

  #[using="U ulen ustr slack ULR"] Lemma u8arr_snoc1 : forall m A bs b, u8arr rsegs m A bs -> rw_cells rsegs m (A + Z.of_nat (length bs)) [C1 b] -> u8arr rsegs m A (bs ++ [b]).
  Proof.
    intros m A bs b [B W] [[_ B1] W1]. cbn [cells_bytes cbytes cells_size csize app Nat.add] in B1, W1. split.
    - apply bytes_at_app. split; [exact B| exact B1].
    - rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. apply (proj2 (wr_at_app rsegs m A (Z.of_nat (length bs)) (Z.of_nat 1) ltac:(lia) ltac:(lia))). split; [exact W| exact W1].
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma hp : forall (bh2 defport : Z) m jA junk
      x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 280 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 216 junk] ->
    (0 <= bh2 <= ulen)%Z -> (0 <= defport < 2^16)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 (Z_to_bv 64 (O + 64)) x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 (Z_to_bv 64 defport) x21 x22 (Z_to_bv 64 bh2) x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x1648c) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FRA FRBm ST OUT BH DP.
    pose proof sp_rangeB as SR. pose proof q_spB as QSP. open_base B. pose proof USTR_len as UL.

    pose proof (rw_cells_split_CB rsegs m O [] 216 junk [] [64; 152]%nat OUT eq_refl) as OUT'. cbn [mk_CB_cells app] in OUT'. clear OUT.
    lazymatch type of OUT' with rw_cells _ _ _ [?a; ?b] => change (rw_cells rsegs m O ([a] ++ [b])) in OUT' end.
    apply rw_cells_app in OUT'. destruct OUT' as [OL HP]. cbn [cells_size csize Nat.add] in HP. change (Z.of_nat 64) with 64%Z in HP.
    zstep. zstep. zstep. zstep. zstep.
    lazymatch type of HP with rw_cells _ _ _ [CB _ ?h] => call (memset0_call (O + 64) 152 h) end.
    all: side (first [exact HP | exact MI | reflexivity | lia]).
    match goal with H : rw_cells _ _ (O + 64)%Z _ |- _ => rename H into HP end. change (Z.to_nat 152) with 152%nat in HP.
    set (h := repeat (Z_to_bv 8 0) 152) in HP. clearbody h.
    sstep.

    destruct (nul_split (skipn (Z.to_nat bh2) ustr) slack) as (str & rest & ES & NI & LS). rewrite skipn_length in LS.
    pose proof (bytes_at_drop _ U _ (Z.to_nat bh2) USTR ltac:(rewrite app_length; cbn [length]; lia)) as SRC. rewrite Z2Nat.id in SRC by lia.
    rewrite skipn_app in SRC. replace (Z.to_nat bh2 - length ustr)%nat with 0%nat in SRC by lia. cbn [skipn] in SRC. rewrite ES in SRC.
    assert (LR : (Z.of_nat (length rest) = ulen - bh2 - Z.of_nat (length str) + Z.of_nat (length slack))%Z).
    { pose proof (f_equal (@length byte) ES) as EL. rewrite !length_app, skipn_length in EL. cbn [length] in EL. rewrite ?length_app in EL. cbn [length] in EL. lia. }
    assert (PAD' : ((- (U + bh2 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length rest))%Z).
    { replace (- (U + bh2 + Z.of_nat (length str) + 1))%Z with (- (U + ulen + 1) + (ulen - bh2 - Z.of_nat (length str)))%Z by lia.
      etransitivity; [apply mod8_shift; lia|]. lia. }

    lazymatch goal with FQ : rw_cells _ ?m' q [CB 279 ?a; ?c1] |- _ =>
      pose proof (rw_cells_split_CB rsegs m' q [] 279 a [c1] [24; 255]%nat FQ eq_refl) as FQ'; clear FQ; cbn [mk_CB_cells app] in FQ';
      lazymatch type of FQ' with rw_cells _ _ _ [?c0; ?cw; ?c1] => change (rw_cells rsegs m' q ([c0] ++ [cw] ++ [c1])) in FQ' end;
      apply rw_cells_take3 in FQ'; destruct FQ' as (FQ & WB0 & NUL1); cbn [cells_size csize Nat.add] in WB0, NUL1 end.
    change (Z.of_nat 24) with 24%Z in *. change (Z.of_nat 255) with 255%Z in *.
    pose proof (rw_CB_len _ _ _ _ WB0) as LW0. apply u8arr_of_rw_cells in WB0.
    zstep. zstep. zstep. zstep.
    replace (q + 24)%Z with (SP + -360)%Z in WB0 by lia.
    callq (strncpy_call q lo (SP + -360)%Z (U + bh2)%Z 255 str rest).
    all: side (first [exact WB0 | exact LW0 | exact SRC | exact NI | exact PAD' | exact ST | assumption | reflexivity | (f_equal; lia) | lia]).
    match goal with H : u8arr _ _ _ (stpn_result _ _) |- _ => rename H into WB1 end. change (Z.to_nat 255) with 255%nat in WB1.
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    replace (q + 24 + 255)%Z with (SP + -360 + Z.of_nat (length (stpn_result str 255)))%Z in NUL1 by (rewrite stpn_result_length; lia).
    pose proof (u8arr_snoc1 _ _ _ _ WB1 NUL1) as WB. clear WB1 NUL1.
    set (wb := stpn_result str 255 ++ [Z_to_bv 8 0]) in WB.
    assert (LW : length wb = 256%nat) by (subst wb; rewrite length_app, stpn_result_length; reflexivity).
    set (zn := stpn_k str 255). assert (ZN : (zn <= length str /\ zn <= 255)%nat) by (subst zn; unfold stpn_k; split; [apply Nat.le_min_l | apply Nat.le_min_r]).
    assert (WZ : nth_error wb (Z.to_nat (Z.of_nat zn)) = Some (Z_to_bv 8 0)) by (rewrite Nat2Z.id; subst wb zn; apply wb_nth_z).
    assert (WNZ : forall j' b, (0 <= j' < Z.of_nat zn)%Z -> nth_error wb (Z.to_nat j') = Some b -> bv_unsigned b <> 0%Z).
    { intros j' b Hj' Hb E0. subst wb. rewrite wb_nth_lt in Hb by lia. apply NI. assert (b = Z_to_bv 8 0) as <- by (apply bv_eq; rewrite E0; reflexivity).
      eapply nth_error_In. exact Hb. }
    clearbody wb zn.
    destruct (wb_nth wb 0 LW ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0. change (Z.to_nat 0) with 0%nat in Hb0.
    pose proof (u8arr_read rsegs _ _ wb 0 b0 (Z_to_bv 64 (SP + -384 + 24)) WB Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    replace (O + 64 + 152)%Z with (O + 216)%Z in * by lia.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    -
      replace (SP + -360)%Z with (q + 24)%Z in WB by lia.
      eapply (v4 bh2 (Z.of_nat zn) defport); try eassumption; try reflexivity; try lia. close_base.
    -
      replace (SP + -360)%Z with (q + 24)%Z in WB by lia.
      assert (b0 = Z_to_bv 8 91) as E91 by (apply bv_eq; rewrite K0; reflexivity). rewrite E91 in Hb0. rewrite K0.
      eapply (v6 bh2 (Z.of_nat zn) defport); try eassumption; try reflexivity; try lia. close_base.
  Qed.
End WALK.

