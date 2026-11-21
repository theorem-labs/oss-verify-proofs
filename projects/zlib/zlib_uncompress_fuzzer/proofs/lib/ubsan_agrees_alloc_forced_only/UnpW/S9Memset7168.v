(* (uncompress 1.4): musl memset(d, 0, 7168) at 0x20560, for inflateInit_'s memset of the
   inflate_state (state + 8, 7176 - 8 bytes). Same style and code facts as S8Memset's memset304_run (whose opening
   steps this reuses with n = 7168), with the 32-byte loop (0x20638 .. 0x20650, 223 passes) as an induction instead
   of unrolled. The final memory is wbytes mem d (zeros 7168) (ZStores.zstores_cover, as memset304_run). *)

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* a worker 2026-11-07 (uncompress 1.4): musl memset(d, 0, 7168) at 0x20560, for inflateInit_'s memset of the
   inflate_state (state + 8, 7176 - 8 bytes). Same style and code facts as S9Memset's memset304_run (whose opening
   steps this reuses with n = 7168), with the 32-byte loop (0x20638 .. 0x20650, 223 passes) as an induction instead
   of unrolled. The final memory is wbytes mem d (zeros 7168) (ZStores.zstores_cover, as memset304_run). *)

Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.GcF06.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import StartupTac. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import S9_code_20000_20a74 S9Memset.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require L10Walk.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac.chain_step ::= OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_chain_step.
Ltac OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.ok_sub Hok ::=
  OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_peel; OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_peel; eapply OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk.store_ok_sub; [ | exact Hok | | ];
  rewrite ?OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec.length_N_to_le_bytes, ?OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ZStores.length_zeros; OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.StartupTac.unorm; Stdlib.micromega.Lia.lia.

Abbreviation SEGS := SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* the branch conditions with symbolic counts *)
Ltac brc := gres; pin; unfold c_ltu, bv_ltu; unorm; first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia].
(* (the run file S9Memset7168R defines gfin for its closed register values) *)
(* *)

Lemma zstores_app : forall ws1 ws2 m d, zstores m d (ws1 ++ ws2) = zstores (zstores m d ws1) d ws2.
Proof. induction ws1 as [|[o n] ws1 IH]; intros ws2 m d; cbn [app zstores]; [reflexivity | apply IH]. Qed.

Lemma wb_join : forall m (X : Z) (bs1 bs2 : list byte), (0 <= X)%Z -> (X < 2^64)%Z ->
  wbytes (wbytes m (Z_to_bv 64 X) bs1) (Z_to_bv 64 (X + Z.of_nat (length bs1))) bs2 = wbytes m (Z_to_bv 64 X) (bs1 ++ bs2).
Proof. intros m X bs1 bs2 H1 H2. rewrite RefMemcpyLib.wbytes_app. unfold at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma wb4 : forall m (X : Z), (0 <= X)%Z -> (X + 32 < 2^64)%Z ->
  wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 X) (zeros 8)) (Z_to_bv 64 (X + 8)) (zeros 8))
                 (Z_to_bv 64 (X + 16)) (zeros 8)) (Z_to_bv 64 (X + 24)) (zeros 8)
  = wbytes m (Z_to_bv 64 X) (zeros 32).
Proof.
  intros m X H1 H2.
  replace (X + 8)%Z with (X + Z.of_nat (length (zeros 8)))%Z by (rewrite length_zeros; lia).
  rewrite wb_join by lia.
  replace (X + 16)%Z with (X + Z.of_nat (length (zeros 8 ++ zeros 8)))%Z by (rewrite length_app, !length_zeros; lia).
  rewrite wb_join by lia.
  replace (X + 24)%Z with (X + Z.of_nat (length ((zeros 8 ++ zeros 8) ++ zeros 8)))%Z by (rewrite !length_app, !length_zeros; lia).
  rewrite wb_join by lia.
  reflexivity.
Qed.

Lemma wb4_more : forall m (X : Z) (j : nat), (0 <= X)%Z -> (X + 32 + 32 * Z.of_nat j < 2^64)%Z ->
  wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 X) (zeros 8)) (Z_to_bv 64 (X + 8)) (zeros 8))
                 (Z_to_bv 64 (X + 16)) (zeros 8)) (Z_to_bv 64 (X + 24)) (zeros 8))
         (Z_to_bv 64 (X + 32)) (zeros (32 * j)%nat)
  = wbytes m (Z_to_bv 64 X) (zeros (32 * S j)%nat).
Proof.
  intros m X j H1 H2.
  rewrite wb4 by lia.
  replace (X + 32)%Z with (X + Z.of_nat (length (zeros 32)))%Z by (rewrite length_zeros; lia).
  rewrite wb_join by lia.
  unfold zeros. rewrite <- repeat_app. replace (32 + 32 * j)%nat with (32 * S j)%nat by lia. reflexivity.
Qed.

(* one pass of the 32-byte loop that branches back (k >= 2 passes left) *)
Lemma memset7168_iter {RCa1 : RunCtx}  : forall (k : nat) regs (mem rom : word -> option byte) (d : word),
  (2 <= k)%nat -> (k <= 223)%nat ->
  getr regs 11 = Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k)) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 31 ->
  getr regs 14 = Z_to_bv 64 (32 * Z.of_nat k + 8) ->
  (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok (run_segments SEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k))) 32 = true ->
  exists regs1 mem1,
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x2068c : word) mem rom) (mkst regs1 (0x2068c : word) mem1 rom)
    /\ mem1 = wbytes (wbytes (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k))) (zeros 8))
                      (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k) + 8)) (zeros 8))
                      (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k) + 16)) (zeros 8))
                      (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k) + 24)) (zeros 8)
    /\ getr regs1 11 = Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat (k - 1)))
    /\ getr regs1 12 = Z_to_bv 64 0 /\ getr regs1 13 = Z_to_bv 64 31
    /\ getr regs1 14 = Z_to_bv 64 (32 * Z.of_nat (k - 1) + 8)
    /\ regs_agree (fun r => In r memset_clob) regs regs1.
Proof.
  intros k regs mem rom d Hk1 Hk2 H11 H12 H13 H14 Hnw Hok.
  pose proof (u64_range d) as Hdr.
  eexists. eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k))) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k) + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k) + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k) + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_20584 D_20584 (Z_to_bv 64 (32 * Z.of_nat (k - 1) + 8)).
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat (k - 1)))).
    stepb_tk F_2058c D_2058c ltac:(brc).
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - reflexivity.
  - gres; pin; first [reflexivity | f_equal; lia].
  - gres; pin; first [reflexivity | f_equal; lia].
  - gres; pin; first [reflexivity | f_equal; lia].
  - gres; pin; first [reflexivity | f_equal; lia].
  - unfold memset_clob. solve_regs_agree.
Qed.

(* the last pass: falls through to the ret *)
Lemma memset7168_last {RCa1 : RunCtx}  : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 11 = Z_to_bv 64 (bv_unsigned d + 7128) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 40 ->
  (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok (run_segments SEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned d + 7128)) 32 = true ->
  exists regs' mem',
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x2068c : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem (Z_to_bv 64 (bv_unsigned d + 7128)) (zeros 32)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret Hra Hret H11 H12 H13 H14 Hnw Hok.
  pose proof (u64_range d) as Hdr.
  eexists. eexists. split; [|split].
  - stw F_20574 D_20574 (Z_to_bv 64 (bv_unsigned d + 7128)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20578 D_20578 (Z_to_bv 64 (bv_unsigned d + 7128 + 8)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_2057c D_2057c (Z_to_bv 64 (bv_unsigned d + 7128 + 16)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    stw F_20580 D_20580 (Z_to_bv 64 (bv_unsigned d + 7128 + 24)) (Z_to_bv 64 0) ltac:(ok_sub Hok).
    sv F_20584 D_20584 (Z_to_bv 64 8).
    sv F_20588 D_20588 (Z_to_bv 64 (bv_unsigned d + 7160)).
    stepb_ft F_2058c D_2058c ltac:(brc).
    stepret F_20590 D_20590 ret ltac:(pin; reflexivity).
    OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.L10Walk.l10_mst_refl.
  - apply wb4; lia.
  - unfold memset_clob. solve_regs_agree.
Qed.

Lemma memset7168_loop {RCa1 : RunCtx}  : forall (k : nat) regs (mem rom : word -> option byte) (d ret : word),
  (1 <= k)%nat -> (k <= 223)%nat ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 11 = Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k)) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 31 ->
  getr regs 14 = Z_to_bv 64 (32 * Z.of_nat k + 8) ->
  (bv_unsigned d + 7168 < 2^64)%Z ->
  store_ok (run_segments SEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k))) (32 * k)%nat = true ->
  exists regs' mem',
    msteps (run_segments SEGS rc_inp rc_sp rc_mb) (mkst regs (0x2068c : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem (Z_to_bv 64 (bv_unsigned d + (7160 - 32 * Z.of_nat k))) (zeros (32 * k)%nat)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  induction k as [|k IH]; intros regs mem rom d ret Hk1 Hk2 Hra Hret H11 H12 H13 H14 Hnw Hok; [lia|].
  pose proof (u64_range d) as Hdr.
  destruct (Nat.eq_dec k 0) as [Ek|Hk0].
  - subst k.
    destruct (memset7168_last regs mem rom d ret Hra Hret) as (r' & m' & RUN & EQ & AG).
    { rewrite H11; f_equal; lia. }
    { exact H12. } { exact H13. } { rewrite H14; f_equal; lia. } { exact Hnw. }
    { ok_sub Hok. }
    exists r', m'. split; [exact RUN|]. split; [|exact AG].
    rewrite EQ. replace (bv_unsigned d + (7160 - 32 * Z.of_nat 1))%Z with (bv_unsigned d + 7128)%Z by lia.
    reflexivity.
  - destruct (memset7168_iter (S k) regs mem rom d ltac:(lia) Hk2 H11 H12 H13 H14 Hnw)
      as (r1 & m1 & RUN1 & EQ1 & G11 & G12 & G13 & G14 & AG1).
    { ok_sub Hok. }
    replace (S k - 1)%nat with k in * by lia.
    carry AG1 Hra (1:reg) Hra1.
    destruct (IH r1 m1 rom d ret ltac:(lia) ltac:(lia) Hra1 Hret G11 G12 G13 G14 Hnw) as (r2 & m2 & RUN2 & EQ2 & AG2).
    { subst m1. ok_sub Hok. }
    exists r2, m2. split; [eapply msteps_trans; eassumption|]. split; [| eapply regs_agree_trans; eassumption].
    rewrite EQ2, EQ1.
    replace (bv_unsigned d + (7160 - 32 * Z.of_nat k))%Z with (bv_unsigned d + (7160 - 32 * Z.of_nat (S k)) + 32)%Z by lia.
    apply wb4_more; lia.
Qed.
