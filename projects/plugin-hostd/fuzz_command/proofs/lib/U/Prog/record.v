(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 989 of its 1017 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/chain_words.v, with its module paths, module names, addresses and numbers changed; 684 of its 782 lines of code are new or changed and 919 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/arg_s.v, with its module names, addresses and numbers changed; 603 of its 714 lines of code are new or changed and 671 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma rd_sx32 : forall z, (-2^31 <= z < 2^31)%Z -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  change (2^64)%Z with 18446744073709551616%Z. change (2^31)%Z with 2147483648%Z in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rd_lts : forall x y, (-2^63 <= x < 2^63)%Z -> (-2^63 <= y < 2^63)%Z ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with 9223372036854775808%Z.
  change (bv_modulus 64) with 18446744073709551616%Z.
  change (2^63)%Z with 9223372036854775808%Z in Hx, Hy.
  rewrite !Z.mod_small by lia.
  all: f_equal; lia.
Qed.

Lemma rd_addiw : forall z, (0 <= z < 2 ^ 31 - 1)%Z ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 1)%Z) = Z_to_bv 64 (z + 1)%Z.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648%Z. change (bv_modulus 32) with 4294967296%Z.
  change (2 ^ 31)%Z with 2147483648%Z in Hz.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma rd_land7 : forall e, (0 <= e < 2 ^ 64)%Z -> (e mod 8 = 0)%Z ->
  Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 e)) 7) = Z_to_bv 64 0.
Proof.
  intros e He Hm. rewrite unsigned_lit by lia. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2 ^ 3)%Z with 8%Z. rewrite Hm. reflexivity.
Qed.

Lemma rd_mul56 : forall z, (0 <= z < 16)%Z ->
  Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 6)) -
              bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 z)) 3)))%Z = Z_to_bv 64 (56 * z)%Z.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2^6)%Z with 64%Z. change (2^3)%Z with 8%Z.
  rewrite !unsigned_lit by lia. f_equal. lia.
Qed.

Lemma rd_run_lt :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo n e : Z) (sj : list byte),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (0x40000 <= lo)%Z ->
  (0 <= n < 16)%Z -> e = (0x34038 + 56 * n)%Z ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 n)] ->
  rw_cells rsegs m e [CB 8 sj] ->
  evt rsegs (fun ms' => exists a1' a2' m',
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e) a1' a2' a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x34030, 0x34034); (e, e + 8)]%Z m m'
       /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x34030 [C4 (Z_to_bv 64 (n + 1))]
       /\ rw_cells rsegs m' e [C4 a0; C4 (Z_to_bv 64 0)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1612c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n e sj ST LO LO2 Hn Ee NC SL.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (0x34030, 0x34034); (e, e + 8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (U56 : bv_unsigned (Z_to_bv 64 (56 * n)) = (56 * n)%Z) by (apply unsigned_lit; lia).
  assert (EM : (e mod 8 = 0)%Z).
  { rewrite Ee. replace (0x34038 + 56 * n)%Z with ((26631 + 7 * n) * 8)%Z by lia. apply Z.mod_mul. lia. }
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 10 step.
  rewrite rd_sx32 by lia.
  assert (C1 : negb (bv_eqb (Z_to_bv 64 n) (Z_to_bv 64 16)) = true).
  { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
  rewrite C1. cbv iota.
  step. rewrite rd_addiw by lia.
  step. rewrite rd_lts by lia. if_false.
  step.
  step.
  step. if_false.
  do 3 step.
  rewrite rd_mul56 by lia.
  step.
  step.
  step. if_false.
  step.
  step.
  replace (Z_to_bv 64 (0x33ff0 + 56 * n + 72)) with (Z_to_bv 64 e) by (f_equal; lia).
  step.
  rewrite rd_land7 by lia.
  step. if_false.
  do 8 step.
  try replace (Z_to_bv 64 (bv_unsigned sp + -32 + 32)) with sp
    by (replace (bv_unsigned sp + -32 + 32)%Z with (bv_unsigned sp) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. do 3 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma rd_run_eq :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 32 <= bv_unsigned sp)%Z -> (0x40000 <= lo)%Z ->
  rw_cells rsegs m 0x34030 [C4 (Z_to_bv 64 16)] ->
  evt rsegs (fun ms' => exists m' junk,
       ms' = MS (mkR (Z_to_bv 64 0x16160) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0)
                     a0 (Z_to_bv 64 0x33ff0) (Z_to_bv 64 1) (Z_to_bv 64 16) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x15b08) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 32)%Z [CB 8 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1612c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 NC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 10 step.
  try rewrite rd_sx32 by lia.
  if_false.
  do 3 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma rd_run_tail :
  forall ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 s0v s1v fnw : word) (junk sj : list byte),
  rw_cells rsegs m (bv_unsigned sp0 - 32) [CB 8 junk; C8 s1v; C8 s0v; C8 ra0] ->
  rw_cells rsegs m 0x33ff0 [CB 8 sj] ->
  (0x40000 <= bv_unsigned sp0 - 32)%Z ->
  evt rsegs (fun ms' => exists m',
       ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0x33ff0) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra0) fc None m' (seg_rom rsegs)
       /\ munch [(0x33ff0, 0x33ff8)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' 0x33ff0 [C4 fnw; C4 (Z_to_bv 64 0)])
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 32)) gp tp t0 t1 t2 (Z_to_bv 64 0x33ff0) fnw a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16160) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 s0v s1v fnw junk sj FR SL LO.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(0x33ff0, 0x33ff8)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  step.
  try rewrite rd_land7 by lia.
  step. if_false.
  do 8 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 32 + 32)) with sp0
    by (replace (bv_unsigned sp0 - 32 + 32)%Z with (bv_unsigned sp0) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; eassumption.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecSeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecStep RecGlue RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_calls_free_c record_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require snprintf_c.
Local Open Scope Z_scope.

Lemma rd_cells_bytes : forall segs m a cs, rw_cells segs m a cs -> bytes_at segs m a (cells_bytes cs).
Proof. intros segs m a cs [[_ H] _]. exact H. Qed.

Lemma rd_same_bytes : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf' | rewrite Eb; exact Hb]|].
  rewrite Es. exact Hw.
Qed.

Lemma rd_cell4 : forall m a v, GLOB_LO <= a -> a + 4 <= GLOB_LO + Z.of_nat GLOB_N ->
  bytes_at rsegs m a (le4 v) -> rw_cells rsegs m a [C4 v].
Proof.
  intros m a v H1 H2 H. apply (rd_same_bytes _ _ [CB (length (le4 v)) (le4 v)]).
  - apply bytes_rw_cells; [lia | rewrite length_le4; lia | exact H].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes]. reflexivity.
  - cbn [cells_size csize]. rewrite length_le4. reflexivity.
Qed.

Lemma rd_area_glob : forall a, rec_area a -> GLOB_LO <= a < GLOB_LO + Z.of_nat GLOB_N.
Proof. intros a H. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, GLOB_LO, GLOB_N in *. lia. Qed.

Lemma rd_rw_out : forall segs W m m' a cs, rw_cells segs m a cs -> munch W m m' ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> 0 <= a + i < 2 ^ 64 /\ outside W (a + i)) -> rw_cells segs m' a cs.
Proof.
  intros segs W m m' a cs H MU HO. apply (rw_cells_transfer segs m); [exact H|]. intros i Hi.
  destruct (HO i Hi) as [R O]. split; [exact (munch_mbyte segs W m m' _ MU R O)|].
  exact (proj1 (munch_writable segs W m m' _ MU R O)).
Qed.

Lemma rd_f18_out : forall W m m', f18_words rsegs m -> munch W m m' ->
  (forall i, 0 <= i < 8 -> outside W (snprintf_c.GOT_GUARD + i) /\ outside W (snprintf_c.GUARD + i)) ->
  f18_words rsegs m'.
Proof.
  intros W m m' [F1 (g & F2)] MU HO. split; [|exists g].
  - apply (rd_rw_out rsegs W m m' _ _ F1 MU). intros i Hi. cbn in Hi.
    split; [unfold snprintf_c.GOT_GUARD; lia | apply (HO i ltac:(lia))].
  - apply (rd_rw_out rsegs W m m' _ _ F2 MU). intros i Hi. cbn in Hi.
    split; [unfold snprintf_c.GUARD; lia | apply (HO i ltac:(lia))].
Qed.

Lemma rd_ro_out : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 20 -> ro_addr rsegs (Z_to_bv 64 a) = true -> outside W a) -> ro_agree rsegs m'.
Proof.
  intros W m m' RA MU HO x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
  assert (Lx : bv_unsigned x < 2 ^ 20).
  { destruct (Z_lt_le_dec (bv_unsigned x) (2 ^ 20)) as [H|H]; [exact H|].
    rewrite <- (Z_to_bv_bv_unsigned x), ro_addr_hi in Hx by lia. discriminate. }
  assert (E : m' x = m x).
  { apply MU. apply HO; [lia|]. rewrite Z_to_bv_bv_unsigned. exact Hx. }
  unfold mrd. rewrite E. exact (RA x Hx).
Qed.

Lemma rd_ro_f18 : forall S K W m m', ro_agree rsegs m -> f18_words rsegs m -> munch W m m' ->
  2 ^ 21 <= S - K ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  ro_agree rsegs m' /\ f18_words rsegs m'.
Proof.
  intros S K W m m' RA F18 MU HS HW.
  assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ rec_area a -> outside W a).
  { intros a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction. }
  split.
  - apply (rd_ro_out W m m' RA MU). intros a Ha Hro. apply OUT; [lia | lia |].
    intros Hr. rewrite glob_ro_false in Hro by exact (rd_area_glob a Hr). discriminate.
  - apply (rd_f18_out W m m' F18 MU). intros i Hi.
    split; (apply OUT; unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, snprintf_c.GOT_GUARD, snprintf_c.GUARD; lia).
Qed.

Lemma rd_rep_O_in : forall segs gr sc L A mem R O pn, rec_rep segs gr sc L A mem R O -> In pn O -> In pn (blocks L A).
Proof.
  intros segs gr sc L A mem R O pn (Q & HR & HO) Hin. exact (rep_at_blocks segs _ _ _ _ _ _ pn HR (proj1 (HO pn) Hin)).
Qed.

Lemma rd_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma rd_freed_one : forall P : list (Z * Z), (forall pn, In pn P -> fst pn <> 0) -> freed [P] = P.
Proof.
  intros P H. unfold freed. cbn [concat]. rewrite app_nil_r.
  induction P as [|pn P IH]; [reflexivity|]. cbn [List.filter].
  rewrite (proj2 (Z.eqb_neq _ _) (H pn (or_introl eq_refl))). cbn [negb]. f_equal.
  apply IH. intros q Hq. apply H. right. exact Hq.
Qed.

Lemma rd_count_disj : forall (l : list (Z * Z)) x, pairwise ranges_disjoint l -> 0 < snd x ->
  (count_occ rd_pair_dec l x <= 1)%nat.
Proof.
  induction l as [|y l IH]; intros x HP Hx; cbn [count_occ]; [lia|].
  destruct HP as [H1 H2]. destruct (rd_pair_dec y x) as [E|E].
  - subst y. assert (C0 : count_occ rd_pair_dec l x = 0%nat).
    { destruct (count_occ rd_pair_dec l x) eqn:C; [reflexivity|]. exfalso.
      assert (Hin : In x l) by (apply (count_occ_In rd_pair_dec); lia).
      pose proof (H1 x Hin) as D. unfold ranges_disjoint in D. lia. }
    lia.
  - exact (IH x H2 Hx).
Qed.

Lemma rd_perm_not_both : forall (bl bl' P : list (Z * Z)) pn, Permutation bl (bl' ++ P) ->
  pairwise ranges_disjoint bl -> 0 < snd pn -> In pn bl' -> In pn P -> False.
Proof.
  intros bl bl' P pn HP HD Hs H1 H2.
  pose proof (rd_count_disj bl pn HD Hs) as C.
  rewrite (proj1 (Permutation_count_occ rd_pair_dec _ _) HP), count_occ_app in C.
  apply (count_occ_In rd_pair_dec) in H1. apply (count_occ_In rd_pair_dec) in H2. lia.
Qed.

Lemma rd_rfree_eq : forall F bb, rfree_b bb F =
  SB (sb_live bb - Z.of_nat (length F)) (sb_bytes bb - fold_right (fun b acc => snd b + acc) 0 F) (sb_cap bb).
Proof.
  induction F as [|pn F IH]; intros bb.
  - destruct bb as [l y c]. unfold rfree_b. cbn. f_equal; lia.
  - unfold rfree_b in *. cbn [fold_left]. rewrite IH. unfold sb_free. cbn [sb_live sb_bytes sb_cap length fold_right].
    f_equal; lia.
Qed.

Lemma rd_bsum_perm : forall l l' : list (Z * Z), Permutation l l' ->
  fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l'.
Proof. intros l l' Q. induction Q; cbn; lia. Qed.

Lemma rd_rfree_shift : forall bb L A L' A' F, Permutation (blocks L A) (blocks L' A' ++ F) ->
  rfree_b bb F = sb_shift bb A A'.
Proof.
  intros bb L A L' A' F P. rewrite rd_rfree_eq.
  destruct (blocks_counts L A) as (N0 & U0). destruct (blocks_counts L' A') as (N1 & U1).
  pose proof (Permutation_length P) as PL. rewrite length_app in PL.
  pose proof (rd_bsum_perm _ _ P) as PS. rewrite bsum_app in PS.
  unfold sb_shift. f_equal; lia.
Qed.

Ltac rd_saved :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr ? ? ?; unfold callee_saved in Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
              r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct C as [C|C]; [subst r; first [lia | reflexivity]|]);
  subst r; first [lia | reflexivity].

Section Rec.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis RCF : rec_calls_free_contract B API.

Lemma rd_img_low : img_low B.
Proof using SEGS.
  pose proof alloc_ceiling_val as AC.
  apply (img_low_of_check B (2 ^ 21)); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia].
Qed.

Lemma rd_win_out : forall (W : list (Z * Z)) S K,
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (S - K <= a < S) -> ~ rec_area a -> outside W a.
Proof.
  intros W S K HW a Ra H1 H2. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a Ra H); contradiction.
Qed.

Lemma rd_blk_out : forall K S O L A mem md Lc Ac mc mdc W,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  forall q k i, In (q, k) (blocks Lc Ac) -> 0 <= i < k -> 0 <= q + i < 2 ^ 64 /\ outside W (q + i).
Proof using SEGS AX.
  intros K S O L A mem md Lc Ac mc mdc W RJ HW q k i Hin Hi.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & _).
  destruct (block_facts B _ LAWS Lc Ac mc mdc q k i HM Hin Hi) as (_ & H4 & H5 & _).
  split; [lia|]. apply (rd_win_out W S K HW); [lia | lia |].
  intros Hr. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp). cbn in E. injection E as <- <-.
  apply (ax_blocks_img AX Lc Ac mc mdc p k' i HM Hp Hi). apply (glob_in_img B SEGS). exact (rd_area_glob _ Hr).
Qed.

Lemma rd_win : forall K S O L A mem md Lc Ac mc mdc m' W,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  munch W mc m' -> wmono rsegs mc m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> S - K <= a < S \/ rec_area a) ->
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac m' mdc.
Proof using SEGS AX GOWN.
  intros K S O L A mem md Lc Ac mc mdc m' W RJ MU WM HW.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  pose proof RJ as (HM & HWA & _ & _ & HL & _).
  pose proof (rd_blk_out K S O L A mem md Lc Ac mc mdc W RJ HW) as BO.
  apply (rjr_munch B (aa_MR API) SEGS LAWS K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc m' W RJ MU);
    [rewrite SEGS; exact WM | | | | |].
  - intros a Ra Hn _. exact (HW a Ra Hn).
  - intros a Ra Hn Ho. pose proof (mr_owned_low B _ LAWS Lc Ac mc mdc a HM Ho) as Hlo.
    destruct (HW a Ra Hn) as [H|H]; [lia|].
    exact (GOWN Lc Ac mc mdc a HM (glob_in a (rd_area_glob a H)) Ho).
  - intros a Ha. destruct (outside_dec W a) as [H|H]; [exact H|]. destruct (HW a ltac:(lia) H) as [H'|H'];
      [lia | apply rd_area_glob in H'; unfold GLOB_LO, GLOB_N in H'; lia].
  - intros p n i Hin Hg Hi.
    pose proof (rjr_in_cur B _ K S rec_area _ L A mem md Lc Ac mc mdc p n RJ Hin Hg) as Hc.
    rewrite <- (ptr_addr_stable A L Lc p n HWA Hin HL).
    apply (BO (ptr_addr Lc p) n i); [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi].
  - intros p n i Hc Hi. destruct (mr_blocks B _ LAWS Lc Ac mc mdc p n i HM Hc Hi) as (Hp & _).
    destruct (BO (ptr_addr Lc p) n i) as [Rr Oo]; [unfold blocks; apply in_map_iff; exists (p, n); auto | exact Hi|].
    exact (munch_present W mc m' _ MU Rr Oo Hp).
Qed.

Theorem record_holds : record_contract B API.
Proof using SEGS ERRNO_LOW GOTG GRD GOWN AX CTX RCF.
  unfold record_contract.
  intros L A regs mem md fn R O b PRE A0 HFN GR RA F18 RES.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC.
  pose proof rd_img_low as IL.
  assert (KV : RECORD_K = 8336) by reflexivity.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (kb_md B API _ _ _ _ HMR) as [Hh Hl].
  pose proof (kb_stk B API IL _ _ _ _ _ _ PRE0 ltac:(lia)) as ST. rewrite SEGS in ST.
  rewrite SEGS in RA, F18.
  assert (GR' : rec_rep rsegs G_REC REC_SC L A mem R O) by (rewrite <- SEGS; exact GR).
  pose proof (rjr_init B (aa_MR API) RECORD_K rec_area (fun pn => In pn O) L A regs mem md PRE0 ltac:(lia)) as RJ0.
  unfold spZ in *.
  set (sp := getr regs 2) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof GR' as (Q0 & HR0 & HO0).
  pose proof HR0 as (HS0 & (G1 & G2 & G3 & G4 & G5 & G6) & _).
  assert (NC : rw_cells rsegs mem 0x34030 [C4 (Z_to_bv 64 (Z.of_nat (length (r_calls R))))]).
  { apply rd_cell4; [unfold GLOB_LO; lia | unfold GLOB_LO, GLOB_N; lia | exact G3]. }
  assert (Hn : (length (r_calls R) < 16)%nat \/ length (r_calls R) = 16%nat) by lia.
  destruct Hn as [Hn | Hn].
  - set (n := length (r_calls R)) in *.
    destruct (glob_rw_cells mem (0x34038 + 56 * Z.of_nat n) 8 ltac:(unfold GLOB_LO; lia)
                ltac:(unfold GLOB_LO, GLOB_N; lia)) as [sj SL].
    eapply (kb_run B regs (Z_to_bv 64 RECORD) mem md
      (fun R1 pc' m' =>
         pc' = ret_pc (getr regs 1) /\
         munch [(bv_unsigned sp - 32, bv_unsigned sp); (0x34030, 0x34034);
                (0x34038 + 56 * Z.of_nat n, 0x34038 + 56 * Z.of_nat n + 8)] mem m' /\
         wmono rsegs mem m' /\
         rw_cells rsegs m' 0x34030 [C4 (Z_to_bv 64 (Z.of_nat n + 1))] /\
         rw_cells rsegs m' (0x34038 + 56 * Z.of_nat n) [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] /\
         getr R1 10 = Z_to_bv 64 (0x34038 + 56 * Z.of_nat n) /\ regs_preserved regs R1)
      _ Hh Hl).
    { unfold rmk. fold sp. rewrite SEGS. eapply evt_cut.
      - eapply (rd_run_lt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem
                  (bv_unsigned sp - RECORD_K) (Z.of_nat n) (0x34038 + 56 * Z.of_nat n) sj);
          [exact ST | lia | lia | lia | reflexivity | exact NC | exact SL].
      - intros ms' (a1' & a2' & m' & -> & MU & WM & NC' & EN'). apply evt_done.
        do 3 eexists. split; [reflexivity|].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact NC'|].
        split; [rewrite A0 in EN'; exact EN'|]. split; [reflexivity|]. kb_saved. }
    intros R1 pc1 m1 regs1 (-> & MU1 & WM1 & NC1 & EN1 & A1 & P1) HG1.
    rewrite (kb_ret_pc _ HRA).
    apply SR_ret.
    assert (RP1 : regs_preserved regs regs1) by exact (kb_preserved_getr regs R1 regs1 P1 HG1).
    assert (HW1 : forall a, 0 <= a < 2 ^ 64 ->
              ~ outside [(bv_unsigned sp - 32, bv_unsigned sp); (0x34030, 0x34034);
                         (0x34038 + 56 * Z.of_nat n, 0x34038 + 56 * Z.of_nat n + 8)] a ->
              spZ regs - RECORD_K <= a < spZ regs \/ rec_area a).
    { intros a Ra Hm. cbn in Hm. unfold spZ. fold sp. unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE. lia. }
    pose proof (rd_win RECORD_K (spZ regs) O L A mem md L A mem md m1 _ RJ0 MU1 WM1 HW1) as RJ1.
    pose proof (rjr_final B (aa_MR API) CTX RECORD_K rec_area (fun pn => In pn O) (fun a => In a (map fst O))
                  L A regs mem md L A regs1 m1 md PRE0 RJ1 RP1
                  ltac:(intros a k G; exact (in_map fst O (a, k) G))) as FIN.
    pose proof (rjr_others_kept B (aa_MR API) RECORD_K (spZ regs) rec_area (fun pn => In pn O) L A mem md
                  L A m1 md O RJ1 (fun pn H => H)) as OK.
    destruct (rd_ro_f18 (spZ regs) RECORD_K _ mem m1 RA F18 MU1 ltac:(unfold spZ; fold sp; lia) HW1) as [RA1 F181].
    exists L, A, regs1, m1, md, O, [].
    split; [reflexivity|].
    split; [exact FIN|].
    split.
    { rewrite HG1, A1. unfold rec_slot. fold n.
      destruct (Nat.ltb_spec n 16) as [_|C]; [|lia]. f_equal; unfold G_REC, OFF_CALLS, CALL_SIZE; lia. }
    split.
    { unfold g_rec_rep. rewrite SEGS.
      apply rd_cells_bytes in NC1. apply rd_cells_bytes in EN1. cbn [cells_bytes cbytes] in NC1, EN1.
      rewrite app_nil_r in NC1, EN1.
      apply bytes_at_app in EN1 as [EF EA]. rewrite length_le4 in EA.
      apply (rec_rep_record_lt rsegs G_REC REC_SC L A mem m1 R O fn GR' Hn HFN).
      - exact NC1.
      - rewrite (rec_entry_lt G_REC REC_SC R Hn). fold n.
        match goal with |- bytes_at _ _ ?a _ => replace a with (0x34038 + 56 * Z.of_nat n)
          by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia) end. exact EF.
      - rewrite (rec_entry_lt G_REC REC_SC R Hn). fold n.
        match goal with |- bytes_at _ _ ?a _ => replace a with (0x34038 + 56 * Z.of_nat n + Z.of_nat 4)
          by (unfold G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS; lia) end. exact EA.
      - rewrite (rec_entry_lt G_REC REC_SC R Hn). fold n. intros a Ha H1 H2.
        apply (munch_mbyte rsegs _ mem m1 a MU1); [unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia|].
        cbn. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, OFF_NCALLS, OFF_CALLS, CALL_SIZE in Ha, H1, H2 |- *. lia.
      - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in Ha |- *. lia.
      - intros p k i Hin Hi.
        destruct (rd_blk_out RECORD_K (spZ regs) O L A mem md L A mem md _ RJ0 HW1 p k i
                    (rd_rep_O_in _ _ _ _ _ _ _ _ _ GR' Hin) Hi) as [Rr Oo].
        exact (munch_mbyte rsegs _ mem m1 _ MU1 Rr Oo). }
    split; [intros pn H; exact H|].
    split; [intros pn; split; [intros [] | intros [H1 H2]; contradiction]|].
    split; [rewrite app_nil_r; apply Permutation_refl|].
    split; [exact OK|].
    split; [intros pn H; destruct (in_dec rd_pair_dec pn O) as [H1|H1]; [right; exact H1 | left; split; assumption]|].
    split; [rewrite SEGS; exact RA1|].
    split; [rewrite SEGS; exact F181|].
    split; [intros H; exact H|].
    split; [lia|].
    split.
    { intros _. split; [reflexivity|]. split; [reflexivity|]. intros lo Hlo AV0.
      unfold spZ in Hlo. fold sp in Hlo.
      apply (kb_auxv B API (ly_sec L) lo mem m1 _ L A md HMR AV0 MU1).
      - intros x Hx Hxl. cbn [outside]. lia.
      - intros x Hx Ho.
        destruct (outside_dec [(bv_unsigned sp - 32, bv_unsigned sp); (0x34030, 0x34034);
                    (0x34038 + 56 * Z.of_nat n, 0x34038 + 56 * Z.of_nat n + 8)] x) as [H|H]; [exact H|].
        destruct (HW1 x ltac:(lia) H) as [H'|H'].
        + unfold spZ in H'. fold sp in H'. lia.
        + exfalso. exact (GOWN L A mem md x HMR (glob_in x (rd_area_glob x H')) Ho). }
    split; [rewrite sb_shift_refl; apply sb_le_refl|].
    rewrite sb_shift_refl. exact RES.
  - assert (NC16 : rw_cells rsegs mem 0x34030 [C4 (Z_to_bv 64 16)]) by (rewrite Hn in NC; exact NC).
    eapply (kb_run B regs (Z_to_bv 64 RECORD) mem md
      (fun R1 pc' m' => exists junk,
         pc' = Z_to_bv 64 0x15b08 /\
         munch [(bv_unsigned sp - 32, bv_unsigned sp)] mem m' /\ wmono rsegs mem m' /\
         rw_cells rsegs m' (bv_unsigned sp - 32) [CB 8 junk; C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
         getr R1 1 = Z_to_bv 64 0x16160 /\ getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 32) /\
         getr R1 8 = Z_to_bv 64 0x33ff0 /\ getr R1 9 = getr regs 10 /\
         getr R1 10 = Z_to_bv 64 0x33ff0 /\ getr R1 11 = Z_to_bv 64 1 /\
         (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)))
      _ Hh Hl).
    { unfold rmk. fold sp. rewrite SEGS. eapply evt_cut.
      - eapply (rd_run_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem
                  (bv_unsigned sp - RECORD_K)); [exact ST | lia | lia | exact NC16].
      - intros ms' (m' & junk & -> & MU & WM & FR). apply evt_done.
        do 3 eexists. split; [reflexivity|]. exists junk.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact FR|].
        do 6 (split; [reflexivity|]). rd_saved. }
    intros Rk pc1 m1 R1 (junk & -> & MU1 & WM1 & FR1 & E1_1 & E1_2 & E1_8 & E1_9 & E1_10 & E1_11 & E1_S) HG1.
    rewrite <- HG1 in E1_1, E1_2, E1_8, E1_9, E1_10, E1_11.
    assert (E1S : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 ->
              getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r H1 H2 H3 H4. rewrite HG1. exact (E1_S r H1 H2 H3 H4). }
    clear E1_S.
    assert (SP1 : spZ R1 = bv_unsigned sp - 32) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
    assert (HW1 : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(bv_unsigned sp - 32, bv_unsigned sp)] a ->
              spZ regs - RECORD_K <= a < spZ regs \/ rec_area a).
    { intros a Ra Hm. cbn in Hm. unfold spZ. fold sp. lia. }
    pose proof (rd_win RECORD_K (spZ regs) O L A mem md L A mem md m1 _ RJ0 MU1 WM1 HW1) as RJ1.
    pose proof RJ1 as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAX1).
    destruct (rd_ro_f18 (spZ regs) RECORD_K _ mem m1 RA F18 MU1 ltac:(unfold spZ; fold sp; lia) HW1) as [RA1 F181].
    assert (GR1 : rec_rep rsegs G_REC REC_SC L A m1 R O).
    { apply (rec_rep_frame rsegs G_REC REC_SC L A mem R O L A m1 GR').
      - intros a Ha.
        assert (Ho : outside [(bv_unsigned sp - 32, bv_unsigned sp)] a)
          by (cbn; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; split; [lia | exact I]).
        assert (Ra : 0 <= a < 2 ^ 64) by (unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia).
        split; [exact (munch_mbyte rsegs _ mem m1 a MU1 Ra Ho) | exact (proj1 (munch_writable rsegs _ mem m1 a MU1 Ra Ho))].
      - intros p k i Hin Hi.
        destruct (rd_blk_out RECORD_K (spZ regs) O L A mem md L A mem md _ RJ0 HW1 p k i
                    (rd_rep_O_in _ _ _ _ _ _ _ _ _ GR' Hin) Hi) as [Rr Oo].
        exact (munch_mbyte rsegs _ mem m1 _ MU1 Rr Oo).
      - intros pn H. exact (rd_rep_O_in _ _ _ _ _ _ _ _ _ GR' H). }
    destruct GR1 as (Q1 & HR1 & HO1).
    pose proof HR1 as (HS1 & (CC1 & CC2 & CC3 & CC4 & CC5 & CC6) & HA1 & HP1 & HX1 & (ND1 & HAP1)).
    pose proof CC5 as (CF1 & CF2 & CF3 & CF4 & CF5 & CF6 & CF7).
    assert (NZS : forall pn, In pn (l_spill Q1) -> fst pn <> 0 /\ 0 < snd pn /\ In pn (blocks L A)).
    { intros pn Hpn. apply In_nth_error in Hpn as (k & Ek).
      assert (Hk : (k < length (snd (r_spill R)))%nat)
        by (rewrite <- CF3; apply nth_error_Some; rewrite Ek; discriminate).
      destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
      destruct (CF7 k s pn Es Ek) as (_ & NZ & IN & SZ & _). split; [exact NZ|]. split; [lia | exact IN]. }
    assert (FR1' : freed [l_spill Q1] = l_spill Q1)
      by (apply rd_freed_one; intros pn Hpn; exact (proj1 (NZS pn Hpn))).
    assert (NAF : forall a, nargs_field REC_SC (length [l_spill Q1]) a -> REC_SC + 4 <= a < REC_SC + 8).
    { intros a (i & Hi & Ha). cbn in Hi. assert (i = 0%nat) by lia. subst i. cbn in Ha. lia. }
    pose proof RCF as RC. unfold rec_calls_free_contract in RC.
    eapply SR_bind.
    { apply (RC L A R1 m1 md REC_SC [l_spill Q1] b).
      - apply (call_pre_k_of_rjr B _ RECORD_K (spZ regs) rec_area _ L A mem md L A m1 md RCF_K R1 RJ1).
        + rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
        + rewrite SP1. replace (bv_unsigned sp - 32) with (bv_unsigned sp + (-2) * 16) by ring.
          rewrite Z.mod_add by lia. exact HAL.
        + unfold RCF_K, ALLOC_STACK. lia.
        + rewrite SP1. unfold spZ. fold sp. unfold RCF_K, ALLOC_STACK. lia.
        + rewrite SP1. unfold spZ. fold sp. lia.
        + exact (eq_trans (E1S 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)) HTP).
      - rewrite SEGS. exact RA1.
      - exact E1_10.
      - exact E1_11.
      - unfold calls_slots. rewrite SEGS. split; [cbn; lia|]. intros i P0 EP0.
        destruct i as [|i]; [|destruct i; discriminate]. cbn in EP0. injection EP0 as <-.
        split; [lia|]. split.
        { rewrite CF3. replace (REC_SC + 56 * Z.of_nat 0 + 4) with (REC_SC + CALL_OFF_NARGS)
            by (unfold CALL_OFF_NARGS; lia). exact CF5. }
        split; [intros j Hj; apply glob_writable; unfold REC_SC, GLOB_LO, GLOB_N; lia|].
        intros a pn Hpn.
        assert (Ha : (a < length (snd (r_spill R)))%nat)
          by (rewrite <- CF3; apply nth_error_Some; rewrite Hpn; discriminate).
        destruct (nth_error (snd (r_spill R)) a) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
        destruct (CF7 a s pn Es Hpn) as (BY & _ & IN & _). split; [|right; exact IN].
        replace (REC_SC + 56 * Z.of_nat 0 + 8 + 8 * Z.of_nat a) with (REC_SC + CALL_OFF_ARGS + 8 * Z.of_nat a)
          by (unfold CALL_OFF_ARGS; lia).
        exact BY.
      - rewrite FR1'. exact CF6.
      - unfold REC_SC. lia.
      - cbn. unfold REC_SC. lia.
      - intros _. unfold REC_SC. split; [lia | reflexivity].
      - intros j Hj. right. apply glob_in. cbn in Hj. unfold REC_SC, GLOB_LO, GLOB_N in *. lia.
      - exact RES. }
    intros c2 (L' & A' & R2 & m2 & md2 & -> & POST & PERM & BK & UK & US & NA & SCK & FG & RA2 & GK & INI & RGN
      & UNI & RES').
    rewrite FR1' in PERM, BK, UK, RES'.
    pose proof POST as (PM & PW & PB & PL & PA & PR & PV & PF & PK & PS).
    unfold blocks_kept in BK. rewrite SEGS in RA2, PF, FG, BK.
    destruct (kb_md B API _ _ _ _ PM) as [Hh2 Hl2].
    assert (RJ2 : rjr B (aa_MR API) RECORD_K (spZ regs) rec_area (fun pn => In pn O) L A mem md L' A' m2 md2).
    { apply (rjr_post B _ SEGS LAWS AX ERRNO_LOW RECORD_K (spZ regs) rec_area _ L A mem md L A m1 md RCF_K R1
               (nargs_field REC_SC (length [l_spill Q1])) (fun _ => False) L' A' R2 m2 md2 RJ1
               (call_post_k_rec B _ _ _ _ _ _ _ _ _ _ _ _ _ POST)).
      - rewrite SP1. unfold spZ. fold sp. unfold RCF_K, ALLOC_STACK. lia.
      - rewrite SP1. unfold spZ. fold sp. lia.
      - intros a Ha _. pose proof (NAF a Ha) as H. unfold spZ. fold sp.
        split; [left; unfold REC_SC, SC_SIZE in *; lia | unfold REC_SC in *; lia].
      - intros p k _ _ _ [].
      - intros p k Hin Hc Hk. destruct (in_dec rd_pair_dec (ptr_addr L p, k) (l_spill Q1)) as [Hs|Hs].
        + apply HO1. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact Hs.
        + exfalso. exact (Hk (UK p k Hc Hs)).
      - exact RGN.
      - intros Hf. destruct (st_init_done A) eqn:EI.
        + rewrite (INI ltac:(first [exact EI | reflexivity])) in Hf. discriminate.
        + destruct (UNI ltac:(first [exact EI | reflexivity])) as (EL & EA & AUX).
          apply (AUX (spZ regs)).
          * rewrite SP1. unfold spZ. fold sp. lia.
          * change (Z.of_nat (length [l_spill Q1])) with 1. unfold REC_SC, spZ. fold sp. lia.
          * exact (HAX1 ltac:(first [exact EI | reflexivity])). }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 32) [CB 8 junk; C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
    { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
      assert (N1 : ~ owned B L A (bv_unsigned sp - 32 + i))
        by (intro Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HM1 Ho); lia).
      assert (N2 : ~ owned B L' A' (bv_unsigned sp - 32 + i))
        by (intro Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ PM Ho); lia).
      destruct (PF (bv_unsigned sp - 32 + i) ltac:(left; lia) N1 N2
                  ltac:(unfold scratch_k; rewrite SP1; intros [H|H]; lia)
                  ltac:(intros H; pose proof (NAF _ H); unfold REC_SC in *; lia)) as [E W].
      split; [exact E | apply W]. }
    destruct (glob_rw_cells m2 0x33ff0 8 ltac:(unfold GLOB_LO; lia) ltac:(unfold GLOB_LO, GLOB_N; lia)) as [sj SL2].
    assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 32))
      by exact (eq_trans (PR 2 ltac:(unfold callee_saved; lia)) E1_2).
    assert (E2_8 : getr R2 8 = Z_to_bv 64 0x33ff0)
      by exact (eq_trans (PR 8 ltac:(unfold callee_saved; lia)) E1_8).
    assert (E2_9 : getr R2 9 = getr regs 10)
      by exact (eq_trans (PR 9 ltac:(unfold callee_saved; lia)) E1_9).
    assert (E2S : forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 ->
              getr R2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
    { intros r H1 H2 H3 H4. rewrite (PR r H1). exact (E1S r H1 H2 H3 H4). }
    rewrite E1_1.
    eapply (kb_run B R2 (Z_to_bv 64 0x16160) m2 md2
      (fun R3 pc' m' =>
         pc' = ret_pc (getr regs 1) /\ munch [(0x33ff0, 0x33ff8)] m2 m' /\ wmono rsegs m2 m' /\
         rw_cells rsegs m' 0x33ff0 [C4 (Z_to_bv 64 fn); C4 (Z_to_bv 64 0)] /\
         getr R3 10 = Z_to_bv 64 0x33ff0 /\ regs_preserved regs R3)
      _ Hh2 Hl2).
    { unfold rmk. rewrite SEGS. rewrite E2_2, E2_8, E2_9. eapply evt_cut.
      - eapply (rd_run_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr m2
                  sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 10) junk sj);
          [exact FR2 | exact SL2 | lia].
      - intros ms' (m' & -> & MU & WM & EN). apply evt_done.
        do 3 eexists. split; [reflexivity|].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [rewrite A0 in EN; exact EN|].
        split; [reflexivity|].
        intros r Hr. pose proof Hr as Hr0. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 8 \/ r = 9 \/ (r <> 2 /\ r <> 8 /\ r <> 9)) by lia.
        destruct C as [->|[->|[->|(H2 & H8 & H9)]]]; [reflexivity | reflexivity | reflexivity |].
        rewrite <- (E2S r Hr0 H2 H8 H9).
        assert (C : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        clear Hr Hr0 H2 H8 H9.
        repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity. }
    intros R3 pc3 m3 regs3 (-> & MU3 & WM3 & EN3 & A3 & P3) HG3.
    rewrite (kb_ret_pc _ HRA).
    apply SR_ret.
    assert (RP3 : regs_preserved regs regs3) by exact (kb_preserved_getr regs R3 regs3 P3 HG3).
    assert (HW3 : forall a, 0 <= a < 2 ^ 64 -> ~ outside [(0x33ff0, 0x33ff8)] a ->
              spZ regs - RECORD_K <= a < spZ regs \/ rec_area a).
    { intros a Ra Hm. cbn in Hm. right. unfold rec_area, REC_SC, SC_SIZE. lia. }
    pose proof (rd_win RECORD_K (spZ regs) O L A mem md L' A' m2 md2 m3 _ RJ2 MU3 WM3 HW3) as RJ3.
    pose proof (rjr_final B (aa_MR API) CTX RECORD_K rec_area (fun pn => In pn O) (fun a => In a (map fst O))
                  L A regs mem md L' A' regs3 m3 md2 PRE0 RJ3 RP3
                  ltac:(intros a k G; exact (in_map fst O (a, k) G))) as FIN.
    pose proof (rjr_others_kept B (aa_MR API) RECORD_K (spZ regs) rec_area (fun pn => In pn O) L A mem md
                  L' A' m3 md2 O RJ3 (fun pn H => H)) as OK.
    assert (F182 : f18_words rsegs m2).
    { destruct (ax_statics AX L' A' m2 md2 PM) as (_ & (g & Hg & HWg) & _).
      rewrite GRD, SEGS in HWg.
      apply (f18_words_after m1 m2 g F181); [|exact Hg | exact HWg].
      intros i Hi. pose proof (GK i Hi) as G. rewrite GOTG, SEGS in G. exact G. }
    destruct (rd_ro_f18 (spZ regs) RECORD_K _ m2 m3 RA2 F182 MU3 ltac:(unfold spZ; fold sp; lia) HW3) as [RA3 F183].
    exists L', A', regs3, m3, md2, (lay_blocks (RLay (l_calls Q1) [] (l_answer Q1) (l_reply Q1))), (l_spill Q1).
    split; [reflexivity|].
    split; [exact FIN|].
    split.
    { rewrite HG3, A3. unfold rec_slot. rewrite Hn. reflexivity. }
    split.
    { unfold g_rec_rep, rec_rep. rewrite SEGS. exists (RLay (l_calls Q1) [] (l_answer Q1) (l_reply Q1)).
      split; [|intros pn; reflexivity].
      apply rd_cells_bytes in EN3. cbn [cells_bytes cbytes] in EN3. rewrite app_nil_r in EN3.
      apply bytes_at_app in EN3 as [EF EA]. rewrite length_le4 in EA.
      apply (rep_at_record_full rsegs G_REC REC_SC (blocks L A) (blocks L' A') m1 m3 R Q1 fn HR1 Hn HFN).
      - exact EF.
      - exact EA.
      - intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (unfold G_REC, REC_SIZE in Ha; lia).
        rewrite (munch_mbyte rsegs _ m2 m3 a MU3 Ra ltac:(cbn; unfold G_REC, REC_SIZE in Ha; split; [lia | exact I])).
        refine (proj1 (FG a _ _)); [apply glob_in; unfold G_REC, REC_SIZE, GLOB_LO, GLOB_N in Ha |- *; lia|].
        intros Hn'. pose proof (NAF a Hn'). unfold G_REC, REC_SC, REC_SIZE in *. lia.
      - intros a Ha _. apply glob_writable. unfold G_REC, REC_SC, REC_SIZE, SC_SIZE, GLOB_LO, GLOB_N in Ha |- *. lia.
      - intros pn Hin Hs.
        destruct (spill_others_kept rsegs Q1 (blocks L A) (blocks L' A') (l_spill Q1) m1 m2 ND1
                    (fun pn H => rep_at_blocks rsegs _ _ _ _ _ _ pn HR1 H) (fun pn H => H)
                    (fun pn H => in_app_or _ _ _ (Permutation_in pn PERM H)) BK pn Hin Hs) as [Hb Hk].
        split; [exact Hb|]. intros i Hi. destruct pn as [p k]. cbn [fst snd] in *.
        destruct (rd_blk_out RECORD_K (spZ regs) O L A mem md L' A' m2 md2 _ RJ2 HW3 p k i Hb Hi) as [Rr Oo].
        rewrite (munch_mbyte rsegs _ m2 m3 _ MU3 Rr Oo). exact (Hk i Hi). }
    split.
    { intros pn Hpn. apply HO1. exact (proj1 (proj1 (lay_drop_spill Q1 pn ND1) Hpn)). }
    split.
    { intros pn. rewrite HO1, (lay_drop_spill Q1 pn ND1). split.
      - intros Hs. split; [unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hs|].
        intros [_ H]. exact (H Hs).
      - intros [H1 H2]. destruct (in_dec rd_pair_dec pn (l_spill Q1)) as [Hs|Hs]; [exact Hs|].
        exfalso. exact (H2 (conj H1 Hs)). }
    split; [exact PERM|].
    split; [exact OK|].
    split.
    { intros pn Hpn.
      assert (Hb : In pn (blocks L A)) by (apply (Permutation_in pn (Permutation_sym PERM)); apply in_or_app; left; exact Hpn).
      destruct (in_dec rd_pair_dec pn O) as [Ho|Ho]; [right | left; split; assumption].
      apply (lay_drop_spill Q1 pn ND1). split; [apply HO1; exact Ho|].
      intros Hs. exact (rd_perm_not_both _ _ _ pn PERM (mr_blocks_disjoint B _ LAWS L A m1 md HM1)
                          (proj1 (proj2 (NZS pn Hs))) Hpn Hs). }
    split; [rewrite SEGS; exact RA3|].
    split; [rewrite SEGS; exact F183|].
    split; [exact INI|].
    split; [exact RGN|].
    split.
    { intros EI. destruct (UNI EI) as (EL & EA & AUX). split; [exact EL|]. split; [exact EA|].
      intros lo Hlo AV0. unfold spZ in Hlo. fold sp in Hlo.
      assert (AV1 : auxv_pre B (ly_sec L) lo m1).
      { apply (kb_auxv B API (ly_sec L) lo mem m1 _ L A md HMR AV0 MU1).
        - intros x Hx Hxl. cbn [outside]. lia.
        - intros x Hx Ho. cbn [outside]. lia. }
      assert (AV2 : auxv_pre B (ly_sec L') lo m2).
      { apply (AUX lo); [rewrite SP1; lia | change (Z.of_nat (length [l_spill Q1])) with 1; unfold REC_SC; lia | exact AV1]. }
      apply (kb_auxv B API (ly_sec L') lo m2 m3 _ L' A' md2 PM AV2 MU3).
      - intros x Hx Hxl. cbn [outside]. lia.
      - intros x Hx Ho. cbn [outside]. split; [|exact I]. intros Hr.
        exact (GOWN L' A' m2 md2 x PM (glob_in x ltac:(unfold GLOB_LO, GLOB_N; lia)) Ho). }
    split; [rewrite (rd_rfree_shift b L A L' A' (l_spill Q1) PERM); apply sb_le_refl|].
    rewrite <- (rd_rfree_shift b L A L' A' (l_spill Q1) PERM). exact RES'.
Qed.

End Rec.
