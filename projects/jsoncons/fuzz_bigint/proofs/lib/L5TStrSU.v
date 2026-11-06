(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Tgt Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import StoreOk TMemcpyU L5Defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Module TSSU.
Definition STRINIT : Z := 0x20a84.
Definition OPNEW : Z := 0x5abac.
Definition MEMMOVE : Z := 0x59824.
Definition MEMCPY : Z := 0x59420.
Definition str_cap (n : Z) : Z := if Z.eqb (Z.lor n 7) 23 then 26 else Z.lor n 7 + 1.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.

Lemma mem_grows_write' : forall m0 m a bs, mem_grows m0 m -> mem_grows m0 (write_to_mem m a bs).
Proof. intros m0 m a bs H. eapply mem_grows_trans; [exact H| apply write_to_mem_grows]. Qed.

Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | MG : mem_grows ?mq m |- _ => apply (mem_grows_write' mq m (wa a) bs) in MG
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.


(* [comment removed for export] *)
Definition memcpy_postZ (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d src n : Z) (sbytes : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(d, d + n)] m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' d [CB (Z.to_nat n) sbytes]
    /\ bytes_at rsegs m' src sbytes.

Lemma memcpy_specZ : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (d src n : Z) (sbytes junk : list byte),
  0 <= d -> d + n <= 2^47 -> 0 <= src -> src + n <= 2^47 -> 0 <= n ->
  bytes_at rsegs m src sbytes -> length sbytes = Z.to_nat n ->
  rw_cells rsegs m d [CB (Z.to_nat n) junk] ->
  (src + n <= d \/ d + n <= src) ->
  evt rsegs (memcpy_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d src n sbytes m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x59420) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros D0 D1 S0 S1 N0 SB LEN DB SEP.
  eapply evt_mono.
  { apply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sbytes junk);
      rewrite ?unsigned_lit by lia; first [assumption | lia]. }
  intros ms' PO. unfold memcpy_post in PO. rewrite ?unsigned_lit in PO by lia. exact PO.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_defined : forall m A cs i, rw_cells rsegs m A cs ->
  (0 <= A /\ (A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x92000 <= A)) ->   (* [comment removed for export] *)
  A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) <> None.
Proof.
  intros m A cs i [[Hwf Hb] (HA0 & HAn & W)] HA Hi.
  specialize (W (i - A) ltac:(lia)). replace (A + (i - A)) with i in W by lia.
  rewrite ref_wview_overlay in W by (rewrite wa_unsigned by lia; lia). exact W.
Qed.

Lemma mem_grows_of_cover2 : forall o1 h1 o2 h2 ma mb, munch [(o1, h1); (o2, h2)] ma mb ->
  (forall x, (o1 <= x < h1 \/ o2 <= x < h2) -> mb (wa x) <> None) -> mem_grows ma mb.
Proof.
  intros o1 h1 o2 h2 ma mb MU COV x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) o1) as [A1|A1]; [| destruct (Z_lt_le_dec (bv_unsigned x) h1) as [B1|B1]].
  2:{ rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x). apply COV. lia. }
  all: destruct (Z_lt_le_dec (bv_unsigned x) o2) as [A2|A2]; [| destruct (Z_lt_le_dec (bv_unsigned x) h2) as [B2|B2]].
  2,5: rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x); apply COV; lia.
  all: rewrite (MU x) by (cbn; lia); exact Hx.
Qed.

Lemma le1_wz : forall z, le1 (Z_to_bv 64 z) = [b8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_of_bytes_at : forall m bs a, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs m a bs -> rdn rsegs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
  intros m bs. induction bs as [|b bs IH]; intros a Ha Hn (H0 & H1 & H); [reflexivity|].
  cbn [length]. rewrite rdn_unfold.
  pose proof (H 0%nat ltac:(cbn; lia)) as E0. cbn [nth_error Z.of_nat] in E0. rewrite Z.add_0_r in E0. unfold wa in E0. rewrite E0.
  change (Z_to_bv 64 a + 1)%bv with (wa a + 1)%bv. rewrite wa_succ. unfold wa.
  rewrite (IH (a + 1)); [reflexivity| lia| cbn [length] in Hn; lia|].
  split; [lia|]. split; [cbn [length] in Hn; lia|]. intros i Hi. specialize (H (S i) ltac:(cbn; lia)). cbn [nth_error] in H.
  rewrite <- H. f_equal. unfold wa. f_equal. lia.
Qed.

Lemma u64_of_cells : forall m A w cs, rw_cells rsegs m A (C8 w :: cs) -> L5.u64_at rsegs m A (bv_unsigned w).
Proof.
  intros m A w cs [[WF HB] (HA & Hn & _)]. unfold L5.u64_at. rewrite definitions.Z_to_bv_bv_unsigned.
  cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  change (word_to_le_bytes 8 w) with (le8 w). rewrite <- (rdn_of_bytes_at m (le8 w) A); [reflexivity| lia| |exact HB].
  cbn [cells_size csize] in Hn. change (length (le8 w)) with 8%nat. lia.
Qed.

Lemma u8_of_cells : forall m A b cs, rw_cells rsegs m A (C1 b :: cs) -> L5.u8_at rsegs m A (bv_unsigned b).
Proof.
  intros m A b cs [[WF HB] (HA & Hn & _)]. unfold L5.u8_at. rewrite definitions.Z_to_bv_bv_unsigned.
  cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. destruct HB as [HB _].
  rewrite <- (rdn_of_bytes_at m [b] A); [reflexivity| lia| |exact HB]. cbn [cells_size csize length] in Hn |- *. lia.
Qed.

Lemma bytes_of_cells : forall m A n zs cs, rw_cells rsegs m A (CB n (map b8 zs) :: cs) -> length zs = n -> L5.bytes_at rsegs m A zs.
Proof.
  intros m A n zs cs [[WF HB] (HA & Hn & _)] L i Hi. unfold L5.u8_at.
  cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. destruct HB as [(_ & Hl & HB) _]. rewrite length_map in Hl.
  rewrite rdn_unfold. change (Z_to_bv 64 (A + Z.of_nat i)) with (wa (A + Z.of_nat i)). rewrite (HB i) by (rewrite length_map; exact Hi).
  rewrite nth_error_map. rewrite (nth_error_nth' zs 0) by exact Hi. cbn. reflexivity.
Qed.

Lemma cells_of_L5bytes : forall M p zs, L5.bytes_at rsegs M p zs -> 0 <= p -> p + Z.of_nat (length zs) <= 2^64 ->
  bytes_at rsegs M p (map b8 zs).
Proof.
  intros M p zs H Hp Hn. split; [exact Hp|]. split; [rewrite length_map; exact Hn|].
  intros i Hi. rewrite length_map in Hi. specialize (H i Hi). unfold L5.u8_at in H. rewrite rdn_unfold in H.
  change (Z_to_bv 64 (p + Z.of_nat i)) with (wa (p + Z.of_nat i)) in H.
  destruct (mrd rsegs M (wa (p + Z.of_nat i))) as [b|] eqn:E; [|discriminate]. destruct (rdn rsegs M _ 0) eqn:E2; [|discriminate].
  inversion H; subst. rewrite nth_error_map, (nth_error_nth' zs 0) by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_of_defined : forall M a (k : nat), (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (a + i)) <> None) ->
  (0 <= a /\ (a + Z.of_nat k <= 0x10000 \/ 0x92000 <= a)) -> a + Z.of_nat k <= 2^64 ->
  exists bs, rw_cells rsegs M a [CB k bs].
Proof.
  intros M a k D Ha Hk.
  assert (ST : stk rsegs M a (a + Z.of_nat k)).
  { split; [lia|]. split; [lia|]. intros x Hx. specialize (D (x - a) ltac:(lia)). replace (a + (x - a)) with x in D by lia.
    assert (Hwa : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia). split.
    - rewrite ref_wview_overlay by (rewrite Hwa; lia). unfold wa. exact D.
    - rewrite ref_mrd_overlay by (rewrite Hwa; lia). unfold wa. destruct (M (Z_to_bv 64 x)) as [b|]; [exists b; reflexivity| congruence]. }
  destruct (stk_carve rsegs M a (a + Z.of_nat k) k ST ltac:(lia)) as [_ [junk FR]].
  replace (a + Z.of_nat k - Z.of_nat k) with a in FR by lia. exists junk. exact FR.
Qed.

(* [comment removed for export] *)
Lemma rw_recell : forall m A cs cs', rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells rsegs m A cs'.
Proof. intros m A cs cs' [[WF HB] W] WF' EB ES. split; [split; [exact WF'| rewrite EB; exact HB]| rewrite ES; exact W]. Qed.

Lemma rw_split : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[WF HB] (HA & Hn & W)]. apply cells_wf_app in WF. destruct WF as [W1 W2].
  rewrite cells_bytes_app in HB. apply bytes_at_app in HB. destruct HB as [B1 B2]. rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app in Hn, W. split.
  - split; [split; [exact W1| exact B1]|]. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia.
  - split; [split; [exact W2| exact B2]|]. split; [lia|]. split; [lia|]. intros i Hi. replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply W. lia.
Qed.

Lemma CB_cut : forall m A (k1 k2 : nat) bs, rw_cells rsegs m A [CB (k1 + k2) bs] ->
  rw_cells rsegs m A [CB k1 (firstn k1 bs)] /\ rw_cells rsegs m (A + Z.of_nat k1) [CB k2 (skipn k1 bs)].
Proof.
  intros m A k1 k2 bs RW. pose proof (proj1 (proj1 RW)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [L _].
  assert (RW' : rw_cells rsegs m A ([CB k1 (firstn k1 bs)] ++ [CB k2 (skipn k1 bs)])).
  { eapply rw_recell; [exact RW| | |]; cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize app].
    - rewrite firstn_length, skipn_length. repeat split; lia.
    - rewrite !app_nil_r. apply firstn_skipn.
    - lia. }
  apply rw_split in RW'. cbn [cells_size csize] in RW'. rewrite Nat.add_0_r in RW'. exact RW'.
Qed.

Lemma C1_of_CB1 : forall m A bs, rw_cells rsegs m A [CB 1 bs] -> exists b, rw_cells rsegs m A [C1 b].
Proof.
  intros m A bs RW. pose proof (proj1 (proj1 RW)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [L _].
  destruct bs as [|b [|]]; cbn in L; try lia. exists b. eapply rw_recell; [exact RW| exact (conj I I)| reflexivity| reflexivity].
Qed.

Lemma C1CB_of_CB : forall m A (k : nat) bs, rw_cells rsegs m A [CB (S k) bs] -> exists b j, rw_cells rsegs m A [C1 b; CB k j].
Proof.
  intros m A k bs RW. pose proof (proj1 (proj1 RW)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [L _].
  destruct bs as [|b j]; [cbn in L; lia|]. exists b, j. cbn in L.
  eapply rw_recell; [exact RW| cbn; split; [exact I| split; [lia| exact I]]| reflexivity| reflexivity].
Qed.

Lemma testbit_high : forall a i, 0 <= a < 2 ^ 64 -> 64 <= i -> Z.testbit a i = false.
Proof.
  intros a i Ha Hi. destruct (Z.eq_dec a 0) as [->|NZ]; [apply Z.testbit_0_l|].
  apply Z.bits_above_log2; [lia|]. eapply Z.lt_le_trans; [| exact Hi]. apply Z.log2_lt_pow2; lia.
Qed.
(* [comment removed for export] *)
Lemma lxor_ones64 : forall p, 0 <= p < 2^64 -> Z.lxor p 18446744073709551615 = 18446744073709551615 - p.
Proof.
  intros p Hp. change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec.
  destruct (Z_lt_le_dec i 64) as [L|G].
  - rewrite Z.ones_spec_low by lia.
    replace (Z.ones 64 - p) with ((Z.lnot p) mod 2^64).
    2:{ unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l. Z.div_mod_to_equations. lia. }
    rewrite (Z.mod_pow2_bits_low (Z.lnot p) 64 i) by lia. rewrite Z.lnot_spec by lia. destruct (Z.testbit p i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite (testbit_high p i) by lia.
    rewrite (testbit_high (Z.ones 64 - p) i); [reflexivity| unfold Z.ones; rewrite Z.shiftl_1_l; lia| lia].
Qed.

(* [comment removed for export] *)
Lemma memmove_apart : forall src p n cap,
  0 < n -> n + 1 <= cap -> n < 2^60 -> 0 <= src -> src + n <= 2^47 -> 0 <= p -> p + cap <= 2^47 -> (src + n <= p \/ p + cap <= src) ->
  Z.land (src + - (n + p)) 18446744073709551615 <= Z.land (0 + - Z.land (Z.shiftl n 1) 18446744073709551615) 18446744073709551615.
Proof.
  intros src p n cap Hn Hc Hn2 S0 S1 P0 P1 SEP.
  change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (Z.mod_small (n * 2)) by lia.
  replace ((0 + - (n * 2)) mod 2 ^ 64) with (2 ^ 64 - n * 2) by (Z.div_mod_to_equations; lia).
  destruct SEP as [A|A].
  - replace ((src + - (n + p)) mod 2 ^ 64) with (2 ^ 64 + (src - n - p)) by (Z.div_mod_to_equations; lia). lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma w_long1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (lo n : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 48 ->
  a2 = wz n -> 23 <= n < 2^26 ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (wz 0x20af0) (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz n) a1 (wz (str_cap n)) (Z_to_bv 64 (-8)) a2 a3 a4 a5 a6 a7
                   a0 s3 (wz (str_cap n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 OPNEW) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_grows m m' /\ stk rsegs m' lo (bv_unsigned sp + -48))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRINIT) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros ST CLO LO -> Hn. unfold STRINIT, OPNEW.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (mem_grows_refl m) as MG.
  carve_frame 48%nat ST.
  do 7 st1.   (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. lia. }
  rewrite ?wz_unsigned in K, K2 by lia.
  st1. st1. st1. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
  - (* [comment removed for export] *) st1. st1. st1.
    replace (Z.lor n 7 + 1) with (str_cap n) by (unfold str_cap; destruct (Z.eqb_spec (Z.lor n 7) 23); lia).
    finish. all: try exact FR.
  - (* [comment removed for export] *) st1. st1. st1. st1.
    replace 26 with (str_cap n) by (unfold str_cap; destruct (Z.eqb_spec (Z.lor n 7) 23); lia).
    finish. all: try exact FR.
Qed.

(* [comment removed for export] *)
Lemma w_long2 : forall (rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rao s0o s1o s2o s3o s4o : word) F fc m (n cap p o src : Z) (sbytes junkO junk1 junk2 : list byte) (jb : byte),
  23 <= n -> n + 1 <= cap -> cap < 2^40 -> 4096 <= p -> (p + cap <= 0x10000 \/ 0x92000 <= p) -> p + cap <= bv_unsigned sp - 48 ->
  0x7fff7f800000 + 48 <= bv_unsigned sp -> bv_unsigned sp <= o -> o + 24 <= 2^47 ->
  0 <= src -> src + n <= 2^47 -> (src + n <= p \/ p + cap <= src) -> (o + 24 <= src \/ src + n <= o) ->
  length sbytes = Z.to_nat n ->
  rw_cells rsegs m (bv_unsigned sp + -48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  rw_cells rsegs m o [CB 24 junkO] ->
  rw_cells rsegs m p [CB (Z.to_nat n) junk1] ->
  rw_cells rsegs m (p + n) [C1 jb; CB (Z.to_nat (cap - n - 1)) junk2] ->
  bytes_at rsegs m src sbytes ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o a0' a1' a2' a3' a4' a5' a6' a7'
                   s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rao) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' o [C8 (Z_to_bv 64 (cap + 1)); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 p)]
      /\ rw_cells rsegs m' p [CB (Z.to_nat n) sbytes]
      /\ rw_cells rsegs m' (p + n) [C1 (b8 0); CB (Z.to_nat (cap - n - 1)) junk2]
      /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 rao]
      /\ munch [(o, o + 24); (p, p + cap)] m m' /\ wmono rsegs m m' /\ mem_grows m m')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 src) (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 o) s3 (Z_to_bv 64 cap) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20af0) fc None m (seg_rom rsegs)).
Proof.
  intros until jb. intros Hn Hcap Hcap2 Hp Hp2 Hpc SPLO SPO OHI S0 SHI SEP1 SEP2 LEN FR OB PB PZ SB. unfold MEMMOVE.
  pose proof (munch_refl [(o, o + 24); (p, p + cap)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. st1. st1. if_cases K2; zify_cond K2.
  2:{ exfalso. pose proof (memmove_apart src p n cap ltac:(lia) Hcap ltac:(lia) S0 SHI ltac:(lia) ltac:(lia) SEP1). lia. }
  st1.
  call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 p src n sbytes junk1).
  all: try lia. all: try assumption. rename MI into PB. clear POST.
  (* [comment removed for export] *)
  st1. st1. if_cases KU; zify_cond KU. { exfalso. rewrite lxor_ones64 in KU by lia. lia. }
  st1. remember (p + n) as Q eqn:HQ in PZ |- *. st1. rewrite le1_wz. mem_after_store.
  do 7 st1. st1. subst Q.
  finish.
  eapply mem_grows_of_cover2; [exact MU|]. intros xq [Hx|Hx].
  - eapply (rw_cells_defined _ _ _ xq OB); cbn [cells_size csize Nat.add]; lia.
  - destruct (Z_lt_le_dec xq (p + n)); [eapply (rw_cells_defined _ _ _ xq PB)| eapply (rw_cells_defined _ _ _ xq PZ)]; cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma w_sso : forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (lo n o src : Z) (sbytes junk1 junk2 : list byte) (j0 jb : byte),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 48 ->
  0 < n < 23 -> bv_unsigned sp <= o -> o + 24 <= 2^47 ->
  0 <= src -> src + n <= 2^47 -> (o + 24 <= src \/ src + n <= o) -> (src + n <= bv_unsigned sp - 48 \/ bv_unsigned sp <= src) ->
  length sbytes = Z.to_nat n ->
  rw_cells rsegs m o [C1 j0] ->
  rw_cells rsegs m (o + 1) [CB (Z.to_nat n) junk1] ->
  rw_cells rsegs m (o + 1 + n) [C1 jb; CB (Z.to_nat (22 - n)) junk2] ->
  bytes_at rsegs m src sbytes ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (w0 w1 w2 w3 w4 w5 : word),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' o [C1 (b8 (n * 2))]
      /\ rw_cells rsegs m' (o + 1) [CB (Z.to_nat n) sbytes]
      /\ rw_cells rsegs m' (o + 1 + n) [C1 (b8 0); CB (Z.to_nat (22 - n)) junk2]
      /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5]
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (o, o + 24)] m m' /\ wmono rsegs m m' /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRINIT) fc None m (seg_rom rsegs)).
Proof.
  intros until jb. intros ST CLO LO Hn SPO OHI S0 SHI SEP SEPF LEN O0 OD OZ SB. unfold STRINIT, MEMMOVE.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (o, o + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj SB I) as SBK. clear SB.
  carve_frame 48%nat ST.
  do 7 st1.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. lia. }
  st1. st1. rewrite le1_wz, Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. mem_after_store.
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  st1. if_cases K4; zify_cond K4. { exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  st1. st1. st1. st1. st1. if_cases K5; zify_cond K5.
  2:{ exfalso. pose proof (memmove_apart src (o + 1) n 23 ltac:(lia) ltac:(lia) ltac:(lia) S0 SHI ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  st1.
  call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (o + 1) src n sbytes junk1).
  all: try lia. all: try assumption.
  { eapply (bytes_at_transport rsegs _ _ _ _ _ (proj1 SBK)); [eassumption| rewrite LEN, Z2Nat.id by lia; cbn; lia]. }
  rename MI into OD. clear POST.
  (* [comment removed for export] *)
  st1. st1. if_cases KU; zify_cond KU. { exfalso. rewrite lxor_ones64 in KU by lia. lia. }
  st1. remember (o + 1 + n) as Q eqn:HQ in OZ |- *. st1. rewrite le1_wz. mem_after_store.
  do 7 st1. st1. subst Q.
  finish. { exact FR. }
  eapply mem_grows_of_cover2; [exact MU|]. intros xq [Hx|Hx].
  - eapply (rw_cells_defined _ _ _ xq FR); cbn [cells_size csize Nat.add]; lia.
  - destruct (Z_lt_le_dec xq (o + 1)); [eapply (rw_cells_defined _ _ _ xq O0); cbn [cells_size csize Nat.add]; lia|].
    destruct (Z_lt_le_dec xq (o + 1 + n)); [eapply (rw_cells_defined _ _ _ xq OD)| eapply (rw_cells_defined _ _ _ xq OZ)]; cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma w_sso0 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (lo o : Z) (junk2 : list byte) (j0 jb : byte),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 48 ->
  bv_unsigned sp <= o -> o + 24 <= 2^47 ->
  rw_cells rsegs m o [C1 j0] ->
  rw_cells rsegs m (o + 1) [C1 jb; CB 22 junk2] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (w0 w1 w2 w3 w4 w5 : word),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' o [C1 (b8 0)]
      /\ rw_cells rsegs m' (o + 1) [C1 (b8 0); CB 22 junk2]
      /\ rw_cells rsegs m' (bv_unsigned sp + -48) [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5]
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp); (o, o + 24)] m m' /\ wmono rsegs m m' /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1 (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRINIT) fc None m (seg_rom rsegs)).
Proof.
  intros until jb. intros ST CLO LO SPO OHI O0 OZ. unfold STRINIT.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (o, o + 24)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 st1.
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. lia. }
  st1. st1. rewrite le1_wz. change (Z.shiftl 0 1) with 0. mem_after_store.
  st1. st1. if_cases K3; zify_cond K3. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia. lia. }
  st1. st1. st1. if_cases KU; zify_cond KU. { exfalso. rewrite lxor_ones64 in KU by lia. lia. }
  st1. st1. rewrite le1_wz. mem_after_store.
  do 7 st1. st1.
  finish. { exact FR. }
  eapply mem_grows_of_cover2; [exact MU|]. intros xq [Hx|Hx].
  - eapply (rw_cells_defined _ _ _ xq FR); cbn [cells_size csize Nat.add]; lia.
  - destruct (Z_lt_le_dec xq (o + 1)); [eapply (rw_cells_defined _ _ _ xq O0)| eapply (rw_cells_defined _ _ _ xq OZ)]; cbn [cells_size csize Nat.add]; lia.
Qed.
End TSSU.
