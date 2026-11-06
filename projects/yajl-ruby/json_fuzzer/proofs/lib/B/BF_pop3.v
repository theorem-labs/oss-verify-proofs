(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Arr Frame Cells Step.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_place BF_kit BF_kit2 BF_free_kit BF_popdefs BF_pop1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac cstep := stepA; try first [if_true | if_false].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition A_POP_EFARET : Z := 0x37d98.   (* [comment removed for export] *)
Definition A_POP_LOOP : Z := 0x37dc0.
Definition A_POP_TAIL : Z := 0x37de0.
Definition A_POP_FAIL : Z := 0x37e94.

(* [comment removed for export] *)
Fixpoint filln (n : nat) (ws : list word) (j : nat) (au size tf : Z) : list word :=
  match n with
  | O => ws
  | S n' => filln n' (upd ws (Z.to_nat (tf - 1 - Z.of_nat j)) (Z_to_bv 64 ((au + Z.of_nat j * size) / 16))) (S j) au size tf
  end.
Lemma filln_length : forall n ws j au size tf, length (filln n ws j au size tf) = length ws.
Proof. aceil. induction n; intros; cbn; [reflexivity|]. rewrite IHn, upd_length. reflexivity. Qed.

(* [comment removed for export] *)
Lemma wr_at_join : forall segs m a n1 n2, wr_at segs m a n1 -> wr_at segs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at segs m a (n1 + n2).
Proof. aceil.
  intros segs m a n1 n2 (A1 & B1 & W1) (A2 & B2 & W2) H1 H2. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n1); [apply W1; lia|].
  replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.
Lemma u32arr_app : forall m A ws1 ws2,
  u32arr bsegs m A ws1 -> u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2 -> u32arr bsegs m A (ws1 ++ ws2).
Proof. aceil.
  intros m A ws1 ws2 [B1 W1] [B2 W2]. split.
  - rewrite u32s_app. apply bytes_at_app. split; [exact B1|]. rewrite u32s_length.
    replace (A + Z.of_nat (4 * length ws1)) with (A + 4 * Z.of_nat (length ws1)) by lia. exact B2.
  - rewrite length_app. replace (4 * Z.of_nat (length ws1 + length ws2)) with (4 * Z.of_nat (length ws1) + 4 * Z.of_nat (length ws2)) by lia.
    apply wr_at_join; [exact W1| exact W2| lia| lia].
Qed.
Lemma u32arr_split : forall m A ws1 ws2,
  u32arr bsegs m A (ws1 ++ ws2) -> u32arr bsegs m A ws1 /\ u32arr bsegs m (A + 4 * Z.of_nat (length ws1)) ws2.
Proof. aceil.
  intros m A ws1 ws2 [B W]. rewrite u32s_app in B. apply bytes_at_app in B as [B1 B2]. rewrite u32s_length in B2.
  rewrite length_app in W.
  split; split.
  - exact B1.
  - eapply wr_at_sub; [exact W| lia| lia].
  - replace (A + 4 * Z.of_nat (length ws1)) with (A + Z.of_nat (4 * length ws1)) by lia. exact B2.
  - eapply wr_at_sub; [exact W| lia| lia].
Qed.
Lemma u32s_zeros : forall n, u32s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (4 * n)%nat.
Proof. aceil. induction n as [|n IH]; [reflexivity|]. cbn [repeat u32s]. rewrite IH. replace (4 * S n)%nat with (4 + 4 * n)%nat by lia. rewrite repeat_app. reflexivity. Qed.
Lemma u32arr_of_zeros_nat : forall m A n,
  rw_cells bsegs m A [CB (4 * n)%nat (repeat (Z_to_bv 8 0) (4 * n)%nat)] -> u32arr bsegs m A (repeat (Z_to_bv 64 0) n).
Proof. aceil.
  intros m A n [[WF B] W]. split.
  - rewrite u32s_zeros. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
  - rewrite repeat_length. cbn [cells_size csize Nat.add] in W. replace (4 * Z.of_nat n) with (Z.of_nat (4 * n + 0)) by lia. exact W.
Qed.
Lemma u32arr_of_zeros : forall m A L K,
  rw_cells bsegs m A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))] -> L = 4 * K -> 0 <= K ->
  u32arr bsegs m A (repeat (Z_to_bv 64 0) (Z.to_nat K)).
Proof. aceil.
  intros m A L K H HL HK. subst L. rewrite Z2Nat.inj_mul in H by lia. change (Z.to_nat 4) with 4%nat in H.
  apply u32arr_of_zeros_nat. exact H.
Qed.

Lemma v_divu_lit : forall x y, 0 <= x < 2^64 -> 0 < y < 2^64 -> v_divu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof. aceil.
  intros x y Hx Hy. unfold v_divu. rewrite !Z_to_bv_small by (change (bv_modulus 64) with (2^64); lia).
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Section POP3.
Variable P : acc -> Prop.
Variables (gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo : Z) (SB c RI : Z).
Notation INST := 0xaaf58.
Notation RIc := (BF_popdefs.RIc c RI).
Notation RB := (SB + c * 4294967296).
Notation FA := (SB + c * 4294967296 + 3758096384).
Notation size := (class_size c).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 1536.
Hypothesis SPH : usp < 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HSBH : kHighMemBeg <= SB.
Hypothesis HC : 1 <= c <= kLargestClassID.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RIc <= a -> a + Z.of_nat k <= RIc + 128 -> P (Z_to_bv 64 a, k).

Notation pop_frame := (BF_pop1.pop_frame usp).

(* [comment removed for export] *)
Lemma pop_mid : forall m (ra0 s1x s3x s6x t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mtx nf mfa au mu1 na nfr : Z) (Q : machine_state -> Prop),
  mem_inv bsegs m ->
  rw_cells bsegs m RIc (ri_cells mtx nf mfa au mu1 na nfr) ->
  0 <= au <= mu1 -> mu1 <= 3758096384 -> 0 <= nf < 2^40 ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_POP_EFARET) (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 (nf + (mu1 - au) / size)) (Z_to_bv 64 INST)
                          (Z_to_bv 64 RIc) (Z_to_bv 64 RB) (Z_to_bv 64 (nf + (mu1 - au) / size)) a4 a5 a6 a7
                          (Z_to_bv 64 RB) (Z_to_bv 64 ((mu1 - au) / size)) (Z_to_bv 64 (mu1 - au)) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x358c8) fc None m (seg_rom bsegs)) ->
  evtA bsegs P Q (MS (mkR ra0 (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) s1x (Z_to_bv 64 INST) a1 a2 (Z_to_bv 64 au) a4 a5 a6 a7
                          (Z_to_bv 64 RB) s3x (Z_to_bv 64 mu1) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_POP_MID) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros MI RIC AU MU1 NF K. unfold A_POP_MID, A_POP_EFARET, ri_cells in *.
  pose proof HSB as (SB1 & SB2 & SB3). unfold kSpaceSize in SB3; aceil. unfold kLargestClassID in HC.
  pose proof (class_size_mod c ltac:(lia)) as [_ CS].
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  assert (HRIr : 0x603000 <= RIv /\ RIv + 128 <= 2^47) by (rewrite HRIv, HRI; unfold kSpaceSize; clear -CEILB SB1 SB3 HC; lia).
  assert (ND : 0 <= (mu1 - au) / size <= mu1 - au).
  { split; [apply Z.div_pos; clear -CEILB AU CS; lia|]. apply Z.div_le_upper_bound; [clear -CEILB CS; lia|]. clear -CEILB AU CS; nia. }
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  rewrite (v_divu_lit (mu1 - au) size) by (clear -CEILB AU MU1 CS; lia).
  zstepA.                         (* [comment removed for export] *)
  do 3 zstepA.                    (* [comment removed for export] *)
  cstep.                          (* [comment removed for export] *)
  subst RIv. exact K.
Qed.

(* [comment removed for export] *)
Lemma pop_fill_loop : forall (k : nat) (i : Z) m (ws : list word) (ra0 s6x t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (au new tf s4v : Z)
    (Q : machine_state -> Prop),
  Z.of_nat k = new - i -> 0 <= i < new -> new <= tf -> tf <= Z.of_nat (length ws) -> 4 * Z.of_nat (length ws) <= 2^29 ->
  0 <= au -> au + new * size <= 3758096384 ->
  mem_inv bsegs m -> u32arr bsegs m FA ws ->
  (forall a n, FA + 4 * (tf - new) <= a -> a + Z.of_nat n <= FA + 4 * tf -> P (Z_to_bv 64 a, n)) ->
  (forall m', mem_inv bsegs m' -> munch [(FA + 4 * (tf - new), FA + 4 * (tf - i))] m m' -> wmono bsegs m m' ->
     u32arr bsegs m' FA (filln k ws (Z.to_nat i) au size tf) ->
     evtA bsegs P Q (MS (mkR ra0 (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 (4 * tf)) (Z_to_bv 64 new)
                             (Z_to_bv 64 (FA + 4 * tf)) (Z_to_bv 64 (au + new * size)) a3 (Z_to_bv 64 ((au + (new - 1) * size) / 16)) (Z_to_bv 64 (FA + 4 * (tf - new))) a6 a7
                             (Z_to_bv 64 RB) (Z_to_bv 64 new) (Z_to_bv 64 s4v) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 A_POP_TAIL) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra0 (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 (4 * tf)) (Z_to_bv 64 i)
                          (Z_to_bv 64 (FA + 4 * tf)) (Z_to_bv 64 (au + i * size)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 RB) (Z_to_bv 64 new) (Z_to_bv 64 s4v) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_POP_LOOP) fc None m (seg_rom bsegs)).
Proof. aceil.
  induction k as [|k IH]; intros i m ws ra0 s6x t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 au new tf s4v Q Hk Hi NT TL WL AU0 AUB MI FAR PFA CONT; [lia|].
  unfold A_POP_LOOP, A_POP_TAIL in *.
  pose proof HSB as (SB1 & SB2 & SB3). unfold kSpaceSize in SB3; aceil. unfold kLargestClassID in HC.
  pose proof (class_size_mod c ltac:(lia)) as [_ CS].
  set (FAv := SB + c * 4294967296 + 3758096384) in *. assert (HFAv : FAv = SB + c * 4294967296 + 3758096384) by reflexivity. clearbody FAv.
  assert (HFAr : 0 <= FAv /\ FAv + 2^29 <= 2^47) by (rewrite HFAv; clear -CEILB SB1 SB3 HC; nia).
  assert (MU : munch [(FAv + 4 * (tf - new), FAv + 4 * (tf - i))] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  assert (AI : 0 <= au + i * size /\ au + i * size + size <= 3758096384) by (clear -CEILB Hi AU0 AUB CS; nia).
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (FAv + 4 * tf + Z.shiftl (Z.lxor i 18446744073709551615) 2)) with (Z_to_bv 64 (FAv + 4 * (tf - 1 - i)));
    [| apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2^64);
       rewrite ZBridge.zb_lxor_ones by (clear -CEILB Hi NT TL WL; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); change (2^2) with 4;
       clear -CEILB Hi NT TL WL HFAr; Z.div_mod_to_equations; lia ].
  rewrite (Z.shiftr_div_pow2 (au + i * size) 4) by (clear; lia). change (2^4) with 16.
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m0 _) =>
    pose proof (u32arr_store_ok bsegs m0 FAv ws (tf - 1 - i) (Z_to_bv 64 (FAv + 4 * (tf - 1 - i))) FAR ltac:(clear -CEILB Hi NT TL; lia) ltac:(reflexivity)) as SOK;
    pose proof (u32arr_write bsegs m0 FAv ws (tf - 1 - i) (Z_to_bv 64 ((au + i * size) / 16)) FAR ltac:(clear -CEILB Hi NT TL; lia)) as FAR' end.
  stepA.                          (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PFA; clear -CEILB Hi NT TL HFAv; lia | _ => idtac end.
  clear FAR. store_done. rename FAR' into FAR.
  zstepA.                         (* [comment removed for export] *)
  replace (au + i * size + size) with (au + (i + 1) * size) by (clear; lia).
  zstepA. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
    eapply (IH (i + 1) _ (upd ws (Z.to_nat (tf - 1 - i)) (Z_to_bv 64 ((au + i * size) / 16))));
      [clear -CEILB Hk Hi KL; lia| | exact NT| rewrite upd_length; exact TL| rewrite upd_length; exact WL| exact AU0| exact AUB| exact MI| exact FAR| exact PFA|].
    { revert KL. rewrite ?unsigned_lit by lia. clear -CEILB Hi Hk NT TL WL. intros KL. lia. }
    intros m' MI' MU' WM' FAR'. eapply CONT; [exact MI'| eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; intros xq Hq; cbn in Hq |- *; clear -CEILB Hq Hi; lia]
                                            | eapply wmono_trans; [exact WM| exact WM']|].
    cbn [filln]. replace (Z.of_nat (Z.to_nat i)) with i by (clear -CEILB Hi; lia). replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by (clear -CEILB Hi; lia). exact FAR'.
  - (* [comment removed for export] *)
    assert (Ei : new = i + 1) by (revert KL; rewrite ?unsigned_lit by lia; clear -CEILB Hi Hk NT TL WL; intros KL; lia).
    subst new. replace (i + 1 - 1) with i in CONT by (clear; lia). replace (tf - (i + 1)) with (tf - 1 - i) in * by (clear; lia).
    eapply CONT; [exact MI| exact MU| exact WM|].
    replace k with O by (clear -CEILB Hk; lia). cbn [filln]. replace (Z.of_nat (Z.to_nat i)) with i by (clear -CEILB Hi; lia). exact FAR.
Qed.

(* [comment removed for export] *)
Lemma pop_finish : forall m (ws : list word) (ra s0 s1 s2 s3 s4 s5 s6 s6x t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (mtx nf mfa au mu1 na nfr : Z) (Q : machine_state -> Prop),
  let new := (mu1 - au) / size in let tf := nf + new in
  mem_inv bsegs m -> stk bsegs m lo (usp - 64) -> pop_frame m ra s0 s1 s2 s3 s4 s5 s6 ->
  rw_cells bsegs m RIc (ri_cells mtx nf mfa au mu1 na nfr) ->
  0 <= au <= mu1 -> mu1 <= 3758096384 -> 0 <= nf -> tf <= Z.of_nat (length ws) -> 4 * Z.of_nat (length ws) = mfa -> mfa <= 2^29 ->
  u32arr bsegs m FA ws ->
  (forall a n, FA + 4 * nf <= a -> a + Z.of_nat n <= FA + 4 * tf -> P (Z_to_bv 64 a, n)) ->
  (forall m' (a2' a3' a4' a5' : word),
     mem_inv bsegs m' -> stk bsegs m' lo usp ->
     munch [(usp - 64, usp); (FA + 4 * nf, FA + 4 * tf); (RIc + 16, RIc + 24); (RIc + 32, RIc + 40); (RIc + 68, RIc + 69)] m m' -> wmono bsegs m m' ->
     rw_cells bsegs m' RIc (ri_cells mtx tf mfa (au + new * size) mu1 na nfr) ->
     u32arr bsegs m' FA (filln (Z.to_nat new) ws 0 au size tf) ->
     evtA bsegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) a2' a3' a4' a5' a6 a7
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR (Z_to_bv 64 A_POP_EFARET) (Z_to_bv 64 (usp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 RIc) (Z_to_bv 64 tf) (Z_to_bv 64 1)
                          a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 RB) (Z_to_bv 64 new) (Z_to_bv 64 (mu1 - au)) (Z_to_bv 64 size) s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 A_POP_EFARET) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until Q. intros new tf MI SK FR RIC AU MU1 NF TL WL MFR FAR PFA CONT.
  unfold A_POP_EFARET, BF_pop1.pop_frame, ri_cells in *.
  pose proof LOC as LOC0. aceil.
  pose proof HSB as (SB1 & SB2 & SB3). unfold kSpaceSize in SB3; aceil. unfold kLargestClassID in HC.
  pose proof (class_size_mod c ltac:(lia)) as [_ CS].
  unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv : RIv = RI + 128 * c) by reflexivity. clearbody RIv.
  assert (HRIr : 0x603000 <= RIv /\ RIv + 128 <= 2^47) by (rewrite HRIv, HRI; unfold kSpaceSize; clear -CEILB SB1 SB3 HC; lia).
  assert (HRI2 : RI = SB + 137438953472) by (rewrite HRI; reflexivity).
  assert (HFAr : 4294967296 <= SB + c * 4294967296 + 3758096384 /\ SB + c * 4294967296 + 3758096384 + 2^29 <= 2^47) by (clear -CEILB SB1 SB3 HC; nia).
  assert (ND : 0 <= new /\ new * size <= mu1 - au).
  { subst new. split; [apply Z.div_pos; clear -CEILB AU CS; lia|]. rewrite Z.mul_comm. apply Z.mul_div_le. clear -CEILB CS; lia. }
  assert (MU : munch [(usp - 64, usp); (SB + c * 4294967296 + 3758096384 + 4 * nf, SB + c * 4294967296 + 3758096384 + 4 * tf); (RIv + 16, RIv + 24); (RIv + 32, RIv + 40); (RIv + 68, RIv + 69)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  cstep.                          (* [comment removed for export] *)
  zstepA.                         (* [comment removed for export] *)
  zstepA; if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by (clear -CEILB AU MU1 CS; lia).
  - (* [comment removed for export] *)
    assert (N0 : new = 0) by (subst new; apply Z.div_small; clear -CEILB KB AU; lia).
    assert (ETF : tf = nf) by (subst tf; rewrite N0; clear; lia).
    rewrite N0 in *. rewrite ETF in *.
    zstepA.                       (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    zstepA. zstepA.               (* [comment removed for export] *)
    rewrite ?Z.mul_0_l, ?Z.add_0_r.
    cstep. cstep.                 (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB AU MU1; intros K1; lia|].   (* [comment removed for export] *)
    zstepA. zstepA.               (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    do 9 cstep.                   (* [comment removed for export] *)
    release_frame FR SK usp.
    cstep.                        (* [comment removed for export] *)
    replace (usp - 64 + 64) with usp by (clear; lia).
    subst RIv. rewrite Z.mul_0_l, Z.add_0_r in CONT.
    eapply CONT; [exact MI| exact SK| exact MU| exact WM| exact RIC| cbn [Z.to_nat filln]; exact FAR].
  - (* [comment removed for export] *)
    assert (N1 : 1 <= new) by (subst new; apply Z.div_le_lower_bound; clear -CEILB KB AU CS; lia).
    zstepA.                       (* [comment removed for export] *)
    do 3 zstepA.                  (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    replace (tf ≪ 2) with (4 * tf) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; clear; lia).
    rewrite ?(Z.mod_small (4 * tf)) by (clear -CEILB NF ND TL WL MFR; subst tf; lia).
    zstepA.                       (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    replace (Z_to_bv 64 au) with (Z_to_bv 64 (au + 0 * size)) by (f_equal; clear; lia).
    subst RIv.
    eapply (pop_fill_loop (Z.to_nat new) 0) with (tf := tf);
      [clear -CEILB ND; lia| clear -CEILB N1; lia| subst tf; clear -CEILB NF; lia| exact TL| clear -CEILB WL MFR; lia| clear -CEILB AU; lia| clear -CEILB ND AU MU1; lia| exact MI| exact FAR| |].
    { intros a n Ha Hn. apply PFA; subst tf; clear -CEILB Ha Hn; lia. }
    clear MI. intros m2 MI MU2 WM2 FAR2.
    replace (tf - new) with nf in MU2 by (subst tf; clear; lia). replace (tf - 0) with tf in MU2 by (clear; lia).
    replace (au + 0 * size) with au by (clear; lia).
    unfold BF_popdefs.RIc in *. set (RIv := RI + 128 * c) in *. assert (HRIv2 : RIv = SB + 137438953472 + 128 * c) by (subst RIv; rewrite HRI2; reflexivity). clearbody RIv.
    remember (filln (Z.to_nat new) ws (Z.to_nat 0) au size tf) as ws2 eqn:Hws2.
    assert (LEN2 : length ws2 = length ws) by (subst ws2; apply filln_length).
    lazymatch type of MU2 with munch _ ?mc _ => carry_all mc m2 MU2 WM2 end. clear MU2 WM2.
    zstepA.                       (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    zstepA. zstepA.               (* [comment removed for export] *)
    rewrite ?(Z.mod_small (new * size)) by (clear -CEILB ND AU MU1; lia).
    cstep. cstep.                 (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB AU MU1 ND; intros K1; lia|].   (* [comment removed for export] *)
    zstepA. zstepA.               (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    zstepA.                       (* [comment removed for export] *)
    cstep.                        (* [comment removed for export] *)
    do 9 cstep.                   (* [comment removed for export] *)
    release_frame FR SK usp.
    cstep.                        (* [comment removed for export] *)
    replace (usp - 64 + 64) with usp by (clear; lia).
    replace (nf + new) with tf by reflexivity. replace RIv with (RI + 128 * c) in * by (rewrite HRIv2, HRI2; reflexivity).
    eapply CONT; [exact MI| exact SK| exact MU| exact WM| exact RIC| subst ws2; exact FAR2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End POP3.
End RC__1.
