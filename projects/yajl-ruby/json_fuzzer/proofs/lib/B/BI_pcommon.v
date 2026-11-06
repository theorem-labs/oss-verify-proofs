(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr SFModel Image SysStep ZBridge.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BM_stdio_lib BI_shadow BI_memtoshadow BI_mem_is_zero BI_region_is_poisoned BI_ilibc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.lf_ceil_hook.   (* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition printf_common_entry : Z := 0x4588c.
Definition PAT : Z := 0xaaaaaaaaaaaaaaaa.
Definition T_flags : Z := 0x153a9.

Definition pcm_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, q)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo q.

Lemma firstn_repeat : forall {X} (x : X) n k, firstn n (repeat x k) = repeat x (Nat.min n k).
Proof. intros X x n; induction n as [|n IH]; intros [|k]; cbn; try reflexivity. now rewrite IH. Qed.
Lemma skipn_repeat : forall {X} (x : X) n k, skipn n (repeat x k) = repeat x (k - n).
Proof. intros X x n; induction n as [|n IH]; intros [|k]; cbn; try reflexivity. now rewrite IH. Qed.
Lemma landM1 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma landM1_mod : forall x, Z.land x 18446744073709551615 = x mod 2^64.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma zbv_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. Qed.
Lemma range_clean_zero : forall SB A n N, Z.of_nat N = shw_hi SB A n - shw_lo SB A -> 0 <= SB -> 0 <= A -> 1 <= n ->
  range_clean SB A n (repeat (Z_to_bv 8 0) N).
Proof.
  intros SB A n N HN H0 H1 H2 g Hg.
  pose proof (shw_geom SB A n H0 H1 H2) as GE. cbv zeta in GE.
  exists (Z_to_bv 8 0). split; [| left; reflexivity].
  apply nth_error_repeat. lia.
Qed.

(* [comment removed for export] *)
Lemma h3_negb_ltu : forall a b, negb (bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b)) = true ->
  Z.land b 18446744073709551615 <= Z.land a 18446744073709551615.
Proof.
  intros a b H. unfold bv_ltu in H. rewrite !Z_to_bv_unsigned, !landM1_mod in *. change (bv_modulus 64) with (2^64) in H.
  apply Bool.negb_true_iff in H. apply Z.ltb_ge in H. exact H.
Qed.
Lemma h3_negb_ltu_f : forall a b, negb (bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b)) = false ->
  Z.land a 18446744073709551615 < Z.land b 18446744073709551615.
Proof.
  intros a b H. unfold bv_ltu in H. rewrite !Z_to_bv_unsigned, !landM1_mod in *. change (bv_modulus 64) with (2^64) in H.
  apply Bool.negb_false_iff in H. apply Z.ltb_lt in H. exact H.
Qed.

Section Walk.
Variable P : acc -> Prop.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
          (q lo : Z) (ctx : word) (A AQ SB : Z) (pre post : list Z) (c : Z) (NF : nat)
          (SA : Z) (zs : list Z) (NA : nat).
Notation fmt := (pre ++ 37 :: c :: post).
Notation L := (zlength fmt).
Notation LA := (zlength zs).
Hypothesis HPRE : Forall (fun x => 0 < x < 256 /\ x <> 37) pre.
Hypothesis HPOST : Forall (fun x => 0 < x < 256 /\ x <> 37) post.
Hypothesis Hc : c = 115 \/ c = 100 \/ c = 117.
Hypothesis LEN : L <= 63.
Hypothesis FMT : hidden (bytes_at bsegs m A (zb fmt ++ [Z_to_bv 8 0])).
Hypothesis HA : 0x10000 <= A /\ A + 64 <= 0x31000.
Hypothesis FSH : hidden (bytes_at bsegs m (shw_lo SB A) (repeat (Z_to_bv 8 0) NF)).
Hypothesis HNF : Z.of_nat NF = shw_hi SB A (L + 1) - shw_lo SB A.
Hypothesis G : hidden (icp_globals bsegs m SB).
Hypothesis STK : hidden (stk bsegs m lo q).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LOq : lo <= q - 2320.
Hypothesis QHI : q < 2^47.
(* [comment removed for export] *)
Hypothesis MI : mem_inv bsegs m.
Hypothesis HAQ : AQ + 8 <= lo \/ q <= AQ.
Hypothesis AQ8 : 0 < AQ /\ AQ + 8 < 2^47.
(* [comment removed for export] *)
Hypothesis AQV : c = 115 -> hidden (rw_cells bsegs m AQ [C8 (Z_to_bv 64 SA)]).
Hypothesis STR : c = 115 -> hidden (bytes_at bsegs m SA (zb zs ++ [Z_to_bv 8 0])).
Hypothesis HZS : Forall (fun x => 0 < x < 256) zs.
Hypothesis HS : SB + 0x100000000000 <= SA /\ SA + LA + 1 < 2^47 /\ LA + 1 < 2^40.
Hypothesis HSD : SA + LA + 1 <= lo \/ q <= SA.
Hypothesis ASH : c = 115 -> hidden (bytes_at bsegs m (shw_lo SB SA) (repeat (Z_to_bv 8 0) NA)).
Hypothesis HNA : Z.of_nat NA = shw_hi SB SA (LA + 1) - shw_lo SB SA.
(* [comment removed for export] *)
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= q -> P (Z_to_bv 64 a, k).
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PFSH : forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A (L + 1) -> P (Z_to_bv 64 a, k).
Hypothesis PAQ : c = 115 -> P (Z_to_bv 64 AQ, 8%nat).
Hypothesis PSTR : c = 115 -> forall a k, SA <= a -> a + Z.of_nat k <= SA + LA + 1 -> P (Z_to_bv 64 a, k).
Hypothesis PASH : c = 115 -> forall a k, shw_lo SB SA <= a -> a + Z.of_nat k <= shw_hi SB SA (LA + 1) -> P (Z_to_bv 64 a, k).

Notation POST := (pcm_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo).

Lemma fmt_len : L = zlength pre + 2 + zlength post.
Proof. unfold zlength. rewrite length_app. cbn [length]. lia. Qed.
Lemma fmt_chars : Forall (fun x => 0 < x < 256) fmt.
Proof.
  apply Forall_app. split. { eapply Forall_impl; [|exact HPRE]. cbn. intros; lia. }
  constructor; [lia|]. constructor; [lia|]. eapply Forall_impl; [|exact HPOST]. cbn. intros; lia.
Qed.
Lemma SBR : 2^24 <= SB < 2^32.
Proof. pose proof G as G'. unfold hidden, icp_globals in G'. tauto. Qed.

(* [comment removed for export] *)
Lemma GEO_F :
  shw_lo SB A + 8 <= shw_hi SB A (L + 1) /\ shw_hi SB A (L + 1) <= shw_lo SB A + 16 /\
  shw_lo SB A mod 8 = 0 /\ shw_hi SB A (L + 1) mod 8 = 0 /\
  shw_lo SB A <= SB + Z.shiftr A 3 < shw_lo SB A + 8 /\
  shw_hi SB A (L + 1) - 8 <= SB + Z.shiftr (A + L) 3 < shw_hi SB A (L + 1) /\
  al8 (SB + Z.shiftr A 3) = shw_lo SB A /\ al8 (SB + Z.shiftr (A + L) 3) = shw_hi SB A (L + 1) - 8 /\
  SB <= shw_lo SB A /\ shw_hi SB A (L + 1) <= SB + A.
Proof.
  pose proof SBR. pose proof fmt_len.
  pose proof (shw_geom SB A (L + 1) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as GE. cbv zeta in GE.
  clear HPRE HPOST Hc FMT FSH HNF G STK LOC LOq QHI MI HAQ AQ8 AQV STR HZS HS HSD ASH HNA PSTK PIMG PFSH PAQ PSTR PASH.  (* [comment removed for export] *)
  replace (A + (L + 1) + -1) with (A + L) in GE by lia.
  unfold shw_hi, shw_lo in *. replace (A + (L + 1) + -1) with (A + L) by lia.
  pose proof (al8_le (SB + Z.shiftr A 3)). pose proof (al8_gt (SB + Z.shiftr A 3)).
  pose proof (al8_le (SB + Z.shiftr (A + L) 3)). pose proof (al8_gt (SB + Z.shiftr (A + L) 3)).
  rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
  unfold zlength in *. unfold al8 in *. repeat split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition TOPc : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition MREL (m1 : mem) : Prop := mem_inv bsegs m1 /\ munch [(lo, q)] m m1 /\ wmono bsegs m m1.
Definition FRM (m1 : mem) (jmid : list byte) (lowc : list cell) : Prop :=
  stk bsegs m1 lo (q - 2240) /\ rw_cells bsegs m1 (q + -104) TOPc /\
  rw_cells bsegs m1 (q + -2176) [CB 2072 jmid] /\ rw_cells bsegs m1 (q + -2240) lowc.

Lemma fmt_at : forall m1, MREL m1 -> bytes_at bsegs m1 A (zb fmt ++ [Z_to_bv 8 0]).
Proof.
  intros m1 (MI1 & MU1 & WM1). pose proof FMT as X. unhideH X. pose proof fmt_len.
  eapply (bytes_at_transport bsegs _ m m1); [exact X | exact MU1 |].
  cbn. rewrite length_app, zb_length. cbn [length]. unfold alloc_ceiling, sp_window_lo, stack_max_size, zlength in *. lia.
Qed.
Lemma fsh_at : forall m1, MREL m1 -> bytes_at bsegs m1 (shw_lo SB A) (repeat (Z_to_bv 8 0) NF).
Proof.
  intros m1 (MI1 & MU1 & WM1). pose proof FSH as X. unhideH X. pose proof GEO_F. pose proof SBR.
  eapply (bytes_at_transport bsegs _ m m1); [exact X | exact MU1 |].
  cbn. rewrite repeat_length, HNF. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.
Lemma g_at : forall m1, MREL m1 -> icp_globals bsegs m1 SB.
Proof.
  intros m1 (MI1 & MU1 & WM1). pose proof G as X. unhideH X.
  eapply (icp_globals_transport bsegs _ m m1); [exact X | exact MU1 | exact WM1 |].
  cbn. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.

Lemma aqv_at : forall m1, c = 115 -> MREL m1 -> rw_cells bsegs m1 AQ [C8 (Z_to_bv 64 SA)].
Proof.
  intros m1 E (MI1 & MU1 & WM1). pose proof (AQV E) as X. unhideH X.
  eapply (rw_cells_transport bsegs _ m m1); [exact X | exact MU1 | exact WM1 | cbn; lia].
Qed.
Lemma str_at : forall m1, c = 115 -> MREL m1 -> bytes_at bsegs m1 SA (zb zs ++ [Z_to_bv 8 0]).
Proof.
  intros m1 E (MI1 & MU1 & WM1). pose proof (STR E) as X. unhideH X.
  eapply (bytes_at_transport bsegs _ m m1); [exact X | exact MU1 |].
  cbn. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma GEO_A :
  let g1 := Z.shiftr SA 3 in let g2 := Z.shiftr (SA + (LA + 1) + -1) 3 in
  0 <= g1 /\ g1 <= g2 /\
  shw_lo SB SA <= SB + g1 /\ SB + g1 < shw_lo SB SA + 8 /\ shw_lo SB SA mod 8 = 0 /\
  shw_hi SB SA (LA + 1) - 8 <= SB + g2 /\ SB + g2 < shw_hi SB SA (LA + 1) /\ shw_hi SB SA (LA + 1) mod 8 = 0 /\
  shw_lo SB SA + 8 <= shw_hi SB SA (LA + 1) /\
  SB <= shw_lo SB SA /\ shw_hi SB SA (LA + 1) <= SB + Z.shiftr (SA + LA) 3 + 8 /\ Z.shiftr (SA + LA) 3 < 2^44.
Proof.
  pose proof SBR. pose proof HS.
  pose proof (shw_geom SB SA (LA + 1) ltac:(lia) ltac:(lia) ltac:(unfold zlength; lia)) as GE. cbv zeta in GE.
  clear HPRE HPOST Hc LEN FMT HA FSH HNF G STK LOC LOq QHI MI HAQ AQ8 AQV STR HZS HSD ASH HNA PSTK PIMG PFSH PAQ PSTR PASH.  (* [comment removed for export] *)
  replace (SA + (LA + 1) + -1) with (SA + LA) in * by lia. cbv zeta.
  unfold shw_hi, shw_lo, al8 in *. replace (SA + (LA + 1) + -1) with (SA + LA) by lia.
  rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
  unfold zlength in *. repeat split; Z.div_mod_to_equations; lia.
Qed.
Lemma ash_at : forall m1, c = 115 -> MREL m1 -> bytes_at bsegs m1 (shw_lo SB SA) (repeat (Z_to_bv 8 0) NA).
Proof.
  intros m1 E (MI1 & MU1 & WM1). pose proof (ASH E) as X. unhideH X. pose proof GEO_A as GA. cbv zeta in GA. pose proof SBR.
  eapply (bytes_at_transport bsegs _ m m1); [exact X | exact MU1 |].
  cbn. rewrite repeat_length, HNA. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
Qed.
(* [comment removed for export] *)
Lemma zwin_read8 : forall m1 W N (k : Z) a, bytes_at bsegs m1 W (repeat (Z_to_bv 8 0) N) -> 0 <= k -> k + 8 <= Z.of_nat N ->
  a = wa (W + k) -> ov_read_bytes bsegs m1 a 8 = Some (repeat (Z_to_bv 8 0) 8).
Proof.
  intros m1 W N k a B Hk HkN ->. rewrite (bytes_at_read bsegs m1 W _ k 8 B Hk ltac:(rewrite repeat_length; lia)).
  rewrite skipn_repeat, firstn_repeat. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition LOWc (j0 : list byte) (e1 cx fw idx be en : word) (sw sp lm0 lm1 cv : byte) (j3 : list byte) : list cell :=
  [CB 8 j0; C8 e1; C8 cx; C8 fw; C8 idx; C8 be; C8 en; C1 sw; C1 sp; C1 lm0; C1 lm1; C1 cv; CB 3 j3].

Notation M1 := 18446744073709551615.
Notation wz x := (Z_to_bv 64 x) (only parsing).
(* [comment removed for export] *)
Notation AT pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 cur x21 x22 x23 x28 x29 x30 x31 :=
  (MS (mkR x1 (Z_to_bv 64 (q + -2240)) gp tp x5 x6 x7 (Z_to_bv 64 q) x9 x10 x11 x12 x13 x14 x15 x16 x17
          (Z_to_bv 64 10) (Z_to_bv 64 cur) (Z_to_bv 64 T_flags) x21 x22 x23 (Z_to_bv 64 (q + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 M1) (Z_to_bv 64 37) x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

Ltac kz K := rewrite ?landM1, ?unsigned_lit, ?unsigned_lit8 in K by lia.
Ltac hideD := hideH HAQ; hideH HSD; hideH HS; hideH AQ8.
Ltac prep := hideD; unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC;
  let LEN' := fresh "LEN'" in pose proof LEN as LEN'; unfold zlength in LEN'.
Ltac open_frm H := destruct H as (?SK & ?TOP & ?MID & ?LOW).
Ltac open_mrel H := destruct H as (?MI1 & ?MU1 & ?WM1).

(* [comment removed for export] *)
Lemma pcm_epi : forall m1 jmid j0 e1 cx fw idx be en sw sp lm0 lm1 cv j3
    x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 cur x21 x22 x23 x28 x29 x30 x31,
  MREL m1 -> FRM m1 jmid (LOWc j0 e1 cx fw idx be en sw sp lm0 lm1 cv j3) ->
  evtA bsegs P POST (AT 0x46178 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 cur x21 x22 x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros MR FR. open_mrel MR. open_frm FR. hideD.
  unfold alloc_ceiling, sp_window_lo, stack_max_size in LOC. unfold TOPc in TOP.
  stepA. (* [comment removed for export] *)
  do 13 stepA. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  unfold LOWc in LOW.
  release_frame LOW SK (q + -2176).
  release_frame MID SK (q + -104).
  release_frame TOP SK q.
  apply evtA_done. unfold pcm_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. exact SK.
Qed.

(* [comment removed for export] *)
Lemma fmt_read : forall m1 t x a, MREL m1 -> nth_error (fmt ++ [0]) t = Some x -> a = wa (A + Z.of_nat t) ->
  ov_read_bytes bsegs m1 a 1 = Some [Z_to_bv 8 x].
Proof.
  intros m1 t x a MR E ->. pose proof (fmt_at m1 MR) as B.
  pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite length_app, zb_length in BB. cbn [length] in BB.
  assert (t < length fmt + 1)%nat. { pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)) as X. rewrite length_app in X. cbn in X. lia. }
  eapply (u8ro_read bsegs m1 A _ (Z.of_nat t)); [exact B | | lia | reflexivity].
  rewrite Nat2Z.id. replace (zb fmt ++ [Z_to_bv 8 0]) with (zb (fmt ++ [0])) by (unfold zb; rewrite map_app; reflexivity).
  unfold zb. rewrite nth_error_map, E. reflexivity.
Qed.

Lemma fmtz_nth : forall t, (t <= length fmt)%nat -> exists x, nth_error (fmt ++ [0]) t = Some x /\ 0 <= x < 256 /\ (x = 0 <-> t = length fmt).
Proof.
  intros t Ht. pose proof fmt_chars as FC. destruct (Nat.eq_dec t (length fmt)) as [->|NE].
  - exists 0. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. cbn. split; [reflexivity|]. split; [lia|]. tauto.
  - destruct (nth_error fmt t) as [x|] eqn:E.
    + exists x. rewrite nth_error_app1 by lia. split; [exact E|].
      rewrite Forall_nth in FC. pose proof (FC t 0 ltac:(lia)) as X. erewrite nth_error_nth in X by exact E.
      split; [lia|]. split; [lia| intros; lia].
    + apply nth_error_None in E. lia.
Qed.

(* [comment removed for export] *)
Lemma pcm_skip : forall k (i j : nat) (Q : machine_state -> Prop) m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x28 x29 x30 x31,
  (j - i)%nat = k -> (i <= j <= length fmt)%nat -> MREL m1 ->
  (forall t x, (i <= t < j)%nat -> nth_error (fmt ++ [0]) t = Some x -> x <> 0 /\ x <> 37) ->
  (forall x, nth_error (fmt ++ [0]) j = Some x -> x = 0 \/ x = 37) ->
  (nth_error (fmt ++ [0]) j = Some 37 ->
   evtA bsegs P Q (AT 0x459e4 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 37) x11 x12 x13 x14 x15 x16 x17 (A + Z.of_nat j) x21 x22 x23 x28 x29 x30 x31)) ->
  (j = length fmt ->
   evtA bsegs P Q (AT 0x45a74 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 0) x11 x12 x13 x14 x15 x16 x17 (A + Z.of_nat j) x21 x22 x23 x28 x29 x30 x31)) ->
  evtA bsegs P Q (AT 0x459cc m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (A + Z.of_nat i) x21 x22 x23 x28 x29 x30 x31).
Proof.
  induction k as [|k IH]; intros until x31; intros Hk Hij MR INNER ATJ K37 K0; prep.
  - assert (i = j) by lia. subst i.
    destruct (fmtz_nth j ltac:(lia)) as (x & E & R & X0).
    pose proof (fmt_read m1 j x (Z_to_bv 64 (A + Z.of_nat j)) MR E ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 x) by lia.
    destruct (ATJ x E) as [-> | ->].
    + zstepA. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
      zstepA. if_true. apply K0. apply X0. reflexivity.
    + zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
      apply K37. exact E.
  - assert (i < j)%nat by lia.
    destruct (fmtz_nth i ltac:(lia)) as (x & E & R & X0).
    destruct (INNER i x ltac:(lia) E) as [N0 N37].
    pose proof (fmt_read m1 i x (Z_to_bv 64 (A + Z.of_nat i)) MR E ltac:(unfold wa; f_equal; lia)) as RD.
    zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 x) by lia.
    zstepA. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
    zstepA. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    zstepA. zstepA. stepA. (* [comment removed for export] *)
    replace (A + Z.of_nat i + 1) with (A + Z.of_nat (S i)) by lia.
    eapply (IH (S i) j); [lia | lia | exact MR | | exact ATJ | exact K37 | exact K0].
    intros t y Ht Ey. apply (INNER t y); [lia | exact Ey].
Qed.

(* [comment removed for export] *)
Lemma pcm_head : forall (Q : machine_state -> Prop) m1 jmid j0 e1 cx dj x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 cur x21 x22 x23 x28 x29 x30 x31,
  MREL m1 -> FRM m1 jmid [CB 8 j0; C8 e1; C8 cx; CB 40 dj] ->
  (forall m2 x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31', MREL m2 ->
     FRM m2 jmid (LOWc j0 e1 cx (Z_to_bv 64 0) (Z_to_bv 64 M1) (Z_to_bv 64 0) (Z_to_bv 64 0)
                          (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3)) ->
     evtA bsegs P Q (AT 0x459cc m2 x1' x5' x6' x7' x9 x10' x11' x12' x13' x14' x15' x16' x17' cur x21 x22 x23 x28' x29' x30' x31')) ->
  evtA bsegs P Q (AT 0x459a0 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 cur x21 x22 x23 x28 x29 x30 x31).
Proof.
  intros until x31. intros MR FR K. open_mrel MR. open_frm FR. prep. unfold TOPc in TOP.
  do 5 stepA. (* [comment removed for export] *)
  zstepA. zstepA. stepA. stepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    apply (proj1 (rw_cells_app bsegs mx (q + -2240) [CB 8 j0; C8 e1; C8 cx] [_; _; _; _; _])) in LOW;
    destruct LOW as [LOW3 DIR]; cbn [cells_size csize Nat.add] in DIR;
    apply (rw_cells_merge bsegs mx _ [] [C8 (Z_to_bv 64 PAT); C8 (Z_to_bv 64 PAT); C8 (Z_to_bv 64 PAT); C8 (Z_to_bv 64 PAT); C8 (Z_to_bv 64 PAT)] []) in DIR;
    cbn [app cells_size csize Nat.add] in DIR
  end.
  replace (q + -2240 + Z.of_nat 24) with (q + -2216) in DIR by lia.
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_cut; [ eapply (@internal_memset_spec P) with (m := mx) (D := q + -2216) (n := 40) (v := 0);
      [ lia | lia | lia | reflexivity | lia | intros; apply PSTK; lia | lia | assumption | exact DIR ]
    | clear DIR; post_call bsegs mx; ret_pc_lit ] end.
  (* [comment removed for export] *)
  lazymatch goal with DIR : rw_cells bsegs ?mx (q + -2216) [CB _ _] |- _ =>
    assert (DIR' : rw_cells bsegs mx (q + -2216)
              [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
               C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)])
      by (destruct DIR as [[_ B] W]; split; [split; [cbn; repeat split; reflexivity | exact B] | exact W]);
    clear DIR;
    lazymatch goal with LOW3 : rw_cells bsegs mx (q + -2240) _ |- _ =>
      replace (q + -2216) with (q + -2240 + Z.of_nat (cells_size [CB 8 j0; C8 e1; C8 cx])) in DIR' by (cbn; lia);
      pose proof (proj2 (rw_cells_app bsegs mx (q + -2240) [CB 8 j0; C8 e1; C8 cx] _) (conj LOW3 DIR')) as LOW;
      cbn [app] in LOW; clear LOW3 DIR' end end.
  stepA. (* [comment removed for export] *)
  eapply K.
  - split; [assumption|]. split; assumption.
  - split; [assumption|]. split; [assumption|]. split; [assumption|]. unfold LOWc. assumption.
Qed.

(* [comment removed for export] *)
Definition S_flags : list Z := [39; 45; 43; 32; 35; 48].        (* [comment removed for export] *)
Definition T_jztLq : Z := 0x1b43c.  Definition S_jztLq : list Z := [106; 122; 116; 76; 113].
Definition T_cCsS : Z := 0x14179.   Definition S_cCsS : list Z := [99; 67; 115; 83].
Definition T_CS : Z := 0x19b6d.     Definition S_CS : list Z := [67; 83].
Definition T_csb : Z := 0x107f6.    Definition S_csb : list Z := [99; 115; 91].
Definition T_sS : Z := 0x13ab1.     Definition S_sS : list Z := [115; 83].
Definition T_aA : Z := 0x1640a.     Definition S_aA : list Z := [97; 65; 101; 69; 102; 70; 103; 71].

Lemma tables_bytes : forall m1, mem_inv bsegs m1 ->
  bytes_at bsegs m1 T_flags (zb S_flags ++ [Z_to_bv 8 0]) /\ bytes_at bsegs m1 T_jztLq (zb S_jztLq ++ [Z_to_bv 8 0]) /\
  bytes_at bsegs m1 T_cCsS (zb S_cCsS ++ [Z_to_bv 8 0]) /\ bytes_at bsegs m1 T_CS (zb S_CS ++ [Z_to_bv 8 0]) /\
  bytes_at bsegs m1 T_csb (zb S_csb ++ [Z_to_bv 8 0]) /\ bytes_at bsegs m1 T_sS (zb S_sS ++ [Z_to_bv 8 0]) /\
  bytes_at bsegs m1 T_aA (zb S_aA ++ [Z_to_bv 8 0]).
Proof.
  intros m1 MI1. unfold T_flags, T_jztLq, T_cCsS, T_CS, T_csb, T_sS, T_aA.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); (apply rodata_cstr; [exact MI1 | vm_compute; reflexivity | lia | unfold zlength; cbn; lia]).
Qed.

(* [comment removed for export] *)
Ltac call_strchr TT tbb cc :=
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_cut; [ eapply (@internal_strchr_spec P) with (m := mx) (T := TT) (tb := tbb) (c := cc);
      [ pose proof (tables_bytes mx ltac:(assumption)) as TBX; unfold T_flags, T_jztLq, T_cCsS, T_CS, T_csb, T_sS, T_aA in TBX |- *; tauto
      | repeat (constructor; [lia|]); apply Forall_nil
      | lia
      | let a' := fresh "a'" in let k' := fresh "k'" in let Ha' := fresh "Ha'" in let Hk' := fresh "Hk'" in
        intros a' k' Ha' Hk'; cbn in Ha', Hk'; unfold T_flags, T_jztLq, T_cCsS, T_CS, T_csb, T_sS, T_aA in Ha', Hk'; apply PIMG; lia ]
    | intros ms' (?x11 & ?x12 & ?x13 & ->); ret_pc_lit ] end.

Lemma rw_cells_bytes_at' : forall segs mq Aq cs, rw_cells segs mq Aq cs -> bytes_at segs mq Aq (cells_bytes cs).
Proof. intros segs mq Aq cs [[_ B] _]. exact B. Qed.
(* [comment removed for export] *)
Lemma c8_lw_lo : forall m1 A0 pre' (v : word) post' a,
  rw_cells bsegs m1 A0 (pre' ++ C8 v :: post') -> a = wa (A0 + Z.of_nat (cells_size pre')) ->
  ov_read_bytes bsegs m1 a 4 = Some (le4 v).
Proof.
  intros m1 A0 pre' v post' a H ->.
  apply (proj1 (rw_cells_app bsegs m1 A0 pre' (C8 v :: post'))) in H. destruct H as [_ H].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read bsegs m1 _ _ 0 4 Hb) as R. rewrite Z.add_0_r in R.
  rewrite R. 2:{ cbn [skipn]. rewrite length_app, length_le8. lia. }
  change (skipn 0 (le8 v ++ cells_bytes post')) with (le8 v ++ cells_bytes post').
  rewrite firstn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite firstn_O, app_nil_r. reflexivity.
Qed.
Lemma c8_lw_hi : forall m1 A0 pre' (v : word) post' a,
  rw_cells bsegs m1 A0 (pre' ++ C8 v :: post') -> a = wa (A0 + Z.of_nat (cells_size pre') + 4) ->
  ov_read_bytes bsegs m1 a 4 = Some (skipn 4 (le8 v)).
Proof.
  intros m1 A0 pre' v post' a H ->.
  apply (proj1 (rw_cells_app bsegs m1 A0 pre' (C8 v :: post'))) in H. destruct H as [_ H].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as Hb. cbn [cells_bytes cbytes] in Hb.
  pose proof (bytes_at_ov_read bsegs m1 _ _ 4 4 Hb) as R. replace (Z.of_nat 4) with 4 in R by reflexivity.
  rewrite R. 2:{ rewrite length_app, length_le8. lia. }
  rewrite skipn_app, length_le8. change (4 - 8)%nat with 0%nat. rewrite skipn_O, firstn_app, length_skipn, length_le8.
  change (4 - (8 - 4))%nat with 0%nat. rewrite firstn_O, app_nil_r. rewrite firstn_all2 by (rewrite length_skipn, length_le8; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pcm_dir_s : forall (Q : machine_state -> Prop) m1 jmid j0 e1 cx x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
  c = 115 -> MREL m1 ->
  FRM m1 jmid (LOWc j0 e1 cx (Z_to_bv 64 0) (Z_to_bv 64 M1) (Z_to_bv 64 0) (Z_to_bv 64 0)
                   (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3)) ->
  (forall m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31', MREL m2 ->
     FRM m2 jmid (LOWc j0 e1 cx (Z_to_bv 64 0) (Z_to_bv 64 M1) (Z_to_bv 64 (A + zlength pre)) (Z_to_bv 64 (A + zlength pre + 2))
                      (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 115) (repeat (Z_to_bv 8 0) 3)) ->
     evtA bsegs P Q (AT 0x45998 m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' (A + zlength pre + 2) (Z_to_bv 64 (AQ + 8)) x22' (Z_to_bv 64 9) x28' x29' x30' x31')) ->
  evtA bsegs P Q (AT 0x459e4 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 37) x11 x12 x13 x14 x15 x16 x17 (A + zlength pre) (Z_to_bv 64 AQ) x22 (Z_to_bv 64 9) x28 x29 x30 x31).
Proof.
  intros until x31. intros Hc' MR FR K. pose proof MR as MR0. open_mrel MR. open_frm FR. prep. unfold TOPc in TOP. unfold LOWc in LOW.
  pose proof fmt_len as FL. unfold zlength in FL |- *. set (np := length pre) in *.
  assert (E1 : nth_error (fmt ++ [0]) (S np) = Some c).
  { rewrite nth_error_app1 by (rewrite length_app; cbn; lia). rewrite nth_error_app2 by lia. subst np. rewrite Nat.sub_succ_l, Nat.sub_diag by lia. reflexivity. }
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c), Hc' by lia. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  zstepA. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c), Hc' by lia. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. call_strchr T_flags S_flags 115.
  change (strchr_res T_flags S_flags 115) with 0.
  zstepA. zstepA. zstepA. (* [comment removed for export] *) if_false.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1 + 1 + -1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c), Hc' by lia. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *) if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
  zstepA. (* [comment removed for export] *) replace (A + Z.of_nat np + 1 + 1 + -1) with (A + Z.of_nat np + 1) by lia.
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c), Hc' by lia. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *) if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?unsigned_lit in K5 by lia. lia. }
  zstepA. zstepA. (* [comment removed for export] *) if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?unsigned_lit in K6 by lia. lia. }
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. (* [comment removed for export] *) cbv beta. rewrite (unsigned_lit8 c), Hc' by lia.
  stepA. stepA. (* [comment removed for export] *) change (Z_to_bv 64 111676) with (Z_to_bv 64 T_jztLq).
  stepA. call_strchr T_jztLq S_jztLq 115. change (strchr_res T_jztLq S_jztLq 115) with 0.
  zstepA. (* [comment removed for export] *) cbv beta. rewrite (unsigned_lit8 c), Hc' by lia. clear RD.
  zstepA. if_true. (* [comment removed for export] *)
  zstepA. zstepA. if_cases K7; zify_cond K7. { exfalso. rewrite ?unsigned_lit in K7 by lia. lia. }
  zstepA. zstepA. if_cases K8; zify_cond K8. 2:{ exfalso. rewrite ?unsigned_lit in K8 by lia. lia. }
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c), Hc' by lia. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. if_cases K9; zify_cond K9. { exfalso. rewrite ?unsigned_lit, ?unsigned_lit8 in K9 by lia. lia. }
  (* [comment removed for export] *)
  lazymatch goal with LOWx : rw_cells bsegs ?mx (q + -2240) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (c8_lw_lo mx (q + -2240) [CB 8 j0; C8 e1; C8 cx; C8 (Z_to_bv 64 0)] (Z_to_bv 64 M1) _ (Z_to_bv 64 (q + -2184 + -24)) LOWx
                  ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD end.
  stepA. clear RD. (* [comment removed for export] *)
  zstepA. if_cases K10; zify_cond K10. { exfalso. revert K10. rewrite ?unsigned_lit_wrap. clear. intros K10. apply K10. reflexivity. }
  lazymatch goal with LOWx : rw_cells bsegs ?mx (q + -2240) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (c8_lw_hi mx (q + -2240) [CB 8 j0; C8 e1; C8 cx; C8 (Z_to_bv 64 0)] (Z_to_bv 64 M1) _ (Z_to_bv 64 (q + -2184 + -20)) LOWx
                  ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD end.
  stepA. clear RD. (* [comment removed for export] *)
  zstepA. if_cases K11; zify_cond K11. { exfalso. revert K11. rewrite ?unsigned_lit_wrap. clear. intros K11. apply K11. reflexivity. }
  zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. zstepA. if_true. (* [comment removed for export] *)
  zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. zstepA. if_true. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstepA. cbv beta. rewrite ?(unsigned_lit8 115) by lia. (* [comment removed for export] *)
  zstepA. zstepA. if_cases K12; zify_cond K12. { exfalso. rewrite ?unsigned_lit in K12 by lia. lia. }
  stepA. stepA. change (Z_to_bv 64 86118) with (Z_to_bv 64 T_cCsS).
  stepA. call_strchr T_cCsS S_cCsS 115. change (strchr_res T_cCsS S_cCsS 115) with (T_cCsS + 2).
  zstepA. cbv beta. rewrite ?(unsigned_lit8 115) by lia. (* [comment removed for export] *)
  zstepA. if_cases K13; zify_cond K13. { exfalso. revert K13. unfold T_cCsS. rewrite ?landM1, ?unsigned_lit by lia. lia. }
  stepA. stepA. change (Z_to_bv 64 105325) with (Z_to_bv 64 T_CS). zstepA. (* [comment removed for export] *)
  stepA. call_strchr T_CS S_CS 115. change (strchr_res T_CS S_CS 115) with 0.
  stepA. stepA. (* [comment removed for export] *)
  zstepA. if_true. (* [comment removed for export] *)
  stepA. stepA. change (Z_to_bv 64 68982) with (Z_to_bv 64 T_csb). zstepA. (* [comment removed for export] *)
  stepA. call_strchr T_csb S_csb 115. change (strchr_res T_csb S_csb 115) with (T_csb + 1).
  stepA. (* [comment removed for export] *)
  zstepA. if_cases K14; zify_cond K14. { exfalso. revert K14. unfold T_csb. rewrite ?landM1, ?unsigned_lit by lia. lia. }
  zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. zstepA. if_true. (* [comment removed for export] *)
  stepA. stepA. (* [comment removed for export] *)
  zstepA. cbv beta. rewrite ?(unsigned_lit8 115) by lia. (* [comment removed for export] *)
  stepA. stepA. change (Z_to_bv 64 83968) with (Z_to_bv 64 T_sS).
  stepA. call_strchr T_sS S_sS 115. change (strchr_res T_sS S_sS 115) with T_sS.
  zstepA. if_cases K15; zify_cond K15. { exfalso. revert K15. unfold T_sS. rewrite ?landM1, ?unsigned_lit by lia. lia. }
  zstepA. (* [comment removed for export] *)
  zstepA. cbv beta. rewrite ?(unsigned_lit8 115) by lia. (* [comment removed for export] *)
  zstepA. zstepA. if_cases K16; zify_cond K16. 2:{ exfalso. rewrite ?unsigned_lit in K16 by lia. lia. }
  (* [comment removed for export] *)
  zstepA. zstepA. if_cases K17; zify_cond K17. { exfalso. revert K17. rewrite ?unsigned_lit_wrap. clear. cbn. lia. }
  zstepA. if_cases K18; zify_cond K18. { exfalso. revert K18. rewrite ?unsigned_lit_wrap. clear. intros K18. apply K18. reflexivity. }
  (* [comment removed for export] *)
  pose proof (PAQ Hc') as PAQ'.
  lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (aqv_at mx Hc' (conj MIx (conj MUx WMx))) as AQVx end.
  stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  pose proof HS as HS'. unhideH HS'. pose proof SBR as SBR'.
  zstepA. if_cases K19; zify_cond K19. { exfalso. unfold zlength in HS'. rewrite ?landM1, ?unsigned_lit in K19 by lia. lia. }
  zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. zstepA. if_false. (* [comment removed for export] *)
  lazymatch goal with LOWx : rw_cells bsegs ?mx (q + -2240) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (c8_lw_hi mx (q + -2240) [CB 8 j0; C8 e1; C8 cx] (Z_to_bv 64 0) _ (Z_to_bv 64 (q + -2184 + -28)) LOWx
                  ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD end.
  stepA. clear RD. (* [comment removed for export] *)
  zstepA. if_cases K20; zify_cond K20.
  2:{ exfalso. revert K20. clear. intros K20. apply K20. vm_compute. reflexivity. }
  (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_cut; [ eapply (@internal_strlen_spec P) with (m := mx) (S := SA) (s := zs);
      [ exact (str_at mx Hc' (conj MIx (conj MUx WMx))) | exact HZS | exact (PSTR Hc') ]
    | intros ms' (x11' & x12' & ->); ret_pc_lit ] end.
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  if_cases K21; zify_cond K21. { exfalso. revert K21. unfold zlength in *. rewrite ?landM1, ?zb_lxor_ones by lia. rewrite ?landM1 by lia. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  pose proof GEO_A as GA. cbv zeta in GA. unfold zlength in HS', GA.
  (* [comment removed for export] *)
  assert (JOIN : forall m3 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31',
    mem_inv bsegs m3 -> munch [(lo, q)] m m3 -> wmono bsegs m m3 -> stk bsegs m3 lo (q - 2240) ->
    rw_cells bsegs m3 (q + -104) TOPc -> rw_cells bsegs m3 (q + -2176) [CB 2072 jmid] ->
    rw_cells bsegs m3 (q + -2240) (LOWc j0 e1 cx (Z_to_bv 64 0) (Z_to_bv 64 M1) (Z_to_bv 64 (A + Z.of_nat np)) (Z_to_bv 64 (A + Z.of_nat np + 2))
                      (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 115) (repeat (Z_to_bv 8 0) 3)) ->
    evtA bsegs P Q (AT 0x45d18 m3 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' (A + Z.of_nat np + 2) (Z_to_bv 64 (AQ + 8)) x22' (Z_to_bv 64 (LA + 1)) x28' x29' x30' x31')).
  { intros until x31'. intros MI3 MU3 WM3 SK3 TOP3 MID3 LOW3.
    stepA. stepA. (* [comment removed for export] *)
    eapply K. { split; [exact MI3| split; [exact MU3| exact WM3]]. } split; [exact SK3|]. split; [exact TOP3|]. split; [exact MID3| exact LOW3]. }
  unfold zlength in *.
  if_cases K22; [apply h3_negb_ltu in K22| apply h3_negb_ltu_f in K22]; change (Z.land (-65) 18446744073709551615) with 18446744073709551551 in K22.
  - (* [comment removed for export] *)
    assert (65 <= Z.of_nat (length zs) + 1). { revert K22. rewrite ?landM1_mod. clear -HS'. intros K22. unfold zlength in *. Z.div_mod_to_equations. lia. }
    zstepA. if_cases K23; zify_cond K23. 2:{ exfalso. revert K23. unfold zlength in *. rewrite ?landM1, ?unsigned_lit by lia. lia. }
    zstepA. zstepA. (* [comment removed for export] *)
    stepA. (* [comment removed for export] *)
    assert (USP : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
    lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx, SKx : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (g_at mx (conj MIx (conj MUx WMx))) as Gx; pose proof (ash_at mx Hc' (conj MIx (conj MUx WMx))) as SHx;
      callA (region_is_poisoned_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx SA (Z.of_nat (length zs) + 1) SB (repeat (Z_to_bv 8 0) NA) lo P);
      [ rewrite USP; replace (q + -2240) with (q - 2240) by lia; exact SKx | exact LOC | rewrite USP; lia | exact MIx | reflexivity | reflexivity | lia | lia
      | right; unfold A_HIGHEND_VAL; lia
      | exact Gx
      | split; [ exact SHx | rewrite repeat_length; exact HNA ]
      | apply (range_clean_zero SB SA (Z.of_nat (length zs) + 1) NA HNA); lia
      | intros; apply PSTK; rewrite ?USP in * by lia; lia
      | exact PIMG
      | exact (PASH Hc')
      | ] end.
    rewrite ?unsigned_lit in * by lia.
    zstepA. if_true. (* [comment removed for export] *)
    eapply JOIN; try eassumption;
      try (match goal with SKx : stk bsegs _ lo _ |- _ => first [exact SKx | replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx | rewrite unsigned_lit in SKx by lia; replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx] end).
  - (* [comment removed for export] *)
    assert (Z.of_nat (length zs) + 1 <= 64). { revert K22. rewrite ?landM1_mod. clear -HS'. intros K22. unfold zlength in *. Z.div_mod_to_equations. lia. }
    lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (g_at mx (conj MIx (conj MUx WMx))) as Gx; pose proof (ash_at mx Hc' (conj MIx (conj MUx WMx))) as SHx end.
    icp_globals_open Gx.
    stepA. stepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    stepA. (* [comment removed for export] *)
    zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
    rewrite ?land_m8, ?land_m8' by lia.
    replace (SA + (Z.of_nat (length zs) + 1) + -1) with (SA + Z.of_nat (length zs)) in * by lia.
    change (al8 (SB + SA ≫ 3)) with (shw_lo SB SA).
    replace (al8 (SB + (SA + Z.of_nat (length zs)) ≫ 3)) with (shw_hi SB SA (Z.of_nat (length zs) + 1) - 8) by (unfold shw_hi; replace (SA + (Z.of_nat (length zs) + 1) + -1) with (SA + Z.of_nat (length zs)) by lia; lia).
    pose proof (zwin_read8 _ _ _ 0 (Z_to_bv 64 (shw_lo SB SA)) SHx ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    stepA. clear RD. rewrite load8_zero. (* [comment removed for export] *)
    pose proof (zwin_read8 _ _ _ (shw_hi SB SA (Z.of_nat (length zs) + 1) - 8 - shw_lo SB SA) (Z_to_bv 64 (shw_hi SB SA (Z.of_nat (length zs) + 1) - 8)) SHx ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    stepA. clear RD. rewrite load8_zero. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_true. (* [comment removed for export] *)
    clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI.
    eapply JOIN; try eassumption;
      try (match goal with SKx : stk bsegs _ lo _ |- _ => first [exact SKx | replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx | rewrite unsigned_lit in SKx by lia; replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx] end).
Qed.

Lemma du_tables : c = 100 \/ c = 117 ->
  strchr_res T_flags S_flags c = 0 /\ strchr_res T_jztLq S_jztLq c = 0 /\ strchr_res T_cCsS S_cCsS c = 0 /\ strchr_res T_aA S_aA c = 0 /\ In c S_dioux.
Proof. intros [E|E]; rewrite E; (repeat split; try (vm_compute; reflexivity)); cbn; repeat (first [left; reflexivity | right]). Qed.

Lemma low_lm0 : forall m1 j0 e1 cx fw idx be en sw sp lm0 lm1 cv j3,
  rw_cells bsegs m1 (q + -2240) (LOWc j0 e1 cx fw idx be en sw sp lm0 lm1 cv j3) -> bytes_at bsegs m1 (q + -2182) [lm0].
Proof.
  intros until j3. intros H. unfold LOWc in H.
  apply (proj1 (rw_cells_app bsegs m1 _ [CB 8 j0; C8 e1; C8 cx; C8 fw; C8 idx; C8 be; C8 en; C1 sw; C1 sp] _)) in H. destruct H as [_ H].
  apply (proj1 (rw_cells_app bsegs m1 _ [C1 lm0] _)) in H. destruct H as [H _].
  pose proof (rw_cells_bytes_at' _ _ _ _ H) as B. cbn [cells_size csize Nat.add cells_bytes cbytes app] in B.
  match type of B with bytes_at _ _ ?a _ => replace a with (q + -2182) in B by (cbn; lia) end. exact B.
Qed.

(* [comment removed for export] *)
Lemma pcm_dir_du : forall (Q : machine_state -> Prop) m1 jmid j0 e1 cx x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31,
  c = 100 \/ c = 117 -> MREL m1 ->
  FRM m1 jmid (LOWc j0 e1 cx (Z_to_bv 64 0) (Z_to_bv 64 M1) (Z_to_bv 64 0) (Z_to_bv 64 0)
                   (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (repeat (Z_to_bv 8 0) 3)) ->
  (forall m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' x22' x28' x29' x30' x31', MREL m2 ->
     FRM m2 jmid (LOWc j0 e1 cx (Z_to_bv 64 0) (Z_to_bv 64 M1) (Z_to_bv 64 (A + zlength pre)) (Z_to_bv 64 (A + zlength pre + 2))
                      (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 0) (Z_to_bv 8 c) (repeat (Z_to_bv 8 0) 3)) ->
     evtA bsegs P Q (AT 0x45998 m2 x1' x5' x6' x7' x9' x10' x11' x12' x13' x14' x15' x16' x17' (A + zlength pre + 2) (Z_to_bv 64 (AQ + 8)) x22' (Z_to_bv 64 9) x28' x29' x30' x31')) ->
  evtA bsegs P Q (AT 0x459e4 m1 x1 x5 x6 x7 x9 (Z_to_bv 64 37) x11 x12 x13 x14 x15 x16 x17 (A + zlength pre) (Z_to_bv 64 AQ) x22 (Z_to_bv 64 9) x28 x29 x30 x31).
Proof.
  intros until x31. intros Hdu MR FR K. assert (Hcr : 0 < c < 256 /\ c <> 37 /\ c <> 42 /\ c <> 46 /\ c <> 108 /\ c <> 104 /\ c <> 109 /\ c <> 110 /\ 9 < c - 48) by lia.
  destruct (du_tables Hdu) as (RF0 & RJ0 & RC0 & RA0 & HIN). pose proof MR as MR0. open_mrel MR. open_frm FR. prep. unfold TOPc in TOP. unfold LOWc in LOW.
  pose proof fmt_len as FL. unfold zlength in FL |- *. set (np := length pre) in *.
  assert (E1 : nth_error (fmt ++ [0]) (S np) = Some c).
  { rewrite nth_error_app1 by (rewrite length_app; cbn; lia). rewrite nth_error_app2 by lia. subst np. rewrite Nat.sub_succ_l, Nat.sub_diag by lia. reflexivity. }
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. kz K1. lia. }
  zstepA. if_cases K2; zify_cond K2. { exfalso. kz K2. lia. }
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K3; zify_cond K3. 2:{ exfalso. kz K3. lia. }
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  stepA. call_strchr T_flags S_flags c.
  rewrite RF0.
  zstepA. zstepA. zstepA. (* [comment removed for export] *) if_false.
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1 + 1 + -1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *) if_cases K4; zify_cond K4. 2:{ exfalso. kz K4. lia. }
  zstepA. (* [comment removed for export] *) replace (A + Z.of_nat np + 1 + 1 + -1) with (A + Z.of_nat np + 1) by lia.
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *) if_cases K5; zify_cond K5. 2:{ exfalso. kz K5. lia. }
  zstepA. zstepA. (* [comment removed for export] *) if_cases K6; zify_cond K6. 2:{ exfalso. kz K6. lia. }
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. (* [comment removed for export] *) cbv beta. rewrite (unsigned_lit8 c) by lia.
  stepA. stepA. (* [comment removed for export] *) change (Z_to_bv 64 111676) with (Z_to_bv 64 T_jztLq).
  stepA. call_strchr T_jztLq S_jztLq c. rewrite RJ0.
  zstepA. (* [comment removed for export] *) cbv beta. rewrite (unsigned_lit8 c) by lia. clear RD.
  zstepA. if_true. (* [comment removed for export] *)
  zstepA. zstepA. if_cases K7; zify_cond K7. { exfalso. kz K7. lia. }
  zstepA. zstepA. if_cases K8; zify_cond K8. 2:{ exfalso. kz K8. lia. }
  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx (S np) c (Z_to_bv 64 (A + Z.of_nat np + 1)) ltac:(split; [assumption| split; assumption]) E1 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  rewrite ?(Z.mod_small c 256) in * by lia.
  zstepA. if_cases K9; zify_cond K9. { exfalso. kz K9. lia. }
  (* [comment removed for export] *)
  lazymatch goal with LOWx : rw_cells bsegs ?mx (q + -2240) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (c8_lw_lo mx (q + -2240) [CB 8 j0; C8 e1; C8 cx; C8 (Z_to_bv 64 0)] (Z_to_bv 64 M1) _ (Z_to_bv 64 (q + -2184 + -24)) LOWx
                  ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD end.
  stepA. clear RD. (* [comment removed for export] *)
  zstepA. if_cases K10; zify_cond K10. { exfalso. revert K10. rewrite ?unsigned_lit_wrap. clear. intros K10. apply K10. reflexivity. }
  lazymatch goal with LOWx : rw_cells bsegs ?mx (q + -2240) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (c8_lw_hi mx (q + -2240) [CB 8 j0; C8 e1; C8 cx; C8 (Z_to_bv 64 0)] (Z_to_bv 64 M1) _ (Z_to_bv 64 (q + -2184 + -20)) LOWx
                  ltac:(cbn [cells_size csize Nat.add]; unfold wa; f_equal; lia)) as RD end.
  stepA. clear RD. (* [comment removed for export] *)
  zstepA. if_cases K11; zify_cond K11. { exfalso. revert K11. rewrite ?unsigned_lit_wrap. clear. intros K11. apply K11. reflexivity. }
  zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. zstepA. if_true. (* [comment removed for export] *)
  zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. zstepA. if_true. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstepA. cbv beta. rewrite ?(unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. zstepA. if_cases K12; zify_cond K12. { exfalso. kz K12. lia. }
  stepA. stepA. change (Z_to_bv 64 86118) with (Z_to_bv 64 T_cCsS).
  stepA. call_strchr T_cCsS S_cCsS c. rewrite RC0.
  zstepA. cbv beta. rewrite ?(unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. if_true. (* [comment removed for export] *)
  stepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  assert (USP : bv_unsigned (Z_to_bv 64 (q + -2240)) = q + -2240) by (apply unsigned_lit; lia).
  lazymatch goal with LOWx : rw_cells bsegs ?mx (q + -2240) _, MIx : mem_inv bsegs ?mx, SKx : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (low_lm0 mx _ _ _ _ _ _ _ _ _ _ _ _ _ LOWx) as LMB;
    callA (fgvs_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mx c (q + -2182) lo P);
    [ rewrite USP; replace (q + -2240) with (q - 2240) by lia; exact SKx | exact LOC | rewrite USP; lia | exact MIx | reflexivity
    | reflexivity | exact HIN | exact LMB | rewrite USP; lia
    | intros; apply PSTK; rewrite ?USP in * by lia; lia | exact PIMG | apply PSTK; lia | ] end.
  zstepA. stepA. (* [comment removed for export] *)
  zstepA. if_cases K30; zify_cond K30. 2:{ exfalso. revert K30. rewrite ?unsigned_lit by lia. lia. }
  zstepA. cbv beta. rewrite ?(unsigned_lit8 c) by lia. (* [comment removed for export] *)
  zstepA. zstepA. if_cases K31; zify_cond K31. 2:{ exfalso. kz K31. lia. }
  zstepA. zstepA. if_cases K32; zify_cond K32. { exfalso. revert K32. rewrite ?unsigned_lit_wrap, ?unsigned_lit by lia. clear. cbn. lia. }
  zstepA. if_cases K33; zify_cond K33. 2:{ exfalso. revert K33. rewrite ?unsigned_lit_wrap, ?unsigned_lit, ?landM1 by lia. clear. cbn. lia. }
  stepA. stepA. change (Z_to_bv 64 96337) with (Z_to_bv 64 T_aA).
  stepA. call_strchr T_aA S_aA c. rewrite RA0.
  zstepA. if_true. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. if_cases K34; zify_cond K34. { exfalso. revert K34. rewrite ?unsigned_lit by lia. lia. }
  zstepA. zstepA. if_cases K35; zify_cond K35. { exfalso. revert K35. rewrite ?unsigned_lit by lia. lia. }
  zstepA. zstepA. if_cases K36; zify_cond K36. 2:{ exfalso. revert K36. rewrite ?unsigned_lit by lia. lia. }
  zstepA. (* [comment removed for export] *)
  eapply K. { split; [assumption| split; assumption]. }
  split; [| split; [assumption| split; assumption]].
  match goal with SKx : stk bsegs _ lo _ |- _ => first [exact SKx | replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx | rewrite unsigned_lit in SKx by lia; replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx] end.
Qed.

(* [comment removed for export] *)
Lemma pcm_pass2 : forall m1 jmid j0 e1 cx fw idx be en sw sp lm0 lm1 cv j3 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31,
  MREL m1 -> FRM m1 jmid (LOWc j0 e1 cx fw idx be en sw sp lm0 lm1 cv j3) ->
  evtA bsegs P POST (AT 0x45998 m1 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 (A + zlength pre + 2) x21 x22 (Z_to_bv 64 9) x28 x29 x30 x31).
Proof.
  intros until x31. intros MR FR. pose proof MR as MR0. open_mrel MR. open_frm FR. prep.
  pose proof fmt_len as FL. unfold zlength in FL |- *. set (np := length pre) in *.
  destruct (fmtz_nth (np + 2) ltac:(lia)) as (x & E & R & X0).
  pose proof (fmt_read m1 (np + 2) x (Z_to_bv 64 (A + Z.of_nat np + 2)) MR0 E ltac:(unfold wa; f_equal; lia)) as RD.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 x) by lia.
  zstepA. if_cases K1; zify_cond K1.
  - (* [comment removed for export] *)
    eapply pcm_epi. { exact MR0. } split; [exact SK|]. split; [exact TOP|]. split; [exact MID| exact LOW].
  - rewrite ?unsigned_lit in K1 by lia. assert (np + 2 <> length fmt)%nat by (intros X; apply X0 in X; lia).
    (* [comment removed for export] *)
    unfold LOWc in LOW.
    apply (proj1 (rw_cells_app bsegs m1 (q + -2240) [CB 8 j0; C8 e1; C8 cx] _)) in LOW. destruct LOW as [LOW3 DIR].
    apply (rw_cells_merge bsegs m1 _ [] [C8 fw; C8 idx; C8 be; C8 en; C1 sw; C1 sp; C1 lm0; C1 lm1; C1 cv; CB 3 j3] []) in DIR.
    pose proof (proj2 (rw_cells_app bsegs m1 (q + -2240) [CB 8 j0; C8 e1; C8 cx] _) (conj LOW3 DIR)) as LOW. clear LOW3 DIR.
    cbn [app cells_size csize Nat.add] in LOW.
    replace (A + Z.of_nat np + 2) with (A + Z.of_nat (np + 2)) by lia.
    eapply pcm_head. { exact MR0. } { split; [exact SK|]. split; [exact TOP|]. split; [exact MID| exact LOW]. }
    intros m2 x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' MR2 FR2.
    eapply (pcm_skip (length fmt - (np + 2)) (np + 2) (length fmt)); [lia | lia | exact MR2 | | | |].
    + intros t y Ht Ey. rewrite nth_error_app1 in Ey by lia.
      assert (Ey' : nth_error post (t - (np + 2)) = Some y).
      { rewrite nth_error_app2 in Ey by lia.
        replace (t - length pre)%nat with (S (S (t - (np + 2))))%nat in Ey by lia. cbn [nth_error] in Ey. exact Ey. }
      rewrite Forall_nth in HPOST. pose proof (HPOST (t - (np + 2))%nat 0 ltac:(apply nth_error_Some; rewrite Ey'; discriminate)) as X.
      erewrite nth_error_nth in X by exact Ey'. cbn in X. lia.
    + intros y Ey. rewrite nth_error_app2, Nat.sub_diag in Ey by lia. cbn in Ey. left. congruence.
    + intros E37. exfalso. rewrite nth_error_app2, Nat.sub_diag in E37 by lia. cbn in E37. congruence.
    + intros _. pose proof MR2 as MR2'. open_mrel MR2'. destruct FR2 as (SK2 & TOP2 & MID2 & LOW2). unfold LOWc in LOW2.
      zstepA. cbv beta. rewrite (unsigned_lit8 0) by lia. (* [comment removed for export] *)
      zstepA. if_false. stepA. (* [comment removed for export] *)
      destruct (fmtz_nth (length fmt) ltac:(lia)) as (x0 & E0 & R0 & Z0). assert (x0 = 0) by (apply Z0; reflexivity). subst x0.
      pose proof (fmt_read m2 (length fmt) 0 (Z_to_bv 64 (A + Z.of_nat (length fmt))) MR2 E0 ltac:(unfold wa; f_equal; lia)) as RD.
      zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 0) by lia. (* [comment removed for export] *)
      zstepA. if_true.
      eapply pcm_epi. { exact MR2. } split; [exact SK2|]. split; [exact TOP2|]. split; [exact MID2| exact LOW2].
Qed.

(* [comment removed for export] *)
Lemma pcm_main : forall m1 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  MREL m1 -> stk bsegs m1 lo q ->
  evtA bsegs P POST
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 ctx (Z_to_bv 64 A) (Z_to_bv 64 AQ) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 printf_common_entry) fc None m1 (seg_rom bsegs)).
Proof.
  intros until t6. intros MR SK. open_mrel MR. unfold printf_common_entry. prep. pose proof HNF as HNF'. unfold zlength in HNF'.
  pose proof SBR as SBR'. pose proof fmt_len as FL. pose proof fmt_chars as FC. pose proof GEO_F as GE. unfold zlength in FL, GE |- *.
  carve_frame 104%nat SK.
  destruct (stk_split bsegs m1 lo (q + -2176) (q - 104) SK ltac:(lia)) as [SKlo SKmid]. clear SK.
  carve_frame 2072%nat SKmid.
  lazymatch goal with H : rw_cells bsegs m1 (q + -104 + -2072) _ |- _ => replace (q + -104 + -2072) with (q + -2176) in H by lia; rename H into MID end.
  carve_frame 64%nat SKlo.
  lazymatch goal with H : rw_cells bsegs m1 ?a [CB 64 _] |- _ => replace a with (q + -2240) in H by lia; rename H into LOW end.
  lazymatch type of SKlo with stk _ _ lo ?a => replace a with (q - 2240) in SKlo by lia end.
  do 15 stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    eapply evtA_cut; [ eapply (@internal_strlen_spec P) with (m := mx) (S := A) (s := fmt);
      [ exact (fmt_at mx (conj MIx (conj MUx WMx))) | exact FC | intros; apply PIMG; unfold zlength in *; lia ]
    | intros ms' (x11' & x12' & ->); ret_pc_lit ] end.
  unfold zlength.
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?landM1, ?zb_lxor_ones by lia. rewrite ?landM1 by lia. lia. }
  zstepA. zstepA. (* [comment removed for export] *)
  if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?landM1 by lia. lia. }
  (* [comment removed for export] *)
  lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (g_at mx (conj MIx (conj MUx WMx))) as Gx; pose proof (fsh_at mx (conj MIx (conj MUx WMx))) as SHx end.
  icp_globals_open Gx.
  stepA. stepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.of_nat (length fmt) + A) with (A + Z.of_nat (length fmt)) by lia.
  rewrite ?landM1 by lia. rewrite ?land_m8, ?land_m8' by lia.
  change (al8 (SB + A ≫ 3)) with (shw_lo SB A).
  assert (E8 : al8 (SB + Z.shiftr (A + Z.of_nat (length fmt)) 3) = shw_hi SB A (Z.of_nat (length fmt) + 1) - 8).
  { unfold shw_hi. replace (A + (Z.of_nat (length fmt) + 1) + -1) with (A + Z.of_nat (length fmt)) by lia. lia. }
  rewrite E8.
  pose proof (zwin_read8 _ _ _ 0 (Z_to_bv 64 (shw_lo SB A)) SHx ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  stepA. clear RD. rewrite load8_zero. (* [comment removed for export] *)
  pose proof (zwin_read8 _ _ _ (shw_hi SB A (Z.of_nat (length fmt) + 1) - 8 - shw_lo SB A) (Z_to_bv 64 (shw_hi SB A (Z.of_nat (length fmt) + 1) - 8)) SHx ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  stepA. clear RD. rewrite load8_zero. (* [comment removed for export] *)
  zstepA. zstepA. if_false. (* [comment removed for export] *)
  clear GSBP GSB GRICP GRIC GRCPY GRSET GMBP GMB GMEP GME GHEP GHE GINI SHx.
  (* [comment removed for export] *)
  zstepA. zstepA. replace (q - 4096) with (q + -4096) by lia. stepA. (* [comment removed for export] *)
  destruct (fmtz_nth 0 ltac:(lia)) as (x0 & E0 & R0 & X0). assert (x0 <> 0) by (intros X; apply X0 in X; lia).
  lazymatch goal with MUx : munch [(lo, q)] m ?mx, WMx : wmono bsegs m ?mx, MIx : mem_inv bsegs ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (fmt_read mx 0 x0 (Z_to_bv 64 A) (conj MIx (conj MUx WMx)) E0 ltac:(unfold wa; f_equal; lia)) as RD end.
  zstepA. clear RD. cbv beta. rewrite (unsigned_lit8 x0) by lia. (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3. { exfalso. kz K3. lia. }
  (* [comment removed for export] *)
  zstepA. zstepA. zstepA. stepA. stepA. stepA. stepA. stepA. stepA. zstepA. (* [comment removed for export] *)
  stepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. replace (q - 4096) with (q + -4096) by lia. stepA. stepA. (* [comment removed for export] *)
  change (Z_to_bv 64 12297829382473034410) with (Z_to_bv 64 PAT). change (Z_to_bv 64 91629) with (Z_to_bv 64 T_flags).
  rewrite zbv_m1.
  eapply pcm_head.
  { split; [assumption| split; assumption]. }
  { split; [| split; [eassumption| split; eassumption]].
    match goal with SKx : stk bsegs _ lo _ |- _ => first [exact SKx | replace (q + -2240) with (q - 2240) in SKx by lia; exact SKx] end. }
  clear x11' x12'. intros m2 x1' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' MR2 FR2.
  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A + Z.of_nat 0)) by (f_equal; lia).
  set (np := length pre) in *.
  assert (E37 : nth_error (fmt ++ [0]) np = Some 37).
  { rewrite nth_error_app1 by (rewrite length_app; cbn; lia). rewrite nth_error_app2 by lia. subst np. rewrite Nat.sub_diag. reflexivity. }
  eapply (pcm_skip np 0 np); [lia | lia | exact MR2 | | | |].
  - intros t y Ht Ey. rewrite nth_error_app1 in Ey by (rewrite length_app; cbn; lia). rewrite nth_error_app1 in Ey by lia.
    rewrite Forall_nth in HPRE. pose proof (HPRE t 0 ltac:(apply nth_error_Some; rewrite Ey; discriminate)) as X.
    erewrite nth_error_nth in X by exact Ey. cbn in X. lia.
  - intros y Ey. rewrite E37 in Ey. right. congruence.
  - intros _. replace (A + Z.of_nat np) with (A + zlength pre) by (subst np; unfold zlength; lia).
    destruct Hc as [Hs | Hdu].
    + eapply pcm_dir_s; [exact Hs | exact MR2 | exact FR2 |].
      intros. eapply pcm_pass2; eassumption.
    + eapply pcm_dir_du; [exact Hdu | exact MR2 | exact FR2 |].
      intros. eapply pcm_pass2; eassumption.
  - intros X. exfalso. subst np. rewrite length_app in X. cbn in X. lia.
Qed.

End Walk.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem printf_common_spec :
  forall (P : acc -> Prop) (ra gp tp t0 t1 t2 s0 s1 ctx a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo A AQ SB : Z) (pre post : list Z) (c : Z) (NF : nat) (SA : Z) (zs : list Z) (NA : nat),
  let fmt := pre ++ 37 :: c :: post in
  (* [comment removed for export] *)
  Forall (fun x => 0 < x < 256 /\ x <> 37) pre -> Forall (fun x => 0 < x < 256 /\ x <> 37) post ->
  (c = 115 \/ c = 100 \/ c = 117) -> zlength fmt <= 63 ->
  bytes_at bsegs m A (zb fmt ++ [Z_to_bv 8 0]) -> 0x10000 <= A /\ A + 64 <= 0x31000 ->
  bytes_at bsegs m (shw_lo SB A) (repeat (Z_to_bv 8 0) NF) -> Z.of_nat NF = shw_hi SB A (zlength fmt + 1) - shw_lo SB A ->
  (* [comment removed for export] *)
  icp_globals bsegs m SB -> stk bsegs m lo q -> alloc_ceiling <= lo -> lo <= q - 2320 -> q < 2^47 -> mem_inv bsegs m ->
  (* [comment removed for export] *)
  (AQ + 8 <= lo \/ q <= AQ) -> (0 < AQ /\ AQ + 8 < 2^47) ->
  (c = 115 -> rw_cells bsegs m AQ [C8 (Z_to_bv 64 SA)]) ->
  (c = 115 -> bytes_at bsegs m SA (zb zs ++ [Z_to_bv 8 0])) ->
  Forall (fun x => 0 < x < 256) zs ->
  (SB + 0x100000000000 <= SA /\ SA + zlength zs + 1 < 2^47 /\ zlength zs + 1 < 2^40) ->
  (SA + zlength zs + 1 <= lo \/ q <= SA) ->
  (c = 115 -> bytes_at bsegs m (shw_lo SB SA) (repeat (Z_to_bv 8 0) NA)) ->
  Z.of_nat NA = shw_hi SB SA (zlength zs + 1) - shw_lo SB SA ->
  (* [comment removed for export] *)
  (forall a k, lo <= a -> a + Z.of_nat k <= q -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, shw_lo SB A <= a -> a + Z.of_nat k <= shw_hi SB A (zlength fmt + 1) -> P (Z_to_bv 64 a, k)) ->
  (c = 115 -> P (Z_to_bv 64 AQ, 8%nat)) ->
  (c = 115 -> forall a k, SA <= a -> a + Z.of_nat k <= SA + zlength zs + 1 -> P (Z_to_bv 64 a, k)) ->
  (c = 115 -> forall a k, shw_lo SB SA <= a -> a + Z.of_nat k <= shw_hi SB SA (zlength zs + 1) -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (pcm_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 ctx (Z_to_bv 64 A) (Z_to_bv 64 AQ) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 printf_common_entry) fc None m (seg_rom bsegs)).
Proof.
  intros. eapply (@pcm_main P) with (pre := pre) (post := post) (zs := zs) (SA := SA) (NA := NA) (NF := NF) (c := c) (SB := SB) (A := A) (AQ := AQ); try eassumption.
  split; [assumption|]. split; [apply munch_refl | apply wmono_refl].
Qed.

End RC__1.
