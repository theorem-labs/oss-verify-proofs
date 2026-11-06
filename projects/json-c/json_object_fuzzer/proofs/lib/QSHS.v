(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn QRUw QT7i Q7UD Qhd4 Qwm6 QlKV QsKa QpNt QgoM Q4v2 QgHv Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QgoM.Mq1 Q4v2.Mq0 QgHv.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendMain.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Lemma memappend_A_rebase_nf :
forall (buf0 bpos0 cap0 : Z) (content0 : list byte) (xra t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x25 x26 x27 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(obuf ocap buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b -> b + n <= alloc_ceiling ->
(0 < n -> unpoisoned asegs m A_SB b n) -> (n <= 64 \/ app_mem b n) ->
(b + n <= buf \/ buf + cap <= b) ->
(b + n <= obuf \/ obuf + ocap <= b) -> 0 <= obuf -> obuf + ocap <= 2^64 -> 0 < ocap < 2^31 ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - memappend_costX2 cap0 bpos0 n <= bB B -> bD B0 <= bD B ->
cap = memappend_cap2 cap0 bpos0 n ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md' A', memappend_A_post_nf HIx ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf0 bpos0 cap0 content0 src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 obuf) x19 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 1 + A_SB)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + A_SB)) (Z_to_bv 64 ocap) x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a218) fc None m (seg_rom asegs)).
Proof.
intros buf0 bpos0 cap0 content0. intros until fjunk.
intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn UPS AMS BSEP OSEP Ob0 Obn Ocap ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD CAPE Ebpos Epre K.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step. step. step. step.
rewrite (unsigned_lit b) by lia. rewrite (unsigned_lit obuf) by lia.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
destruct (Z.eq_dec b obuf) as [Eb|Nb].
-
assert (Hn0 : n = 0) by lia. subst b.
rewrite (v_sltu_0 (Z_to_bv 64 obuf) (Z_to_bv 64 obuf)) by lia.
replace (obuf - obuf) with 0 by lia.
rewrite (v_sltu_1 (Z_to_bv 64 0) (Z_to_bv 64 ocap)) by (rewrite !unsigned_lit by lia; lia).
match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v end.
step. if_falsex.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
shadow_nowA A4L HIx HP pb 16 SHpb. a4l.
step. step. if_false. rewrite ?zxb_zero.
clear SHpb.
step. step.
try replace (buf + 0) with buf by lia.
assert (src = []) as -> by (destruct src; [reflexivity | cbn in SRCL; lia]).
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
evt_done5.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
eapply (memappend_A_tail_nf HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap buf content [] errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: try (unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption).
all: try (apply bytes_at_nil; unfold_consts; lia).
all: try (intros Hpos; exfalso; lia).
all: try (left; lia).
all: try (unfold_consts; lia).
-
match goal with |- context [Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?v) + 0))] =>
replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))) with (Z_to_bv 64 (-1)) end.
2:{ assert (Hv : forall v, v = 18446744073709551615 -> Z_to_bv 64 (-1) = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))).
{ intros v ->. rewrite (unsigned_lit 18446744073709551615) by lia.
replace (18446744073709551615 + 0) with (-1 + 4294967296 * 4294967296) by lia.
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
apply Hv. clear Hv.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (b - obuf))) as R1. unfold bv_modulus in R1. cbn in R1.
destruct (Z.lt_ge_cases b obuf) as [Hlt|Hge].
- rewrite (v_sltu_1 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 1) by lia. rewrite (swrap32_id (0 - 1)) by lia. change (0 - 1) with (-1). rewrite unsigned_m1.
rewrite lor_ones64_l by lia. rewrite (unsigned_lit 18446744073709551615) by lia.
rewrite lor_ones64_l; [reflexivity|].
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R2; unfold bv_modulus in R2; cbn in R2; lia end.
- assert (obuf + ocap <= b) by lia.
rewrite (v_sltu_0 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite (swrap32_id (0 - 0)) by lia. change (0 - 0) with 0. rewrite (unsigned_lit 0) by lia.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite Z.lor_0_l.
rewrite (v_sltu_0 (Z_to_bv 64 (b - obuf)) (Z_to_bv 64 ocap)) by (rewrite (unsigned_lit (b - obuf)) by lia; rewrite (unsigned_lit ocap) by lia; lia).
rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite unsigned_m1.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite lor_ones64_r by lia. reflexivity. }
step. if_truex.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail_nf HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap b content src errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: first [ unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption | unfold_consts; lia ].
Qed.
End APbMemappendMain.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH Qu4M Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QCcH Q0Ek QjDH.Mq0. Import Qu4M.Mq0.
Import QlKV.Mq2 QsKa Qiiq.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Fixpoint arr_wsum (ws : list Z) : Z := match ws with [] => 0 | x :: r => (2 + x) + arr_wsum r end.
Fixpoint obj_wsum (keys : list blk) (ws : list Z) : Z :=
match keys, ws with (_, kn) :: keys', x :: r => (key_w kn + x) + obj_wsum keys' r | _, _ => 0 end.

Lemma arr_wsum_nonneg : forall ws, Forall (fun x => 0 <= x) ws -> 0 <= arr_wsum ws.
Proof. induction 1; cbn [arr_wsum]; lia. Qed.
Lemma key_w_pos : forall kn, 14 <= key_w kn. Proof. intros kn. unfold key_w. lia. Qed.
Lemma obj_wsum_nonneg : forall keys ws, Forall (fun x => 0 <= x) ws -> 0 <= obj_wsum keys ws.
Proof.
intros keys ws H. revert keys. induction H as [|x r Hx Hr IH]; intros [|[k kn] keys]; cbn [obj_wsum]; try lia.
pose proof (key_w_pos kn). specialize (IH keys). lia.
Qed.
Lemma arr_wsum_len : forall ws, Forall (fun x => 0 <= x) ws -> 2 * Z.of_nat (length ws) <= arr_wsum ws.
Proof. induction 1 as [|x l Hx Hl IH]; cbn [arr_wsum length]; lia. Qed.
Lemma arr_wsum_skipn : forall ws i x, nth_error ws i = Some x -> arr_wsum (skipn i ws) = (2 + x) + arr_wsum (skipn (S i) ws).
Proof. induction ws as [|y ws IH]; intros [|i] x H; cbn in H; try discriminate; [injection H as ->; reflexivity | exact (IH i x H)]. Qed.

Lemma jtx_ge8 : forall s bs w r, jtx s bs = Some (w, r) -> 8 <= w.
Proof.
intros s bs w r H. destruct s as [|u| |h|kids|kids].
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as <- _; lia | discriminate].
- destruct u; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 48); [injection H as <- _; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 48); [injection H as <- _; lia | discriminate].
- cbn in H. destruct bs as [|[a z] bs]; [discriminate|]. destruct (z =? 56); [injection H as <- _; lia | discriminate].
- destruct h; cbn in H.
+ destruct bs as [|[a z] [|[a1 z1] bs]]; try discriminate. destruct (z =? 56); [injection H as <- _; lia | discriminate].
+ destruct bs as [|[a z] bs]; [discriminate|]. destruct (Z.leb_spec 57 z); [injection H as <- _; unfold str_w; lia | discriminate].
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_obj_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 56) && (length kids <=? length r0)%nat); [|discriminate].
pose proof (jtxk_obj_acc kids (fun s0 _ => jtx_nonneg s0) _ _ _ _ _ H). lia.
- destruct bs as [|[a0 z0] [|[a1 z1] [|b2 r0]]]; try discriminate. rewrite jtx_arr_eq in H.
destruct ((snd (a0, z0) =? 48) && (snd (a1, z1) =? 32)); [|discriminate].
pose proof (jtxk_arr_acc (fun _ => True) kids (fun s0 _ => jtx_nonneg s0) _ _ _ _ H). lia.
Qed.
Lemma obj_wsum_skipn : forall (keys : list blk) (ws : list Z) j k kn x, nth_error keys j = Some (k, kn) -> nth_error ws j = Some x ->
obj_wsum (skipn j keys) (skipn j ws) = (key_w kn + x) + obj_wsum (skipn (S j) keys) (skipn (S j) ws).
Proof.
induction keys as [|[k0 kn0] keys IH]; intros ws [|j] k kn x Hk Hx; cbn in Hk; try discriminate.
- destruct ws as [|y ws]; cbn in Hx; [discriminate|]. injection Hk as -> ->. injection Hx as ->. reflexivity.
- destruct ws as [|y ws]; cbn in Hx; [discriminate|]. exact (IH ws j k kn x Hk Hx).
Qed.
Lemma Forall_skipn_nonneg : forall (ws : list Z) i, Forall (fun x => 0 <= x) ws -> Forall (fun x => 0 <= x) (skipn i ws).
Proof. induction ws as [|x ws IHw]; intros [|i] H; cbn [skipn]; try exact H. apply IHw. inversion H; assumption. Qed.
Lemma arr_wsum_skipn_nonneg : forall ws i, Forall (fun x => 0 <= x) ws -> 0 <= arr_wsum (skipn i ws).
Proof. intros ws i H. apply arr_wsum_nonneg. apply Forall_skipn_nonneg. exact H. Qed.
Lemma nth_error_nth_len : forall (ws : list Z) i, (i < length ws)%nat -> nth_error ws i = Some (nth i ws 0).
Proof. intros ws i H. apply nth_error_nth'. exact H. Qed.

Lemma odep_le_okmax : forall kids k, In k kids -> odep k <= okmax kids.
Proof. induction kids as [|o l IH]; intros k Hk; [destruct Hk|]. rewrite okmax_cons. destruct Hk as [->|H]; [lia | specialize (IH k H); lia]. Qed.

Lemma PhiA_nonneg : forall cap len, arr_inv cap len -> 0 <= PhiA cap len.
Proof. intros cap len (H32 & Hl & Hc). unfold PhiA. lia. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.

Lemma jtxk_arr_kidw : forall m kids ps KBS, kids_okp segs fn m kids ps KBS ->
forall P0 Y acc w R, pbtail P0 -> jtxk_arr kids (P0 ++ concat KBS ++ Y) acc = Some (w, R) ->
exists ws, length ws = length kids /\ w = acc + arr_wsum ws /\ Forall (fun x => 0 <= x) ws /\
(forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri)) /\
(forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W).
Proof.
intros m kids. induction kids as [|[s'|] kids IH]; intros ps KBS OK P0 Y acc w R HP0 H.
- destruct ps; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_arr] in H. injection H as <- _. exists [].
split; [reflexivity|]. split; [cbn; lia|]. split; [constructor|]. split; [intros [|i] s bs Hk; discriminate | intros [|i] Hk; discriminate].
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [jtxk_arr concat] in H. destruct (jtx s' (P0 ++ (bs1 ++ concat KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP0 E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (jtx_val_tail segs fn s' m bs1 v 1 JV _ _ _ E) as (P1 & -> & HP1).
destruct (IH ps KBS OK P1 Y _ w R HP1 H) as (ws & L & Ew & NNw & K1 & K2).
exists (w1 :: ws). split; [cbn [length]; lia|]. split; [cbn [arr_wsum]; lia|].
split; [constructor; [exact (jtx_nonneg _ _ _ _ E) | exact NNw] |].
split.
+ intros [|i] s bs Hk Hb; cbn in Hk, Hb.
* injection Hk as <-. injection Hb as <-. cbn [nth]. eexists _, _. exact E.
* cbn [nth]. exact (K1 i s bs Hk Hb).
+ intros [|i] Hk; cbn in Hk; [discriminate | cbn [nth]; exact (K2 i Hk)].
- destruct ps as [|v ps]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_arr concat app] in H.
destruct (IH ps KBS OK P0 Y _ w R HP0 H) as (ws & L & Ew & NNw & K1 & K2).
exists (NULL_W :: ws). split; [cbn [length]; lia|]. split; [cbn [arr_wsum]; lia|].
split; [constructor; [unfold NULL_W; lia | exact NNw] |].
split.
+ intros [|i] s bs Hk Hb; cbn in Hk, Hb; [discriminate | cbn [nth]; exact (K1 i s bs Hk Hb)].
+ intros [|i] Hk; cbn in Hk; [reflexivity | cbn [nth]; exact (K2 i Hk)].
Qed.

Lemma jtx_arr_kidw : forall m kids ps KBS PBS (b0 b1 b2 : blk) Y w R,
kids_okp segs fn m kids ps KBS ->
jtx (Sarr kids) (((b0 :: [b1; b2] ++ concat KBS) ++ PBS) ++ Y) = Some (w, R) ->
exists ws, length ws = length kids /\ w = 24 + arr_wsum ws /\ Forall (fun x => 0 <= x) ws /\
(forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri)) /\
(forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W).
Proof.
intros m kids ps KBS PBS b0 b1 b2 Y w R OK H.
cbn [app] in H. rewrite <- ?app_assoc in H. rewrite jtx_arr_eq in H.
destruct ((snd b0 =? 48) && (snd b1 =? 32)); [| discriminate].
exact (jtxk_arr_kidw m kids ps KBS OK [] (PBS ++ Y) 24 w R pbtail_nil H).
Qed.

Lemma jtxk_obj_kidw : forall m kids kvs KBS, kids_okv segs fn m kids kvs KBS ->
forall keys P0 Y acc w R, pbtail P0 -> jtxk_obj kids keys (P0 ++ concat KBS ++ Y) acc = Some (w, R) ->
exists ws, length ws = length kids /\ w = acc + obj_wsum keys ws /\ Forall (fun x => 0 <= x) ws /\
(forall i s bs, nth_error kids i = Some (Some s) -> nth_error KBS i = Some bs -> exists Yi Ri, jtx s (bs ++ Yi) = Some (nth i ws 0, Ri)) /\
(forall i, nth_error kids i = Some None -> nth i ws 0 = NULL_W).
Proof.
intros m kids. induction kids as [|[s'|] kids IH]; intros kvs KBS OK keys P0 Y acc w R HP0 H.
- destruct kvs; [|destruct OK]. destruct KBS; [|destruct OK]. cbn [jtxk_obj] in H. injection H as <- _. exists [].
split; [reflexivity|]. split; [destruct keys as [|[? ?] ?]; cbn; lia|]. split; [constructor|]. split; [intros [|i] s bs Hk; discriminate | intros [|i] Hk; discriminate].
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv JV] OK].
cbn [jtxk_obj concat] in H. destruct keys as [|[k kn] keys]; [discriminate|].
destruct (jtx s' (P0 ++ (bs1 ++ concat KBS) ++ Y)) as [[w1 R1]|] eqn:E; [|discriminate].
pose proof (jtx_pbtail_nil _ _ _ _ _ HP0 E) as ->. cbn [app] in E. rewrite <- app_assoc in E.
destruct (jtx_val_tail segs fn s' m bs1 v 1 JV _ _ _ E) as (P1 & -> & HP1).
destruct (IH kvs KBS OK keys P1 Y _ w R HP1 H) as (ws & L & Ew & NNw & K1 & K2).
exists (w1 :: ws). split; [cbn [length]; lia|]. split; [cbn [obj_wsum]; lia|].
split; [constructor; [exact (jtx_nonneg _ _ _ _ E) | exact NNw] |].
split.
+ intros [|i] s bs Hk Hb; cbn in Hk, Hb.
* injection Hk as <-. injection Hb as <-. cbn [nth]. eexists _, _. exact E.
* cbn [nth]. exact (K1 i s bs Hk Hb).
+ intros [|i] Hk; cbn in Hk; [discriminate | cbn [nth]; exact (K2 i Hk)].
- destruct kvs as [|[kk v] kvs]; [destruct OK|]. destruct KBS as [|bs1 KBS]; [destruct OK|]. destruct OK as [[Hv ->] OK].
cbn [jtxk_obj concat app] in H. destruct keys as [|[k kn] keys]; [discriminate|].
destruct (IH kvs KBS OK keys P0 Y _ w R HP0 H) as (ws & L & Ew & NNw & K1 & K2).
exists (NULL_W :: ws). split; [cbn [length]; lia|]. split; [cbn [obj_wsum]; lia|].
split; [constructor; [unfold NULL_W; lia | exact NNw] |].
split.
+ intros [|i] s bs Hk Hb; cbn in Hk, Hb; [discriminate | cbn [nth]; exact (K1 i s bs Hk Hb)].
+ intros [|i] Hk; cbn in Hk; [reflexivity | cbn [nth]; exact (K2 i Hk)].
Qed.
End WithSegs.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import QbFI. Import QRUw.    Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QpNt.Mq8 QgoM Q4v2 QgHv.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendMain.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Lemma memappend_A_rebase_nf :
forall (buf0 bpos0 cap0 : Z) (content0 : list byte) (xra t0 t1 t2 a3 a4 a5 a6 a7 x18 x19 x25 x26 x27 t3 t4 t5 t6 : word)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(obuf ocap buf bpos cap b : Z) (content src : list byte) (errv : word) (fjunk : list byte),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B m md ->
pbufx m pb buf bpos cap content ->
bpos + n + 1 <= cap -> 0 <= n < 2^31 ->
bytes_at asegs m b src -> Z.of_nat (length src) = n -> 0 <= b -> b + n <= alloc_ceiling ->
(0 < n -> unpoisoned asegs m A_SB b n) -> (n <= 64 \/ app_mem b n) ->
(b + n <= buf \/ buf + cap <= b) ->
(b + n <= obuf \/ obuf + ocap <= b) -> 0 <= obuf -> obuf + ocap <= 2^64 -> 0 < ocap < 2^31 ->
stk asegs m lo (bv_unsigned sp + -112) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m (bv_unsigned sp + -112) [CB 8 fjunk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
bB B0 - memappend_costX2 cap0 bpos0 n <= bB B -> bD B0 <= bD B ->
cap = memappend_cap2 cap0 bpos0 n ->
bpos = bpos0 -> firstn (Z.to_nat bpos) content = firstn (Z.to_nat bpos0) content0 ->
(forall ms' md' A', memappend_A_post_nf HIx ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf0 bpos0 cap0 content0 src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pb + 8)) (Z_to_bv 64 (pb + 12))
(Z_to_bv 64 pb) (Z_to_bv 64 b) (Z_to_bv 64 n) a3 a4 a5 a6 a7
(Z_to_bv 64 obuf) x19 (Z_to_bv 64 A_SB) (Z_to_bv 64 (pb / 8 + 1 + A_SB)) (Z_to_bv 64 (pb / 8)) (Z_to_bv 64 (pb / 8 + A_SB)) (Z_to_bv 64 ocap) x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b6bc) fc None m (seg_rom asegs)).
Proof.
intros buf0 bpos0 cap0 content0. intros until fjunk.
intros HP PBX ROOM Hn SRC SRCL Hb0 Hbn UPS AMS BSEP OSEP Ob0 Obn Ocap ST LO LOS SPA HT FR ERR RA VM0 HPR BB BD CAPE Ebpos Epre K.
unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
reenterA asegs A4L HIx asegs_wx HP.
step. step. step. step. step. step. step. step.
rewrite (unsigned_lit b) by lia. rewrite (unsigned_lit obuf) by lia.
destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
destruct (Z.eq_dec b obuf) as [Eb|Nb].
-
assert (Hn0 : n = 0) by lia. subst b.
rewrite (v_sltu_0 (Z_to_bv 64 obuf) (Z_to_bv 64 obuf)) by lia.
replace (obuf - obuf) with 0 by lia.
rewrite (v_sltu_1 (Z_to_bv 64 0) (Z_to_bv 64 ocap)) by (rewrite !unsigned_lit by lia; lia).
match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v end.
step. if_falsex.
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
shadow_nowA A4L HIx HP pb 16 SHpb. a4l.
step. step. if_false. rewrite ?zxb_zero.
clear SHpb.
step. step.
try replace (buf + 0) with buf by lia.
blk_factsA A4L HIx HP buf cap Hbal0 Hblo0 Hbhi0 Hbimg0.
step. if_falsex.
step. step. ub_nzpair buf buf.
step. rewrite ?unsigned_lit by lia. change (Z.lxor 1 0) with 1.
step. if_falsex.
assert (src = []) as -> by (destruct src; [reflexivity | cbn in SRCL; lia]).
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
evt_done5.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
eapply (memappend_A_tail_nf HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap buf content [] errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: try (unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption).
all: try (apply bytes_at_nil; unfold_consts; lia).
all: try (intros Hpos; exfalso; lia).
all: try (left; lia).
all: try (unfold_consts; lia).
-
match goal with |- context [Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?v) + 0))] =>
replace (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))) with (Z_to_bv 64 (-1)) end.
2:{ assert (Hv : forall v, v = 18446744073709551615 -> Z_to_bv 64 (-1) = Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0))).
{ intros v ->. rewrite (unsigned_lit 18446744073709551615) by lia.
replace (18446744073709551615 + 0) with (-1 + 4294967296 * 4294967296) by lia.
rewrite swrap32_shift, swrap32_id by lia. reflexivity. }
apply Hv. clear Hv.
pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 (b - obuf))) as R1. unfold bv_modulus in R1. cbn in R1.
destruct (Z.lt_ge_cases b obuf) as [Hlt|Hge].
- rewrite (v_sltu_1 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 1) by lia. rewrite (swrap32_id (0 - 1)) by lia. change (0 - 1) with (-1). rewrite unsigned_m1.
rewrite lor_ones64_l by lia. rewrite (unsigned_lit 18446744073709551615) by lia.
rewrite lor_ones64_l; [reflexivity|].
match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R2; unfold bv_modulus in R2; cbn in R2; lia end.
- assert (obuf + ocap <= b) by lia.
rewrite (v_sltu_0 (Z_to_bv 64 b) (Z_to_bv 64 obuf)) by (rewrite (unsigned_lit b) by lia; rewrite (unsigned_lit obuf) by lia; lia).
rewrite (unsigned_lit 0) by lia. rewrite (swrap32_id (0 - 0)) by lia. change (0 - 0) with 0. rewrite (unsigned_lit 0) by lia.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite Z.lor_0_l.
rewrite (v_sltu_0 (Z_to_bv 64 (b - obuf)) (Z_to_bv 64 ocap)) by (rewrite (unsigned_lit (b - obuf)) by lia; rewrite (unsigned_lit ocap) by lia; lia).
rewrite (unsigned_lit 0) by lia. change (0 + -1) with (-1). rewrite unsigned_m1.
rewrite (unsigned_lit (b - obuf)) by lia. rewrite lor_ones64_r by lia. reflexivity. }
step. if_truex.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail_nf HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf0 bpos0 cap0 n content0 T s0
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m md A B buf bpos cap b content src errv fjunk);
first [ reflexivity | eassumption | lia | idtac ].
all: first [ unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption | unfold_consts; lia ].
Qed.
End APbMemappendMain.
End RC__1.
End Mq2.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyh.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition APE_LOOP : Z := 0x93f2c.
Definition APE_REDO : Z := 0x95bc4.
Definition APE_REDO0 : Z := 0x93fd4.
Definition APE_DISPJ : Z := 0x94018.
Definition APE_STBRK : Z := 0x98704.
Definition APE_EATBRK : Z := 0x97f18.
Definition APE_BREAK : Z := 0x98708.
Definition APE_OUT : Z := 0x998bc.
Definition APE_ERR2 : Z := 0x998b4.
Definition APE_ERR3 : Z := 0x9a30c.
Definition APE_EPI : Z := 0x93c2c.
Definition APE_JTAB : Z := 0x22ca8.
Definition APE_FRAME : Z := 416.
Definition AFF_SIZE : Z := 256.

Definition pe_jtA (st : Z) : Z :=
match st with
| 0 => 0x94b5c | 1 => 0x94cd0 | 2 => 0x946e8 | 3 => 0x948c4 | 4 => 0x97058 | 5 => 0x97434 | 6 => 0x97350
| 7 => 0x96f7c | 8 => 0x96dd4 | 9 => 0x97298 | 10 => 0x97080 | 11 => 0x94774 | 12 => 0x945b4 | 13 => 0x94330
| 14 => 0x94164 | 15 => 0x94088 | 16 => 0x9423c | 17 => 0x9776c | 18 => 0x96b24 | 19 => 0x9752c | 20 => 0x97718
| 21 => 0x94100 | 22 => 0x94d68 | 23 => 0x976bc | 24 => 0x94088 | 25 => 0x96b24 | 26 => 0x94f24
| _ => 0
end.

Definition pe_jtabA : list byte := Eval vm_compute in match image_bytes asegs 0x22ca8 108 with Some bs => bs | None => [] end.
Lemma pe_jtabA_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x22ca8 [CB 108 pe_jtabA].
Proof.
intros m MI. change 108%nat with (length pe_jtabA).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtabA)) with 108%Z. lia.
Qed.

Definition shA (x : Z) : Z := x / 8 + A_SB.

Definition SB2 : Z := 2147450882.
Definition SB4 : Z := 2147450884.
Definition SB7 : Z := 2147450887.
Definition SB8 : Z := 2147450888.

Record pe_fixA := PEFA {
pa_sp0 : Z;
pa_F : Z;
pa_oldloc : Z;
pa_newloc : Z;
pa_bslack : Z;
pa_dslack : Z }.

Record pe_junkA := PEJA { pj_0 : list byte; pj_8 : word; pj_16 : word; pj_obj : word; pj_288 : list byte; pj_304 : list byte;
pj_gap : list byte;
pj_fhd : list byte; pj_f1 : list byte; pj_f2 : list byte  }.

Definition pe_slotsA (pf : pe_fix) (pa : pe_fixA) (nb : word) (pj : pe_junkA) : list cell :=
let tk := pf_tk pf in let F := pa_F pa in
[C8 (pj_8 pj);
C8 (wz ((tk + 20) mod 8 + 3)); C8 (wz ((tk + 64) mod 8 + 3)); C8 (wz ((tk + 32) mod 8 + 3));
C8 (wz (F + 128)); C8 (wz (F + 112)); C8 (wz (F + 96)); C8 (wz (F + 80)); C8 (wz (F + 176)); C8 (wz (F + 144));
C8 (wz (tk + 48)); C8 (wz (F + 32)); C8 (wz (tk + 44)); C8 (wz (pa_newloc pa)); C8 (wz (tk + 40)); C8 (wz (tk + 16));
C8 (pj_obj pj); C8 (wz (tk + 24)); C8 (wz (tk + 28)); C8 (wz (pa_oldloc pa)); C8 (wz (tk + 36));
C8 (wz (tk / 8 + 2 + A_SB)); C8 (wz (tk + 8)); C8 (wz (tk / 8 + 4 + A_SB)); C8 (wz F); C8 (wz F);
C8 (wz (tk + 32)); C8 (wz (tk / 8 + 7 + A_SB)); C8 (wz (tk + 56)); C8 (wz (tk + 20)); C8 (wz tk);
C8 (wz (pf_lenr pf)); C8 (wz (tk / 8 + 8 + A_SB)); C8 (wz (tk + 64)); C8 (wz (F + 64)); C8 (wz (tk / 8 + 4 + A_SB));
CB 8 (pj_288 pj); C8 (wz F); CB 4 (pj_304 pj); C4 nb].

Lemma pe_slotsA_size : forall pf pa nb pj, Z.of_nat (cells_size (pe_slotsA pf pa nb pj)) = 312.
Proof. reflexivity. Qed.

Definition pe_savedA_cells (sv : pe_saved) : list cell :=
[C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)].

Definition ff_cellsA (cb : byte) (pj : pe_junkA) : list cell :=
[CB 24 (pj_fhd pj); CB 40 (pj_f1 pj); C1 cb; CB 183 (pj_f2 pj)].

Definition FSH0 : list Z :=
[0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf2; 0xf2; 0xf2; 0x01; 0xf2; 0xf8; 0xf2; 0xf8; 0xf2; 0xf8; 0xf2;
0xf8; 0xf2; 0xf8; 0xf2; 0xf2; 0xf2; 0xf8; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3; 0; 0; 0; 0].
Definition ffsh_cells (vals : list Z) : list cell := map (fun v => C1 (Z_to_bv 8 v)) vals.

Definition pe_frameA (segs : list Segment) (m : word -> option byte) (pf : pe_fix) (pa : pe_fixA)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) : Prop :=
rw_cells segs m (pf_spf pf) (pe_slotsA pf pa nb pj) /\
rw_cells segs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) (pj_gap pj)] /\
rw_cells segs m (pa_sp0 pa - 104) (pe_savedA_cells sv) /\
rw_cells segs m (pa_F pa) (ff_cellsA cb pj) /\
rw_cells segs m (shA (pa_F pa)) (ffsh_cells FSH0).

Definition pe_geomA (pf : pe_fix) (pa : pe_fixA) : Prop :=
pf_spf pf mod 32 = 0 /\ pa_sp0 pa mod 16 = 0 /\ pa_sp0 pa - 432 <= pf_spf pf <= pa_sp0 pa - 416 /\
pa_F pa mod 256 = 0 /\ 0 < pa_F pa /\ pa_F pa + 256 <= alloc_ceiling /\
pf_tk pf mod 16 = 0.

Definition pe_msA (segs : list Segment) (pf : pe_fix) (pa : pe_fixA) (pc : Z) (co : Z)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
let tk := pf_tk pf in
MS (mkR (Z_to_bv 64 (tk / 8 + SB2)) (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 (Z_to_bv 64 (pf_lenr pf)) (Z_to_bv 64 (tk + 32))
(Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 (Z_to_bv 64 (pf_sb pf + co)) s5 s6 s7 s8 s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs).

Definition pe_msO (segs : list Segment) (pf : pe_fix) (pa : pe_fixA) (pc : Z)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
let tk := pf_tk pf in
MS (mkR (Z_to_bv 64 (tk / 8 + SB2)) (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs).

Definition pe_msX (segs : list Segment) (pf : pe_fix) (pa : pe_fixA) (pc : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom segs).

Section Inv.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.

Definition payload_locA (pf : pe_fix) (pa : pe_fixA) (LB0 : list blk) (FRS : list frame) (m : word -> option byte) : Prop :=
(exists b, In b LB0 /\ blk_addr b <= pf_sb pf /\ pf_sb pf + pf_len pf <= blk_addr b + blk_size b)
\/ (exists Fh kh, In (Fh, kh) FRS /\ Fh <= pf_sb pf /\ pf_sb pf + pf_len pf <= Fh + fr_size kh - 8 /\
unpoisoned asegs m A_SB (pf_sb pf) (pf_len pf)).

Definition PE_BUD (pf : pe_fix) (pa : pe_fixA) (ts : tstate) (B : bud) : Prop :=

K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B /\ pa_dslack pa <= bD B.

Lemma PE_BUD_exit : forall pf pa ts B, 0 <= t_co ts <= pf_len pf -> PE_BUD pf pa ts B ->
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B /\ pa_dslack pa <= bD B.
Proof. intros pf pa ts B _ H. exact H. Qed.

Definition pe_blocksA (pf : pe_fix) (q : Z) (LB0 : list blk) (ts : tstate) : list blk :=
tstate_blocks ts ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LB0.

Definition PE_CORE_A (pf : pe_fix) (pa : pe_fixA) (q : Z) (m : word -> option byte) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) : Prop :=
length (t_levels ts) = Z.to_nat (pf_mxd pf) /\ (t_depth ts < Z.to_nat (pf_mxd pf))%nat /\
0 <= t_co ts <= pf_len pf /\ ts_choff (t_x ts) = Z_to_bv 64 (t_co ts) /\
rw_cells asegs m (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q (t_x ts)) /\
pbuf asegs m (t_pbs ts) (t_pb ts) /\ t_pb ts <> 0 /\
tstack asegs m q (t_levels ts) /\
pe_frameA asegs m pf pa cb nb pj sv.

Definition PE_REST_A (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (errv : word) : Prop :=
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur asegs A4F m (t_depth ts) i l) /\
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []) /\
stk asegs m lo (pf_spf pf) /\
rw_cells asegs m A_ERRNO [C4 errv] /\
bytes_at asegs m (pf_sb pf) payload /\ Z.of_nat (length payload) = pf_len pf /\
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) /\
heap_presx A4H a4_volatile (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m /\
model_vm_only (pf_md pf) (cfg_model md) /\
GA m /\
PE_BUD pf pa ts B.

Definition PE_INV_A (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\ PE_REST_A pf pa q LB0 LM FRS payload me lo m md A B ts errv.

Definition PE_STATIC_A (pf : pe_fix) (pa : pe_fixA) (lo : Z) : Prop :=
alloc_ceiling <= lo /\ lo <= pf_spf pf - 12288 /\
pe_geomA pf pa /\ pa_sp0 pa + 32 <= hiA_top A4L HIx /\ 0 <= pf_spf pf < 2^62 /\
0 <= pf_len pf < 2^26 /\ 0 <= pf_sb pf /\ pf_sb pf + pf_len pf < 2^63 /\
(0 <= pf_lenr pf < 2^64 /\ (1 <= pf_mxd pf <= 32 /\ 0 <= pf_fl pf < 2^32)) /\ LENR_OK pf.

Definition PE_BASE_A (pf : pe_fix) (pa : pe_fixA) (LB0 LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (LBall : list blk) (errv : word) : Prop :=
HEAPA A4L HIx A LBall LM ((pa_F pa, 2) :: FRS) B m md /\
stk asegs m lo (pf_spf pf) /\
rw_cells asegs m A_ERRNO [C4 errv] /\
bytes_at asegs m (pf_sb pf) payload /\ Z.of_nat (length payload) = pf_len pf /\
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) /\
heap_presx A4H a4_volatile (LB0 ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m /\
model_vm_only (pf_md pf) (cfg_model md) /\
GA m.

Definition lvl_weakA (m : word -> option byte) (depth i : nat) (l : tlevel) : Prop :=
(0 <= tl_st l <= 26 /\ 0 <= tl_ss l <= 26) /\
jopt asegs A4F (tl_cs l) m (tl_cbs l) (tl_cur l) /\
(name_ok asegs m false l \/ name_ok asegs m true l) /\
((depth < i)%nat -> lvl_clean l).

Definition PE_INVW_A (pf : pe_fix) (pa : pe_fixA) (q : Z) (LB0 LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud) (ts : tstate) (LK : list blk)
(cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word) : Prop :=
PE_CORE_A pf pa q m ts cb nb pj sv /\
PE_BASE_A pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 ts ++ LK) errv /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_weakA m (t_depth ts) i l) /\
K_free * Z.of_nat (length (tstate_blocks ts)) + K_exit + pa_bslack pa <= bB B /\ pa_dslack pa <= bD B.

Lemma lvl_cur_weakA : forall m depth i l, lvl_cur asegs A4F m depth i l -> lvl_weakA m depth i l.
Proof.
intros m depth i l (R1 & R2 & J & M). split; [split; [exact R1 | exact R2]|]. split; [exact J|].
destruct (Nat.ltb_spec i depth) as [Hlt|Hge].
- destruct M as [(_ & _ & N)|(_ & _ & N)]; (split; [| intros; exfalso; lia]); [left | right]; exact N.
- destruct (Nat.eqb_spec i depth) as [->|Hne].
+ destruct M as (c & hn & _ & _ & N). split; [| intros; exfalso; lia]. destruct hn; [right | left]; exact N.
+ pose proof M as (C1 & C2 & C3 & C4 & C5). split; [| intros _; exact M]. left. cbn. split; [exact C4 | exact C5].
Qed.

Lemma PE_REST_A_base : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv,
PE_REST_A pf pa q LB0 LM FRS payload me lo m md A B ts errv ->
PE_BASE_A pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 ts) errv /\
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur asegs A4F m (t_depth ts) i l) /\
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []) /\
PE_BUD pf pa ts B.
Proof.
intros until errv. intros (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD).
split; [| split; [exact LV | split; [exact OBJ | exact BUD]]].
split; [exact HP|]. split; [exact ST|]. split; [exact ERR|]. split; [exact STR|]. split; [exact PLEN|].
split; [exact SBin | split; [exact HPR | split; [exact MDV | exact G]]].
Qed.

Lemma PE_REST_A_of_base : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv,
PE_BASE_A pf pa LB0 LM FRS payload me lo m md A B (pe_blocksA pf q LB0 ts) errv ->
(forall i l, nth_error (t_levels ts) i = Some l -> lvl_cur asegs A4F m (t_depth ts) i l) ->
(if zin (cur_st ts) [ST_array_add; ST_ovadd] then jopt asegs A4F (t_objs ts) m (t_objbs ts) (t_obj ts) else t_objbs ts = []) ->
PE_BUD pf pa ts B ->
PE_REST_A pf pa q LB0 LM FRS payload me lo m md A B ts errv.
Proof.
intros until errv. intros (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & G) LV OBJ BUD.
split; [exact HP|]. split; [exact LV|]. split; [exact OBJ|]. split; [exact ST|]. split; [exact ERR|]. split; [exact STR|].
split; [exact PLEN|]. split; [exact SBin | split; [exact HPR | split; [exact MDV | split; [exact G | exact BUD]]]].
Qed.

Lemma PE_INV_A_W : forall pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv,
PE_INV_A pf pa q LB0 LM FRS payload me lo m md A B ts cb nb pj sv errv ->
PE_INVW_A pf pa q LB0 LM FRS payload me lo m md A B ts [] cb nb pj sv errv.
Proof.
intros until errv. intros [CORE REST]. split; [exact CORE|].
apply PE_REST_A_base in REST as (BASE & LV & OBJ & BUD).
split; [rewrite app_nil_r; exact BASE|].
split; [intros i l Hl; apply lvl_cur_weakA; exact (LV i l Hl)|].
destruct CORE as (_ & _ & Hco & _). exact (PE_BUD_exit _ _ _ _ Hco BUD).
Qed.

Lemma PE_REST_A_set_co : forall pf pa q LB0 LM FRS payload me lo m md A B ts errv co',
PE_REST_A pf pa q LB0 LM FRS payload me lo m md A B ts errv -> t_co ts <= co' <= pf_len pf ->
PE_REST_A pf pa q LB0 LM FRS payload me lo m md A B (ts_set_co ts co') errv.
Proof.
intros until co'. intros (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) Hco.
unfold ts_set_co. split; [exact HP|]. split; [exact LV|]. split; [exact OBJ|]. split; [exact ST|]. split; [exact ERR|].
split; [exact STR|]. split; [exact PLEN|]. split; [exact SBin|]. split; [exact HPR|]. split; [exact MDV|]. split; [exact G|].
exact BUD.
Qed.

Definition pe_privateA (pf : pe_fix) (pa : pe_fixA) (q : Z) (pbs : list blk) (iv : Z * Z) : Prop :=
(pf_tk pf <= fst iv /\ snd iv <= pf_tk pf + 72) \/
(q <= fst iv /\ snd iv <= q + 32 * pf_mxd pf) \/
(exists a n, In (a, n) pbs /\ a <= fst iv /\ snd iv <= a + n) \/
(pf_spf pf <= fst iv /\ snd iv <= pa_sp0 pa) \/
(pa_F pa <= fst iv /\ snd iv <= pa_F pa + 248) \/
(shA (pa_F pa) <= fst iv /\ snd iv <= shA (pa_F pa) + 32).

Lemma fr_size_pos : forall k, 0 <= k -> 0 < fr_size k.
Proof. intros k Hk. unfold fr_size. pose proof (Z.pow_pos_nonneg 2 k). lia. Qed.
Lemma fr_shadow_len_bnd : forall k, 0 <= k <= 3 -> 0 < fr_shadow_len k <= 64.
Proof.
intros k Hk. unfold fr_shadow_len. split; [pose proof (Z.pow_pos_nonneg 2 k); lia|].
apply (Z.le_trans _ (8 * 2^3)); [apply Z.mul_le_mono_nonneg_l; [lia | apply Z.pow_le_mono_r; lia] | cbn; lia].
Qed.
Lemma fr_size_2 : fr_size 2 = 256. Proof. reflexivity. Qed.
Lemma fr_shadow_len_2 : fr_shadow_len 2 = 32. Proof. reflexivity. Qed.
Lemma fr_size_shadow : forall k, 0 <= k -> fr_size k = 8 * fr_shadow_len k.
Proof. intros k Hk. unfold fr_size, fr_shadow_len. lia. Qed.
Lemma frame_class_unique : forall A LB LM FR B m md F k k',
HEAPA A4L HIx A LB LM FR B m md -> In (F, k) FR -> In (F, k') FR -> k = k'.
Proof.
intros A LB LM FR B m md F k k' HP H1 H2. pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. clear HP.
induction FR as [|[G kg] FR IH]; [destruct H1|]. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- injection E1; injection E2; intros; subst; reflexivity.
- injection E1; intros; subst. exfalso. apply Hni. exact (in_map fr_base _ _ H2).
- injection E2; intros; subst. exfalso. apply Hni. exact (in_map fr_base _ _ H1).
- exact (IH H1 H2 ND).
Qed.

Lemma shadow_blk_apart : forall A LB LM FR B m md a n x k,
HEAPA A4L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> 0 <= x -> x < alloc_ceiling -> 0 <= k <= 2^20 ->
a + n <= shA x \/ shA x + k <= a.
Proof.
intros A LB LM FR B m md a n x k HP Hin Hx Hxc Hk.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as AM. cbn [hl_sb A4L] in AM. unfold shA, A_SB in *.
pose proof alloc_ceiling_range. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _ & Ha0 & _).
destruct AM as [AM | AM]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma blk_not_fr_iv : forall A LB LM FR B m md a n,
HEAPA A4L HIx A LB LM FR B m md -> In (a, n) (LB ++ LM) -> ~ In (a, n) (fr_ivs A4L FR).
Proof.
intros A LB LM FR B m md a n HP Hin Hf. unfold fr_ivs in Hf. apply in_flat_map in Hf as ([F k] & HF & Hb). cbn in Hb.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _).
pose proof (fr_size_pos k ltac:(lia)) as Hsz.
assert (Hsz64 : 64 <= fr_size k) by (unfold fr_size; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)); lia).
destruct Hb as [E | [E | []]]; injection E as <- <-.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF Hin). lia.
- pose proof alloc_ceiling_range.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ F (fr_shadow_len k) HP Hin ltac:(lia) ltac:(lia)) as D.
unfold shad, shA in *. cbn [hl_sb A4L] in *. unfold A_SB in *.
pose proof (fr_shadow_len_bnd k ltac:(lia)). pose proof (fr_size_pos k ltac:(lia)).
specialize (D ltac:(lia)).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _). lia.
Qed.

Lemma private_disjointA : forall pf pa q LB0 LM FRS B ts A m md lo a n W,
PE_STATIC_A pf pa lo ->
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
In (a, n) (pe_blocksA pf q LB0 ts ++ LM) -> a <> pf_tk pf -> a <> q -> (forall b k, In (b, k) (t_pbs ts) -> a <> b) ->
Forall (pe_privateA pf pa q (t_pbs ts)) W ->
disjoint_from W a n.
Proof.
intros pf pa q LB0 LM FRS B ts A m md lo a n W STC HP Hin Htk Hq Hpb HW.
destruct STC as (LO & LOS & GEO & _). pose proof GEO as (_ & _ & Hspf & _ & HF0 & HFc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (Hn & _ & _ & Hhi & _).
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof alloc_ceiling_range.
induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from]. split; [| apply IH; exact HW].
unfold pe_privateA in H1. cbn [fst snd] in H1. destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
- pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n _ _ HP Hin INtk Htk). lia.
- pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n _ _ HP Hin INq Hq). lia.
- assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n _ _ HP Hin INb (Hpb b k Hb)). lia.
- lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin). unfold fr_size in *. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in *. lia.
- pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Definition payload_safeA (pf : pe_fix) (pa : pe_fixA) (LB0 : list blk) (FRS : list frame) (LBall : list blk) (iv : Z * Z) : Prop :=
(alloc_ceiling <= fst iv /\ snd iv <= pa_sp0 pa)
\/ (exists a n, In (a, n) LBall /\ (forall k, ~ In (a, k) LB0) /\ a <= fst iv /\ snd iv <= a + n)
\/ (hl_img_lo A4H <= fst iv /\ snd iv <= hl_img_hi A4H)
\/ (snd iv <= alloc_ceiling /\ (forall a n, In (a, n) LBall -> a + n <= fst iv \/ snd iv <= a) /\
(forall Fh kh, In (Fh, kh) FRS -> Fh + fr_size kh <= fst iv \/ snd iv <= Fh)).

Lemma payload_disjointA : forall pf pa LB0 LBall LM FR FRS B A m md lo W,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A LBall LM FR B m md -> incl LB0 LBall -> incl FRS FR -> payload_locA pf pa LB0 FRS m ->
Forall (payload_safeA pf pa LB0 FRS (LBall ++ LM)) W -> disjoint_from W (pf_sb pf) (pf_len pf).
Proof.
intros pf pa LB0 LBall LM FR FRS B A m md lo W STC HP Hincl HinclF PL HW.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & _). pose proof alloc_ceiling_range. pose proof (hiA_top_hi A4L HIx).
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
unfold payload_locA in PL.
induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW].
cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
unfold payload_safeA in H1. cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H] in H1.
destruct PL as [(b & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)].
- destruct b as [b0 k]. cbn [blk_addr blk_size fst snd] in Hb1, Hb2. pose proof (Hincl _ Hb) as HbL.
assert (HbL' : In (b0, k) (LBall ++ LM)) by (apply in_or_app; left; exact HbL).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP HbL') as (_ & _ & _ & Hbhi & _).
destruct H1 as [H1 | [(a & n & Ha & Hnot & H1) | [H1 | (H1 & Hap & _)]]].
+ lia.
+ assert (Hne : a <> b0) by (intros ->; exact (Hnot k Hb)).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP Ha HbL' Hne). lia.
+ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP HbL') as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi. lia.
+ pose proof (Hap _ _ HbL'). lia.
- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (HinclF _ HFh)) as (Hkh & _ & HFh0 & HFhc & HFhimg & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFhimg.
destruct H1 as [H1 | [(a & n & Ha & Hnot & H1) | [H1 | (H1 & _ & Hfr)]]].
+ lia.
+ pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP (HinclF _ HFh) Ha). lia.
+ lia.
+ pose proof (Hfr _ _ HFh). lia.
Qed.

Lemma payload_transportA : forall pf pa LB0 LBall LM FR FRS B A m m' md lo W payload,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A LBall LM FR B m md -> incl LB0 LBall -> incl FRS FR ->
bytes_at asegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) ->
munch W m m' -> Forall (payload_safeA pf pa LB0 FRS (LBall ++ LM)) W ->
bytes_at asegs m' (pf_sb pf) payload.
Proof.
intros pf pa LB0 LBall LM FR FRS B A m m' md lo W payload STC HP Hincl HinclF STR PLEN SBin MU HW.
destruct SBin as [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. destruct STR as (S1 & S2 & _). split; [exact S1|]. split; [exact S2|]. intros i Hi. cbn in Hi. lia.
- eapply bytes_at_transport; [exact STR | exact MU |]. rewrite PLEN. eapply payload_disjointA; [exact STC | exact HP | exact Hincl | exact HinclF | exact PL | exact HW].
Qed.

Lemma payload_crangeA : forall pf pa LB0 FRS m LB SP off n,
payload_locA pf pa LB0 FRS m -> incl LB0 LB -> incl (fr_ivs A4L FRS) LB -> SP <= pa_sp0 pa ->
0 <= off -> 0 <= n -> off + n <= pf_len pf ->
client_range A4H LB SP (pf_sb pf + off) n.
Proof.
intros pf pa LB0 FRS m LB SP off n [(b & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)] Hincl HinclF HSP Hoff Hn Hle.
- right; right. exists b. split; [exact (Hincl _ Hb) | lia].
- right; right. exists (Fh, fr_size kh - 8). split; [apply HinclF; unfold fr_ivs; apply in_flat_map; exists (Fh, kh); split; [exact HFh | left; reflexivity] | cbn [blk_addr blk_size fst snd]; lia].
Qed.
Lemma payload_crangexA : forall X pf pa LB0 FRS m LB SP off n,
payload_locA pf pa LB0 FRS m -> incl LB0 LB -> incl (fr_ivs A4L FRS) LB -> SP <= pa_sp0 pa ->
0 <= off -> 0 <= n -> off + n <= pf_len pf ->
client_rangex A4H X LB SP (pf_sb pf + off) n.
Proof.
intros X pf pa LB0 FRS m LB SP off n [(b & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & _)] Hincl HinclF HSP Hoff Hn Hle.
- right; right. exists b. split; [exact (Hincl _ Hb) | lia].
- right; right. exists (Fh, fr_size kh - 8). split; [apply HinclF; unfold fr_ivs; apply in_flat_map; exists (Fh, kh); split; [exact HFh | left; reflexivity] | cbn [blk_addr blk_size fst snd]; lia].
Qed.

Lemma payload_presA : forall pf pa LB0 FRS LBc SP m m' payload,
heap_pres A4H LBc SP m m' -> incl LB0 LBc -> incl (fr_ivs A4L FRS) LBc -> SP <= pa_sp0 pa ->
bytes_at asegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) ->
bytes_at asegs m' (pf_sb pf) payload.
Proof.
intros pf pa LB0 FRS LBc SP m m' payload HPR Hincl HinclF HSP STR PLEN [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. destruct STR as (S1 & S2 & _). split; [exact S1|]. split; [exact S2|]. intros i Hi. cbn in Hi. lia.
- eapply (heap_pres_bytes_at A4H); [exact HPR | exact STR |]. rewrite PLEN. replace (pf_sb pf) with (pf_sb pf + 0) by lia.
eapply payload_crangeA; [exact PL | exact Hincl | exact HinclF | exact HSP | lia | lia | lia].
Qed.
Lemma payload_presxA : forall X pf pa LB0 FRS LBc SP m m' payload,
heap_presx A4H X LBc SP m m' -> incl LB0 LBc -> incl (fr_ivs A4L FRS) LBc -> SP <= pa_sp0 pa ->
bytes_at asegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) ->
bytes_at asegs m' (pf_sb pf) payload.
Proof.
intros X pf pa LB0 FRS LBc SP m m' payload HPR Hincl HinclF HSP STR PLEN [L0 | PL].
- destruct payload; [| cbn in PLEN; lia]. destruct STR as (S1 & S2 & _). split; [exact S1|]. split; [exact S2|]. intros i Hi. cbn in Hi. lia.
- eapply (heap_presx_bytes_at A4H); [exact HPR | exact STR |]. rewrite PLEN. replace (pf_sb pf) with (pf_sb pf + 0) by lia.
eapply payload_crangexA; [exact PL | exact Hincl | exact HinclF | exact HSP | lia | lia | lia].
Qed.

Lemma payload_locA_pres : forall pf pa LB0 FRS A LB LM FR B m0 md LBX SP m m',
HEAPA A4L HIx A LB LM FR B m0 md -> incl FRS FR ->
heap_pres A4H (LBX ++ LM ++ fr_ivs A4L FR) SP m m' ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) -> (pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m').
Proof.
intros pf pa LB0 FRS A LB LM FR B m0 md LBX SP m m' HP HinclF HPR [L0 | PL]; [left; exact L0 | right].
destruct PL as [BL | (Fh & kh & HFh & HF1 & HF2 & UPS)]; [left; exact BL | right].
exists Fh, kh. split; [exact HFh|]. split; [exact HF1|]. split; [exact HF2|].
eapply (unpoisoned_pres_frame HIx); [exact HP | exact (HinclF _ HFh) | exact HF1 | exact HF2 | exact UPS | exact HPR].
Qed.

Lemma private_in_blocksA : forall pf q LB0 LM ts a n,
In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> In (a, n) (pe_blocksA pf q LB0 ts ++ LM).
Proof.
intros pf q LB0 LM ts a n Hin. unfold pe_blocksA. apply in_or_app; left. apply in_app_or in Hin.
destruct Hin as [Hin | [E | [E | []]]]; [| injection E; intros <- <- | injection E; intros <- <-]; apply in_or_app;
[left; exact Hin | right; left; reflexivity | right; right; left; reflexivity].
Qed.
Lemma private_not_LB0A : forall pf q LB0 LM FRS B ts A m md a n k,
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM FRS B m md ->
In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> ~ In (a, k) LB0.
Proof.
intros pf q LB0 LM FRS B ts A m md a n k HP Hin Hk. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (ND' : List.NoDup (map blk_addr ((tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) ++ (LB0 ++ LM)))).
{ unfold pe_blocksA in ND. rewrite <- !app_assoc in *. cbn [app] in *. exact ND. }
exact (nodup_app_ne _ _ _ _ _ _ ND' Hin ltac:(apply in_or_app; left; exact Hk) eq_refl).
Qed.

Lemma own_frame_ne : forall LBall LM FRS B A m md F0 Fh kh,
HEAPA A4L HIx A LBall LM ((F0, 2) :: FRS) B m md -> In (Fh, kh) FRS -> Fh <> F0.
Proof.
intros LBall LM FRS B A m md F0 Fh kh HP HFh E. subst Fh.
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni _].
apply Hni. exact (in_map fr_base _ _ HFh).
Qed.

Lemma payload_privateA : forall pf pa q LB0 LM FRS B ts A m m' md lo W payload,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
bytes_at asegs m (pf_sb pf) payload -> Z.of_nat (length payload) = pf_len pf ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) ->
munch W m m' -> Forall (pe_privateA pf pa q (t_pbs ts)) W ->
bytes_at asegs m' (pf_sb pf) payload.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W payload STC HP STR PLEN SBin MU HW.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (_ & _ & Hspf & _ & HF0 & HFc & _). pose proof alloc_ceiling_range.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
eapply payload_transportA; [exact STC | exact HP | intros x Hx; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hx
| apply incl_tl; apply incl_refl | exact STR | exact PLEN | exact SBin | exact MU |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. unfold payload_safeA. cbn [fst snd] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
- right; left. exists (pf_tk pf), 72.
assert (Hin : In (pf_tk pf, 72) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)])) by (apply in_or_app; right; left; reflexivity).
split; [exact (private_in_blocksA _ _ _ _ _ _ _ Hin) | split; [intros kk; exact (private_not_LB0A _ _ _ _ _ _ _ _ _ _ _ _ kk HP Hin) | lia]].
- right; left. exists q, (32 * pf_mxd pf).
assert (Hin : In (q, 32 * pf_mxd pf) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)])) by (apply in_or_app; right; right; left; reflexivity).
split; [exact (private_in_blocksA _ _ _ _ _ _ _ Hin) | split; [intros kk; exact (private_not_LB0A _ _ _ _ _ _ _ _ _ _ _ _ kk HP Hin) | lia]].
- right; left. exists b, k.
assert (Hin : In (b, k) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)])) by (apply in_or_app; left; unfold tstate_blocks; apply in_or_app; left; exact Hb).
split; [exact (private_in_blocksA _ _ _ _ _ _ _ Hin) | split; [intros kk; exact (private_not_LB0A _ _ _ _ _ _ _ _ _ _ _ _ kk HP Hin) | lia]].
- left. lia.
- right; right; right. split; [lia|]. split.
+ intros a n Ha.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Ha). unfold fr_size in *. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in *. lia.
+ intros Fh kh HFh.
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (or_intror HFh) (fun E => own_frame_ne _ _ _ _ _ _ _ _ _ _ HP HFh (eq_sym E))) as AP.
rewrite fr_size_2 in AP. lia.
- right; right; right. unfold shA, A_SB in *. split; [lia|]. split.
+ intros a n Ha.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Ha ltac:(lia) ltac:(lia) ltac:(lia)). unfold shA, A_SB in *. lia.
+ intros Fh kh HFh.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as AM. cbn [hl_sb A4L] in AM. unfold A_SB in AM.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (Hkh & _).
pose proof (fr_size_pos kh ltac:(lia)). Z.div_mod_to_equations. lia.
Qed.

Lemma payload_locA_private : forall pf pa q LB0 LM FRS B ts A m m' md lo W,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m) ->
munch W m m' -> Forall (pe_privateA pf pa q (t_pbs ts)) W ->
(pf_len pf = 0 \/ payload_locA pf pa LB0 FRS m').
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W STC HP [L0 | PL] MU HW; [left; exact L0 | right].
destruct PL as [BL | (Fh & kh & HFh & HF1 & HF2 & UPS)]; [left; exact BL | right].
exists Fh, kh. split; [exact HFh|]. split; [exact HF1|]. split; [exact HF2|].
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (_ & _ & Hspf & GF & HF0 & HFc & _). pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFh)) as (Hkh & HFhal & HFh0 & HFhc & _).
pose proof (fr_size_pos kh ltac:(lia)) as HFS. pose proof (fr_shadow_len_bnd kh Hkh) as HSK.
assert (HF64 : Fh mod 64 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kh)); [| apply Z.mod_divide; [lia | exact HFhal]].
exists (2 ^ kh). unfold fr_size. lia. }
pose proof UPS as (Hn & _).

assert (SPAN : forall a k, shadow_span_lo A_SB (pf_sb pf) <= a -> a + k <= shadow_span_hi A_SB (pf_sb pf) (pf_len pf) ->
shA Fh <= a /\ a + k <= shA Fh + fr_shadow_len kh).
{ intros a k Ha Hk. unfold shadow_span_lo, shadow_span_hi, shA, A_SB in *. rewrite (fr_size_shadow kh) in HF2 by lia.
clear - Ha Hk HF1 HF2 HF64 Hn HSK. unfold fr_shadow_len in *. Z.div_mod_to_equations. lia. }
eapply unpoisoned_transport; [exact UPS | exact MU |].
intros a k Ha Hk. destruct (SPAN a k Ha Hk) as [S1 S2]. clear SPAN Ha Hk MU.
induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 HW].
cbn [disjoint_from fst snd]. split; [| apply IH; exact HW].
unfold pe_privateA in H1. cbn [fst snd] in H1.
assert (BLK : forall b n, In (b, n) (pe_blocksA pf q LB0 ts ++ LM) -> b <= lo' -> hi' <= b + n -> a + k <= lo' \/ hi' <= a).
{ intros b n Hb Hlo Hhi. pose proof (shadow_blk_apart _ _ _ _ _ _ _ b n Fh (fr_shadow_len kh) HP Hb ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
destruct H1 as [H1 | [H1 | [(b & n & Hb & H1) | [H1 | [H1 | H1]]]]].
- eapply (BLK (pf_tk pf) 72); [unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity | lia | lia].
- eapply (BLK q (32 * pf_mxd pf)); [unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity | lia | lia].
- eapply (BLK b n); [unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb | lia | lia].
- unfold shA, A_SB in *. Z.div_mod_to_equations. lia.
- pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as AM. cbn [hl_sb A4L] in AM. rewrite fr_size_2 in AM. unfold shA, A_SB in *. Z.div_mod_to_equations. lia.
- pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (or_intror HFh) (fun E => own_frame_ne _ _ _ _ _ _ _ _ _ _ HP HFh (eq_sym E))) as AP.
rewrite fr_size_2 in AP. rewrite (fr_size_shadow kh) in AP by lia.
assert (HG8 : pa_F pa mod 8 = 0) by (clear - GF; Z.div_mod_to_equations; lia).
unfold shA, A_SB in *. clear - AP HF64 HG8 H1 S1 S2 HSK. Z.div_mod_to_equations. lia.
Qed.

Lemma in_fr_ivs : forall FR b, In b (fr_ivs A4L FR) -> exists F k, In (F, k) FR /\ (b = (F, fr_size k - 8) \/ b = (shad A4L F, fr_shadow_len k)).
Proof.
intros FR b H. unfold fr_ivs in H. apply in_flat_map in H as ([F k] & Hf & Hb). exists F, k. split; [exact Hf|].
cbn in Hb. destruct Hb as [<- | [<- | []]]; [left | right]; reflexivity.
Qed.
Lemma fr_ivs_frame : forall FR F k, In (F, k) FR -> In (F, fr_size k - 8) (fr_ivs A4L FR).
Proof. intros FR F k H. unfold fr_ivs. apply in_flat_map. exists (F, k). split; [exact H | left; reflexivity]. Qed.
Lemma fr_ivs_shadow : forall FR F k, In (F, k) FR -> In (shad A4L F, fr_shadow_len k) (fr_ivs A4L FR).
Proof. intros FR F k H. unfold fr_ivs. apply in_flat_map. exists (F, k). split; [exact H | right; left; reflexivity]. Qed.

Lemma client_outsideF : forall A LB LM FR B LB0 m md W SP,
HEAPA A4L HIx A LB LM FR B m md ->
(forall b, In b LB0 -> In b (LB ++ LM) \/ In b (fr_ivs A4L FR)) ->
alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LB ++ LM) /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) LB0 /\ ~ In (shad A4L F, fr_shadow_len k) LB0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W ->
forall a, 0 <= a < 2^64 -> client_addr A4H LB0 SP a -> outside W a.
Proof.
intros A LB LM FR B LB0 m md W SP HP Hsub HSP HW a Ha Hc. pose proof alloc_ceiling_range as ACR.
induction W as [|[lo hi] W IH]; cbn; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. split; [| apply IH; exact HW]. cbn in H1.
destruct Hc as [Hc | [Hc | (b & Hb0 & Hbr)]].
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | [Hsc | (F & k & HF & _ & _ & HFr)]]]; [lia| | |].
+ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
+ intros Hin. pose proof (hl_scratch_in_img A4L a (Hsc a Hin)). pose proof (hl_img_range A4L). lia.
+ pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _).
pose proof (fr_shadow_len_bnd k ltac:(lia)). pose proof (fr_size_pos k ltac:(lia)).
unfold shad in HFr. cbn [hl_sb hla_base A4L A4H] in HFr. unfold A_SB in HFr. intros Hin.
pose proof (fr_size_pos k ltac:(lia)) as Hfs.
destruct HFr as [HFr|HFr]; [lia | Z.div_mod_to_equations; lia].
- destruct H1 as [H1 | [(b & n & Hb & Hnb & Hlo & Hhi) | [Hsc | (F & k & HF & _ & _ & HFr)]]].
+ intros Hin. pose proof (hl_static_in_img A4L a Hc). pose proof (hl_img_range A4L). lia.
+ intros Hin. destruct (in_block_factsA _ _ _ _ _ _ _ _ _ _ _ a HP Hb ltac:(lia)) as (_ & Hns & _). exact (Hns Hc).
+ intros Hin. exact (hl_scratch_not_static A4L a (Hsc a Hin) Hc).
+ intros Hin. pose proof (hl_static_in_img A4L a Hc) as Hai. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hai.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & HFimg & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
destruct HFr as [HFr | HFr]; [lia|].
assert (HI : 0 <= a - shad A4L F < fr_shadow_len k) by lia.
pose proof (heapA_frame_shadow_sep A4L HIx _ _ _ _ _ _ _ _ _ (a - shad A4L F) HP HF HI) as [Hnc' Himg].
replace (shad A4L F + (a - shad A4L F)) with a in Himg by lia. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg. lia.
- destruct b as [ba bn]. cbn in Hbr. destruct (Hsub _ Hb0) as [Hb | Hfr].
+ destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | [Hsc | (F & k & HF & _ & _ & HFr)]]].
* pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (_ & _ & _ & Hbhi & _). lia.
* intros Hin. assert (Hne : b <> ba).
{ intros ->. apply Hnb. rewrite (nodup_addr_size (LB ++ LM) ba n bn (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) Hb' Hb). exact Hb0. }
destruct (in_block_factsA _ _ _ _ _ _ _ _ _ _ _ a HP Hb' ltac:(lia)) as (_ & _ & Hdis).
exact (Hdis ba bn Hb ltac:(congruence) ltac:(lia)).
* intros Hin. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP Hb) as Himg.
pose proof (hl_scratch_in_img A4L a (Hsc a Hin)). lia.
* intros Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hb) as (Hn0 & _ & Hb0' & Hbhi & _).
destruct HFr as [HFr | HFr].
-- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF Hb). lia.
-- pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk & _ & HF0 & HFc & _).
pose proof (fr_shadow_len_bnd k ltac:(lia)) as HSK. pose proof (fr_size_pos k ltac:(lia)) as HFS.
assert (HF0' : 0 <= F) by lia. assert (HFc' : F < alloc_ceiling) by lia. assert (HSK' : 0 <= fr_shadow_len k <= 2^20) by lia.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ F (fr_shadow_len k) HP Hb HF0' HFc' HSK') as D. unfold shad, shA in *. cbn [hl_sb hla_base A4L A4H] in *. unfold A_SB in *. lia.
+ apply in_fr_ivs in Hfr as (G & kg & HG & [E | E]); injection E as -> ->.
*
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & HGc & HGimg & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HGimg.
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | [Hsc | (F & k & HF & HnF & HnS & HFr)]]].
-- lia.
-- intros Hin. pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HG Hb'). lia.
-- intros Hin. pose proof (hl_scratch_in_img A4L a (Hsc a Hin)) as Hai. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hai. lia.
-- intros Hin. destruct (Z.eq_dec F G) as [-> | Hne].
++ destruct HFr as [HFr | HFr].
** exfalso. apply HnF. rewrite (frame_class_unique _ _ _ _ _ _ _ _ _ _ HP HF HG). exact Hb0.
** exfalso. pose proof (frame_class_unique _ _ _ _ _ _ _ _ _ _ HP HF HG) as ->.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as AM. unfold shad in HFr. cbn [hl_sb hla_base A4L A4H] in *. unfold A_SB in *.
pose proof (fr_shadow_len_bnd kg ltac:(lia)).
Z.div_mod_to_equations. lia.
++ destruct HFr as [HFr | HFr].
** pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF HG Hne). lia.
** pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as AM. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk' & _ & HF0 & HFc & _).
unfold shad in HFr. cbn [hl_sb hla_base A4L A4H] in *. unfold A_SB in *.
pose proof (fr_shadow_len_bnd k ltac:(lia)). pose proof (fr_size_pos k ltac:(lia)).
pose proof (fr_size_pos kg ltac:(lia)).
Z.div_mod_to_equations. lia.
*
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (Hkg & _ & HG0 & HGc & HGimg & _).
pose proof (fr_shadow_len_bnd kg ltac:(lia)) as HSG. pose proof (fr_size_pos kg ltac:(lia)) as HGS.
assert (HI : 0 <= a - shad A4L G < fr_shadow_len kg) by lia.
pose proof (heapA_frame_shadow_sep A4L HIx _ _ _ _ _ _ _ _ _ (a - shad A4L G) HP HG HI) as [Hnc Himg].
replace (shad A4L G + (a - shad A4L G)) with a in Hnc, Himg by lia. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg.
destruct H1 as [H1 | [(b & n & Hb' & Hnb & Hlo & Hhi) | [Hsc | (F & k & HF & HnF & HnS & HFr)]]].
-- intros Hin. apply Hnc. left. lia.
-- intros Hin. apply Hnc. right. right. exists (b, n). split; [exact Hb' | cbn; lia].
-- intros Hin. pose proof (hl_scratch_in_img A4L a (Hsc a Hin)) as Hai. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hai. lia.
-- intros Hin. destruct (Z.eq_dec F G) as [-> | Hne].
++ destruct HFr as [HFr | HFr].
** exfalso. pose proof (frame_class_unique _ _ _ _ _ _ _ _ _ _ HP HF HG) as ->.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as AM. unfold shad in *. cbn [hl_sb hla_base A4L A4H] in *. unfold A_SB in *.
Z.div_mod_to_equations. lia.
** exfalso. apply HnS. rewrite (frame_class_unique _ _ _ _ _ _ _ _ _ _ HP HF HG). exact Hb0.
++ pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as (Hk' & HFal & HF0 & HFc & _).
destruct HFr as [HFr | HFr].
** pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HF) as AM. unfold shad in *. cbn [hl_sb hla_base A4L A4H] in *. unfold A_SB in *.
pose proof (fr_size_pos k ltac:(lia)).
Z.div_mod_to_equations. lia.
**
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP HF HG Hne) as AP.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HG) as (_ & HGal & _).
pose proof (fr_shadow_len_bnd k ltac:(lia)) as HSK. pose proof (fr_size_pos k ltac:(lia)) as HFS.
assert (HF8 : F mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size k)); [| apply Z.mod_divide; [lia | exact HFal]].
exists (fr_shadow_len k). rewrite (fr_size_shadow k) by lia. lia. }
assert (HG8 : G mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kg)); [| apply Z.mod_divide; [lia | exact HGal]].
exists (fr_shadow_len kg). rewrite (fr_size_shadow kg) by lia. lia. }
rewrite (fr_size_shadow k) in AP by lia. rewrite (fr_size_shadow kg) in AP by lia.
unfold shad in *. cbn [hl_sb hla_base A4L A4H] in *. unfold A_SB in *.
clear - AP HF8 HG8 HI HFr Hin HSK HSG.
Z.div_mod_to_equations. lia.
Qed.

Lemma own_frame_fresh : forall pf pa q LB0 LM FRS B ts A m md,
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
~ In (pa_F pa, fr_size 2 - 8) (LB0 ++ LM ++ fr_ivs A4L FRS) /\ ~ In (shad A4L (pa_F pa), fr_shadow_len 2) (LB0 ++ LM ++ fr_ivs A4L FRS).
Proof.
intros pf pa q LB0 LM FRS B ts A m md HP.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP)) as ND. cbn in ND. apply List.NoDup_cons_iff in ND as [Hni ND].
assert (SUB : forall b, In b (LB0 ++ LM) -> In b (pe_blocksA pf q LB0 ts ++ LM)).
{ intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | right; exact Hb]. }
split; intros Hin; rewrite app_assoc in Hin; apply in_app_or in Hin as [Hin | Hin].
- exact (blk_not_fr_iv _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_frame _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG _. apply Hni. cbn [fr_base fst]. rewrite EG. exact (in_map fr_base _ _ HG).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
pose proof (fr_shadow_len_bnd kg Hkg). unfold fr_size in EK. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in EK. lia.
- exact (blk_not_fr_iv _ _ _ _ _ _ _ _ _ HP (SUB _ Hin) (fr_ivs_shadow _ _ _ INF)).
- apply in_fr_ivs in Hin as (G & kg & HG & [E|E]).
+ injection E as EG EK. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & _).
rewrite (fr_size_shadow kg) in EK by lia. pose proof (fr_shadow_len_bnd kg Hkg).
unfold fr_shadow_len at 1 in EK. cbn [Z.pow Z.pow_pos Pos.iter Z.mul] in EK.
assert (8 <= fr_shadow_len kg) by (unfold fr_shadow_len; pose proof (Z.pow_pos_nonneg 2 kg); lia). lia.
+ injection E as EG _. pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(right; exact HG)) as (Hkg & HGal & HG0 & _).
assert (HF8 : pa_F pa mod 8 = 0) by (unfold fr_size in HFal; cbn in HFal; Z.div_mod_to_equations; lia).
assert (HG8 : G mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (fr_size kg)); [| apply Z.mod_divide; [pose proof (fr_size_pos kg); lia | exact HGal]].
exists (fr_shadow_len kg). rewrite (fr_size_shadow kg) by lia. lia. }
apply Hni. replace (pa_F pa) with G; [exact (in_map fr_base _ _ HG)|]. unfold shad in EG. Z.div_mod_to_equations. lia.
Qed.

Lemma PE_REST_A_private_write : forall pf pa q LB0 LM FRS payload me lo m m' md A B ts errv W,
PE_STATIC_A pf pa lo ->
PE_REST_A pf pa q LB0 LM FRS payload me lo m md A B ts errv ->
munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
Forall (pe_privateA pf pa q (t_pbs ts)) W ->
PE_REST_A pf pa q LB0 LM FRS payload me lo m' md A B ts errv.
Proof.
intros pf pa q LB0 LM FRS payload me lo m m' md A B ts errv W STC (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & G & BUD) MU WM MI HW.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN & SB0 & SBL & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_hi A4L HIx) as HTH.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as (_ & _ & _ & Htkhi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INq) as (_ & _ & _ & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INtk) as Himg_t. pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INq) as Himg_q.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t, Himg_q, HFimg. rewrite fr_size_2 in HFimg.
pose proof (own_frame_fresh _ _ _ _ _ _ _ _ _ _ _ HP) as [OFF OFS].

assert (AG : agree_on asegs (t_objbs ts ++ concat (map lvl_blocks (t_levels ts))) m m').
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin.
assert (HinP : In (a, n) (tstate_blocks ts)) by (unfold tstate_blocks; apply in_or_app; right; exact Hin).
assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; left; exact HinP).
unfold pe_blocksA in ND.
eapply private_disjointA; [exact STC | exact HP | exact HinL | | | | exact HW].
- rewrite <- app_assoc in ND. eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). left; reflexivity.
- rewrite <- app_assoc in ND. eapply (nodup_app_ne _ _ _ _ _ _ ND HinP). right; left; reflexivity.
- intros b k Hb. unfold tstate_blocks in ND. rewrite <- app_assoc in ND. exact (nd_pbs_ne _ _ _ _ _ _ _ _ ND Hb Hin). }

assert (HWF : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hiA_top A4L HIx)
\/ (exists a n, In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) ((pa_F pa, 2) :: FRS) /\ ((F <= fst iv /\ snd iv <= F + fr_size k - 8)
\/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
- right; left. exists (pf_tk pf), 72. split; [exact INtk | lia].
- right; left. exists q, (32 * pf_mxd pf). split; [exact INq | lia].
- right; left. exists b, k. split; [| lia]. unfold pe_blocksA, tstate_blocks. apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb.
- left. lia.
- right; right; right. exists (pa_F pa), 2. split; [exact INF|]. left. rewrite fr_size_2. lia.
- right; right; right. exists (pa_F pa), 2. split; [exact INF|]. right. unfold shad, shA in H1 |- *. cbn [hl_sb hla_base A4L A4H]; rewrite ?fr_size_2, ?fr_shadow_len_2. unfold A_SB in H1 |- *. lia. }
assert (HIMG : Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H] in *.
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; [lia | lia | | lia | lia |].
- pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b k HP ltac:(unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb)) as Hbi.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi. lia.
- unfold shA in H1. unfold A_SB in H1. pose proof (Z.div_pos (pa_F pa) 8 ltac:(lia) ltac:(lia)). lia. }
split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [exact MDV | split; [exact (GA_outside _ _ _ G MU WM HIMG) | exact BUD]]]]]]]]]]].
- eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx); [exact HP | exact MU | exact HWF].
- intros i l Hl. eapply (lvl_cur_agree asegs A4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. apply in_or_app; right. apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In; exact Hl.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ].
eapply (jopt_agree asegs A4F); [exact OBJ | exact AG | intros b Hb; apply in_or_app; left; exact Hb].
- eapply (stk_transport_disjoint asegs); [exact ST | exact MU | exact WM |].
destruct ST as (ST0 & ST1 & _).
clear - HW LOS LO ST0 ST1 Htkhi Hqhi HP Gle GFc ACR. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_privateA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; try lia.
+ assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as (_ & _ & _ & Hbhi & _). lia.
+ unfold shA, A_SB in H1. Z.div_mod_to_equations. lia.
- eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat]. unfold A_ERRNO, A_TP.
clear - HW LOS LO Himg_t Himg_q Htkhi Hqhi HP SP0 HFimg Gle GFc GF0 ACR. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_privateA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]]; try lia.
+ assert (INb : In (b, k) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INb) as (Hk0 & _ & _ & _ & _). lia.
+ unfold shA, A_SB in H1. Z.div_mod_to_equations. lia.
- eapply payload_privateA; [exact STC | exact HP | exact STR | exact PLEN | exact SBin | exact MU | exact HW].
- exact PLEN.
- eapply payload_locA_private; [exact STC | exact HP | exact SBin | exact MU | exact HW].
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch A4H a4_volatile); [exact MU | exact WM |].
eapply client_outsideF; [exact HP | | lia |].
{ intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb].
- left. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; unfold pe_blocksA; apply in_or_app; right; right; right; exact Hb | right; exact Hb].
- right. unfold fr_ivs in *. cbn [flat_map]. apply in_or_app; right. exact Hb. }
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold pe_privateA in Hiv. cbn [fst snd] in *.
assert (NB : forall a n, In (a, n) (tstate_blocks ts ++ [(pf_tk pf, 72); (q, 32 * pf_mxd pf)]) -> ~ In (a, n) (LB0 ++ LM ++ fr_ivs A4L FRS)).
{ intros a n Ha Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_app_or in Hin as [Hin | Hin]; [exact (private_not_LB0A _ _ _ _ _ _ _ _ _ _ _ _ n HP Ha Hin)|].
assert (HaX : In (a, n) (pe_blocksA pf q LB0 ts)).
{ unfold pe_blocksA. apply in_app_or in Ha. apply in_or_app. destruct Ha as [Ha | [Ha | [Ha | []]]]; [left; exact Ha | right; left; exact Ha | right; right; left; exact Ha]. }
exact (nodup_app_ne _ _ _ _ _ _ ND HaX Hin eq_refl).
- exact (blk_not_fr_iv _ _ _ _ _ _ _ _ _ HP (private_in_blocksA _ _ _ LM _ _ _ Ha) ltac:(unfold fr_ivs in *; cbn [flat_map]; apply in_or_app; right; exact Hin)). }
destruct Hiv as [H1 | [H1 | [(b & k & Hb & H1) | [H1 | [H1 | H1]]]]].
+ right; left. exists (pf_tk pf), 72. split; [exact INtk|]. split; [| lia]. apply NB. apply in_or_app; right; left; reflexivity.
+ right; left. exists q, (32 * pf_mxd pf). split; [exact INq|]. split; [| lia]. apply NB. apply in_or_app; right; right; left; reflexivity.
+ right; left. exists b, k. split; [unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hb|]. split; [| lia].
apply NB. apply in_or_app; left. unfold tstate_blocks; apply in_or_app; left; exact Hb.
+ left. lia.
+ right; right; right. exists (pa_F pa), 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. rewrite fr_size_2. lia.
+ right; right; right. exists (pa_F pa), 2. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right.
unfold shad, shA in H1 |- *. cbn [hl_sb hla_base A4L A4H]; rewrite ?fr_size_2, ?fr_shadow_len_2. unfold A_SB in H1 |- *. lia.
Qed.

Lemma disjoint_from_blocks : forall A LB LM FR B m md W a0 n0,
HEAPA A4L HIx A LB LM FR B m md ->
Forall (fun iv => exists a n, In (a, n) (LB ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
(forall a n, In (a, n) (LB ++ LM) -> a + n <= a0 \/ a0 + n0 <= a) ->
disjoint_from W a0 n0.
Proof.
intros A LB LM FR B m md W a0 n0 HP HW Hap. induction W as [|[lo hi] W IH]; [exact I|].
apply Forall_cons_iff in HW as [(a & n & Hin & Hlo & Hhi) HW]. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
pose proof (Hap a n Hin). lia.
Qed.

Lemma pe_frameA_blkwriteG : forall pf pa (LBX : list blk) LM FRS B A m m' md lo W cb nb pj sv,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A LBX LM ((pa_F pa, 2) :: FRS) B m md ->
Forall (fun iv => exists a n, In (a, n) (LBX ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
pe_frameA asegs m pf pa cb nb pj sv -> munch W m m' -> wmono asegs m m' ->
pe_frameA asegs m' pf pa cb nb pj sv.
Proof.
intros pf pa LBX LM FRS B A m m' md lo W cb nb pj sv STC HP HW (SL & GP & SV & FF & FSH) MU WM.
pose proof STC as (LO & LOS & GEO & HT & SP0 & _). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk). pose proof alloc_ceiling_range.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
assert (BLO : forall a n, In (a, n) (LBX ++ LM) -> 0 <= n /\ a + n <= alloc_ceiling).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as (Hn & _ & _ & Hhi & _). lia. }
pose proof SL as [[Hwf _] _].
split; [| split; [| split; [| split]]].
- eapply rw_cells_transport; [exact SL | exact MU | exact WM |]. rewrite pe_slotsA_size.
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- eapply rw_cells_transport; [exact GP | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- eapply rw_cells_transport; [exact SV | exact MU | exact WM |]. cbn [cells_size csize Nat.add pe_savedA_cells].
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin; destruct (BLO a n Hin); lia].
- eapply rw_cells_transport; [exact FF | exact MU | exact WM |]. cbn [cells_size csize Nat.add ff_cellsA].
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin].
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin). rewrite fr_size_2 in *. lia.
- eapply rw_cells_transport; [exact FSH | exact MU | exact WM |]. unfold ffsh_cells, FSH0. cbn [cells_size csize Nat.add map length].
eapply disjoint_from_blocks; [exact HP | exact HW | intros a n Hin].
assert (HF0' : 0 <= pa_F pa) by lia. assert (HFc' : pa_F pa < alloc_ceiling) by lia.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin HF0' HFc' ltac:(lia)) as DD. unfold shA in DD |- *. lia.
Qed.

Lemma pe_frameA_blkwrite : forall pf pa q LB0 LM FRS B ts A m m' md lo W cb nb pj sv,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
Forall (fun iv => exists a n, In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <= fst iv /\ snd iv <= a + n) W ->
pe_frameA asegs m pf pa cb nb pj sv -> munch W m m' -> wmono asegs m m' ->
pe_frameA asegs m' pf pa cb nb pj sv.
Proof. intros. eapply pe_frameA_blkwriteG; eassumption. Qed.

Lemma pe_frameA_pres : forall pf pa (L : list blk) SP me m cb nb pj sv,
heap_pres A4H L SP me m -> SP <= pf_spf pf -> pe_geomA pf pa ->
In (pa_F pa, 248) L -> In (shA (pa_F pa), 32) L ->
pe_frameA asegs me pf pa cb nb pj sv -> pe_frameA asegs m pf pa cb nb pj sv.
Proof.
intros pf pa L SP me m cb nb pj sv HPR HSP GEO InF InS (SL & GP & SV & FF & FSH).
pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
split; [| split; [| split; [| split]]].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SL | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact GP | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact SV | left; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FF | right; right]. exists (pa_F pa, 248). split; [exact InF | cbn; lia].
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact FSH | right; right]. exists (shA (pa_F pa), 32). split; [exact InS | cbn; lia].
Qed.

Definition pe_wtfA (pf : pe_fix) (pa : pe_fixA) (iv : Z * Z) : Prop :=
(pf_tk pf <= fst iv /\ snd iv <= pf_tk pf + 72) \/ (pf_spf pf <= fst iv /\ snd iv <= pa_sp0 pa) \/
(pa_F pa <= fst iv /\ snd iv <= pa_F pa + 248) \/ (shA (pa_F pa) <= fst iv /\ snd iv <= shA (pa_F pa) + 32).

Lemma pe_wtfA_private : forall pf pa q pbs W, Forall (pe_wtfA pf pa) W -> Forall (pe_privateA pf pa q pbs) W.
Proof.
intros pf pa q pbs W H. eapply Forall_impl; [| exact H]. unfold pe_wtfA, pe_privateA.
intros iv [X|[X|[X|X]]]; tauto.
Qed.

Lemma agree_wtfA : forall pf pa q LB0 LM FRS B ts A m m' md lo W BS,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
munch W m m' -> wmono asegs m m' -> Forall (pe_wtfA pf pa) W ->
(forall a n, In (a, n) BS -> In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <> pf_tk pf) ->
agree_on asegs BS m m'.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W BS STC HP MU WM HW HBS.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (_ & _ & Hspf & _ & HF0 & HFc & _). pose proof alloc_ceiling_range.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. destruct (HBS a n Hin) as [HinL Hne].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP HinL) as (Hn & _ & _ & Hhi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n _ _ HP HinL INtk Hne) as Hd.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF HinL) as HdF. rewrite fr_size_2 in HdF.
assert (HF0' : 0 <= pa_F pa) by lia. assert (HFc' : pa_F pa < alloc_ceiling) by lia.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP HinL HF0' HFc' ltac:(lia)) as HdS.
clear - HW Hd HdF HdS Hhi LO LOS Hspf. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_wtfA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
lia.
Qed.

Lemma q_ne_tkA : forall pf q LB0 LM FRS B ts A m md,
HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM FRS B m md -> q <> pf_tk pf.
Proof.
intros pf q LB0 LM FRS B ts A m md HP.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc, map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst app] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. exact E.
Qed.

Lemma tstack_wtfA : forall pf pa q LB0 LM FRS B ts A m m' md lo W,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
tstack asegs m q (t_levels ts) -> length (t_levels ts) = Z.to_nat (pf_mxd pf) ->
munch W m m' -> wmono asegs m m' -> Forall (pe_wtfA pf pa) W ->
tstack asegs m' q (t_levels ts).
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W STC HP TSK LEN MU WM HW.
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
pose proof (q_ne_tkA _ _ _ _ _ _ _ _ _ _ HP) as Hq.
pose proof (agree_wtfA pf pa q LB0 LM FRS B ts A m m' md lo W [(q, 32 * pf_mxd pf)] STC HP MU WM HW ltac:(intros a n [E|[]]; injection E as <- <-; split; [exact INq | exact Hq])) as AG.
intros j l Hl. pose proof (nth_error_Some_length Hl) as Hj.
eapply rw_cells_agree; [exact (TSK j l Hl) | exact AG |]. exists q, (32 * pf_mxd pf). split; [left; reflexivity|]. rewrite srec_cells_size. cbn [Z.of_nat]. lia.
Qed.

Lemma pbuf_wtfA : forall pf pa q LB0 LM FRS B ts A m m' md lo W,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
pbuf asegs m (t_pbs ts) (t_pb ts) ->
munch W m m' -> wmono asegs m m' -> Forall (pe_wtfA pf pa) W ->
pbuf asegs m' (t_pbs ts) (t_pb ts).
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W STC HP PB MU WM HW.
eapply pbuf_agree; [exact PB | | apply incl_refl].
eapply agree_wtfA; [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND.
intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
Qed.

Definition pe_wtqA (pf : pe_fix) (pa : pe_fixA) (q : Z) (iv : Z * Z) : Prop :=
pe_wtfA pf pa iv \/ (q <= fst iv /\ snd iv <= q + 32 * pf_mxd pf).

Lemma pe_wtqA_private : forall pf pa q pbs W, Forall (pe_wtqA pf pa q) W -> Forall (pe_privateA pf pa q pbs) W.
Proof.
intros pf pa q pbs W H. eapply Forall_impl; [| exact H]. unfold pe_wtqA, pe_wtfA, pe_privateA. intros iv X; tauto.
Qed.
Lemma pe_wtfA_wtqA : forall pf pa q W, Forall (pe_wtfA pf pa) W -> Forall (pe_wtqA pf pa q) W.
Proof. intros pf pa q W H. eapply Forall_impl; [| exact H]. intros iv X. left; exact X. Qed.

Lemma agree_wtqA : forall pf pa q LB0 LM FRS B ts A m m' md lo W BS,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
munch W m m' -> wmono asegs m m' -> Forall (pe_wtqA pf pa q) W ->
(forall a n, In (a, n) BS -> In (a, n) (pe_blocksA pf q LB0 ts ++ LM) /\ a <> pf_tk pf /\ a <> q) ->
agree_on asegs BS m m'.
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W BS STC HP MU WM HW HBS.
pose proof STC as (LO & LOS & GEO & _). pose proof GEO as (_ & _ & Hspf & _ & HF0 & HFc & _). pose proof alloc_ceiling_range.
assert (INtk : In (pf_tk pf, 72) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, 32 * pf_mxd pf) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA; apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
eapply agree_of_munch; [exact MU | exact WM |]. intros a n Hin. destruct (HBS a n Hin) as (HinL & Hne & Hnq).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP HinL) as (Hn & _ & _ & Hhi & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n _ _ HP HinL INtk Hne) as Hd.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a n _ _ HP HinL INq Hnq) as Hdq.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF HinL) as HdF. rewrite fr_size_2 in HdF.
assert (HF0' : 0 <= pa_F pa) by lia. assert (HFc' : pa_F pa < alloc_ceiling) by lia.
pose proof (shadow_blk_apart _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP HinL HF0' HFc' ltac:(lia)) as HdS.
clear - HW Hd Hdq HdF HdS Hhi LO LOS Hspf. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. unfold pe_wtqA, pe_wtfA in H1. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
lia.
Qed.

Lemma pbuf_wtqA : forall pf pa q LB0 LM FRS B ts A m m' md lo W,
PE_STATIC_A pf pa lo -> HEAPA A4L HIx A (pe_blocksA pf q LB0 ts) LM ((pa_F pa, 2) :: FRS) B m md ->
pbuf asegs m (t_pbs ts) (t_pb ts) ->
munch W m m' -> wmono asegs m m' -> Forall (pe_wtqA pf pa q) W ->
pbuf asegs m' (t_pbs ts) (t_pb ts).
Proof.
intros pf pa q LB0 LM FRS B ts A m m' md lo W STC HP PB MU WM HW.
eapply pbuf_agree; [exact PB | | apply incl_refl].
eapply agree_wtqA; [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocksA pf q LB0 ts ++ LM)) by (unfold pe_blocksA, tstate_blocks; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. unfold pe_blocksA in ND. rewrite <- app_assoc in ND. split.
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
- intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | right; left; reflexivity].
Qed.
End Inv.

Lemma tok_flags_byteA : forall mxd fl m tk pb d q x,
rw_cells asegs m tk (tok_cells_g mxd fl pb d q x) ->
ov_read_bytes asegs m (Z_to_bv 64 (tk + 64)) 1 = Some [Z_to_bv 8 fl].
Proof.
intros mxd fl m tk pb d q x H.
pose proof (bytes_at_read asegs m tk _ 64 1 (rw_cells_bytes_at' _ _ _ _ H) ltac:(lia)) as R.
unfold tok_cells_g in R. cbn [cells_bytes cbytes app length le8 le4 word_to_le_bytes Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add skipn firstn repeat] in R.
specialize (R ltac:(cbn; lia)). change (Z.to_nat 64) with 64%nat in R. cbn [skipn firstn] in R. etransitivity; [exact R|].
f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. symmetry.
apply Znumtheory.Zmod_div_mod; [reflexivity | reflexivity | exists (2^56); reflexivity].
Qed.

Lemma payload_byteA : forall m sb payload co c,
bytes_at asegs m sb payload -> nth_error payload (Z.to_nat co) = Some c -> 0 <= co ->
ov_read_bytes asegs m (Z_to_bv 64 (sb + co)) 1 = Some [c].
Proof.
intros m sb payload co c B Hn Hco.
pose proof (nth_error_Some_length Hn) as L.
pose proof (bytes_at_read asegs m sb payload co 1 B Hco ltac:(lia)) as R.
replace (firstn 1 (skipn (Z.to_nat co) payload)) with [c] in R; [exact R|].
pose proof (@nth_error_split _ payload (Z.to_nat co) c Hn) as (l1 & l2 & E & Hl1). rewrite E at 1.
rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.
End RC__1.
