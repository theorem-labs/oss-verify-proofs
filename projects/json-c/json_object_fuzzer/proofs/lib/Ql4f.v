(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QCcH QfLs Q7UD Qhd4 Qwm6 QlKV Q1Ey Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QCcH QfLs.
Import Q7UD Qhd4 Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Lemma bytes_at_sub : forall segs m a (bs : list byte) (k n : nat),
bytes_at segs m a bs -> (k + n <= length bs)%nat -> bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
intros segs m a bs k n (H0 & H1 & H2) Hl.
assert (L : length (firstn n (skipn k bs)) = n) by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite (H2 (k + i)%nat) by lia.
rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [| lia]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma neq_wzA : forall x y, 0 <= x < 2^64 -> -2^64 <= y < 2^64 -> x <> y -> x <> y + 2^64 ->
bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y Hx Hy N1 N2. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small x) by lia.
destruct (Z.lt_ge_cases y 0).
- replace y with ((y + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Lemma bytes_at_pointwiseA : forall segs (m m' : word -> option byte) A bs,
bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) -> bytes_at segs m' A bs.
Proof.
intros segs m m' A bs (H0 & H1 & HB) E. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd. rewrite (E (A + Z.of_nat i)) by lia. reflexivity.
Qed.
Lemma rw_cells_pointwiseA : forall segs (m m' : word -> option byte) A cs,
rw_cells segs m A cs ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
rw_cells segs m' A cs.
Proof.
intros segs m m' A cs [[WF HB] (W0 & W1 & HW)] E. split; [split; [exact WF|]|].
- eapply bytes_at_pointwiseA; [exact HB|]. intros a Ha. rewrite cells_bytes_length in Ha by exact WF. apply (proj1 (E a ltac:(lia))).
- split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (E (A + i) ltac:(lia))). apply HW. exact Hi.
Qed.

Lemma bytes_at_skipn : forall segs m a (bs : list byte) (k : Z),
bytes_at segs m a bs -> 0 <= k <= Z.of_nat (length bs) -> bytes_at segs m (a + k) (skipn (Z.to_nat k) bs).
Proof.
intros segs m a bs k B Hk.
pose proof (bytes_at_sub segs m a bs (Z.to_nat k) (length bs - Z.to_nat k) B ltac:(lia)) as X.
rewrite Z2Nat.id in X by lia. rewrite firstn_all2 in X by (rewrite length_skipn; lia). exact X.
Qed.

Lemma unpoisoned_of_fshadow : forall m Fr (shb : list byte) (g0 g1 : nat),
bytes_at asegs m (Fr / 8 + A_SB) shb -> length shb = 32%nat -> Fr mod 256 = 0 -> 0 <= Fr ->
(g0 < g1)%nat -> (g1 <= 32)%nat ->
forallb (fun b => bv_unsigned b =? 0) (firstn (g1 - g0) (skipn g0 shb)) = true ->
unpoisoned asegs m A_SB (Fr + 8 * Z.of_nat g0) (8 * Z.of_nat (g1 - g0)).
Proof.
intros m Fr shb g0 g1 SH L AL F0 Hg Hg1 Z0.
assert (GZ : forall g : nat, (g0 <= g < g1)%nat -> bytes_at asegs m (Fr / 8 + A_SB + Z.of_nat g) [Z_to_bv 8 0]).
{ intros g Hgg. pose proof (bytes_at_sub asegs m _ shb g 1 SH ltac:(lia)) as X.
assert (E : firstn 1 (skipn g shb) = [Z_to_bv 8 0]); [| rewrite E in X; exact X].
rewrite forallb_forall in Z0.
destruct (nth_error shb g) as [b|] eqn:Hb; [| apply nth_error_None in Hb; lia].
assert (Hin : In b (firstn (g1 - g0) (skipn g0 shb))).
{ apply (nth_error_In _ (g - g0)). rewrite nth_error_firstn. destruct (Nat.ltb_spec (g - g0) (g1 - g0)); [| lia]. rewrite nth_error_skipn. replace (g0 + (g - g0))%nat with g by lia. exact Hb. }
specialize (Z0 b Hin). apply Z.eqb_eq in Z0.
pose proof (@nth_error_split _ shb g b Hb) as (l1 & l2 & E & Hl1). rewrite E. rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal. apply bv_eq. rewrite Z0. reflexivity. }
assert (E1 : (Fr + 8 * Z.of_nat g0) / 8 = Fr / 8 + Z.of_nat g0) by (Z.div_mod_to_equations; lia).
assert (E2 : (Fr + 8 * Z.of_nat g0 + 8 * Z.of_nat (g1 - g0) - 1) / 8 = Fr / 8 + Z.of_nat g1 - 1) by (Z.div_mod_to_equations; lia).
unfold unpoisoned. split; [lia|]. split; [| split].
- intros g Hgr. rewrite E1, E2 in Hgr. replace (g + A_SB) with (Fr / 8 + A_SB + Z.of_nat (Z.to_nat (g - Fr / 8))) by lia. apply GZ. lia.
- exists 0. split; [| left; reflexivity]. rewrite E2. replace (Fr / 8 + Z.of_nat g1 - 1 + A_SB) with (Fr / 8 + A_SB + Z.of_nat (g1 - 1)) by lia. apply GZ. lia.
- intros w Hw. rewrite E1, E2 in Hw.
assert (EW : exists j : nat, (j < 4)%nat /\ w * 8 = Fr / 8 + A_SB + Z.of_nat (8 * j)).
{ exists (Z.to_nat (w - (Fr / 8 + A_SB) / 8)). unfold A_SB in *. split; Z.div_mod_to_equations; lia. }
destruct EW as (j & Hj & ->). exists (firstn 8 (skipn (8 * j) shb)). split.
+ rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia].
+ apply bytes_at_sub; [exact SH | lia].
Qed.

Lemma land_even_1A : forall n, Z.land (2 * n) 1 = 0.
Proof. intros n. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma short_flag0A : forall n, 0 <= n <= 127 -> Z.land (bv_unsigned (zxb (Z_to_bv 8 (2 * n)))) 1 = 0.
Proof.
intros n Hn. unfold zxb. rewrite unsigned_lit.
2:{ pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (2 * n))) as R. unfold bv_modulus in R. cbn in R. lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2^8). rewrite Z.mod_small by lia.
apply land_even_1A.
Qed.
Lemma short_sizeA : forall n, 0 <= n <= 127 -> Z.shiftr (bv_unsigned (zxb (Z_to_bv 8 (2 * n)))) 1 = n.
Proof.
intros n Hn. unfold zxb. rewrite unsigned_lit.
2:{ pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (2 * n))) as R. unfold bv_modulus in R. cbn in R. lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2^8). rewrite Z.mod_small by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma unpoisoned_of_run : forall m (g0 : Z) (k : nat) s n,
bytes_at asegs m (g0 + A_SB) (repeat (Z_to_bv 8 0) k) -> 0 <= g0 -> 0 < n ->
g0 <= (s / 8) / 8 * 8 -> ((s + n - 1) / 8) / 8 * 8 + 8 <= g0 + Z.of_nat k ->
unpoisoned asegs m A_SB s n.
Proof.
intros m g0 k s n RUN G0 Hn Hlo Hhi.
assert (GZ : forall g, g0 <= g < g0 + Z.of_nat k -> bytes_at asegs m (g + A_SB) [Z_to_bv 8 0]).
{ intros g Hg. pose proof (bytes_at_sub asegs m _ _ (Z.to_nat (g - g0)) 1 RUN ltac:(rewrite repeat_length; lia)) as X.
replace (g0 + A_SB + Z.of_nat (Z.to_nat (g - g0))) with (g + A_SB) in X by lia.
assert (E : firstn 1 (skipn (Z.to_nat (g - g0)) (repeat (Z_to_bv 8 0) k)) = [Z_to_bv 8 0]); [| rewrite E in X; exact X].
assert (Hnth : nth_error (repeat (Z_to_bv 8 0) k) (Z.to_nat (g - g0)) = Some (Z_to_bv 8 0)) by (apply nth_error_repeat; lia).
pose proof (@nth_error_split _ _ _ _ Hnth) as (l1 & l2 & E & Hl1). rewrite E. rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. reflexivity. }
unfold unpoisoned. split; [exact Hn|]. split; [| split].
- intros g Hg. apply GZ. Z.div_mod_to_equations. lia.
- exists 0. split; [| left; reflexivity]. apply GZ. Z.div_mod_to_equations. lia.
- intros w Hw.
assert (EW : exists j : nat, (j + 8 <= k)%nat /\ w * 8 = g0 + A_SB + Z.of_nat j).
{ exists (Z.to_nat (w * 8 - (g0 + A_SB))). unfold A_SB in *. split; Z.div_mod_to_equations; lia. }
destruct EW as (j & Hj & ->). exists (firstn 8 (skipn j (repeat (Z_to_bv 8 0) k))). split.
+ rewrite firstn_length_le; [reflexivity | rewrite length_skipn, repeat_length; lia].
+ apply bytes_at_sub; [exact RUN | rewrite repeat_length; lia].
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma presx_ownA : forall (X : Z -> Prop) A LBall LM FR B m m' md W L0 SP,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W ->
heap_presx A4H X L0 SP m m'.
Proof.
intros X A LBall LM FR B m m' md W L0 SP HP MU WM Hsub HSP HW a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
exact (Q1Ey.client_outsideF HIx A LBall LM FR B L0 m md W SP HP Hsub HSP HW a Ha (client_addrx_addr A4H _ _ _ _ Hc)).
Qed.
End WithIface.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 Lib.GwApply QRjH QHnV Q0Ek Qtgi QjDH Qsw7 QJjn QRUw QkMG QG8z QsKa Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 Q1Ey.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma ro_C1_of_bytes_at : forall m a v, bytes_at asegs m a [Z_to_bv 8 v] -> ro_cells asegs m a [C1 (Z_to_bv 8 v)].
Proof. intros m a v H. split; [cbn; split; exact I | cbn; exact H]. Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small (v + 128) 256) by lia. lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma div8_add_mul32 : forall q d, q mod 8 = 0 -> 0 <= d -> (q + 32 * d) / 8 = q / 8 + 4 * d.
Proof. intros q d Hq Hd. Z.div_mod_to_equations. lia. Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma tok_shadowA : forall A LB LM FR B m md tk,
HEAPAx A LB LM FR B m md -> In (tk, 72) LB ->
ro_cells asegs m (tk / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md tk HP Hin.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
apply shadow_ro_cells in SH. exact SH.
Qed.

Lemma stack_shadowA : forall A LB LM FR B m md q mxd d j,
HEAPAx A LB LM FR B m md -> In (q, 32 * mxd) LB -> 0 <= d < mxd -> 0 <= j < 4 ->
ro_cells asegs m (q / 8 + 4 * d + j + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md q mxd d j HP Hin Hd Hj.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
pose proof (shadow_granule0 asegs m (q / 8 + A_SB) (32 * mxd) (4 * d + j) ltac:(lia) ltac:(lia) SH) as G.
replace (q / 8 + A_SB + (4 * d + j)) with (q / 8 + 4 * d + j + A_SB) in G by lia. exact G.
Qed.

Definition payload_shadowA (m : word -> option byte) (x : Z) : Prop :=
exists v, ro_cells asegs m (x / 8 + A_SB) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ x mod 8 < v)).

Lemma payload_shadow_of_blk : forall A LB LM FR B m md b n x,
HEAPAx A LB LM FR B m md -> In (b, n) LB -> b <= x < b + n -> payload_shadowA m x.
Proof.
intros A LB LM FR B m md b n x HP Hin Hx.
destruct (unpoisoned_of_blk HIx _ _ _ _ _ _ _ _ _ x 1 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & (v & Hv & Hvr) & _).
replace (x + 1 - 1) with x in Hv, Hvr by lia. exists v. split; [apply ro_C1_of_bytes_at; exact Hv | exact Hvr].
Qed.

Lemma payload_shadow_of_unp : forall m s n x, unpoisoned asegs m A_SB s n -> s <= x < s + n -> payload_shadowA m x.
Proof.
intros m s n x (Hn & GZ & (v & Hv & Hvr) & _) Hx.
destruct (Z_lt_ge_dec (x / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
- exists 0. split; [apply ro_C1_of_bytes_at; apply GZ; split; [Z.div_mod_to_equations; lia | exact Hlt] | left; reflexivity].
- assert (E : x / 8 = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
exists v. split; [apply ro_C1_of_bytes_at; rewrite E; exact Hv|].
destruct Hvr as [-> | [Hv8 Hm]]; [left; reflexivity | right]. split; [exact Hv8|]. Z.div_mod_to_equations. lia.
Qed.

Lemma payload_shadow_pe : forall pf pa LB0 FRS A LBall LM FR B m md co,
HEAPAx A LBall LM FR B m md -> incl LB0 LBall -> payload_locA pf pa LB0 FRS m -> 0 <= co < pf_len pf ->
payload_shadowA m (pf_sb pf + co).
Proof.
intros pf pa LB0 FRS A LBall LM FR B m md co HP Hincl PL Hco.
destruct PL as [([b n] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)].
- cbn [blk_addr blk_size fst snd] in Hb1, Hb2. eapply payload_shadow_of_blk; [exact HP | exact (Hincl _ Hb) | lia].
- eapply payload_shadow_of_unp; [exact UPS | lia].
Qed.
End WithIface.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1 Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Qw5U.Mq0 QlKV.Mq6.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SBUF_SHW : list byte := map (Z_to_bv 8) [241; 241; 241; 241; 0; 0; 5; 243].

Lemma sbuf_sh_byte : forall m sh i v, bytes_at asegs m sh SBUF_SHW -> (i < 8)%nat -> nth_error SBUF_SHW i = Some v -> bytes_at asegs m (sh + Z.of_nat i) [v].
Proof.
intros m sh i v B Hi Hn. pose proof (bytes_at_subG asegs m sh SBUF_SHW i 1 B ltac:(cbn [SBUF_SHW map length]; lia)) as X.
replace (firstn 1 (skipn i SBUF_SHW)) with [v] in X; [exact X|].
do 8 (destruct i as [|i]; [cbn in Hn |- *; injection Hn as <-; reflexivity|]). lia.
Qed.

Lemma unpoisoned_sbuf : forall m Fr n, Fr mod 128 = 0 -> 0 <= Fr ->
bytes_at asegs m (Fr / 8 + A_SB) SBUF_SHW -> 0 < n <= 21 -> unpoisoned asegs m A_SB (Fr + 32) n.
Proof.
intros m Fr n HF HF0 B Hn. unfold A_SB in *.
assert (E4 : (Fr + 32) / 8 = Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
split; [lia|]. split; [| split].
- intros g Hg. assert (C : g = Fr / 8 + 4 \/ g = Fr / 8 + 5) by (Z.div_mod_to_equations; lia).
destruct C as [-> | ->].
+ replace (Fr / 8 + 4 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 4) by lia. apply (sbuf_sh_byte m _ 4 _ B); [lia | reflexivity].
+ replace (Fr / 8 + 5 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 5) by lia. apply (sbuf_sh_byte m _ 5 _ B); [lia | reflexivity].
- assert (C : (n <= 8 /\ (Fr + 32 + n - 1) / 8 = Fr / 8 + 4) \/ (8 < n <= 16 /\ (Fr + 32 + n - 1) / 8 = Fr / 8 + 5) \/ (16 < n /\ (Fr + 32 + n - 1) / 8 = Fr / 8 + 6))
by (Z.div_mod_to_equations; lia).
destruct C as [[_ ->] | [[_ ->] | [H16 ->]]].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 4 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 4) by lia. apply (sbuf_sh_byte m _ 4 _ B); [lia | reflexivity].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 5 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 5) by lia. apply (sbuf_sh_byte m _ 5 _ B); [lia | reflexivity].
+ exists 5. split; [| right; split; [lia | Z.div_mod_to_equations; lia]].
replace (Fr / 8 + 6 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 6) by lia. apply (sbuf_sh_byte m _ 6 _ B); [lia | reflexivity].
- intros w Hw. exists SBUF_SHW. split; [reflexivity|].
replace (w * 8) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia). exact B.
Qed.

Lemma rng_okJ_sbuf : forall m Fr (w : word) n, Fr mod 128 = 0 -> 0 < Fr -> Fr + 128 + 8 <= 2^47 ->
rw_cells asegs m (Fr / 8 + A_SB) [C8 w] -> le8 w = SBUF_SHW -> 0 < n <= 21 -> rng_okJ m (Fr + 32) n.
Proof.
intros m Fr w n HF HF0 HFhi RW LE Hn. unfold A_SB in *.
assert (B : bytes_at asegs m (Fr / 8 + 2147450880) SBUF_SHW).
{ pose proof (rw_cells_bytes_at asegs _ _ _ RW) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r, LE in X. exact X. }
split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
- intros _ k Hk Hkn. unfold SHJ, A_SB.
replace ((Fr + 32) / 8 * 8) with (Fr + 32) in * by (Z.div_mod_to_equations; lia).
replace ((Fr + 32) / 8) with (Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
assert (C : k = 0 \/ k = 1 \/ k = 2) by lia. destruct C as [-> | [-> | ->]].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 4 + 2147450880 + 0) with (Fr / 8 + 2147450880 + Z.of_nat 4) by lia. apply (sbuf_sh_byte m _ 4 _ B); [lia | reflexivity].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 4 + 2147450880 + 1) with (Fr / 8 + 2147450880 + Z.of_nat 5) by lia. apply (sbuf_sh_byte m _ 5 _ B); [lia | reflexivity].
+ exists 5. split; [| right; lia].
replace (Fr / 8 + 4 + 2147450880 + 2) with (Fr / 8 + 2147450880 + Z.of_nat 6) by lia. apply (sbuf_sh_byte m _ 6 _ B); [lia | reflexivity].
- intros _. unfold SHJ, A_SB.
replace (8 * (((Fr + 32) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
replace (8 * (((Fr + 32 + n - 1) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
split; exists w; exact RW.
Qed.

Lemma bytes_eq_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof. induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate H; [reflexivity|]. cbn in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2]. Qed.

Definition SBUF_SHWORD : word := Z_to_bv 64 0xf3050000f1f1f1f1.
Lemma le8_SBUF_SHWORD : le8 SBUF_SHWORD = SBUF_SHW.
Proof. apply bytes_eq_unsigned. vm_compute. reflexivity. Qed.

Lemma sbuf_shadow_word : forall m sh,
rw_cells asegs m sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 243)] ->
rw_cells asegs m sh [C8 SBUF_SHWORD] /\ bytes_at asegs m sh SBUF_SHW.
Proof.
intros m sh H. split.
- eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes app]. rewrite app_nil_r, le8_SBUF_SHWORD. reflexivity.
- pose proof (rw_cells_bytes_at asegs _ _ _ H) as X. exact X.
Qed.

Definition SBUF7_SHW : list byte := map (Z_to_bv 8) [241; 241; 241; 241; 7; 243; 243; 243].
Definition SBUF7_SHWORD : word := Z_to_bv 64 0xf3f3f307f1f1f1f1.
Lemma le8_SBUF7_SHWORD : le8 SBUF7_SHWORD = SBUF7_SHW.
Proof. apply bytes_eq_unsigned. vm_compute. reflexivity. Qed.

Lemma sbuf7_shadow_word : forall m sh,
rw_cells asegs m sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 7); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
rw_cells asegs m sh [C8 SBUF7_SHWORD] /\ bytes_at asegs m sh SBUF7_SHW.
Proof.
intros m sh H. split.
- eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes app]. rewrite app_nil_r, le8_SBUF7_SHWORD. reflexivity.
- pose proof (rw_cells_bytes_at asegs _ _ _ H) as X. exact X.
Qed.

Lemma sbuf7_sh_byte4 : forall m sh, bytes_at asegs m sh SBUF7_SHW -> bytes_at asegs m (sh + 4) [Z_to_bv 8 7].
Proof.
intros m sh B. pose proof (bytes_at_subG asegs m sh SBUF7_SHW 4 1 B ltac:(cbn [SBUF7_SHW map length]; lia)) as X.
change (Z.of_nat 4) with 4 in X. exact X.
Qed.

Lemma unpoisoned_sbuf7 : forall m Fr n, Fr mod 64 = 0 -> 0 <= Fr ->
bytes_at asegs m (Fr / 8 + A_SB) SBUF7_SHW -> 0 < n <= 7 -> unpoisoned asegs m A_SB (Fr + 32) n.
Proof.
intros m Fr n HF HF0 B Hn. unfold A_SB in *.
split; [lia|]. split; [| split].
- intros g Hg. exfalso. Z.div_mod_to_equations. lia.
- exists 7. split; [| right; split; [lia | Z.div_mod_to_equations; lia]].
replace ((Fr + 32 + n - 1) / 8 + 2147450880) with (Fr / 8 + 2147450880 + 4) by (Z.div_mod_to_equations; lia). apply sbuf7_sh_byte4. exact B.
- intros w Hw. exists SBUF7_SHW. split; [reflexivity|].
replace (w * 8) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia). exact B.
Qed.

Lemma rng_okJ_sbuf7 : forall m Fr n, Fr mod 64 = 0 -> 0 < Fr -> Fr + 64 + 8 <= 2^47 ->
rw_cells asegs m (Fr / 8 + A_SB) [C8 SBUF7_SHWORD] -> 0 < n <= 7 -> rng_okJ m (Fr + 32) n.
Proof.
intros m Fr n HF HF0 HFhi RW Hn. unfold A_SB in *.
assert (B : bytes_at asegs m (Fr / 8 + 2147450880) SBUF7_SHW).
{ pose proof (rw_cells_bytes_at asegs _ _ _ RW) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r, le8_SBUF7_SHWORD in X. exact X. }
split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
- intros _ k Hk Hkn. unfold SHJ, A_SB.
replace ((Fr + 32) / 8 * 8) with (Fr + 32) in * by (Z.div_mod_to_equations; lia).
replace ((Fr + 32) / 8) with (Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
assert (k = 0) as -> by lia.
exists 7. split; [| right; lia].
replace (Fr / 8 + 4 + 2147450880 + 0) with (Fr / 8 + 2147450880 + 4) by lia. apply sbuf7_sh_byte4. exact B.
- intros _. unfold SHJ, A_SB.
replace (8 * (((Fr + 32) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
replace (8 * (((Fr + 32 + n - 1) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
split; exists SBUF7_SHWORD; exact RW.
Qed.

Lemma rw_cells_empty : forall m a, 0 <= a -> a <= 2^64 -> rw_cells asegs m a [CB 0 []].
Proof.
intros m a H0 H1. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize app length Nat.add].
split; [split; [split; [reflexivity | exact I]|]|].
- unfold bytes_at. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia.
- unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section K.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma pres_private : forall A LBall LM FR B m m' md W L0 SP,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W ->
heap_pres A4H L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md W L0 SP HP MU WM Hsub HSP HW.
eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
exact (Q1Ey.client_outsideF HIx A LBall LM FR B L0 m md W SP HP Hsub HSP HW).
Qed.

Lemma pres_fp : forall A LBall LM FR B m m' md L0 SP fp,
HEAPAx A LBall LM FR B m md ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
~ client_addr A4H (LBall ++ LM) alloc_ceiling fp ->
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
heap_pres A4H L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md L0 SP fp HP Hsub HSP FPnc FPfr Hoff Hwv a Ha Hc. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- destruct (Hsub b Hb) as [Hb' | Hb'].
+ apply FPnc. right; right. exists b. split; [exact Hb' | exact Hbr].
+ apply in_fr_ivs in Hb' as (F & k & HF & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr F k HF) as [N1 N2]; [apply N1 | apply N2]; lia.
Qed.
End K.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import QCcH QfLs.
Import QbFI. Import QRBl. Import Qhd4. Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj.

Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Lemma bytes_at_sub : forall segs m a (bs : list byte) (k n : nat),
bytes_at segs m a bs -> (k + n <= length bs)%nat -> bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
intros segs m a bs k n (H0 & H1 & H2) Hl.
assert (L : length (firstn n (skipn k bs)) = n) by (rewrite firstn_length_le; [reflexivity | rewrite length_skipn; lia]).
split; [lia|]. split; [rewrite L; lia|]. intros i Hi. rewrite L in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite (H2 (k + i)%nat) by lia.
rewrite nth_error_firstn. destruct (Nat.ltb_spec i n); [| lia]. rewrite nth_error_skipn. reflexivity.
Qed.

Lemma bytes_at_pointwiseA : forall segs (m m' : word -> option byte) A bs,
bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> m' (wa a) = m (wa a)) -> bytes_at segs m' A bs.
Proof.
intros segs m m' A bs (H0 & H1 & HB) E. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd. rewrite (E (A + Z.of_nat i)) by lia. reflexivity.
Qed.
Lemma rw_cells_pointwiseA : forall segs (m m' : word -> option byte) A cs,
rw_cells segs m A cs ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
rw_cells segs m' A cs.
Proof.
intros segs m m' A cs [[WF HB] (W0 & W1 & HW)] E. split; [split; [exact WF|]|].
- eapply bytes_at_pointwiseA; [exact HB|]. intros a Ha. rewrite cells_bytes_length in Ha by exact WF. apply (proj1 (E a ltac:(lia))).
- split; [exact W0|]. split; [exact W1|]. intros i Hi. apply (proj2 (E (A + i) ltac:(lia))). apply HW. exact Hi.
Qed.

Lemma bytes_at_skipn : forall segs m a (bs : list byte) (k : Z),
bytes_at segs m a bs -> 0 <= k <= Z.of_nat (length bs) -> bytes_at segs m (a + k) (skipn (Z.to_nat k) bs).
Proof.
intros segs m a bs k B Hk.
pose proof (bytes_at_sub segs m a bs (Z.to_nat k) (length bs - Z.to_nat k) B ltac:(lia)) as X.
rewrite Z2Nat.id in X by lia. rewrite firstn_all2 in X by (rewrite length_skipn; lia). exact X.
Qed.

Lemma land_even_1A : forall n, Z.land (2 * n) 1 = 0.
Proof. intros n. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
Lemma short_flag0A : forall n, 0 <= n <= 127 -> Z.land (bv_unsigned (zxb (Z_to_bv 8 (2 * n)))) 1 = 0.
Proof.
intros n Hn. unfold zxb. rewrite unsigned_lit.
2:{ pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (2 * n))) as R. unfold bv_modulus in R. cbn in R. lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2^8). rewrite Z.mod_small by lia.
apply land_even_1A.
Qed.
Lemma short_sizeA : forall n, 0 <= n <= 127 -> Z.shiftr (bv_unsigned (zxb (Z_to_bv 8 (2 * n)))) 1 = n.
Proof.
intros n Hn. unfold zxb. rewrite unsigned_lit.
2:{ pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (2 * n))) as R. unfold bv_modulus in R. cbn in R. lia. }
rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2^8). rewrite Z.mod_small by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma presx_ownA : forall (X : Z -> Prop) A LBall LM FR B m m' md W L0 SP,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W ->
heap_presx A4H X L0 SP m m'.
Proof.
intros X A LBall LM FR B m m' md W L0 SP HP MU WM Hsub HSP HW a Ha Hc. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
exact (QSHS.client_outsideF HIx A LBall LM FR B L0 m md W SP HP Hsub HSP HW a Ha (client_addrx_addr A4H _ _ _ _ Hc)).
Qed.
End WithIface.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo_c1 QWxq_c1 QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw QkMG. Import QG8z.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QSHS.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma ro_C1_of_bytes_at : forall m a v, bytes_at asegs m a [Z_to_bv 8 v] -> ro_cells asegs m a [C1 (Z_to_bv 8 v)].
Proof. intros m a v H. split; [cbn; split; exact I | cbn; exact H]. Qed.

Lemma sxb_small : forall v, 0 <= v < 128 -> sxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sxb. f_equal. unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small (v + 128) 256) by lia. lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma div8_add_mul32 : forall q d, q mod 8 = 0 -> 0 <= d -> (q + 32 * d) / 8 = q / 8 + 4 * d.
Proof. intros q d Hq Hd. Z.div_mod_to_equations. lia. Qed.

Section WithIface.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma tok_shadowA : forall A LB LM FR B m md tk,
HEAPAx A LB LM FR B m md -> In (tk, 72) LB ->
ro_cells asegs m (tk / 8 + A_SB)
[C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md tk HP Hin.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
apply shadow_ro_cells in SH. exact SH.
Qed.

Lemma stack_shadowA : forall A LB LM FR B m md q mxd d j,
HEAPAx A LB LM FR B m md -> In (q, 32 * mxd) LB -> 0 <= d < mxd -> 0 <= j < 4 ->
ro_cells asegs m (q / 8 + 4 * d + j + A_SB) [C1 (Z_to_bv 8 0)].
Proof.
intros A LB LM FR B m md q mxd d j HP Hin Hd Hj.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH. unfold shad in SH. cbn [hl_sb A4L] in SH.
pose proof (shadow_granule0 asegs m (q / 8 + A_SB) (32 * mxd) (4 * d + j) ltac:(lia) ltac:(lia) SH) as G.
replace (q / 8 + A_SB + (4 * d + j)) with (q / 8 + 4 * d + j + A_SB) in G by lia. exact G.
Qed.

Definition payload_shadowA (m : word -> option byte) (x : Z) : Prop :=
exists v, ro_cells asegs m (x / 8 + A_SB) [C1 (Z_to_bv 8 v)] /\ (v = 0 \/ (0 < v < 8 /\ x mod 8 < v)).

Lemma payload_shadow_of_blk : forall A LB LM FR B m md b n x,
HEAPAx A LB LM FR B m md -> In (b, n) LB -> b <= x < b + n -> payload_shadowA m x.
Proof.
intros A LB LM FR B m md b n x HP Hin Hx.
destruct (unpoisoned_of_blk HIx _ _ _ _ _ _ _ _ _ x 1 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & (v & Hv & Hvr) & _).
replace (x + 1 - 1) with x in Hv, Hvr by lia. exists v. split; [apply ro_C1_of_bytes_at; exact Hv | exact Hvr].
Qed.

Lemma payload_shadow_of_unp : forall m s n x, unpoisoned asegs m A_SB s n -> s <= x < s + n -> payload_shadowA m x.
Proof.
intros m s n x (Hn & GZ & (v & Hv & Hvr) & _) Hx.
destruct (Z_lt_ge_dec (x / 8) ((s + n - 1) / 8)) as [Hlt | Hge].
- exists 0. split; [apply ro_C1_of_bytes_at; apply GZ; split; [Z.div_mod_to_equations; lia | exact Hlt] | left; reflexivity].
- assert (E : x / 8 = (s + n - 1) / 8) by (Z.div_mod_to_equations; lia).
exists v. split; [apply ro_C1_of_bytes_at; rewrite E; exact Hv|].
destruct Hvr as [-> | [Hv8 Hm]]; [left; reflexivity | right]. split; [exact Hv8|]. Z.div_mod_to_equations. lia.
Qed.

Lemma payload_shadow_pe : forall pf pa LB0 FRS A LBall LM FR B m md co,
HEAPAx A LBall LM FR B m md -> incl LB0 LBall -> payload_locA pf pa LB0 FRS m -> 0 <= co < pf_len pf ->
payload_shadowA m (pf_sb pf + co).
Proof.
intros pf pa LB0 FRS A LBall LM FR B m md co HP Hincl PL Hco.
destruct PL as [([b n] & Hb & Hb1 & Hb2) | (Fh & kh & HFh & HF1 & HF2 & UPS)].
- cbn [blk_addr blk_size fst snd] in Hb1, Hb2. eapply payload_shadow_of_blk; [exact HP | exact (Hincl _ Hb) | lia].
- eapply payload_shadow_of_unp; [exact UPS | lia].
Qed.
End WithIface.
End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SBUF_SHW : list byte := map (Z_to_bv 8) [241; 241; 241; 241; 0; 0; 5; 243].

Lemma sbuf_sh_byte : forall m sh i v, bytes_at asegs m sh SBUF_SHW -> (i < 8)%nat -> nth_error SBUF_SHW i = Some v -> bytes_at asegs m (sh + Z.of_nat i) [v].
Proof.
intros m sh i v B Hi Hn. pose proof (bytes_at_subG asegs m sh SBUF_SHW i 1 B ltac:(cbn [SBUF_SHW map length]; lia)) as X.
replace (firstn 1 (skipn i SBUF_SHW)) with [v] in X; [exact X|].
do 8 (destruct i as [|i]; [cbn in Hn |- *; injection Hn as <-; reflexivity|]). lia.
Qed.

Lemma unpoisoned_sbuf : forall m Fr n, Fr mod 128 = 0 -> 0 <= Fr ->
bytes_at asegs m (Fr / 8 + A_SB) SBUF_SHW -> 0 < n <= 21 -> unpoisoned asegs m A_SB (Fr + 32) n.
Proof.
intros m Fr n HF HF0 B Hn. unfold A_SB in *.
assert (E4 : (Fr + 32) / 8 = Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
split; [lia|]. split; [| split].
- intros g Hg. assert (C : g = Fr / 8 + 4 \/ g = Fr / 8 + 5) by (Z.div_mod_to_equations; lia).
destruct C as [-> | ->].
+ replace (Fr / 8 + 4 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 4) by lia. apply (sbuf_sh_byte m _ 4 _ B); [lia | reflexivity].
+ replace (Fr / 8 + 5 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 5) by lia. apply (sbuf_sh_byte m _ 5 _ B); [lia | reflexivity].
- assert (C : (n <= 8 /\ (Fr + 32 + n - 1) / 8 = Fr / 8 + 4) \/ (8 < n <= 16 /\ (Fr + 32 + n - 1) / 8 = Fr / 8 + 5) \/ (16 < n /\ (Fr + 32 + n - 1) / 8 = Fr / 8 + 6))
by (Z.div_mod_to_equations; lia).
destruct C as [[_ ->] | [[_ ->] | [H16 ->]]].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 4 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 4) by lia. apply (sbuf_sh_byte m _ 4 _ B); [lia | reflexivity].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 5 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 5) by lia. apply (sbuf_sh_byte m _ 5 _ B); [lia | reflexivity].
+ exists 5. split; [| right; split; [lia | Z.div_mod_to_equations; lia]].
replace (Fr / 8 + 6 + 2147450880) with (Fr / 8 + 2147450880 + Z.of_nat 6) by lia. apply (sbuf_sh_byte m _ 6 _ B); [lia | reflexivity].
- intros w Hw. exists SBUF_SHW. split; [reflexivity|].
replace (w * 8) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia). exact B.
Qed.

Lemma rng_okJ_sbuf : forall m Fr (w : word) n, Fr mod 128 = 0 -> 0 < Fr -> Fr + 128 + 8 <= 2^47 ->
rw_cells asegs m (Fr / 8 + A_SB) [C8 w] -> le8 w = SBUF_SHW -> 0 < n <= 21 -> rng_okJ m (Fr + 32) n.
Proof.
intros m Fr w n HF HF0 HFhi RW LE Hn. unfold A_SB in *.
assert (B : bytes_at asegs m (Fr / 8 + 2147450880) SBUF_SHW).
{ pose proof (rw_cells_bytes_at asegs _ _ _ RW) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r, LE in X. exact X. }
split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
- intros _ k Hk Hkn. unfold SHJ, A_SB.
replace ((Fr + 32) / 8 * 8) with (Fr + 32) in * by (Z.div_mod_to_equations; lia).
replace ((Fr + 32) / 8) with (Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
assert (C : k = 0 \/ k = 1 \/ k = 2) by lia. destruct C as [-> | [-> | ->]].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 4 + 2147450880 + 0) with (Fr / 8 + 2147450880 + Z.of_nat 4) by lia. apply (sbuf_sh_byte m _ 4 _ B); [lia | reflexivity].
+ exists 0. split; [| left; reflexivity].
replace (Fr / 8 + 4 + 2147450880 + 1) with (Fr / 8 + 2147450880 + Z.of_nat 5) by lia. apply (sbuf_sh_byte m _ 5 _ B); [lia | reflexivity].
+ exists 5. split; [| right; lia].
replace (Fr / 8 + 4 + 2147450880 + 2) with (Fr / 8 + 2147450880 + Z.of_nat 6) by lia. apply (sbuf_sh_byte m _ 6 _ B); [lia | reflexivity].
- intros _. unfold SHJ, A_SB.
replace (8 * (((Fr + 32) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
replace (8 * (((Fr + 32 + n - 1) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
split; exists w; exact RW.
Qed.

Lemma bytes_eq_unsigned : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof. induction l1 as [|a l1 IH]; intros [|b l2] H; try discriminate H; [reflexivity|]. cbn in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2]. Qed.

Definition SBUF_SHWORD : word := Z_to_bv 64 0xf3050000f1f1f1f1.
Lemma le8_SBUF_SHWORD : le8 SBUF_SHWORD = SBUF_SHW.
Proof. apply bytes_eq_unsigned. vm_compute. reflexivity. Qed.

Lemma sbuf_shadow_word : forall m sh,
rw_cells asegs m sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 5); C1 (Z_to_bv 8 243)] ->
rw_cells asegs m sh [C8 SBUF_SHWORD] /\ bytes_at asegs m sh SBUF_SHW.
Proof.
intros m sh H. split.
- eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes app]. rewrite app_nil_r, le8_SBUF_SHWORD. reflexivity.
- pose proof (rw_cells_bytes_at asegs _ _ _ H) as X. exact X.
Qed.

Definition SBUF7_SHW : list byte := map (Z_to_bv 8) [241; 241; 241; 241; 7; 243; 243; 243].
Definition SBUF7_SHWORD : word := Z_to_bv 64 0xf3f3f307f1f1f1f1.
Lemma le8_SBUF7_SHWORD : le8 SBUF7_SHWORD = SBUF7_SHW.
Proof. apply bytes_eq_unsigned. vm_compute. reflexivity. Qed.

Lemma sbuf7_shadow_word : forall m sh,
rw_cells asegs m sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 7); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
rw_cells asegs m sh [C8 SBUF7_SHWORD] /\ bytes_at asegs m sh SBUF7_SHW.
Proof.
intros m sh H. split.
- eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes app]. rewrite app_nil_r, le8_SBUF7_SHWORD. reflexivity.
- pose proof (rw_cells_bytes_at asegs _ _ _ H) as X. exact X.
Qed.

Lemma sbuf7_sh_byte4 : forall m sh, bytes_at asegs m sh SBUF7_SHW -> bytes_at asegs m (sh + 4) [Z_to_bv 8 7].
Proof.
intros m sh B. pose proof (bytes_at_subG asegs m sh SBUF7_SHW 4 1 B ltac:(cbn [SBUF7_SHW map length]; lia)) as X.
change (Z.of_nat 4) with 4 in X. exact X.
Qed.

Lemma unpoisoned_sbuf7 : forall m Fr n, Fr mod 64 = 0 -> 0 <= Fr ->
bytes_at asegs m (Fr / 8 + A_SB) SBUF7_SHW -> 0 < n <= 7 -> unpoisoned asegs m A_SB (Fr + 32) n.
Proof.
intros m Fr n HF HF0 B Hn. unfold A_SB in *.
split; [lia|]. split; [| split].
- intros g Hg. exfalso. Z.div_mod_to_equations. lia.
- exists 7. split; [| right; split; [lia | Z.div_mod_to_equations; lia]].
replace ((Fr + 32 + n - 1) / 8 + 2147450880) with (Fr / 8 + 2147450880 + 4) by (Z.div_mod_to_equations; lia). apply sbuf7_sh_byte4. exact B.
- intros w Hw. exists SBUF7_SHW. split; [reflexivity|].
replace (w * 8) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia). exact B.
Qed.

Lemma rng_okJ_sbuf7 : forall m Fr n, Fr mod 64 = 0 -> 0 < Fr -> Fr + 64 + 8 <= 2^47 ->
rw_cells asegs m (Fr / 8 + A_SB) [C8 SBUF7_SHWORD] -> 0 < n <= 7 -> rng_okJ m (Fr + 32) n.
Proof.
intros m Fr n HF HF0 HFhi RW Hn. unfold A_SB in *.
assert (B : bytes_at asegs m (Fr / 8 + 2147450880) SBUF7_SHW).
{ pose proof (rw_cells_bytes_at asegs _ _ _ RW) as X. cbn [cells_bytes cbytes app] in X. rewrite app_nil_r, le8_SBUF7_SHWORD in X. exact X. }
split; [lia|]. split; [lia|]. split; [| split; [intros; lia|]].
- intros _ k Hk Hkn. unfold SHJ, A_SB.
replace ((Fr + 32) / 8 * 8) with (Fr + 32) in * by (Z.div_mod_to_equations; lia).
replace ((Fr + 32) / 8) with (Fr / 8 + 4) by (Z.div_mod_to_equations; lia).
assert (k = 0) as -> by lia.
exists 7. split; [| right; lia].
replace (Fr / 8 + 4 + 2147450880 + 0) with (Fr / 8 + 2147450880 + 4) by lia. apply sbuf7_sh_byte4. exact B.
- intros _. unfold SHJ, A_SB.
replace (8 * (((Fr + 32) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
replace (8 * (((Fr + 32 + n - 1) / 8 + 2147450880) / 8)) with (Fr / 8 + 2147450880) by (Z.div_mod_to_equations; lia).
split; exists SBUF7_SHWORD; exact RW.
Qed.

Lemma rw_cells_empty : forall m a, 0 <= a -> a <= 2^64 -> rw_cells asegs m a [CB 0 []].
Proof.
intros m a H0 H1. unfold rw_cells, cells_at. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize app length Nat.add].
split; [split; [split; [reflexivity | exact I]|]|].
- unfold bytes_at. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia.
- unfold wr_at. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section K.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma pres_private : forall A LBall LM FR B m m' md W L0 SP,
HEAPAx A LBall LM FR B m md -> munch W m m' -> wmono asegs m m' ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) (LBall ++ LM) /\ ~ In (a, n) L0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch A4L x)
\/ (exists F k, In (F, k) FR /\ ~ In (F, fr_size k - 8) L0 /\ ~ In (shad A4L F, fr_shadow_len k) L0 /\
((F <= fst iv /\ snd iv <= F + fr_size k) \/ (shad A4L F <= fst iv /\ snd iv <= shad A4L F + fr_shadow_len k)))) W ->
heap_pres A4H L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md W L0 SP HP MU WM Hsub HSP HW.
eapply (heap_pres_of_munch A4H); [exact MU | exact WM |].
exact (QSHS.client_outsideF HIx A LBall LM FR B L0 m md W SP HP Hsub HSP HW).
Qed.

Lemma pres_fp : forall A LBall LM FR B m m' md L0 SP fp,
HEAPAx A LBall LM FR B m md ->
(forall b, In b L0 -> In b (LBall ++ LM) \/ In b (fr_ivs A4L FR)) -> alloc_ceiling <= SP ->
~ client_addr A4H (LBall ++ LM) alloc_ceiling fp ->
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
heap_pres A4H L0 SP m m'.
Proof.
intros A LBall LM FR B m m' md L0 SP fp HP Hsub HSP FPnc FPfr Hoff Hwv a Ha Hc. split; [| apply Hwv]. apply Hoff; [exact Ha|]. intros ->.
destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- destruct (Hsub b Hb) as [Hb' | Hb'].
+ apply FPnc. right; right. exists b. split; [exact Hb' | exact Hbr].
+ apply in_fr_ivs in Hb' as (F & k & HF & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr F k HF) as [N1 N2]; [apply N1 | apply N2]; lia.
Qed.
End K.
End RC__1.
