(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QsV0 QBxa QSpR QCKW Qujl QuXQ QQ7a QZsi Q0TL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import Q7UD.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4 QSpR.Mq0 QBxa.Mq1 QBxa.Mq3 QBxa.Mq2.
Import QCKW.Mq2 Qujl.Mq1 QuXQ.Mq1 QQ7a.
Import QZsi.

Import QCKW.Mq4.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Variable J : aj_base RSEGS.
Hypothesis SYS : @Q0TL.aj_sys fF fC RSEGS J.

Lemma AJ_emit_nil : forall c ms K, K [] -> AJ J K c ms -> AJ J (t_emit [] K) c ms.
Proof.
intros c ms K HK HR. eapply (aj_conseq J); [exact HR|].
apply t_eq_sym. apply t_emit_nil_eq. exact HK.
Qed.

Lemma same_io_trans : forall a b c : config, Q0TL.same_io a b -> Q0TL.same_io b c -> Q0TL.same_io a c.
Proof. intros a b c [F1 S1] [F2 S2]. split; [rewrite F2; exact F1 | rewrite S2; exact S1]. Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
(k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
(length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
\/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
intros b k Hk Hle. unfold at_. pose proof (u64_range b).
destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
- right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
- left. u_norm. reflexivity.
Qed.

Section Loop.
Variables (su f fd : Z) (l bufp bufsz can ret : word).
Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
Variable mem1 : word -> option byte.
Variable model : config.
Variable K : TSet.

Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
Hypothesis SUhi : (su <= 0x800000000000)%Z.
Hypothesis Flo : (0xe7000 <= f)%Z.
Hypothesis Fhi : (f + 232 <= 0x642ea0)%Z.
Hypothesis FD : (fd = 1 \/ fd = 2)%Z.

Definition CN (c : config) : Prop := CNEXT J model c /\ Q0TL.same_io model c.
Lemma CN_next : forall c c', CN c -> CNEXT J c c' -> Q0TL.same_io c c' -> CN c'.
Proof. intros c c' [N S] N' S'. split; [exact (cnext_trans _ J _ _ _ N N') | exact (same_io_trans _ _ _ S S')]. Qed.
Lemma CN_ck : forall c, CN c -> CK J c.
Proof. intros c [N _]. exact (cnext_ck _ J _ _ N). Qed.
Local Notation RZAc md ms K := (AJ J K md ms).
Hypothesis Hret : ret_ok ret.
Hypothesis HKnil : K [].
Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x642ea0) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

Definition LM (m : word -> option byte) : Prop :=
(forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

Hypothesis HK : forall regs' m c',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = e8 -> getr regs' 9 = e9 ->
getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
LM m -> CN c' ->
RZAc c' (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) K.

Definition RI (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
/\ getr regs 21 = Z_to_bv 64 0x642ea0 /\ getr regs 3 = g3 /\ getr regs 4 = g4
/\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
/\ getr regs 26 = g26 /\ getr regs 27 = g27.

Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
Proof.
intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
(P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
Qed.

Lemma LM_refl : LM mem1.
Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma LM_rdn : forall m (a : word) n bs,
LM m -> rdn RSEGS mem1 a n = Some bs ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
rdn RSEGS m a n = Some bs.
Proof.
intros m a n bs [E G] H Hnw D.
rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
intros x Hx. apply E. lia.
Qed.

Lemma LM_store_ok : forall m (a : word) n,
LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

Lemma LM_wbytes8 : forall m (a : Z) (v : word),
LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
Proof.
intros m a v [E G] Hlo Hhi. split.
- intros x Hx. rewrite wbytes_outside.
+ apply E, Hx.
+ unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+ rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.

Lemma finish : forall c, CN c -> forall regs m,
RI regs -> LM m ->
RZAc c (mkst regs (0xd2a64 : word) m (seg_rom RSEGS)) K.
Proof.
intros c HCN regs m RIr LMm.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
try assumption.
all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
apply (HK regs2 m c); try assumption.
- rewrite Q23; exact R23.
- rewrite Q24; exact R24.
- rewrite Q25; exact R25.
- rewrite Q26; exact R26.
- rewrite Q27; exact R27.
- rewrite Q3; exact R3.
- rewrite Q4; exact R4.
Qed.

Lemma finish_nil : forall c, CN c -> forall regs m,
RI regs -> LM m ->
RZAc c (mkst regs (0xd2a64 : word) m (seg_rom RSEGS)) (t_emit [] K).
Proof. intros. apply AJ_emit_nil; [exact HKnil|]. apply finish; assumption. Qed.

Lemma pc_d27fc : v_addi (0xd2ae0 : word) 4 = (0xd2ae4 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma loop1 : forall n c, CN c -> forall regs m (k : nat) (b : word) (bs : list byte),
(length bs <= n)%nat ->
RI regs -> LM m ->
getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
(1 <= k < length bs)%nat ->
rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
rdn RSEGS mem1 b (length bs) = Some bs ->
(bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
(bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->
(Z.of_nat (length bs) <= 67108864)%Z ->
RZAc c (mkst regs (0xd2af0 : word) m (seg_rom RSEGS))
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
Proof.
induction n as [|n IH]; intros c HCN regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b) as Hb.

destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
(Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).

eapply (AJ_writev1_wall RSEGS J SYS regs1 (0xd2ae0 : word) m' c W_d2b04 fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
[ exact F_d2b04 | exact E_d2b04 | exact (CN_ck c HCN) | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
- subst m'. rdn_solve.
- subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
- rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
- unfold TASK_SIZE. u_norm. lia.
- unfold TASK_SIZE. u_norm. lia.
- u_norm. lia.
- u_norm. lia.
-
intros k' c' K1 K2 HN' HS'. pose proof (CN_next c c' HCN HN' HS') as HCN'. rewrite pc_d27fc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
+
destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
apply (finish_nil c' HCN'); [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (IH c' HCN' regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
* rewrite length_skipn. lia.
* eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* exact LMm'.
* exact P10.
* rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
* rewrite P18. gres. exact Q18.
* rewrite P19. gres. exact Q20.
* rewrite length_skipn. lia.
* subst m'. unfold at_. rdn_solve.
* subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
* rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
* unfold at_. rewrite length_skipn. u_norm. lia.
* unfold at_. rewrite length_skipn. u_norm. lia.
* rewrite length_skipn. lia.
Qed.

Lemma loop2 : forall n c, CN c -> forall regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
(length bs0 + length bs1 <= n)%nat ->
RI regs -> LM m ->
getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
(1 <= k < length bs0 + length bs1)%nat ->
rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
(bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
(bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
(bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
(bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
(Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 67108864)%Z ->
RZAc c (mkst regs (0xd2af0 : word) m (seg_rom RSEGS))
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
Proof.
induction n as [|n IH]; intros c HCN regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
-
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_le k bs0 bs1 LE).
eapply (AJ_writev2_wall RSEGS J SYS regs1 (0xd2ae0 : word) m' c W_d2b04 fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
[ exact F_d2b04 | exact E_d2b04 | exact (CN_ck c HCN) | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
+ subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
{ replace (length bs0 - k)%nat with 0%nat by lia.
rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
+ rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
subst m'. repeat rdn_peel1.
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' c' K1 K2 HN' HS'. pose proof (CN_next c c' HCN HN' HS') as HCN'. rewrite pc_d27fc. rewrite length_app, length_skipn in K2.
destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
apply (finish_nil c' HCN'); [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (IH c' HCN' regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
-- subst m'. repeat rdn_peel1. exact Mb1.
-- subst m'. repeat rdn_peel1. exact Mn1.
-- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
-- exact Bbs1.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- exact DISJ1.
-- exact NW1.
-- rewrite length_skipn. lia.
-
destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs1))
(Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
{ replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_ge k bs0 bs1) by lia.
eapply (AJ_writev1_wall RSEGS J SYS regs1 (0xd2ae0 : word) m' c W_d2b04 fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
(Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
(skipn (k - length bs0) bs1) K);
[ exact F_d2b04 | exact E_d2b04 | exact (CN_ck c HCN) | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' c' K1 K2 HN' HS'. pose proof (CN_next c c' HCN HN' HS') as HCN'. rewrite pc_d27fc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
apply (finish_nil c' HCN'); [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (loop1 (length bs1) c' HCN' regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
rdn_solve.
-- rewrite length_skipn.
apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- rewrite length_skipn. lia.
Qed.

End Loop.
End FPGEN1.

Ltac wout1 :=
rewrite wbytes_outside;
[ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.
Variable J : aj_base RSEGS.
Hypothesis SYS : @Q0TL.aj_sys fF fC RSEGS J.
Local Notation RZAc md ms K := (AJ J K md ms).

Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
constructor.
- intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
unfold mem_sw2. do 3 wout1.
rewrite (E x) by lia.
unfold mem_sw1. do 13 wout1. reflexivity.
- unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
eapply mem_grows_trans; [|exact G].
unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
apply mem_grows_refl.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
Qed.

Lemma pc_d2774 : v_addi (0xd2a58 : word) 4 = (0xd2a5c : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Theorem ref_stdio_write :
forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
(pending extra : list byte) (K : TSet),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0xe7000 <= f)%Z -> (f + 232 <= 0x642ea0)%Z ->
sw_file mem f wb wp fd bufp bufsz ->
ssp_cells mem can ->
(fd = 1 \/ fd = 2)%Z ->
CK J model ->
(0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 67108864)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS mem s (length extra) = Some extra ->
ret_ok ret ->
K [] ->
(forall regs' mem' c',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
sw_post mem su f bufp bufsz mem' ->
CNEXT J model c' -> Q0TL.same_io model c' ->
RZAc c' (mkst regs' ret mem' (seg_rom RSEGS)) K) ->
RZAc model (mkst regs (0xd29d0 : word) mem (seg_rom RSEGS))
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD HCK0 WBP WPhi
LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
pose proof SWF as SWF'. pose proof SSP as SSP'.
destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
{ rewrite <- LENE. symmetry. apply u64_roundtrip'. }

set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
{ subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x642ea0) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }

assert (HK' : forall regs' m c',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
LM su mem1 m -> CN J model c' ->
RZAc c' (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) K).
{ intros until c'. intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 XL [XN XS]. apply HK. all: try assumption.
eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
match goal with H : LM _ _ _ |- _ => exact H end. }
pose proof (finish_nil J su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi Hret HKnil M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
pose proof (loop1 J SYS su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
pose proof (loop2 J SYS su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
pose proof (LM_refl su mem1) as LM1.
destruct (Z.eq_dec wb wp) as [EQ|NEQ].
-
destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
subst wb.
destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN1 |]. clear RUN1.
lazymatch goal with |- AJ _ _ _ (mkst _ _ ?M _) =>
replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
rewrite Z.sub_diag in M96.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
destruct extra as [|x0 extra'].
+
cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
eapply (AJ_writev1_zero RSEGS J SYS regs1 (0xd2a58 : word) mem1 model W_d2a7c fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
[ exact F_d2a7c | exact E_d2a7c | exact HCK0 | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | ].
{ u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
{ unfold TASK_SIZE. u_norm. lia. }
{ unfold TASK_SIZE. lia. }
intros c' HN' HS'. rewrite pc_d2774.
destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. exact HlZ. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (FIN c' (conj HN' HS')); [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
eapply (AJ_writev1_wall RSEGS J SYS regs1 (0xd2a58 : word) mem1 model W_d2a7c fd
(Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
[ exact F_d2a7c | exact E_d2a7c | exact HCK0 | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
* u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
* unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
* unfold TASK_SIZE. u_norm. lia.
* unfold TASK_SIZE. lia.
* cbn [length] in LENE. lia.
* lia.
* intros k c' K1 K2 HN' HS'. rewrite pc_d2774.
destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
-- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
apply (FIN c' (conj HN' HS')); [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(Z.of_nat (length (x0 :: extra'))))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. reflexivity. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (L1 (length (x0 :: extra')) c' (conj HN' HS') regs2 mem1 k s (x0 :: extra')); try lia.
++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
++ exact LM1.
++ exact P10.
++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
++ rewrite P18. gres. exact R18.
++ rewrite P19. gres. exact R19.
++ exact M88.
++ rewrite <- HlZ. exact M80.
++ exact Be.
-
destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN1 |]. clear RUN1. fold mem1.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
eapply (AJ_writev2_wall RSEGS J SYS regs1 (0xd2a58 : word) mem1 model W_d2a7c fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
[ exact F_d2a7c | exact E_d2a7c | exact HCK0 | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
+ u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
+ u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
+ u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
+ rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
+ unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k c' K1 K2 HN' HS'. rewrite pc_d2774. rewrite length_app in K2.
destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
* destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
apply (FIN c' (conj HN' HS')); [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(wp - wb + bv_unsigned l))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact R22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (L2 (length pending + length extra)%nat c' (conj HN' HS') regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LM1.
-- exact P10.
-- rewrite P22. gres. rewrite R22. f_equal. lia.
-- rewrite P18. gres. exact R18.
-- rewrite P19. gres. exact R19.
-- exact M104.
-- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
-- exact M88.
-- rewrite <- HlZ. exact M80.
-- exact Bp.
-- exact Be.
-- u_norm. lia.
-- u_norm. lia.
Qed.
End FPGEN2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From Stdlib Require NArith.
From LinuxProcessSemantics.Riscv Require Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Qwm6 QlKV Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Q7UD Qwm6.
Import QuXQ.Mq2.
Import Qwm6.Mq0 QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_IMEMCPY : Z := 0x61740.

Definition imemcpy_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> (0 < n -> unpoisoned asegs m A_SB s n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> 0 <= s -> s + n <= 2^47 -> (64 < n -> app_mem d n /\ app_mem s n) ->
(d + n <= lo \/ bv_unsigned sp <= d) -> (s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^31 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_IMEMCPY) fc None m (seg_rom asegs)).

Section IMemcpy.
Hypothesis OBL_REGION : region_is_poisoned_spec_U.

Local Ltac slow_head x n v Hv :=
step; rewrite (sxb_small v) by lia;
step; rewrite (unsigned_lit (x + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (? & ?)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((x + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ].

Local Ltac qc_addrs x n :=
sh_norm;
replace (2147450880 + x / 8) with (x / 8 + 2147450880) by lia;
replace (2147450880 + (x + n - 1) / 8) with ((x + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (x / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((x + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia.

Lemma imemcpy_sound : imemcpy_spec_U.
Proof.
unfold imemcpy_spec_U.
intros until Q. intros UPd UPs RT Hd Hdn Hs Hsn APP SEPd SEPs Ha0 Ha1 Ha2 Hn Hdisj DST SRC SRCL ST LO LOS SPA MI RA K.
subst a0 a1 a2. word_range sp SPR. pose proof alloc_ceiling_ge as ACG.
rt_cell RT 0xe6928 as GOTF. rt_cell RT 0xf07d9 as FLAG. rt_cell RT 0xe5db8 as GOTSB. rt_cell RT 0xefaf8 as SBC.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in GOTSB. apply ro_C8_of_bytes_at in SBC.
assert (FLAGc : ro_cells asegs m 0xf07d9 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.

stash SRC.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_IMEMCPY. carve_frame 80%nat ST.
step.
do 13 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : asan_rt_ok mc) by (eapply (asan_rt_ok_stack m mc lo (bv_unsigned sp)); [exact RT | exact MU0 | exact LO]);
assert (UPd1 : 0 < n -> unpoisoned asegs mc A_SB d n)
by (intros Hn0; eapply unpoisoned_transport; [exact (UPd Hn0) | exact MU0
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]);
assert (UPs1 : 0 < n -> unpoisoned asegs mc A_SB s n)
by (intros Hn0; eapply unpoisoned_transport; [exact (UPs Hn0) | exact MU0
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia])
end.
clear MU0 UPd UPs RT.
unstash SRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC1 : bytes_at asegs mc s src)
by (eapply bytes_at_transport; [exact SRC | exact MU | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia])
end.
clear SRC.
do 4 step. if_false.
step. step.
step. step.

lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
assert (TAIL : forall (w x0 x1 x2 x3 x4 x5 x6 x7 y3 y4 y5 y6 z1 z2 z3 z4 z6 z7 z8 : word) (mc : word -> option byte) (oldx : list byte),
munch [(d, d + n); (lo, bv_unsigned sp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> asan_rt_ok mc ->
rw_cells asegs mc d [CB (Z.to_nat n) oldx] -> bytes_at asegs mc s src ->
stk asegs mc lo (bv_unsigned sp + -80) -> rw_cells asegs mc fa fcs ->
evt asegs Q (MS (mkR w (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x0 x1 x2 sp z1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 z2 z3 z4 (Z_to_bv 64 (bv_unsigned sp + -2152)) z6 z7 z8 s9 s10 s11 y3 y4 y5 y6)
F (Z_to_bv 64 0x62a34) fc None mc (seg_rom asegs)))
end.
{ clear UPd1 UPs1 RT1 MU WM MI DST SRC1 ST FR GOTF GOTSB SBC FLAGc.
intros w x0 x1 x2 x3 x4 x5 x6 x7 y3 y4 y5 y6 z1 z2 z3 z4 z6 z7 z8 mc oldx MU WM MI RTm DSTm SRCm ST FR.
rt_cell RTm 0xe7da8 as REALC. apply ro_C8_of_bytes_at in REALC. clear RTm.
step. step. step.
(call real_memcpy_specZ); [lia | lia | lia | lia | lia | exact SRCm | exact SRCL | exact DSTm | lia | assumption |].
do 13 step.
eapply K;
[ match goal with H : munch _ m ?mf |- munch _ m ?mf => exact H end
| match goal with H : wmono _ m ?mf |- wmono _ m ?mf => exact H end
| assumption
| match goal with H : rw_cells _ ?mf d [CB _ src] |- _ => exact H end
| match goal with H : bytes_at _ ?mf s src |- _ => exact H end
| release_frame FR ST (bv_unsigned sp); exact ST ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AD : forall x3 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 a4 a5 a6 a7 s2 (Z_to_bv 64 (s + n)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x629a0) fc None mc (seg_rom asegs)))
end.
{ intros x3.
step. step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step.
destruct (Z_lt_le_dec 0 n) as [Hn0 | Hnz]; [destruct (Z.le_gt_cases n 64) as [Hn64 | Hbig]|].
-
rewrite (size_test_n n) by lia. cbv iota.
specialize (UPd1 Hn0). specialize (UPs1 Hn0). clear APP.
assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).
assert (Hh : s / 8 <= (s + n - 1) / 8 <= s / 8 + 8) by (clear Hg; Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + n - 1) / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in W1c, W2c, V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPd1); lia |];
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPs1); lia |];
assert (HRLd : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPd1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (HRLs : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPs1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPd1 UPs1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP2 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n - 1)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62dc0) fc None mc (seg_rom asegs)))
end.
{ clear GS0 GOTF FLAGc GOTSB SBC Hh HRLd HRLs W1c W2c V1c V2c;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GR0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true;
eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]
| if_truex; replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 s2 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x629ec) fc None mc (seg_rom asegs)))
end.
{ intros p3 p4 p5 p6 p7.
clear V1c V2c GS0 GOTF FLAGc Hh HRLs.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. rewrite (size_test_n n) by lia. cbv iota.
do 3 step.
step. replace (d + n + -1) with (d + n - 1) by lia.
do 2 step. do 2 step. do 2 step.
qc_addrs d n.
do 2 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]. }

destruct HRLd as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear W1c W2c Hg.
slow_head d n v Hv; clear HR;
step;
(destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true;
eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]
| if_falsex; replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia;
apply (LOOP2 (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia ]). }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP1 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((s + n - 1) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62cc0) fc None mc (seg_rom asegs)))
end.
{ clear W1c W2c V1c V2c GR0 GOTF FLAGc GOTSB SBC Hg TAIL LOOP2 HRLd HRLs MU WM DST SRC1 ST FR RT1;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GS0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (s / 8 + i + 1) ((s + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply MID
| if_truex; replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

clear W1c W2c GR0 GOTF FLAGc Hg TAIL LOOP2 HRLd MU WM DST SRC1 ST FR RT1.
do 3 step.
step. replace (s + n + -1) with (s + n - 1) by lia.
do 2 step. do 2 step. do 2 step.
qc_addrs s n.
do 2 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply MID. }

destruct HRLs as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c Hh.
slow_head s n v Hv; clear HR;
step;
(destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply MID
| if_falsex; replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia;
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia ]).
-
rewrite (size_test_big n) by lia. cbv iota.
specialize (UPd1 Hn0). specialize (UPs1 Hn0). destruct (APP Hbig) as [APPd APPs]. clear APP GOTSB SBC.
step. if_truex.
do 5 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2160) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
stash SRC1.
eapply (OBL_REGION _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s n lo);
[ exact UPs1 | exact RT1 | exact APPs | lia
| rewrite unsigned_lit by lia; lia | reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| assumption | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
clear UPs1 RT1.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 z3 z4 z5 z6 m2 MU2 WM2 MI2 ST1' UPs2 RT2.
assert (UPd2 : unpoisoned asegs m2 A_SB d n)
by (eapply unpoisoned_transport; [exact UPd1 | exact MU2
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]).
clear UPd1.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
unstash SRC1.
assert (SRC2 : bytes_at asegs m2 s src)
by (eapply bytes_at_transport; [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear MU2 WM2 SRC1.
replace (ret_pc (Z_to_bv 64 0x62cf0)) with (Z_to_bv 64 0x62cf0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. rewrite (size_test_big n) by lia. cbv iota.
step. if_truex.
do 4 step.
step.
stash SRC2.
eapply (OBL_REGION _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d n lo);
[ exact UPd2 | exact RT2 | exact APPd | lia
| rewrite unsigned_lit by lia; lia | reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1' | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
clear UPd2 RT2 UPs2.
intros p0 p1 p2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 m3 MU3 WM3 MI3 ST1'' UPd3 RT3.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
unstash SRC2.
assert (SRC3 : bytes_at asegs m3 s src)
by (eapply bytes_at_transport; [exact SRC2 | exact MU3 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear MU3 WM3 SRC2.
replace (ret_pc (Z_to_bv 64 0x62dec)) with (Z_to_bv 64 0x62dec) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAIL; [exact MU | exact WM | exact MI3 | exact RT3 | exact DST | exact SRC3
| eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR].
-
rewrite (size_test_big n) by lia. cbv iota.
clear UPd1 UPs1 APP GOTSB SBC.
step. if_falsex.
step.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. rewrite (size_test_big n) by lia. cbv iota.
step. if_falsex.
step.
eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]. }

clear UPd1 UPs1 GOTF FLAGc GOTSB SBC TAIL MU WM DST SRC1 ST FR RT1 APP.
destruct (Z.eq_dec d s) as [Eds | Nds].
- rewrite <- Eds in *. step. if_truex. apply AD.
- step. if_falsex.
step.
destruct Hdisj as [Hsd | Hds].
+ if_falsex. step. if_falsex. apply AD.
+ if_truex. apply AD.
Qed.
End IMemcpy.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI Qwsr Qfub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QbFI.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4 QSpR.Mq0 QBxa.Mq1 QBxa.Mq3 QBxa.Mq2.
Import QCKW.Mq7 Qujl.Mq3 QuXQ.Mq4 Qwsr.
Import QZsi.

Import QCKW.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Variable J : aj_base RSEGS.
Hypothesis SYS : @Qfub.aj_sys fF fC RSEGS J.

Lemma AJ_emit_nil : forall c ms K, K [] -> AJ J K c ms -> AJ J (t_emit [] K) c ms.
Proof.
intros c ms K HK HR. eapply (aj_conseq J); [exact HR|].
apply t_eq_sym. apply t_emit_nil_eq. exact HK.
Qed.

Lemma same_io_trans : forall a b c : config, Qfub.same_io a b -> Qfub.same_io b c -> Qfub.same_io a c.
Proof. intros a b c [F1 S1] [F2 S2]. split; [rewrite F2; exact F1 | rewrite S2; exact S1]. Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
(k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. replace (k - length l1)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
(length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
intros A k l1 l2 Hk. rewrite skipn_app. rewrite (proj1 (skipn_all_iff k l1) Hk). reflexivity.
Qed.

Lemma u_at_le : forall (b : word) (k : Z), (0 <= k)%Z -> (bv_unsigned b + k <= 2 ^ 64)%Z ->
bv_unsigned (at_ b k) = (bv_unsigned b + k)%Z
\/ (bv_unsigned (at_ b k) = 0 /\ bv_unsigned b + k = 2 ^ 64)%Z.
Proof.
intros b k Hk Hle. unfold at_. pose proof (u64_range b).
destruct (Z.eq_dec (bv_unsigned b + k) (2 ^ 64)) as [E|NE].
- right. split; [|exact E]. rewrite E. vm_compute. reflexivity.
- left. u_norm. reflexivity.
Qed.

Section Loop.
Variables (su f fd : Z) (l bufp bufsz can ret : word).
Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
Variable mem1 : word -> option byte.
Variable model : config.
Variable K : TSet.

Hypothesis SUlo : (4294967296 + 112 <= su)%Z.
Hypothesis SUhi : (su <= 0x800000000000)%Z.
Hypothesis Flo : (0xea000 <= f)%Z.
Hypothesis Fhi : (f + 232 <= 0x645560)%Z.
Hypothesis FD : (fd = 1 \/ fd = 2)%Z.

Definition CN (c : config) : Prop := CNEXT J model c /\ Qfub.same_io model c.
Lemma CN_next : forall c c', CN c -> CNEXT J c c' -> Qfub.same_io c c' -> CN c'.
Proof. intros c c' [N S] N' S'. split; [exact (cnext_trans _ J _ _ _ N N') | exact (same_io_trans _ _ _ S S')]. Qed.
Lemma CN_ck : forall c, CN c -> CK J c.
Proof. intros c [N _]. exact (cnext_ck _ J _ _ N). Qed.
Local Notation RZAc md ms K := (AJ J K md ms).
Hypothesis Hret : ret_ok ret.
Hypothesis HKnil : K [].
Hypothesis SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true.
Hypothesis M8  : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret).
Hypothesis M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 e8).
Hypothesis M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 e9).
Hypothesis M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 e18).
Hypothesis M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 e19).
Hypothesis M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 e20).
Hypothesis M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 e21).
Hypothesis M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 e22).
Hypothesis M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x645560) 8%nat = Some (word_to_le_bytes 8 can).
Hypothesis Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp).
Hypothesis Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz).
Hypothesis Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)).

Definition LM (m : word -> option byte) : Prop :=
(forall x : word, ~ (su - 104 <= bv_unsigned x < su - 72)%Z -> m x = mem1 x) /\ mem_grows mem1 m.

Hypothesis HK : forall regs' m c',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = e8 -> getr regs' 9 = e9 ->
getr regs' 18 = e18 -> getr regs' 19 = e19 -> getr regs' 20 = e20 ->
getr regs' 21 = e21 -> getr regs' 22 = e22 -> getr regs' 23 = g23 ->
getr regs' 24 = g24 -> getr regs' 25 = g25 -> getr regs' 26 = g26 ->
getr regs' 27 = g27 -> getr regs' 3 = g3 -> getr regs' 4 = g4 ->
LM m -> CN c' ->
RZAc c' (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) K.

Definition RI (regs : bvmap 5 word) : Prop :=
getr regs 2 = Z_to_bv 64 (su - 112) /\ getr regs 8 = l /\ getr regs 9 = Z_to_bv 64 f
/\ getr regs 21 = Z_to_bv 64 0x645560 /\ getr regs 3 = g3 /\ getr regs 4 = g4
/\ getr regs 23 = g23 /\ getr regs 24 = g24 /\ getr regs 25 = g25
/\ getr regs 26 = g26 /\ getr regs 27 = g27.

Lemma RI_but : forall regs regs', RI regs -> sw_regs_but regs regs' -> RI regs'.
Proof.
intros regs regs' (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27)
(P2 & P8 & P9 & P21 & P3 & P4 & P23 & P24 & P25 & P26 & P27).
unfold RI. rewrite P2, P8, P9, P21, P3, P4, P23, P24, P25, P26, P27. repeat split; assumption.
Qed.

Lemma LM_refl : LM mem1.
Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma LM_rdn : forall m (a : word) n bs,
LM m -> rdn RSEGS mem1 a n = Some bs ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
(bv_unsigned a + Z.of_nat n <= su - 104 \/ su - 72 <= bv_unsigned a)%Z ->
rdn RSEGS m a n = Some bs.
Proof.
intros m a n bs [E G] H Hnw D.
rewrite (rdn_ext RSEGS n m mem1 a Hnw); [exact H|].
intros x Hx. apply E. lia.
Qed.

Lemma LM_store_ok : forall m (a : word) n,
LM m -> store_ok RSEGS mem1 a n = true -> store_ok RSEGS m a n = true.
Proof. intros m a n [E G] H. eapply store_ok_mono; [exact G | exact H]. Qed.

Lemma LM_wbytes8 : forall m (a : Z) (v : word),
LM m -> (su - 104 <= a)%Z -> (a + 8 <= su - 72)%Z ->
LM (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)).
Proof.
intros m a v [E G] Hlo Hhi. split.
- intros x Hx. rewrite wbytes_outside.
+ apply E, Hx.
+ unfold in_rng. rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
+ rewrite length_N_to_le_bytes. u_norm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- eapply mem_grows_trans; [exact G | apply wbytes_grows].
Qed.

Lemma finish : forall c, CN c -> forall regs m,
RI regs -> LM m ->
RZAc c (mkst regs (0xd5128 : word) m (seg_rom RSEGS)) K.
Proof.
intros c HCN regs m RIr LMm.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
destruct (sw_done regs m (seg_rom RSEGS) su f l bufp bufsz can ret e8 e9 e18 e19 e20 e21 e22)
as (regs2 & RUN & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q3 & Q4 & Q23 & Q24 & Q25 & Q26 & Q27);
try assumption.
all: try (eapply LM_rdn; [exact LMm | eassumption | u_norm; lia | u_norm; lia]).
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
apply (HK regs2 m c); try assumption.
- rewrite Q23; exact R23.
- rewrite Q24; exact R24.
- rewrite Q25; exact R25.
- rewrite Q26; exact R26.
- rewrite Q27; exact R27.
- rewrite Q3; exact R3.
- rewrite Q4; exact R4.
Qed.

Lemma finish_nil : forall c, CN c -> forall regs m,
RI regs -> LM m ->
RZAc c (mkst regs (0xd5128 : word) m (seg_rom RSEGS)) (t_emit [] K).
Proof. intros. apply AJ_emit_nil; [exact HKnil|]. apply finish; assumption. Qed.

Lemma pc_d27fc : v_addi (0xd51a4 : word) 4 = (0xd51a8 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Lemma loop1 : forall n c, CN c -> forall regs m (k : nat) (b : word) (bs : list byte),
(length bs <= n)%nat ->
RI regs -> LM m ->
getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs)) ->
getr regs 18 = Z_to_bv 64 1 -> getr regs 19 = Z_to_bv 64 (su - 88) ->
(1 <= k < length bs)%nat ->
rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b) ->
rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs)))) ->
rdn RSEGS mem1 b (length bs) = Some bs ->
(bv_unsigned b + Z.of_nat (length bs) <= su - 112 \/ su <= bv_unsigned b)%Z ->
(bv_unsigned b + Z.of_nat (length bs) <= 0x800000000000)%Z ->
(Z.of_nat (length bs) <= 67108864)%Z ->
RZAc c (mkst regs (0xd51b4 : word) m (seg_rom RSEGS))
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K).
Proof.
induction n as [|n IH]; intros c HCN regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b) as Hb.

destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
(Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).

eapply (AJ_writev1_wall RSEGS J SYS regs1 (0xd51a4 : word) m' c W_d51f0 fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
[ exact F_d51f0 | exact E_d51f0 | exact (CN_ck c HCN) | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
- subst m'. rdn_solve.
- subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
- rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
- unfold TASK_SIZE. u_norm. lia.
- unfold TASK_SIZE. u_norm. lia.
- u_norm. lia.
- u_norm. lia.
-
intros k' c' K1 K2 HN' HS'. pose proof (CN_next c c' HCN HN' HS') as HCN'. rewrite pc_d27fc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
+
destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
apply (finish_nil c' HCN'); [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (IH c' HCN' regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
* rewrite length_skipn. lia.
* eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* exact LMm'.
* exact P10.
* rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
* rewrite P18. gres. exact Q18.
* rewrite P19. gres. exact Q20.
* rewrite length_skipn. lia.
* subst m'. unfold at_. rdn_solve.
* subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
* rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
* unfold at_. rewrite length_skipn. u_norm. lia.
* unfold at_. rewrite length_skipn. u_norm. lia.
* rewrite length_skipn. lia.
Qed.

Lemma loop2 : forall n c, CN c -> forall regs m (k : nat) (b0 : word) (bs0 : list byte) (b1 : word) (bs1 : list byte),
(length bs0 + length bs1 <= n)%nat ->
RI regs -> LM m ->
getr regs 10 = Z_to_bv 64 (Z.of_nat k) ->
getr regs 22 = Z_to_bv 64 (Z.of_nat (length bs0) + Z.of_nat (length bs1)) ->
getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 (su - 104) ->
(1 <= k < length bs0 + length bs1)%nat ->
rdn RSEGS m (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 b0) ->
rdn RSEGS m (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs0)))) ->
rdn RSEGS m (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 b1) ->
rdn RSEGS m (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (Z.of_nat (length bs1)))) ->
rdn RSEGS mem1 b0 (length bs0) = Some bs0 ->
rdn RSEGS mem1 b1 (length bs1) = Some bs1 ->
(bv_unsigned b0 + Z.of_nat (length bs0) <= su - 112 \/ su <= bv_unsigned b0)%Z ->
(bv_unsigned b0 + Z.of_nat (length bs0) <= 0x800000000000)%Z ->
(bv_unsigned b1 + Z.of_nat (length bs1) <= su - 112 \/ su <= bv_unsigned b1)%Z ->
(bv_unsigned b1 + Z.of_nat (length bs1) <= 0x800000000000)%Z ->
(Z.of_nat (length bs0) + Z.of_nat (length bs1) <= 67108864)%Z ->
RZAc c (mkst regs (0xd51b4 : word) m (seg_rom RSEGS))
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k (bs0 ++ bs1))) K).
Proof.
induction n as [|n IH]; intros c HCN regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
{ exfalso. lia. }
pose proof RIr as RIr'.
destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
-
destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_le k bs0 bs1 LE).
eapply (AJ_writev2_wall RSEGS J SYS regs1 (0xd51a4 : word) m' c W_d51f0 fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
(Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
[ exact F_d51f0 | exact E_d51f0 | exact (CN_ck c HCN) | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
+ subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
+ subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
{ replace (length bs0 - k)%nat with 0%nat by lia.
rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
+ rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
subst m'. repeat rdn_peel1.
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' c' K1 K2 HN' HS'. pose proof (CN_next c c' HCN HN' HS') as HCN'. rewrite pc_d27fc. rewrite length_app, length_skipn in K2.
destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
apply (finish_nil c' HCN'); [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (IH c' HCN' regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
-- subst m'. repeat rdn_peel1. exact Mb1.
-- subst m'. repeat rdn_peel1. exact Mn1.
-- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
-- exact Bbs1.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
-- exact DISJ1.
-- exact NW1.
-- rewrite length_skipn. lia.
-
destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
(Z.of_nat (length bs0)) (Z.of_nat (length bs1))
(Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
{ eapply LM_store_ok; [exact LMm | exact SOK1]. }
{ replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
{ replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
{ replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
{ eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN |]. clear RUN.
replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
set (m' := wbytes (wbytes m _ _) _ _).
assert (LMm' : LM m').
{ subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
rewrite (skipn_app_ge k bs0 bs1) by lia.
eapply (AJ_writev1_wall RSEGS J SYS regs1 (0xd51a4 : word) m' c W_d51f0 fd
(Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
(Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
(skipn (k - length bs0) bs1) K);
[ exact F_d51f0 | exact E_d51f0 | exact (CN_ck c HCN) | exact FD
| exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
+ subst m'. rdn_solve.
+ subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
+ rewrite word_to_nat_Z by lia.
replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
subst m'. repeat rdn_peel1.
change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k' c' K1 K2 HN' HS'. pose proof (CN_next c c' HCN HN' HS') as HCN'. rewrite pc_d27fc. rewrite length_skipn in K2.
destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
* destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite Q22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
apply (finish_nil c' HCN'); [| exact LMm'].
eapply RI_but; [exact RI1|].
revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
(Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact Q22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (loop1 (length bs1) c' HCN' regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
-- rewrite length_skipn. lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LMm'.
-- exact P10.
-- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
-- rewrite P18. gres. exact Q18.
-- rewrite P19. gres. exact Q20.
-- rewrite length_skipn. lia.
-- subst m'. unfold at_. rdn_solve.
-- subst m'. rewrite length_skipn.
replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
rdn_solve.
-- rewrite length_skipn.
apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- unfold at_. rewrite length_skipn. u_norm. lia.
-- rewrite length_skipn. lia.
Qed.

End Loop.
End FPGEN1.

Ltac wout1 :=
rewrite wbytes_outside;
[ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
| rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].
Section FPGEN2.
Context {fF : FPF} {fC : FPC}.
Variable J : aj_base RSEGS.
Hypothesis SYS : @Qfub.aj_sys fF fC RSEGS J.
Local Notation RZAc md ms K := (AJ J K md ms).

Lemma sw_post_of_LM : forall mem m (su f : Z) (ra s0 s1 s2 s3 s4 s5 s6 can : word) (wb n : Z) (s l bufp bufsz : word),
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
LM su (mem_sw1 mem su ra s0 s1 s2 s3 s4 s5 s6 can wb n s l) m ->
sw_post mem su f bufp bufsz (mem_sw2 m f bufp bufsz).
Proof.
intros mem m su f ra s0 s1 s2 s3 s4 s5 s6 can wb n s l bufp bufsz SUlo SUhi Flo Fhi [E G].
constructor.
- intros x Hx1 Hx2 Hx3. pose proof (u64_range x) as Hx.
unfold mem_sw2. do 3 wout1.
rewrite (E x) by lia.
unfold mem_sw1. do 13 wout1. reflexivity.
- unfold mem_sw2. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
eapply mem_grows_trans; [|exact G].
unfold mem_sw1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]).
apply mem_grows_refl.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
- unfold mem_sw2. rdn_solve.
Qed.

Lemma pc_d2774 : v_addi (0xd511c : word) 4 = (0xd5120 : word).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Theorem ref_stdio_write :
forall regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
(pending extra : list byte) (K : TSet),
getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
(4294967296 + 112 <= su)%Z -> (su <= 0x800000000000)%Z ->
store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112%nat = true ->
(0xea000 <= f)%Z -> (f + 232 <= 0x645560)%Z ->
sw_file mem f wb wp fd bufp bufsz ->
ssp_cells mem can ->
(fd = 1 \/ fd = 2)%Z ->
CK J model ->
(0 <= wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 67108864)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS mem s (length extra) = Some extra ->
ret_ok ret ->
K [] ->
(forall regs' mem' c',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
sw_post mem su f bufp bufsz mem' ->
CNEXT J model c' -> Qfub.same_io model c' ->
RZAc c' (mkst regs' ret mem' (seg_rom RSEGS)) K) ->
RZAc model (mkst regs (0xd5094 : word) mem (seg_rom RSEGS))
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD HCK0 WBP WPhi
LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
pose proof SWF as SWF'. pose proof SSP as SSP'.
destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
{ rewrite <- LENE. symmetry. apply u64_roundtrip'. }

set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
{ subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x645560) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
{ subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }

assert (HK' : forall regs' m c',
getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
LM su mem1 m -> CN J model c' ->
RZAc c' (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) K).
{ intros until c'. intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 XL [XN XS]. apply HK. all: try assumption.
eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
match goal with H : LM _ _ _ |- _ => exact H end. }
pose proof (finish_nil J su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi Hret HKnil M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
pose proof (loop1 J SYS su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
pose proof (loop2 J SYS su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
(getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
(getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
SUlo SUhi Flo Fhi FD Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
pose proof (LM_refl su mem1) as LM1.
destruct (Z.eq_dec wb wp) as [EQ|NEQ].
-
destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
subst wb.
destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN1 |]. clear RUN1.
lazymatch goal with |- AJ _ _ _ (mkst _ _ ?M _) =>
replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
rewrite Z.sub_diag in M96.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
destruct extra as [|x0 extra'].
+
cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
eapply (AJ_writev1_zero RSEGS J SYS regs1 (0xd511c : word) mem1 model W_d5168 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
[ exact F_d5168 | exact E_d5168 | exact HCK0 | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | ].
{ u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
{ unfold TASK_SIZE. u_norm. lia. }
{ unfold TASK_SIZE. lia. }
intros c' HN' HS'. rewrite pc_d2774.
destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. exact HlZ. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (FIN c' (conj HN' HS')); [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
+
eapply (AJ_writev1_wall RSEGS J SYS regs1 (0xd511c : word) mem1 model W_d5168 fd
(Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
[ exact F_d5168 | exact E_d5168 | exact HCK0 | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
* u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
* unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
* unfold TASK_SIZE. u_norm. lia.
* unfold TASK_SIZE. lia.
* cbn [length] in LENE. lia.
* lia.
* intros k c' K1 K2 HN' HS'. rewrite pc_d2774.
destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
-- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
apply (FIN c' (conj HN' HS')); [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(Z.of_nat (length (x0 :: extra'))))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22, HlZ. reflexivity. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (L1 (length (x0 :: extra')) c' (conj HN' HS') regs2 mem1 k s (x0 :: extra')); try lia.
++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
++ exact LM1.
++ exact P10.
++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
++ rewrite P18. gres. exact R18.
++ rewrite P19. gres. exact R19.
++ exact M88.
++ rewrite <- HlZ. exact M80.
++ exact Be.
-
destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
try assumption; try lia.
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN1 |]. clear RUN1. fold mem1.
assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
(getr regs 26) (getr regs 27) regs1).
{ unfold RI. repeat split; assumption. }
eapply (AJ_writev2_wall RSEGS J SYS regs1 (0xd511c : word) mem1 model W_d5168 fd
(Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
[ exact F_d5168 | exact E_d5168 | exact HCK0 | exact FD
| exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
+ u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
+ u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
+ u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
+ rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
+ unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. u_norm. lia.
+ unfold TASK_SIZE. lia.
+ u_norm. lia.
+ u_norm. lia.
+ intros k c' K1 K2 HN' HS'. rewrite pc_d2774. rewrite length_app in K2.
destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
* destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. rewrite R22. f_equal. lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
apply (FIN c' (conj HN' HS')); [|exact LM1].
eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
* destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
(wp - wb + bv_unsigned l))
as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
{ gres. reflexivity. }
{ gres. exact R22. }
{ lia. }
{ lia. }
{ lia. }
eapply (AJ_msteps RSEGS J); [apply (msteps_of_ascatsim RSEGS); exact RUN2 |]. clear RUN2.
apply (L2 (length pending + length extra)%nat c' (conj HN' HS') regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
-- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
-- exact LM1.
-- exact P10.
-- rewrite P22. gres. rewrite R22. f_equal. lia.
-- rewrite P18. gres. exact R18.
-- rewrite P19. gres. exact R19.
-- exact M104.
-- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
-- exact M88.
-- rewrite <- HlZ. exact M80.
-- exact Bp.
-- exact Be.
-- u_norm. lia.
-- u_norm. lia.
Qed.
End FPGEN2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuXQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuXQ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_IMEMCPY : Z := 0x61b18.

Definition imemcpy_spec_U : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (d s n lo : Z) (old src : list byte)
(Q : machine_state -> Prop),
(0 < n -> unpoisoned asegs m A_SB d n) -> (0 < n -> unpoisoned asegs m A_SB s n) -> asan_rt_ok m ->
0 <= d -> d + n <= 2^47 -> 0 <= s -> s + n <= 2^47 -> (64 < n -> app_mem d n /\ app_mem s n) ->
(d + n <= lo \/ bv_unsigned sp <= d) -> (s + n <= lo \/ bv_unsigned sp <= s) ->
a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 n -> 0 <= n < 2^31 -> (s + n <= d \/ d + n <= s) ->
rw_cells asegs m d [CB (Z.to_nat n) old] -> bytes_at asegs m s src -> length src = Z.to_nat n ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 4096 -> bv_unsigned sp mod 16 = 0 ->
mem_inv asegs m -> bv_unsigned ra mod 2 = 0 ->
(forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
munch [(d, d + n); (lo, bv_unsigned sp)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
rw_cells asegs m' d [CB (Z.to_nat n) src] -> bytes_at asegs m' s src ->
stk asegs m' lo (bv_unsigned sp) ->
evt asegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_IMEMCPY) fc None m (seg_rom asegs)).

Section IMemcpy.
Hypothesis OBL_REGION : region_is_poisoned_spec_U.

Local Ltac slow_head x n v Hv :=
step; rewrite (sxb_small v) by lia;
step; rewrite (unsigned_lit (x + n - 1)) by lia; rewrite land7_mod8 by lia;
step; step; step; step;
destruct Hv as [-> | (? & ?)];
[ rewrite (v_sltu_0' (Z_to_bv 64 0) (Z_to_bv 64 0)) by (rewrite !unsigned_lit by lia; lia);
rewrite (unsigned_lit 0) by lia; rewrite Z.land_0_l
| rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 v)) by (rewrite !unsigned_lit by lia; lia);
rewrite (v_slt_1 (Z_to_bv 64 ((x + n - 1) mod 8)) (Z_to_bv 64 v)) by (rewrite !signed_lit by lia; Z.div_mod_to_equations; lia);
rewrite !(unsigned_lit 1) by lia; change (Z.lxor 1 1) with 0; rewrite Z.land_0_r ].

Local Ltac qc_addrs x n :=
sh_norm;
replace (2147450880 + x / 8) with (x / 8 + 2147450880) by lia;
replace (2147450880 + (x + n - 1) / 8) with ((x + n - 1) / 8 + 2147450880) by lia;
rewrite (unsigned_lit (x / 8 + 2147450880)) by lia; rewrite (unsigned_lit ((x + n - 1) / 8 + 2147450880)) by lia;
rewrite !land_m8_64 by lia.

Lemma imemcpy_sound : imemcpy_spec_U.
Proof.
unfold imemcpy_spec_U.
intros until Q. intros UPd UPs RT Hd Hdn Hs Hsn APP SEPd SEPs Ha0 Ha1 Ha2 Hn Hdisj DST SRC SRCL ST LO LOS SPA MI RA K.
subst a0 a1 a2. word_range sp SPR. pose proof alloc_ceiling_ge as ACG.
rt_cell RT 0xe8d28 as GOTF. rt_cell RT 0xf2e99 as FLAG. rt_cell RT 0xe81b8 as GOTSB. rt_cell RT 0xf21b8 as SBC.
apply ro_C8_of_bytes_at in GOTF. apply ro_C8_of_bytes_at in GOTSB. apply ro_C8_of_bytes_at in SBC.
assert (FLAGc : ro_cells asegs m 0xf2e99 [C1 (Z_to_bv 8 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact FLAG]). clear FLAG.

stash SRC.
pose proof (munch_refl [(d, d + n); (lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU0.
unfold A_IMEMCPY. carve_frame 80%nat ST.
step.
do 13 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (RT1 : asan_rt_ok mc) by (eapply (asan_rt_ok_stack m mc lo (bv_unsigned sp)); [exact RT | exact MU0 | exact LO]);
assert (UPd1 : 0 < n -> unpoisoned asegs mc A_SB d n)
by (intros Hn0; eapply unpoisoned_transport; [exact (UPd Hn0) | exact MU0
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]);
assert (UPs1 : 0 < n -> unpoisoned asegs mc A_SB s n)
by (intros Hn0; eapply unpoisoned_transport; [exact (UPs Hn0) | exact MU0
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB s n); try eassumption; unfold A_SB; lia])
end.
clear MU0 UPd UPs RT.
unstash SRC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SRC1 : bytes_at asegs mc s src)
by (eapply bytes_at_transport; [exact SRC | exact MU | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia])
end.
clear SRC.
do 4 step. if_false.
step. step.
step. step.

lazymatch type of FR with rw_cells _ _ ?fa ?fcs =>
assert (TAIL : forall (w x0 x1 x2 x3 x4 x5 x6 x7 y3 y4 y5 y6 z1 z2 z3 z4 z6 z7 z8 : word) (mc : word -> option byte) (oldx : list byte),
munch [(d, d + n); (lo, bv_unsigned sp)] m mc -> wmono asegs m mc -> mem_inv asegs mc -> asan_rt_ok mc ->
rw_cells asegs mc d [CB (Z.to_nat n) oldx] -> bytes_at asegs mc s src ->
stk asegs mc lo (bv_unsigned sp + -80) -> rw_cells asegs mc fa fcs ->
evt asegs Q (MS (mkR w (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x0 x1 x2 sp z1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 z2 z3 z4 (Z_to_bv 64 (bv_unsigned sp + -2152)) z6 z7 z8 s9 s10 s11 y3 y4 y5 y6)
F (Z_to_bv 64 0x62e0c) fc None mc (seg_rom asegs)))
end.
{ clear UPd1 UPs1 RT1 MU WM MI DST SRC1 ST FR GOTF GOTSB SBC FLAGc.
intros w x0 x1 x2 x3 x4 x5 x6 x7 y3 y4 y5 y6 z1 z2 z3 z4 z6 z7 z8 mc oldx MU WM MI RTm DSTm SRCm ST FR.
rt_cell RTm 0xea1c8 as REALC. apply ro_C8_of_bytes_at in REALC. clear RTm.
step. step. step.
(call real_memcpy_specZ); [lia | lia | lia | lia | lia | exact SRCm | exact SRCL | exact DSTm | lia | assumption |].
do 13 step.
eapply K;
[ match goal with H : munch _ m ?mf |- munch _ m ?mf => exact H end
| match goal with H : wmono _ m ?mf |- wmono _ m ?mf => exact H end
| assumption
| match goal with H : rw_cells _ ?mf d [CB _ src] |- _ => exact H end
| match goal with H : bytes_at _ ?mf s src |- _ => exact H end
| release_frame FR ST (bv_unsigned sp); exact ST ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (AD : forall x3 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 a4 a5 a6 a7 s2 (Z_to_bv 64 (s + n)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62d78) fc None mc (seg_rom asegs)))
end.
{ intros x3.
step. step. rewrite (unsigned_lit s) by lia. rewrite (lxor_ones64 s) by lia. if_falsex.
step. step. step.
destruct (Z_lt_le_dec 0 n) as [Hn0 | Hnz]; [destruct (Z.le_gt_cases n 64) as [Hn64 | Hbig]|].
-
rewrite (size_test_n n) by lia. cbv iota.
specialize (UPd1 Hn0). specialize (UPs1 Hn0). clear APP.
assert (Hg : d / 8 <= (d + n - 1) / 8 <= d / 8 + 8) by (Z.div_mod_to_equations; lia).
assert (Hh : s / 8 <= (s + n - 1) / 8 <= s / 8 + 8) by (clear Hg; Z.div_mod_to_equations; lia).
destruct (unpoisoned_word asegs _ _ _ _ (d / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & W1c).
destruct (unpoisoned_word asegs _ _ _ _ ((d + n - 1) / 8 + A_SB) UPd1 ltac:(unfold A_SB; clear Hh; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & W2c).
destruct (unpoisoned_word asegs _ _ _ _ (s / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v1 & Lv1 & V1c).
destruct (unpoisoned_word asegs _ _ _ _ ((s + n - 1) / 8 + A_SB) UPs1 ltac:(unfold A_SB; clear Hg; Z.div_mod_to_equations; lia)) as (v2 & Lv2 & V2c).
unfold A_SB in W1c, W2c, V1c, V2c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (GR0 : forall j, 0 <= j -> d / 8 + j < (d + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (d / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (d / 8 + 2147450880 + j) with ((d / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPd1); lia |];
assert (GS0 : forall j, 0 <= j -> s / 8 + j < (s + n - 1) / 8 ->
ov_read_bytes asegs mc (Z_to_bv 64 (s / 8 + 2147450880 + j)) 1 = Some [Z_to_bv 8 0]);
[ intros j Hj Hjl; apply ov_read1_of_ro;
replace (s / 8 + 2147450880 + j) with ((s / 8 + j) + A_SB) by (unfold A_SB; lia);
apply (unpoisoned_gran0 asegs _ _ _ _ _ UPs1); lia |];
assert (HRLd : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (d + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPd1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro);
assert (HRLs : exists v, ov_read_bytes asegs mc (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (s + n - 1) mod 8 < v)))
by (destruct (unpoisoned_last asegs _ _ _ _ UPs1) as (v & Hro & Hv); exists v; split; [| exact Hv]; apply ov_read1_of_ro; unfold A_SB in Hro; exact Hro)
end.
clear UPd1 UPs1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP2 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((d + n - 1) / 8 - d / 8 - i) = Kn -> 0 <= i -> d / 8 + i < (d + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (d / 8 + 2147450880 + i)) (Z_to_bv 64 ((d + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n - 1)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x63198) fc None mc (seg_rom asegs)))
end.
{ clear GS0 GOTF FLAGc GOTSB SBC Hh HRLd HRLs W1c W2c V1c V2c;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GR0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (d / 8 + i + 1) ((d + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true;
eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]
| if_truex; replace (d / 8 + 2147450880 + i + 1) with (d / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (MID : forall x3 x4 x5 x6 x7 : word,
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
x3 x4 x5 x6 x7 s2 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x62dc4) fc None mc (seg_rom asegs)))
end.
{ intros p3 p4 p5 p6 p7.
clear V1c V2c GS0 GOTF FLAGc Hh HRLs.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. rewrite (size_test_n n) by lia. cbv iota.
do 3 step.
step. replace (d + n + -1) with (d + n - 1) by lia.
do 2 step. do 2 step. do 2 step.
qc_addrs d n.
do 2 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]. }

destruct HRLd as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear W1c W2c Hg.
slow_head d n v Hv; clear HR;
step;
(destruct (Z.eq_dec (d / 8) ((d + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true;
eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]
| if_falsex; replace (d / 8 + 2147450880) with (d / 8 + 2147450880 + 0) by lia;
apply (LOOP2 (Z.to_nat ((d + n - 1) / 8 - d / 8 - 0)) 0); lia ]). }

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (LOOP1 : forall (Kn : nat) (i : Z) (x6 x7 : word),
Z.to_nat ((s + n - 1) / 8 - s / 8 - i) = Kn -> 0 <= i -> s / 8 + i < (s + n - 1) / 8 ->
evt asegs Q (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp t0 t1 t2 sp s1 (Z_to_bv 64 d) (Z_to_bv 64 s) (Z_to_bv 64 n)
(Z_to_bv 64 (s / 8 + 2147450880 + i)) (Z_to_bv 64 ((s + n - 1) / 8 + 2147450880)) (Z_to_bv 64 0) x6 x7
s2 (Z_to_bv 64 (s + n - 1)) (Z_to_bv 64 (d + n)) (Z_to_bv 64 (bv_unsigned sp + -2152)) (Z_to_bv 64 (n + -65)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x63098) fc None mc (seg_rom asegs)))
end.
{ clear W1c W2c V1c V2c GR0 GOTF FLAGc GOTSB SBC Hg TAIL LOOP2 HRLd HRLs MU WM DST SRC1 ST FR RT1;
induction Kn as [|Kn IH]; intros i x6 x7 HK Hi Hig; [lia|];
pose proof (GS0 i Hi Hig) as HR;
step; rewrite ?zxb_zero; clear HR;
step; step; rewrite ?(unsigned_lit 0) by lia; change (Z.lor 0 0) with 0;
step;
destruct (Z.eq_dec (s / 8 + i + 1) ((s + n - 1) / 8)) as [Heq|Hne];
[ if_falsex; step; step; if_true; apply MID
| if_truex; replace (s / 8 + 2147450880 + i + 1) with (s / 8 + 2147450880 + (i + 1)) by lia; apply (IH (i + 1)); lia ]. }

clear W1c W2c GR0 GOTF FLAGc Hg TAIL LOOP2 HRLd MU WM DST SRC1 ST FR RT1.
do 3 step.
step. replace (s + n + -1) with (s + n - 1) by lia.
do 2 step. do 2 step. do 2 step.
qc_addrs s n.
do 2 step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) => destruct cnd end.
2: { apply MID. }

destruct HRLs as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
clear V1c V2c Hh.
slow_head s n v Hv; clear HR;
step;
(destruct (Z.eq_dec (s / 8) ((s + n - 1) / 8)) as [Heq1|Hne1];
[ if_truex; step; step; if_true; apply MID
| if_falsex; replace (s / 8 + 2147450880) with (s / 8 + 2147450880 + 0) by lia;
apply (LOOP1 (Z.to_nat ((s + n - 1) / 8 - s / 8 - 0)) 0); lia ]).
-
rewrite (size_test_big n) by lia. cbv iota.
specialize (UPd1 Hn0). specialize (UPs1 Hn0). destruct (APP Hbig) as [APPd APPs]. clear APP GOTSB SBC.
step. if_truex.
do 5 step.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with STc : stk asegs mc lo ?hi |- _ =>
destruct (stk_split asegs mc lo (bv_unsigned sp - 2160) hi STc ltac:(lia)) as [ST1 ST2]; clear STc end end.
stash SRC1.
eapply (OBL_REGION _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s n lo);
[ exact UPs1 | exact RT1 | exact APPs | lia
| rewrite unsigned_lit by lia; lia | reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1 | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| assumption | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
clear UPs1 RT1.
intros x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 z3 z4 z5 z6 m2 MU2 WM2 MI2 ST1' UPs2 RT2.
assert (UPd2 : unpoisoned asegs m2 A_SB d n)
by (eapply unpoisoned_transport; [exact UPd1 | exact MU2
| intros a k Ha Hk; eapply (shadow_outside_stack A_SB d n); try eassumption; unfold A_SB; lia]).
clear UPd1.
lazymatch type of MU2 with munch _ ?mc _ =>
transport_after_call asegs mc m2 MU2 WM2; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
unstash SRC1.
assert (SRC2 : bytes_at asegs m2 s src)
by (eapply bytes_at_transport; [exact SRC1 | exact MU2 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear MU2 WM2 SRC1.
replace (ret_pc (Z_to_bv 64 0x630c8)) with (Z_to_bv 64 0x630c8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. rewrite (size_test_big n) by lia. cbv iota.
step. if_truex.
do 4 step.
step.
stash SRC2.
eapply (OBL_REGION _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d n lo);
[ exact UPd2 | exact RT2 | exact APPd | lia
| rewrite unsigned_lit by lia; lia | reflexivity | reflexivity
| rewrite unsigned_lit by lia; exact ST1' | exact LO | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
| exact MI2 | rewrite unsigned_lit by lia; reflexivity |].
rewrite ?unsigned_lit by lia.
clear UPd2 RT2 UPs2.
intros p0 p1 p2 q1 q2 q3 q4 q5 q6 q7 r3 r4 r5 r6 m3 MU3 WM3 MI3 ST1'' UPd3 RT3.
lazymatch type of MU3 with munch _ ?mc _ =>
transport_after_call asegs mc m3 MU3 WM3; try match goal with H : mem_inv asegs mc |- _ => clear H end end.
unstash SRC2.
assert (SRC3 : bytes_at asegs m3 s src)
by (eapply bytes_at_transport; [exact SRC2 | exact MU3 | cbn [disjoint_from]; rewrite SRCL, Z2Nat.id by lia; lia]).
clear MU3 WM3 SRC2.
replace (ret_pc (Z_to_bv 64 0x631c4)) with (Z_to_bv 64 0x631c4) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
do 4 step.
step. if_true.
eapply TAIL; [exact MU | exact WM | exact MI3 | exact RT3 | exact DST | exact SRC3
| eapply stk_merge; [exact ST1'' | exact ST2 | lia] | exact FR].
-
rewrite (size_test_big n) by lia. cbv iota.
clear UPd1 UPs1 APP GOTSB SBC.
step. if_falsex.
step.
step. step. rewrite (unsigned_lit d) by lia. rewrite (lxor_ones64 d) by lia. if_falsex.
step. step. rewrite (size_test_big n) by lia. cbv iota.
step. if_falsex.
step.
eapply TAIL; [exact MU | exact WM | assumption | exact RT1 | exact DST | exact SRC1 | exact ST | exact FR]. }

clear UPd1 UPs1 GOTF FLAGc GOTSB SBC TAIL MU WM DST SRC1 ST FR RT1 APP.
destruct (Z.eq_dec d s) as [Eds | Nds].
- rewrite <- Eds in *. step. if_truex. apply AD.
- step. if_falsex.
step.
destruct Hdisj as [Hsd | Hds].
+ if_falsex. step. if_falsex. apply AD.
+ if_truex. apply AD.
Qed.
End IMemcpy.
End RC__1.
