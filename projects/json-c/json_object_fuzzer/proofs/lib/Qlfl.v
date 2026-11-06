(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 Q5Rg Qc3B QZAi QfYR QfcC Lib.SepCache QnDM_c1 QDUx Q9Ay Qy5Y Qbf8 QSzV QvBB QmBS QKwd QTp6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import Qbf8 QSzV QvBB.Mq1 QmBS.Mq0 QKwd.
Import QTp6.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.

Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
(sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ (J = ssJ /\ False))%Z.

Section RF.
Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
Hypothesis Hp : 0 <= p < zlength txt.
Hypothesis Hnul : znth txt p = 0.
Hypothesis T0 : 0 < T.
Hypothesis T1 : T + 2^41 <= 2^63.

Notation RFI := (RFJ T txt p true J).

#[using="Type"] Lemma RFI_ok : forall kmin c f, RFI kmin c f -> sh_ok T txt f.
Proof. intros kmin c f (OK & _). exact OK. Qed.

#[using="Hp"] Lemma RFI_rpos : forall kmin c f, RFI kmin c f -> 0 <= sh_rpos f <= p + 1.
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
destruct (sh_stdio f) eqn:ES; [destruct (SS eq_refl) as (N1 & N2 & _); lia | destruct (NS eq_refl) as (N1 & N2 & N3); lia].
Qed.

#[using="Hp"] Lemma rf_getc_fast : forall kmin c f, RFI kmin c f ->
T + sh_rpos f <> rf_rend T p true f ->
sh_getc f = (znth txt (sh_rpos f), mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in NE. unfold sh_getc. rewrite Hbuf.
destruct (sh_stdio f) eqn:ES; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). rewrite N1.
destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE']; [exfalso; lia|]. reflexivity.
- reflexivity.
Qed.

#[using="Hp"] Lemma rf_getc_fast_lt : forall kmin c f, RFI kmin c f -> c <> 0 ->
T + sh_rpos f <> rf_rend T p true f -> 0 <= sh_rpos f < zlength txt.
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
- destruct (SS eq_refl) as (N1 & N2 & N3 & _). lia.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). lia.
Qed.

#[using="Hp T1"] Lemma rf_getc_slow : forall kmin c f, RFI kmin c f ->
T + sh_rpos f = rf_rend T p true f ->
sh_stdio f = true /\ J = ssJ /\ sh_n f = p /\ sh_rpos f = p /\ 0 <= sh_cnt0 f <= sh_rpos f.
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) E. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in E. destruct (sh_stdio f) eqn:ES.
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). repeat split; try assumption; unfold M64 in E; lia.
- exfalso. unfold M64 in E. lia.
Qed.

Ltac crush := repeat progress (repeat split; try reflexivity; try discriminate; try assumption; try lia;
try lazymatch goal with |- (_ -> _) => intro end).

#[using="BYT Hp Hnul"] Lemma RFI_getc : forall kmin c f, RFI kmin c f -> c <> 0 -> RFI (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold zlength in *.
assert (R0 : forall i, 0 <= i < Z.of_nat (length txt) -> 0 <= znth txt i < 256).
{ intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply Qy5Y.znth_In'. unfold zlength. lia. }
destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
destruct st; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). subst n.
destruct (Z.eqb_spec rpos p) as [E|NE]; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
+ unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
+ pose proof (R0 rpos ltac:(lia)).
assert (SN : sn = false) by (destruct sn; [specialize (N3 eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). subst sn. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
pose proof (R0 rpos ltac:(lia)). specialize (KM eq_refl).
unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
Qed.

#[using="Hp"] Lemma RFI_unget : forall kmin c f, RFI kmin c f -> 1 <= kmin -> RFI (kmin - 1) c (sh_unget f).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hk. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
unfold RFJ, sh_unget, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
- destruct st.
+ destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). specialize (N3 eq_refl). crush.
+ destruct (NS eq_refl) as (N1 & _). discriminate N1.
- specialize (KM eq_refl). destruct st.
+ destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). crush.
+ destruct (NS eq_refl) as (N1 & N2 & N3). crush.
Qed.

#[using="Type"] Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
Proof. intros [b r c n st sn]. unfold sh_unget. cbn. destruct sn; reflexivity. Qed.
#[using="Type"] Lemma rf_unget_eq : forall f, sh_shlim_neg f = false ->
sh_unget f = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).
Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
#[using="Type"] Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
End RF.

Open Scope bv_scope.

Lemma shgetc_callJ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells rsegs m Fp (rf_cells T p true f J) ->
RFJ T txt p true J kmin c f ->
(T + sh_rpos f = rf_rend T p true f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros FC RJ SLOW TXT Hp BY SSP T0 T1 SEP ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
pose proof RJ as RJ'. destruct RJ' as (OK & Rc & CC & KM & NS & SS).
assert (Hp2 : (0 <= p < zlength txt)%Z).
{ destruct TXT as (Htxt & _ & _ & _ & _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. }
destruct (rf_getc_slow T txt p J Hp2 T1 kmin c f RJ SLOW) as (ST0 & EJ & Hn & Hrp & Hc0).
exfalso. destruct (SS ST0) as (X1 & X2 & X3 & X4 & [X5 FF]). exact FF.
Qed.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 QlEo_c1 Q2qa Q4J3 QytA Qnxq QJE4 QWTl QPjm QUZl Q7S0 Ql2m QGeV QLsg QkQT QlkP QM7w QXxF QCwx QFqQ Q98Z QkLq QnOf QdZ1 Qv4L QQbX QnkH Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb QmBS.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rsmall_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RSMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes rsegs RMED_CNT 4 with Some bs => bs | None => [] end).

#[using="Type"] Lemma rsmall_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
#[using="Type"] Lemma rmed_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.

#[using="Type"] Lemma rsmall_cnt_read : forall m sc i, mem_inv rsegs m -> 0 <= sc < 9 -> 0 <= i < 3 ->
ov_read_bytes rsegs m (wa (RSMALL_CNT + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof.
intros m sc i MI Hsc Hi.
destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
rewrite (bytes_at_read rsegs m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
unfold small_cnt. rewrite !Nat2Z.id.
Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.

#[using="Type"] Lemma rmed_cnt_read : forall m i, mem_inv rsegs m -> 0 <= i < 4 ->
ov_read_bytes rsegs m (wa (RMED_CNT + i)) 1 = Some [b8 (med_cnt i)].
Proof.
intros m i MI Hi.
destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite (bytes_at_read rsegs m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.

Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

#[using="SZ"] Lemma rhalve_big_walk : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists a2' a3',
ms' = MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec44) fc None m (seg_rom rsegs))
(MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec30) fc None m (seg_rom rsegs)).
Proof.
induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
- cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
- cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
step. rewrite (unsigned_lit (size * cnt)) by lia.
step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
+
rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
rewrite (QDUx.Mq9.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
+ rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
#[using="Type"] Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
intros H.
assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
destruct (Z.eq_dec n 1) as [->|NE].
- change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
- replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

#[using="UR"] Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists a3' a4',
ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec30) fc None m (seg_rom rsegs))
(MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec08) fc None m (seg_rom rsegs)).
Proof.
induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
- change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
- cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).

step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
+
replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
step. apply evt_done. do 2 eexists. reflexivity.
+ replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).

step. rewrite (wz_unsigned cnt) by lia. rewrite (QDUx.Mq9.srliw_small cnt 1) by lia.
step. rewrite (wz_unsigned cnt) by lia. step.
assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.

step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
*
assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
{ rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
*
step.
assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
apply evt_done. do 2 eexists. reflexivity.
Qed.

#[using="UR"] Lemma rhalve_even_walk : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists a3' a4',
ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec30) fc None m (seg_rom rsegs))
(MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec00) fc None m (seg_rom rsegs)).
Proof.
intros until m; intros CR C32 MI; unfold rcnt_regs.

step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
-
assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
step. step. apply evt_done. do 2 eexists. reflexivity.
- assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
End HALVE2.

Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof.
unfold cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
- pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

#[using="RC__ MR SC UR"] Lemma rcount_walk :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
mem_inv rsegs m ->
evt rsegs (fun ms' => exists a2' a3' a4',
ms' = MS (rcnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec44) fc None m (seg_rom rsegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xceba4) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros MI.
pose proof (size_class_range sc SC) as SZR.
pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
pose proof rcnt0_range as C0R.
unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.

pose proof (rmrep_usage_read st m sc (wa (6566376 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
step. clear RDU.

step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).

step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
-
apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].

step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
step. clear RDM. rewrite zxb_b8 by lia.

eapply evt_cut.
{ eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
eapply evt_mono.
{ eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
-
assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.

step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
replace (wa (159656 + 3 * sc + 0)) with (Z_to_bv 64 (159656 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
step. clear RD0. rewrite zxb_b8 by lia.

step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
{ replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].

pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
replace (wa (159656 + 3 * sc + 1)) with (Z_to_bv 64 (159656 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
step. clear RD1. rewrite zxb_b8 by lia.
step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
{ replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].

pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
replace (wa (159656 + 3 * sc + 2)) with (Z_to_bv 64 (159656 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
step. clear RD2. rewrite zxb_b8 by lia. step.
apply evt_done. do 3 eexists. reflexivity.
Qed.
End COUNT.

Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="SZ C0"] Lemma rcnt2_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (if big then 0xcec6c else 0xcecb0)) fc None m (seg_rom rsegs))
(MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xcec44) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros MI. unfold rcnt_regs.
assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.

step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.

step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
-
assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).

step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
-
step. rewrite ?unsigned_lit by lia. step. step.
assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
{ unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
{ rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
rewrite EV. clear EV.
assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).

step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qv4L.Mq0 QnkH.Mq2 QmBS.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
evt rsegs (fun ms' => exists (a1' a2' : word),
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom rsegs)
/\ stk rsegs m lo (bv_unsigned sp))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcf200) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR' MI FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.

step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

step. step. step. step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.

End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QTp6.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QDUx.Mq0 Q9Ay.Mq3 Q9Ay.Mq4 Q9Ay.Mq5 Q9Ay.Mq6 Q9Ay.Mq7 Q9Ay.Mq8 QJE4.Mq3.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq1 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 QnOf.Mq0 QdZ1.Mq3 Qv4L.Mqa QQbX.Mq3 Qn9M.Mq0 Qv4L.Mq8 Qi8L.Mq4 QdZ1.Mq2 QQbX.Mq2 Qv4L.Mq0 QnkH.Mq2 QnkH.Mqb.
Import QmBS.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

#[using="MR SC CLO AMS"] Lemma ras_entry_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
a0 = Z_to_bv 64 sc ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' : word) m' junk,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 rc_canary a1' (pw st (active st sc)) a3 a4 a5 a6 a7
a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (match active st sc with None => 0xceb80 | Some _ => 0xcea04 end)) fc None m' (seg_rom rsegs)
/\ rw_cells rsegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ stk rsegs m' lo (bv_unsigned sp + -144)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep st m')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros HA ST LO MI. subst a0.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & G6) & _). unfold wz in G4.
unfold ralloc_slot_entry, alloc_ceiling, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD in *.

step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.

step. step. step. step. step. step. step. step. step. step.
rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]) end.
pose proof (rmrep_active_read st _ sc (wa (6566376 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
step. clear RDA.

step.
replace (6566368 + sc * 8 + 88) with (6566376 + 80 + 8 * sc) by lia.
replace (6566368 + sc * 8) with (6566368 + 8 * sc) by lia.
lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.

step. if_cases K; zify_cond K.
- destruct (active st sc) as [g|] eqn:HA.
{ exfalso. pose proof (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _).
unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
- destruct (active st sc) as [g|] eqn:HA.
2:{ exfalso. apply K. reflexivity. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.

Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

#[using="RC__ MR MSL AVR"] Lemma rt1_fin_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr <> 0 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb40) fc None m (seg_rom rsegs))
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea04) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros AVNZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
pose proof (sxv_range (m_avail mr)) as RA.

step. rewrite sx32_wz_sxv by lia.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
{ exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
step. step.
apply evt_done. reflexivity.
Qed.

#[using="RC__ MR MSL"] Lemma rt1_deq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr = 0 -> m_freed mr = 0 -> mem_inv rsegs m ->
evt rsegs (fun ms' =>
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea28) fc None m (seg_rom rsegs))
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea04) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.

step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. unfold pw, wz. reflexivity.
Qed.

#[using="MR MSL SC FRR"] Lemma rt1_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea68) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_active sc (m_next mr) st) m')
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea04) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
pose proof (sxv_range (m_freed mr)) as RF.

step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. step.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
{ exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.

clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (6566376 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6566376 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.

step.
apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

#[using="MR MSL SC"] Lemma rdeq_self_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_next mr = Some g -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xceb80) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (put_meta g (clr mr) (set_active sc None st)) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea28) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step.

pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (6566376 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
rraw_store_finish0 (6566376 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
set (st1 := set_active sc None st) in MR1.
assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).

rmeta_open G MUg WMg.
rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
st1. st1.
rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.

pose proof (rmrep_active_read _ _ sc (wa (6566376 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

#[using="MR MSL SC HA"] Lemma rdeq_other_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
mem_inv rsegs m ->
let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
let st3 := set_active sc (Some nx) st2 in
let st4 := put_meta g (clr mr) st3 in
evt rsegs (fun ms' => exists (a1' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea68) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
/\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep st4 m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea28) fc None m (seg_rom rsegs)).
Proof.
intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _).
assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
unfold RCTX, RMLOCK, RSSP_GUARD in *.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.

rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
step. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmchunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. step. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmchunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

pose proof (rmrep_active_read st2 _ sc (wa (6566376 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.

step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. clear CH. step.

pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st2) sc (wa (6566376 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
rraw_store_finish0 (6566376 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
fold st3 in MR3.
assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).

rmeta_open G MUg WMg.
rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
replace (get_meta_rec st3 g) with mr in CH.
2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.

pose proof (rmrep_active_read _ _ sc (wa (6566376 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End DEQ.

Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

#[using="RC__ MR MSL FRR MW"] Lemma rm_act_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
full_skip st g = false -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' : word),
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea94) fc None m (seg_rom rsegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea68) fc None m (seg_rom rsegs)).
Proof.
intros until fc. intros NSK MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (QDUx.Mqb.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{  apply evt_done. do 2 eexists. reflexivity. }

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
{ apply evt_done. do 2 eexists. reflexivity. }
exfalso. unfold full_skip in NSK. fold mr f in NSK.
assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

#[using="f MR MSL SC FRR MW"] Lemma rm_skip_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea94) fc None m' (seg_rom rsegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xcea68) fc None m (seg_rom rsegs)).
Proof.
intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (QDUx.Mqb.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.

step. clear CH.

pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok rsegs _ _ (actives st) sc (Z_to_bv 64 (6566376 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6566376 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
step. rewrite sx32_wz_sxv by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End M.

End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QFkE Q6y7 Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QTp6.
Import Q2qa.Mq1 Q4J3.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QJE4.Mq4 Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq3 QFkE Q6y7 QDUx.Mq6 QJE4.Mq2 Q3o5.Mq0.
Import Q9A7.Mq0.
Import QCwx.Mq1 QFqQ.Mq0 Q98Z.Mq2 QkLq.Mq0 QkLq.Mq1 Q98Z.Mq1 QnOf.Mq0.
Import Qv4L.Mq4 Qv4L.Mq5 Qv4L.Mq6 QmBS.Mq4 QdZ1.Mq1.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
(st' : mstate) (s' : PState) : machine_state -> Prop :=
fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
/\ rmrep st' m'
/\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 6434236 <= a < 6434240) m m'
/\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
/\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
/\ c_brk (ctx st') = c_brk (ctx st)
/\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

#[using="Type"] Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> 6434236 <= a < 6434240 -> ~ rfree_fp st lo sp a.
Proof.
intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [[A|[A|A]]|[A|A]].
- lia.
- unfold RCTX in A. lia.
- destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
- destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.

#[using="Type"] Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
(s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
munch [(slo, shi); (6434236, 6434240); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
alloc_ceiling <= slo ->
rmrep (drop_region rid st2) m5.
Proof.
intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). unfold alloc_ceiling in RBC.
eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
assert (LOW : a < alloc_ceiling /\ ~ (6434236 <= a < 6434240) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
{ destruct HF as [HF|HF].
- split; [| split].
+ destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
* unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold QW7x.Mq0.RPAGE_SIZE in C; lia.
* destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). unfold alloc_ceiling in RC. lia.
* destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold alloc_ceiling in RC. lia.
* destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
* unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
+ intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
+ intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
* unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold QW7x.Mq0.RPAGE_SIZE in C; lia.
* destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
* destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> rid).
{ intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
* destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
* unfold RGOT_SSP in C. lia.
* unfold RSSP_GUARD in C. lia.
- destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). unfold alloc_ceiling in RC.
split; [lia|]. split; [lia|].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

#[using="Type"] Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

#[using="Type"] Lemma bytes4_range (x0 x1 x2 x3 : byte) :
0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof.
pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

#[using="Type"] Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof.
pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
rewrite le4_bytes by lia. unfold b8.

f_equal; [|f_equal; [|f_equal; [|f_equal]]];
(apply bv_eq; rewrite Z_to_bv_unsigned;
match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
Z.div_mod_to_equations; lia).
Qed.

#[using="Type"] Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
(st : mstate) (blk : block) (off : Z) (errv : word),
CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
rmrep st m -> mem_inv rsegs m ->
stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
a0 = Z_to_bv 64 (blk_addr blk) ->
rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
(rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof using LO TP.
intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
pose proof (ci_ticks _ _ C) as TK.
pose proof (KINV_of_CINV _ _ C) as K0.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
assert (off' = off) as ->.
{ rewrite HA in OA. unfold UNIT in OA. lia. }
clear OA.
set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
pose proof (ci_gmetas _ _ C b g HB) as GO.
destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
cbn [aadd fst snd] in C3, C2, C1, OFF.

assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
{ rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : bv_unsigned tp + -164 = 6434236) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof LO as LOv. unfold alloc_ceiling in LOv.

assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
{ unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
assert (P16m : snd pf mod 16 = 0).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
unfold UNIT, IB in *.
assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (unfold alloc_ceiling in RBC; pose proof (round_up_pg_ge (r_len r)); lia).
assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x645000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).

clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
{ unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
destruct HB as [ai Hgh].

assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
pose proof (shiftr5_range v3) as SR5.
destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].

assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
exists x : byte, bytes_at rsegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
{ intros q Fq Hq.
assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
destruct (SH _ r Hr Kr) as [WRr _].
assert (W1 : wr_at rsegs m (r_base r + snd q) 1).
{ destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); unfold alloc_ceiling in RBC; lia|].
intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }

unfold free.
eapply (rimplT_bind m (free_hdr st pf) _ s
(fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
{ unfold free_hdr, get_meta. apply rimplT_guard. intros _.
apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
rewrite V31 in G12, G13, G14, G16.
set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
assert (Fe : fst e = fst b) by reflexivity.
assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
{ unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }

pose proof (go_sc _ _ _ GO) as GSC.
assert (WALK : forall r32 : Z,
(160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
/\ bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
/\ bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
(if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
evt rsegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
{ intros r32 BIG RSVLE RB0r RE0.
eapply evt_mono.
{ eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
all: rewrite ?EB, ?V31.
- lia.
- rewrite Fp. exact Hr.
- rewrite A0, HAp. apply unsigned_lit. lia.
- exact P16m.
- rewrite Sp, Sc. lia.
- unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
- exact PHI.
- replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
- replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
- replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
- replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
- exact Hgh.
- reflexivity.
- exact (go_slot _ _ _ GO).
- destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
- exact (go_mem _ _ _ GO).
- exact AR1.
- exact G15.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
- lia.
- rewrite (go_freeable _ _ _ GO). lia.
- lia.
- pose proof (go_maplen _ _ _ GO). lia.
- exact G12.
- exact G13.
- exact G14.
- intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
- intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
- intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
unfold UNIT in G17.
replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
rewrite Z.div_mul in G17 by lia. lia.
- lia.
- exact S16.
- rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
- rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
- exact BIG.
- exact RSVLE.
- exact RB0r.
- exact RE0.
- intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
clear - HD HAp SZ. lia.  }
intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }

assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
{ intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
{ rewrite Se, Cb. unfold UNIT, IB. lia. }
assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
{ rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
{ rewrite Se, Cb. unfold UNIT, IB. lia. }

unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
apply rimplT_if; intros HR5.
-
apply Z.leb_le in HR5.
apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
apply rimplT_rd32.
destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0.
destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1.
destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
apply rimplT_guard; intros G21. apply Z.leb_le in G21.
apply rimplT_rd8. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
apply rimplT_guard; intros G22. apply Z.leb_le in G22.
apply rimplT_rd8. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
apply rimplT_ret. rewrite V31.
specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).

apply (WALK r32).
+ intros _. split; [exact G20|]. split; [lia|]. split.
* rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
-- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
-- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
* rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
+ rewrite H160, <- DIFF. exact G22.
+ rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
+ rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
-
apply Z.leb_gt in HR5.
apply rimplT_guard; intros G22. apply Z.leb_le in G22.
apply rimplT_rd8. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
apply rimplT_ret. rewrite V31.
specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).

apply (WALK 0).
+ intros H. exfalso. clear -H V160. lia.
+ rewrite H160, <- DIFF. exact G22.
+ rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
+ rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
set (st1 := hdr_st st pf) in *.
assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
{ intros k Hk. unfold pf; cbn [aadd fst snd].
assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
destruct CS as [-> |[-> | ->]];
[exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
|exists lo8|exists v3];
[rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
{ intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
assert (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
{ destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
{ destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }

assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
{ intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
apply rimplT_guard. intros _.
apply rimplT_if; intros HC.
-
apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
apply rimplT_ret.
eapply evt_mono.
{ eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
intros ms' TPo. unfold rftriv_post in TPo.
destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
split; [exact MR'|].
split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
split; [intros rid r' H; exact H|].
split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
split; reflexivity.
-

assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
{ apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
eapply rimplT_evt.
{ eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
{ intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
assert (K1 : KINV st1 LB' 0).
{ unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
assert (L1 : LPRE st1 LB' 0 g b i).
{ unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
assert (OOK1 : oracle_ok m m1 st1).
{ unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
[exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].

intros st2 mi ms3 NQ. unfold rntf_q in NQ.
destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
rewrite unsigned_lit in ST3, PE3 by lia.
replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
replace (ret_pc (Z_to_bv 64 0xcde18)) with (Z_to_bv 64 0xcde18) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
assert (FR3' : rw_cells rsegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
destruct mi as [[bm len]|].
+
cbv beta iota.
destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). unfold alloc_ceiling in R2C.
assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x645000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
pose proof (round_up_pg_ge (r_len r2)) as RU2.
eapply rimplT_evt.
{ eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
intros ms4 FM. unfold rfmun_post in FM.
destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
eapply (rimplT_munmap m (conc st2 bm) len _ s).
{ eapply rmunmap_spec.
- rewrite unsigned_lit by lia. exact ST4.
- exact ERR4.
- exact MI4.
- pose proof MR4 as (_ & _ & (_ & _ & _ & _ & _ & VML4) & _). exact VML4.
- unfold RVMLOCK. lia.
- rewrite Lr2, mmap_len_round. unfold RVMLOCK. lia.
- unfold wz. reflexivity.
- unfold wz. reflexivity.
- lia.
- rewrite Lr2, mmap_len_round. lia.
- lia.
- rewrite unsigned_lit by lia. lia.
- rewrite ETP, unsigned_lit by lia. lia.
- rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
- rewrite ETP, Lr2, mmap_len_round. lia.
- rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
rewrite (munmap_ok_range_val a ltac:(destruct a; cbn in ERNG |- *; [lia| exact Logic.I])).
apply rimplT_ret.
replace (ret_pc (Z_to_bv 64 0xcde48)) with (Z_to_bv 64 0xcde48) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.

assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
{ eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
rewrite ?ETP. cbn [outside]. repeat split; lia. }
eapply evt_mono.
{ eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
intros ms' FIN. unfold rffin_post in FIN.
destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
split.
{
assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
{ intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
{ intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 6434236 <= a < 6434240)); [| exact NC].
cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
{ intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 6434236 <= a < 6434240)); [| exact NC].
cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia | right; left; apply DR; lia]). }
eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 6434236 <= a < 6434240)); [| exact NC].
cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia]). }
split.
{ intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
split.
{ intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
split; [exact EB3|].
intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
+

cbv beta iota. cbn in RES3. subst a1v.
apply rimplT_ret.
eapply evt_mono.
{ eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
intros ms' FIN. unfold rffin_post in FIN.
destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 6434236 <= a < 6434240)); [| exact NC].
cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
split; [intros rid r' H; rewrite <- ER3; exact H|].
split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
split; [exact EB3|].
intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.

End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeTw Q1BE Quzq QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1 Q5Rg Qc3B.
Import QZAi.Mq1 QZAi QfYR QfcC.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
Import QnDM_c1 QDUx Q9Ay Qy5Y.
Import QeTw Q1BE QvBB.Mq2 QmBS.Mq5 Quzq.
Import QBpX.
Import ListNotations. Unset Keyed Unification. Local Ltac QJE4.decide_ifs ::= QJE4.mkr__decide_ifs_6. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4.
Open Scope Z_scope.

Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
(sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
(sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
(sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
(w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ (J = ssJ /\ False))%Z.

Section RF.
Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
Hypothesis Hp : 0 <= p < zlength txt.
Hypothesis Hnul : znth txt p = 0.
Hypothesis T0 : 0 < T.
Hypothesis T1 : T + 2^41 <= 2^63.

Notation RFI := (RFJ T txt p true J).

#[using="Type"] Lemma RFI_ok : forall kmin c f, RFI kmin c f -> sh_ok T txt f.
Proof. intros kmin c f (OK & _). exact OK. Qed.

#[using="Hp"] Lemma RFI_rpos : forall kmin c f, RFI kmin c f -> 0 <= sh_rpos f <= p + 1.
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
destruct (sh_stdio f) eqn:ES; [destruct (SS eq_refl) as (N1 & N2 & _); lia | destruct (NS eq_refl) as (N1 & N2 & N3); lia].
Qed.

#[using="Hp"] Lemma rf_getc_fast : forall kmin c f, RFI kmin c f ->
T + sh_rpos f <> rf_rend T p true f ->
sh_getc f = (znth txt (sh_rpos f), mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in NE. unfold sh_getc. rewrite Hbuf.
destruct (sh_stdio f) eqn:ES; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). rewrite N1.
destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE']; [exfalso; lia|]. reflexivity.
- reflexivity.
Qed.

#[using="Hp"] Lemma rf_getc_fast_lt : forall kmin c f, RFI kmin c f -> c <> 0 ->
T + sh_rpos f <> rf_rend T p true f -> 0 <= sh_rpos f < zlength txt.
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
- destruct (SS eq_refl) as (N1 & N2 & N3 & _). lia.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). lia.
Qed.

#[using="Hp T1"] Lemma rf_getc_slow : forall kmin c f, RFI kmin c f ->
T + sh_rpos f = rf_rend T p true f ->
sh_stdio f = true /\ J = ssJ /\ sh_n f = p /\ sh_rpos f = p /\ 0 <= sh_cnt0 f <= sh_rpos f.
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) E. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
unfold rf_rend in E. destruct (sh_stdio f) eqn:ES.
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). repeat split; try assumption; unfold M64 in E; lia.
- exfalso. unfold M64 in E. lia.
Qed.

Ltac crush := repeat progress (repeat split; try reflexivity; try discriminate; try assumption; try lia;
try lazymatch goal with |- (_ -> _) => intro end).

#[using="BYT Hp Hnul"] Lemma RFI_getc : forall kmin c f, RFI kmin c f -> c <> 0 -> RFI (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold zlength in *.
assert (R0 : forall i, 0 <= i < Z.of_nat (length txt) -> 0 <= znth txt i < 256).
{ intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply Qy5Y.znth_In'. unfold zlength. lia. }
destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
destruct st; cbn [negb].
- destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). subst n.
destruct (Z.eqb_spec rpos p) as [E|NE]; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
+ unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
+ pose proof (R0 rpos ltac:(lia)).
assert (SN : sn = false) by (destruct sn; [specialize (N3 eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
- destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). subst sn. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
pose proof (R0 rpos ltac:(lia)). specialize (KM eq_refl).
unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
Qed.

#[using="Hp"] Lemma RFI_unget : forall kmin c f, RFI kmin c f -> 1 <= kmin -> RFI (kmin - 1) c (sh_unget f).
Proof.
intros kmin c f (OK & Rc & CC & KM & NS & SS) Hk. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
unfold RFJ, sh_unget, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
- destruct st.
+ destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). specialize (N3 eq_refl). crush.
+ destruct (NS eq_refl) as (N1 & _). discriminate N1.
- specialize (KM eq_refl). destruct st.
+ destruct (SS eq_refl) as (N1 & N2 & N3 & N4 & [N5 FF]). crush.
+ destruct (NS eq_refl) as (N1 & N2 & N3). crush.
Qed.

#[using="Type"] Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
Proof. intros [b r c n st sn]. unfold sh_unget. cbn. destruct sn; reflexivity. Qed.
#[using="Type"] Lemma rf_unget_eq : forall f, sh_shlim_neg f = false ->
sh_unget f = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).
Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
#[using="Type"] Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
End RF.

Open Scope bv_scope.

Lemma shgetc_callJ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
rw_cells usegs m Fp (rf_cells T p true f J) ->
RFJ T txt p true J kmin c f ->
(T + sh_rpos f = rf_rend T p true f)%Z ->
rtext T txt pre post -> p = zlength pre -> bytes_at usegs m T (zbytes txt) -> ssp_cells m canary ->
(0 < T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk usegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(T + zlength txt <= q - 160 \/ q <= T)%Z ->
(ssp_guard + 8 <= q - 160)%Z ->
(T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv usegs m ->
evt usegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 SHGETC) fc None m (seg_rom usegs)).
Proof.
intros until canary. intros FC RJ SLOW TXT Hp BY SSP T0 T1 SEP ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
pose proof RJ as RJ'. destruct RJ' as (OK & Rc & CC & KM & NS & SS).
assert (Hp2 : (0 <= p < zlength txt)%Z).
{ destruct TXT as (Htxt & _ & _ & _ & _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. }
destruct (rf_getc_slow T txt p J Hp2 T1 kmin c f RJ SLOW) as (ST0 & EJ & Hn & Hrp & Hc0).
exfalso. destruct (SS ST0) as (X1 & X2 & X3 & X4 & [X5 FF]). exact FF.
Qed.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq9 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w QXxF.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq4 Q98Z.Mq5 QkLq QkLq.Mq3 QnOf QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QnkH.Mqm QmBS.Mq6.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rsmall_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes usegs RSMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
Eval vm_compute in (match image_bytes usegs RMED_CNT 4 with Some bs => bs | None => [] end).

#[using="Type"] Lemma rsmall_cnt_ro : forall m, mem_inv usegs m -> ro_cells usegs m RSMALL_CNT [CB 27 rsmall_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RSMALL_CNT; lia | unfold RSMALL_CNT; cbn; lia]. Qed.
#[using="Type"] Lemma rmed_cnt_ro : forall m, mem_inv usegs m -> ro_cells usegs m RMED_CNT [CB 4 rmed_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image usegs m); [exact MI | vm_compute; reflexivity | unfold RMED_CNT; lia | unfold RMED_CNT; cbn; lia]. Qed.

#[using="Type"] Lemma rsmall_cnt_read : forall m sc i, mem_inv usegs m -> 0 <= sc < 9 -> 0 <= i < 3 ->
ov_read_bytes usegs m (wa (RSMALL_CNT + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof.
intros m sc i MI Hsc Hi.
destruct (rsmall_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
replace (RSMALL_CNT + 3 * sc + i) with (RSMALL_CNT + (3 * sc + i)) by lia.
rewrite (bytes_at_read usegs m RSMALL_CNT rsmall_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
unfold small_cnt. rewrite !Nat2Z.id.
Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.

#[using="Type"] Lemma rmed_cnt_read : forall m i, mem_inv usegs m -> 0 <= i < 4 ->
ov_read_bytes usegs m (wa (RMED_CNT + i)) 1 = Some [b8 (med_cnt i)].
Proof.
intros m i MI Hi.
destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite (bytes_at_read usegs m RMED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.

Section HALVE.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

Definition rcnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

#[using="SZ"] Lemma rhalve_big_walk : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv usegs m ->
evt usegs (fun ms' => exists a2' a3',
ms' = MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1308) fc None m (seg_rom usegs))
(MS (rcnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd12f4) fc None m (seg_rom usegs)).
Proof.
induction F as [|F IH]; intros until m; intros CR C32 MI; unfold rcnt_regs.
- cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
- cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
step. rewrite (unsigned_lit (size * cnt)) by lia.
step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
+
rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
rewrite (QDUx.Mq9.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
+ rewrite Z.shiftr_div_pow2 in K by lia.
replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
#[using="Type"] Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
intros H.
assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
destruct (Z.eq_dec n 1) as [->|NE].
- change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
- replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.

Section HALVE2.
Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

#[using="UR"] Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv usegs m ->
evt usegs (fun ms' => exists a3' a4',
ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd12f4) fc None m (seg_rom usegs))
(MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd12cc) fc None m (seg_rom usegs)).
Proof.
induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold rcnt_regs.
- change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
- cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).

step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
+
replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
step. apply evt_done. do 2 eexists. reflexivity.
+ replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).

step. rewrite (wz_unsigned cnt) by lia. rewrite (QDUx.Mq9.srliw_small cnt 1) by lia.
step. rewrite (wz_unsigned cnt) by lia. step.
assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.

step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
*
assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
{ rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
*
step.
assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
apply evt_done. do 2 eexists. reflexivity.
Qed.

#[using="UR"] Lemma rhalve_even_walk : forall (F : nat) (cnt : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv usegs m ->
evt usegs (fun ms' => exists a3' a4',
ms' = MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd12f4) fc None m (seg_rom usegs))
(MS (rcnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd12c4) fc None m (seg_rom usegs)).
Proof.
intros until m; intros CR C32 MI; unfold rcnt_regs.

step. rewrite (wz_unsigned cnt) by lia.
step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
-
assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
step. step. apply evt_done. do 2 eexists. reflexivity.
- assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
End HALVE2.

Section COUNT.
Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma rcnt0_range : 0 <= cnt0 <= 32.
Proof.
unfold cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
- pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

#[using="RC__ MR SC UR"] Lemma rcount_walk :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
mem_inv usegs m ->
evt usegs (fun ms' => exists a2' a3' a4',
ms' = MS (rcnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1308) fc None m (seg_rom usegs))
(MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 RSSP_GUARD) s5 (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1268) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros MI.
pose proof (size_class_range sc SC) as SZR.
pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
pose proof rcnt0_range as C0R.
unfold rcnt_regs, RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES, RPAGE_SIZE, RSMALL_CNT, RMED_CNT in *.

pose proof (rmrep_usage_read st m sc (wa (6576296 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
step. clear RDU.

step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).

step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
-
apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].

step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold RMED_CNT in RDM.
step. clear RDM. rewrite zxb_b8 by lia.

eapply evt_cut.
{ eapply (rhalve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
cbv beta. intros ms' (a3' & a4' & ->). unfold rcnt_regs.
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
eapply evt_mono.
{ eapply (rhalve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
cbv beta. intros ms' (a2'' & a3'' & ->). unfold rcnt_regs. do 3 eexists. reflexivity.
-
assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.

step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
pose proof (rsmall_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold RSMALL_CNT in RD0.
replace (wa (159752 + 3 * sc + 0)) with (Z_to_bv 64 (159752 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
step. clear RD0. rewrite zxb_b8 by lia.

step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
{ replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].

pose proof (rsmall_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold RSMALL_CNT in RD1.
replace (wa (159752 + 3 * sc + 1)) with (Z_to_bv 64 (159752 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
step. clear RD1. rewrite zxb_b8 by lia.
step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
{ replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].

pose proof (rsmall_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold RSMALL_CNT in RD2.
replace (wa (159752 + 3 * sc + 2)) with (Z_to_bv 64 (159752 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
step. clear RD2. rewrite zxb_b8 by lia. step.
apply evt_done. do 3 eexists. reflexivity.
Qed.
End COUNT.

Section CNT2.
Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="SZ C0"] Lemma rcnt2_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (if big then 0xd1330 else 0xd1374)) fc None m (seg_rom usegs))
(MS (rcnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0xd1308) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MI. unfold rcnt_regs.
assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
pose proof (cnt1_range size cnt0 C0) as C1R. fold cnt1 in C1R.
assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.

step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.

step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
-
assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).

step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB, E1. apply evt_done. reflexivity.
-
step. rewrite ?unsigned_lit by lia. step. step.
assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
{ unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
{ rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
rewrite EV. clear EV.
assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).

step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
+ assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
+ assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.

End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QBpX.
Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4 Qy5Y.Mq5 QWTl.Mq5 QDUx.Mqb Qy5Y.Mq6 QPjm.Mq3 Q4J3.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg Qy5Y.Mq7 QkQT QlkP QWTl.Mq0 QM7w.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq3 QdZ1 Qv4L.Mqk QQbX Qv4L.Mqb QnkH QmBS.Mq6.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk usegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
evt usegs (fun ms' => exists (a1' a2' : word),
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m (seg_rom usegs)
/\ stk usegs m lo (bv_unsigned sp))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd18c4) fc None m (seg_rom usegs)).
Proof.
intros until lo. intros MR' MI FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD & _) & _).
unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.

step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

step. step. step. step. step. step. step. step. step. step. step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.

End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.
Import QBpX.
Import Q2qa.Mq1 Q4J3.Mq1 Qy5Y.Mq4 Q4J3.Mq3 QlQE QPjm.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QJE4.Mq4 Qy5Y.Mq6 QPjm.Mq2 Q4J3.Mq4 QPjm.Mq3 QFkE Q6y7 QDUx.Mq6 QJE4.Mq2 Q3o5.Mq0.
Import Q9A7.Mq0.
Import QCwx.Mq3 QFqQ.Mq1 Q98Z.Mq5 QkLq QkLq.Mq3 Q98Z.Mq4 QnOf.
Import Qv4L.Mqf Qv4L.Mqg Qv4L.Mqh QmBS.Mq8 QdZ1.Mq6.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
(st' : mstate) (s' : PState) : machine_state -> Prop :=
fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv]
/\ rmrep st' m'
/\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 6444156 <= a < 6444160) m m'
/\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
/\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
/\ c_brk (ctx st') = c_brk (ctx st)
/\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

#[using="Type"] Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> 6444156 <= a < 6444160 -> ~ rfree_fp st lo sp a.
Proof.
intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
intros [[A|[A|A]]|[A|A]].
- lia.
- unfold RCTX in A. lia.
- destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
- destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
- destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.

#[using="Type"] Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
(s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
munch [(slo, shi); (6444156, 6444160); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
alloc_ceiling <= slo ->
rmrep (drop_region rid st2) m5.
Proof.
intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in LO.
pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). unfold alloc_ceiling in RBC.
eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
assert (LOW : a < alloc_ceiling /\ ~ (6444156 <= a < 6444160) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
{ destruct HF as [HF|HF].
- split; [| split].
+ destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
* unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold QXEH.RPAGE_SIZE in C; lia.
* destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). unfold alloc_ceiling in RC. lia.
* destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). unfold alloc_ceiling in RC. lia.
* destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). unfold alloc_ceiling in RC. lia.
* unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
+ intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
+ intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
* unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold QXEH.RPAGE_SIZE in C; lia.
* destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
* destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> rid).
{ intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
* destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
* unfold RGOT_SSP in C. lia.
* unfold RSSP_GUARD in C. lia.
- destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). unfold alloc_ceiling in RC.
split; [lia|]. split; [lia|].
pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

#[using="Type"] Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

#[using="Type"] Lemma bytes4_range (x0 x1 x2 x3 : byte) :
0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof.
pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

#[using="Type"] Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof.
pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
rewrite le4_bytes by lia. unfold b8.

f_equal; [|f_equal; [|f_equal; [|f_equal]]];
(apply bv_eq; rewrite Z_to_bv_unsigned;
match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
Z.div_mod_to_equations; lia).
Qed.

#[using="Type"] Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
#[using="Type"] Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
(st : mstate) (blk : block) (off : Z) (errv : word),
CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
rmrep st m -> mem_inv usegs m ->
stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
a0 = Z_to_bv 64 (blk_addr blk) ->
rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
(rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs)).
Proof using LO TP.
intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
pose proof (ci_ticks _ _ C) as TK.
pose proof (KINV_of_CINV _ _ C) as K0.
pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
assert (off' = off) as ->.
{ rewrite HA in OA. unfold UNIT in OA. lia. }
clear OA.
set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
pose proof (ci_gmetas _ _ C b g HB) as GO.
destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
cbn [aadd fst snd] in C3, C2, C1, OFF.

assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
{ rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : bv_unsigned tp + -164 = 6444156) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
pose proof LO as LOv. unfold alloc_ceiling in LOv.

assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
{ unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
{ apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
assert (P16m : snd pf mod 16 = 0).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
{ rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
unfold UNIT, IB in *.
assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (unfold alloc_ceiling in RBC; pose proof (round_up_pg_ge (r_len r)); lia).
assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x647000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).

clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
{ unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
destruct HB as [ai Hgh].

assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
pose proof (shiftr5_range v3) as SR5.
destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].

assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
exists x : byte, bytes_at usegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
{ intros q Fq Hq.
assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
destruct (SH _ r Hr Kr) as [WRr _].
assert (W1 : wr_at usegs m (r_base r + snd q) 1).
{ destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); unfold alloc_ceiling in RBC; lia|].
intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }

unfold free.
eapply (rimplT_bind m (free_hdr st pf) _ s
(fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
{ unfold free_hdr, get_meta. apply rimplT_guard. intros _.
apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
rewrite V31 in G12, G13, G14, G16.
set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
assert (Fe : fst e = fst b) by reflexivity.
assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
{ unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }

pose proof (go_sc _ _ _ GO) as GSC.
assert (WALK : forall r32 : Z,
(160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
/\ bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
/\ bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
(if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
evt usegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))).
{ intros r32 BIG RSVLE RB0r RE0.
eapply evt_mono.
{ eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
all: rewrite ?EB, ?V31.
- lia.
- rewrite Fp. exact Hr.
- rewrite A0, HAp. apply unsigned_lit. lia.
- exact P16m.
- rewrite Sp, Sc. lia.
- unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
- exact PHI.
- replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
- replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
- replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
- replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
- exact Hgh.
- reflexivity.
- exact (go_slot _ _ _ GO).
- destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
- exact (go_mem _ _ _ GO).
- exact AR1.
- exact G15.
- exact (go_avail _ _ _ GO).
- exact (go_freed _ _ _ GO).
- exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
- lia.
- rewrite (go_freeable _ _ _ GO). lia.
- lia.
- pose proof (go_maplen _ _ _ GO). lia.
- exact G12.
- exact G13.
- exact G14.
- intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
- intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
- intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
unfold UNIT in G17.
replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
rewrite Z.div_mul in G17 by lia. lia.
- lia.
- exact S16.
- rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
- rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
- exact BIG.
- exact RSVLE.
- exact RB0r.
- exact RE0.
- intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
clear - HD HAp SZ. lia.  }
intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }

assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
{ intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
{ rewrite Se, Cb. unfold UNIT, IB. lia. }
assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
{ rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
{ rewrite Se, Cb. unfold UNIT, IB. lia. }

unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
apply rimplT_if; intros HR5.
-
apply Z.leb_le in HR5.
apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
apply rimplT_rd32.
destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0.
destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1.
destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
apply rimplT_guard; intros G21. apply Z.leb_le in G21.
apply rimplT_rd8. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
apply rimplT_guard; intros G22. apply Z.leb_le in G22.
apply rimplT_rd8. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
apply rimplT_ret. rewrite V31.
specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).

apply (WALK r32).
+ intros _. split; [exact G20|]. split; [lia|]. split.
* rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
-- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
-- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
* rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
+ rewrite H160, <- DIFF. exact G22.
+ rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
+ rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
-
apply Z.leb_gt in HR5.
apply rimplT_guard; intros G22. apply Z.leb_le in G22.
apply rimplT_rd8. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
apply rimplT_rd8. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
apply rimplT_ret. rewrite V31.
specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).

apply (WALK 0).
+ intros H. exfalso. clear -H V160. lia.
+ rewrite H160, <- DIFF. exact G22.
+ rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
+ rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
set (st1 := hdr_st st pf) in *.
assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
{ intros k Hk. unfold pf; cbn [aadd fst snd].
assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
destruct CS as [-> |[-> | ->]];
[exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
|exists lo8|exists v3];
[rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
{ intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
{ destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
{ destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }

assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
{ intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
apply rimplT_guard. intros _.
apply rimplT_if; intros HC.
-
apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
apply rimplT_ret.
eapply evt_mono.
{ eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
intros ms' TPo. unfold rftriv_post in TPo.
destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [exact MI'|]. split; [exact ST'|].
split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
split; [exact MR'|].
split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
split; [intros rid r' H; exact H|].
split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
split; reflexivity.
-

assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
{ apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
eapply rimplT_evt.
{ eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
{ intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
assert (K1 : KINV st1 LB' 0).
{ unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
assert (L1 : LPRE st1 LB' 0 g b i).
{ unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
assert (OOK1 : oracle_ok m m1 st1).
{ unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
[exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].

intros st2 mi ms3 NQ. unfold rntf_q in NQ.
destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
rewrite unsigned_lit in ST3, PE3 by lia.
replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
replace (ret_pc (Z_to_bv 64 0xd04dc)) with (Z_to_bv 64 0xd04dc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
{ eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
assert (FR3' : rw_cells usegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 errv]).
{ eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
destruct mi as [[bm len]|].
+
cbv beta iota.
destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). unfold alloc_ceiling in R2C.
assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x647000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
pose proof (round_up_pg_ge (r_len r2)) as RU2.
eapply rimplT_evt.
{ eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
intros ms4 FM. unfold rfmun_post in FM.
destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
eapply (rimplT_munmap m (conc st2 bm) len _ s).
{ eapply rmunmap_spec.
- rewrite unsigned_lit by lia. exact ST4.
- exact ERR4.
- exact MI4.
- pose proof MR4 as (_ & _ & (_ & _ & _ & _ & _ & VML4) & _). exact VML4.
- unfold RVMLOCK. lia.
- rewrite Lr2, mmap_len_round. unfold RVMLOCK. lia.
- unfold wz. reflexivity.
- unfold wz. reflexivity.
- lia.
- rewrite Lr2, mmap_len_round. lia.
- lia.
- rewrite unsigned_lit by lia. lia.
- rewrite ETP, unsigned_lit by lia. lia.
- rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
- rewrite ETP, Lr2, mmap_len_round. lia.
- rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
rewrite (munmap_ok_range_val a ltac:(destruct a; cbn in ERNG |- *; [lia| exact Logic.I])).
apply rimplT_ret.
replace (ret_pc (Z_to_bv 64 0xd050c)) with (Z_to_bv 64 0xd050c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.

assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
{ eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
{ eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
rewrite ?ETP. cbn [outside]. repeat split; lia. }
eapply evt_mono.
{ eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
intros ms' FIN. unfold rffin_post in FIN.
destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
split.
{
assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
{ intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
{ intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 6444156 <= a < 6444160)); [| exact NC].
cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
{ intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 6444156 <= a < 6444160)); [| exact NC].
cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia | right; left; apply DR; lia]). }
eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 6444156 <= a < 6444160)); [| exact NC].
cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia]). }
split.
{ intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
split.
{ intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
split; [exact EB3|].
intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
+

cbv beta iota. cbn in RES3. subst a1v.
apply rimplT_ret.
eapply evt_mono.
{ eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
intros ms' FIN. unfold rffin_post in FIN.
destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
split.
{ eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 6444156 <= a < 6444160)); [| exact NC].
cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
split; [intros rid r' H; rewrite <- ER3; exact H|].
split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
split; [exact EB3|].
intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.

End RC__1.
End Mq8.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBpX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBpX.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlkP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlkP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCwx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCwx.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFqQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFqQ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q98Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q98Z.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkLq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkLq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnOf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnOf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn9M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn9M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qi8L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qi8L.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdZ1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdZ1.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQbX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQbX.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv4L.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv4L.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnkH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnkH.Mqm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmBS.Mq6.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ENTRY.
Variables (st : mstate) (m : mem) (sc : Z) (lo : Z).
Hypothesis MR : rmrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis AMS : forall g, active st sc = Some g -> meta_slot st g.

#[using="MR SC CLO AMS"] Lemma ras_entry_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
a0 = Z_to_bv 64 sc ->
stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' : word) m' junk,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 rc_canary a1' (pw st (active st sc)) a3 a4 a5 a6 a7
a1 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (match active st sc with None => 0xd1244 | Some _ => 0xd10c8 end)) fc None m' (seg_rom usegs)
/\ rw_cells usegs m' (bv_unsigned sp + -144) (rta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
/\ stk usegs m' lo (bv_unsigned sp + -144)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep st m')
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros HA ST LO MI. subst a0.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5 & G6) & _). unfold wz in G4.
unfold ralloc_slot_entry, alloc_ceiling, RCTX, RMLOCK, RGOT_SSP, RSSP_GUARD in *.

step. carve_frame 144%nat ST. step. step. step. step. step. step. step. step. step. step. step.

step. step. step. step. step. step. step. step. step. step.
rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply (rmrep_transport_high st m mX); [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]) end.
pose proof (rmrep_active_read st _ sc (wa (6576296 + 80 + 8 * sc)) MR1 SC eq_refl) as RDA.
step. clear RDA.

step.
replace (6576288 + sc * 8 + 88) with (6576296 + 80 + 8 * sc) by lia.
replace (6576288 + sc * 8) with (6576288 + 8 * sc) by lia.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -144) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.

step. if_cases K; zify_cond K.
- destruct (active st sc) as [g|] eqn:HA.
{ exfalso. pose proof (rmeta_slot_bounds st m g MR (AMS g eq_refl)) as (Gpos & GC & _).
unfold pw, wz in K; cbn [oconc] in K. rewrite ?unsigned_lit in K by lia. lia. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
- destruct (active st sc) as [g|] eqn:HA.
2:{ exfalso. apply K. reflexivity. }
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR|].
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.
End ENTRY.

Section T1.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis AVR : 0 <= m_avail mr < 2^32.
Hypothesis FRR : 0 <= m_freed mr < 2^32.

Definition rt1_regs (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
(Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6.

#[using="RC__ MR MSL AVR"] Lemma rt1_fin_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr <> 0 -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) (wz (sxv (m_avail mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1204) fc None m (seg_rom usegs))
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd10c8) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros AVNZ MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH.
pose proof (sxv_range (m_avail mr)) as RA.

step. rewrite sx32_wz_sxv by lia.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_avail mr))), ?unsigned_lit in K by lia.
{ exfalso. apply AVNZ. apply (proj1 (sxv_zero (m_avail mr) AVR)). exact K. }
step. step.
apply evt_done. reflexivity.
Qed.

#[using="RC__ MR MSL"] Lemma rt1_deq_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr = 0 -> m_freed mr = 0 -> mem_inv usegs m ->
evt usegs (fun ms' =>
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz 0) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd10ec) fc None m (seg_rom usegs))
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd10c8) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros AV0 FR0 MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0, FR0 in CH.

step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0. step.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. unfold pw, wz. reflexivity.
Qed.

#[using="MR MSL SC FRR"] Lemma rt1_next_walk :
forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_avail mr = 0 -> m_freed mr <> 0 -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (rt1_regs ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) (wz (sxv (m_freed mr))) (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd112c) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (set_active sc (m_next mr) st) m')
(MS (rt1_regs ra sp gp tp t0 t1 t2 s1 a0 a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd10c8) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros AV0 FRNZ MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite AV0 in CH.
pose proof (sxv_range (m_freed mr)) as RF.

step. rewrite sx32_wz_sxv by lia. change (sxv 0) with 0.
step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step. rewrite sx32_wz_sxv by lia. step.
step. if_cases K; zify_cond K; rewrite ?(wz_unsigned (sxv (m_freed mr))), ?unsigned_lit in K by lia.
{ exfalso. apply FRNZ. apply (proj1 (sxv_zero (m_freed mr) FRR)). exact K. } clear K.

clear CH.
pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (6576296 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (m_next mr) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6576296 + 80 + 8 * sc) (le8 (pw st (m_next mr))) MU WM SOK.

step.
apply evt_done. eexists. split; [unfold pw, wz; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End T1.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.

#[using="MR MSL SC"] Lemma rdeq_self_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
m_next mr = Some g -> mem_inv usegs m ->
evt usegs (fun ms' => exists m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (wz 0) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1244) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (put_meta g (clr mr) (set_active sc None st)) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd10ec) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros GN MI. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
unfold RCTX, RMLOCK, RSSP_GUARD in *.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
step.

pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (6576296 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc None MR SC) as MR1; unfold RCTX in MR1 end.
rraw_store_finish0 (6576296 + 80 + 8 * sc) (le8 (pw st None)) MU WM SOK.
set (st1 := set_active sc None st) in MR1.
assert (MS1 : meta_slot st1 g) by (apply meta_slot_set_active; exact MSL).

rmeta_open G MUg WMg.
rmchunk MR1 MS1 CH. change (conc st1 g) with G in CH. change (get_meta_rec st1 g) with mr in CH.
st1. st1.
rmeta_close2 MR1 MS1 MUg WMg CH (put_meta g (clr mr) st1) MR2 GN GN.

pose proof (rmrep_active_read _ _ sc (wa (6576296 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active _ sc) with (active st1 sc) in RDA. unfold st1 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. unfold wz.

step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.

#[using="MR MSL SC HA"] Lemma rdeq_other_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (nx pv : aptr),
m_next mr = Some nx -> m_prev mr = Some pv -> nx <> g -> pv <> g -> meta_slot st nx -> meta_slot st pv ->
mem_inv usegs m ->
let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
let st3 := set_active sc (Some nx) st2 in
let st4 := put_meta g (clr mr) st3 in
evt usegs (fun ms' => exists (a1' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st nx)) a1' (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd112c) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m m'
/\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep st4 m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (pw st (m_next mr)) a1 (Z_to_bv 64 G) a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd10ec) fc None m (seg_rom usegs)).
Proof.
intros until pv. intros GN GP NEn NEp MSn MSp MI st1 st2 st3 st4. unfold rt1_regs. rewrite GN. unfold pw. cbn [oconc]. fold G. unfold wz.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8); (G, G + 40); (conc st pv, conc st pv + 40); (conc st nx, conc st nx + 40)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m nx MR MSn) as (Npos & NC & NI & _ & _).
pose proof (rmeta_slot_bounds st m pv MR MSp) as (Ppos & PC & PI & _ & _).
assert (NEG : conc st nx <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
unfold RCTX, RMLOCK, RSSP_GUARD in *.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.

rmchunk MR MSL CH. fold mr G in CH. fold G in CH. rewrite GN, GP in CH. cbn [oconc] in CH.
step. clear CH.

rmeta_open (conc st pv) MUp WMp.
rmchunk MR MSp CH.
st1.
rmeta_close2 MR MSp MUp WMp CH st1 MR1 GP GN.
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta; exact MSL).
assert (MSn1 : meta_slot st1 nx) by (apply meta_slot_put_meta; exact MSn).

rmchunk MR1 MSg1 CH. unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. step. clear CH.

rmeta_open (conc st nx) MUn WMn.
rmchunk MR1 MSn1 CH.
st1.
rmeta_close2 MR1 MSn1 MUn WMn CH st2 MR2 GP GN.
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; exact MSg1).

pose proof (rmrep_active_read st2 _ sc (wa (6576296 + 80 + 8 * sc)) MR2 SC eq_refl) as RDA.
change (active st2 sc) with (active st sc) in RDA. rewrite HA in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st2 g) with G. unfold wz.

step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.

rmchunk MR2 MSg2 CH. unfold st2 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEn; symmetry; exact E).
unfold st1 in CH. rewrite ?get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; exact E).
fold mr in CH. rewrite GN, GP in CH. cbn [oconc] in CH. fold G in CH.
step. clear CH. step.

pose proof MR2 as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st2) sc (wa (6576296 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st2 mX sc (Some nx) MR2 SC) as MR3; unfold RCTX in MR3 end.
rraw_store_finish0 (6576296 + 80 + 8 * sc) (le8 (pw st2 (Some nx))) MU WM SOK.
fold st3 in MR3.
assert (MSg3 : meta_slot st3 g) by (apply meta_slot_set_active; exact MSg2).

rmeta_open G MUg WMg.
rmchunk MR3 MSg3 CH. change (conc st3 g) with G in CH.
replace (get_meta_rec st3 g) with mr in CH.
2:{ unfold st3, st2, st1. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E). rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity. }
rewrite GN, GP in CH. cbn [oconc] in CH.
st1. st1.
rmeta_close2 MR3 MSg3 MUg WMg CH st4 MR4 GN GN.

pose proof (rmrep_active_read _ _ sc (wa (6576296 + 80 + 8 * sc)) MR4 SC eq_refl) as RDA.
change (active st4 sc) with (active st3 sc) in RDA. unfold st3 in RDA. rewrite active_set_active, Z.eqb_refl in RDA.
step. clear RDA. unfold pw. cbn [oconc]. change (conc st4 nx) with (conc st nx). unfold wz.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR4].
Qed.
End DEQ.

Section M.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis FRR : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.

#[using="RC__ MR MSL FRR MW"] Lemma rm_act_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
full_skip st g = false -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' a2' : word),
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' (wz (sxv f)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1158) fc None m (seg_rom usegs))
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd112c) fc None m (seg_rom usegs)).
Proof.
intros until fc. intros NSK MI. unfold rt1_regs.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (QDUx.Mqb.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{  apply evt_done. do 2 eexists. reflexivity. }

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia.
{ apply evt_done. do 2 eexists. reflexivity. }
exfalso. unfold full_skip in NSK. fold mr f in NSK.
assert (E : f = mask_upto (m_last_idx mr)) by (apply sxv_inj; [lia|lia|exact K2]).
rewrite E, Z.eqb_refl in NSK. cbn [andb] in NSK. apply Bool.negb_false_iff in NSK. apply Z.eqb_eq in NSK. lia.
Qed.

#[using="f MR MSL SC FRR MW"] Lemma rm_skip_walk :
forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mn : aptr),
full_skip st g = true -> m_next mr = Some mn -> meta_slot st mn ->
0 <= m_freed (get_meta_rec st mn) < 2^32 -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' (wz (sxv (m_freed (get_meta_rec st mn)))) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd1158) fc None m' (seg_rom usegs)
/\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (set_active sc (Some mn) st) m')
(MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xd112c) fc None m (seg_rom usegs)).
Proof.
intros until mn. intros FSK GN MSn FNR MI. unfold rt1_regs.
pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
pose proof (QDUx.Mqb.mask_upto_range (m_last_idx mr) ltac:(lia)) as MUR.
unfold full_skip in FSK. fold mr f in FSK. apply andb_prop in FSK. destruct FSK as [FEQ FBNZ].
apply Z.eqb_eq in FEQ. apply Bool.negb_true_iff in FBNZ. apply Z.eqb_neq in FBNZ.
unfold RCTX, RMLOCK, RSSP_GUARD in *.
rmchunk MR MSL CH. fold mr G in CH. fold G in CH. fold f in CH. rewrite GN in CH. cbn [oconc] in CH.
pose proof (sxv_range f) as RF. pose proof (sxv_range (mask_upto (m_last_idx mr))) as RM.

step. rewrite sx32_wz_sxv by lia. step. step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_freeable mr MW). step.

step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.

step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 mr MW).
step. rewrite addiw_m1_word. change (2 ^ (m_last_idx mr + 1) - 1) with (mask_upto (m_last_idx mr)).
step. if_cases K2; zify_cond K2; rewrite ?wz_unsigned, ?unsigned_lit in K2 by lia. { exfalso. apply K2. rewrite FEQ. reflexivity. } clear K2.

step. clear CH.

pose proof MR as (_ & (_ & ACTS & _) & _).
pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (6576296 + 80 + 8 * sc)) ACTS
ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
rraw_store_finish0 (6576296 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.

assert (MSn2 : meta_slot (set_active sc (Some mn) st) mn) by (apply meta_slot_set_active; exact MSn).
rmchunk MR2 MSn2 CH. rewrite rec_set_active, conc_set_active in CH.
step. rewrite sx32_wz_sxv by lia.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
End M.

End RC__1.
