(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJvR.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QeZD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeZD.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qod2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qod2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDH9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDH9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5Hp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5Hp. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtkK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtkK.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTWd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTWd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQ4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQ4u.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWOb.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition P1STOPS : list Z := [0x551dc; 0x20f30]%Z.
Definition runP (ss : sym_state) := sym_exec RSEGS FUEL true P1STOPS scr0 ss [].

Definition p1_kn : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff00000000 0x7fffffffffff;
KWr (SA (EVar 0) (-1536)) 1536;
KImg 0x10000 0x658d8; KWord (SA (ELit 0) 0x658d8) 8 (ELit 0x66a30); KImg 0x658e0 0x659d0;
KWord (SA (ELit 0) 0x659d0) 8 (ELit 0x97e70); KImg 0x659d8 0x66000;
KImg 0x66e28 0x66f10;
KWord (SA (ELit 0) 0x97e70) 8 (EVar 2);
KWr (SA (ELit 0) 0x66000) 0x33000].

Definition p1_rA := Eval vm_compute in runP (SS 0x20fdc pf_sr [] p1_kn 35).
Definition p1_srA : list expr := Eval vm_compute in s_regs (fst (fst p1_rA)).
Definition p1_knA : list kentry := Eval vm_compute in kn_after p1_rA p1_kn.
Definition p1_logA : list sentry := Eval vm_compute in s_log (fst (fst p1_rA)).

Definition p1_srA' : list expr := Eval vm_compute in sr_upd p1_srA (ridx 10) (ELit 18446744073709551591).
Definition p1_rB := Eval vm_compute in runP (SS 0x553d4 p1_srA' [] p1_knA 35).
Definition p1_srB : list expr := Eval vm_compute in s_regs (fst (fst p1_rB)).
Definition p1_knB : list kentry := Eval vm_compute in kn_after p1_rB p1_knA.
Definition p1_logB : list sentry := Eval vm_compute in s_log (fst (fst p1_rB)).

Definition p1_res : stdio_res :=
Eval vm_compute in match stdio_call 35 p1_srB p1_knB with Some r => r
| None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma p1_res_eq : stdio_call 35 p1_srB p1_knB = Some p1_res. Proof. vm_compute. reflexivity. Qed.

Definition p1_srC0 : list expr := Eval vm_compute in sc_sr p1_res.
Definition p1_knC0 : list kentry := Eval vm_compute in sc_kn p1_res.
Definition p1_rC := Eval vm_compute in runP (SS 0x553f4 p1_srC0 [] p1_knC0 67).
Definition p1_knC : list kentry := Eval vm_compute in kn_after p1_rC p1_knC0.
Definition p1_logC : list sentry := Eval vm_compute in s_log (fst (fst p1_rC)).

Definition p1_regions : list sregion :=
[(SA (EVar 0) (-1536), 1536); (SA (ELit 0) 0x66e28, 232); (SA (ELit 0) 0x98350, 1024)].
Lemma p1_covA : log_covered p1_regions p1_logA = true. Proof. vm_compute. reflexivity. Qed.
Lemma p1_covB : log_covered p1_regions p1_logB = true. Proof. vm_compute. reflexivity. Qed.
Lemma p1_covC : log_covered p1_regions p1_logC = true. Proof. vm_compute. reflexivity. Qed.

Lemma nl_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x10d33) 1 = Some [Z_to_bv 8 10].
Proof. vm_compute. reflexivity. Qed.

Definition regions_lt (E : env) (rs : list sregion) : Prop :=
forall r, In r rs -> estart E (fst r) + snd r < 2^64.

Lemma entry_covered_flat : forall E rs a w,
entry_covered rs a w = true -> regions_flat E rs -> regions_lt E rs -> flat E a (Z.of_nat w).
Proof.
intros E rs a w. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered]; intros Hc Hrf Hlt; [discriminate|].
apply orb_prop in Hc as [Hc|Hc].
- apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
pose proof (Hrf _ (or_introl eq_refl)) as Hfr. pose proof (Hlt _ (or_introl eq_refl)) as Hfl. cbn [fst snd] in Hfr, Hfl.
unfold flat, estart in *. cbn [a_base a_off] in *. destruct a as [ab ao]. cbn [a_base a_off] in *. subst ab. lia.
- apply IH; [exact Hc| |]. { intros r Hr. apply Hrf. right. exact Hr. } { intros r Hr. apply Hlt. right. exact Hr. }
Qed.

Lemma mem_denot_frame : forall E base rs log (x : word),
log_covered rs log = true -> regions_flat E rs -> regions_lt E rs -> outside x (map (rdenot E) rs) ->
mem_denot E base log x = base x.
Proof.
intros E base rs log x. induction log as [|[a w v] rest IH]; cbn [log_covered mem_denot]; intros Hc Hrf Hlt Hout; [reflexivity|].
apply andb_prop in Hc as [H1 H2].
pose proof (entry_covered_flat E rs a w H1 Hrf Hlt) as Hfa. pose proof (flat_u E a _ Hfa) as Hu. pose proof Hfa as (F1 & F2 & F3 & F4).
rewrite wbytes_outside.
- apply IH; assumption.
- unfold in_rng. rewrite length_N_to_le_bytes, Hu. intros X.
exact (entry_covered_in E rs a w x H1 Hrf Hfa X Hout).
- rewrite length_N_to_le_bytes, Hu. lia.
Qed.

Section Entry.
Variables (regs : bvmap 5 word) (mem : word -> option byte) (sp : word).
Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
Hypothesis SPLO : 0x7fff00000000 <= bv_unsigned sp.
Hypothesis SPHI : bv_unsigned sp <= 0x7fffffffffff.
Hypothesis STK : stk_ok RSEGS mem sp 1536.
Hypothesis IM1 : forall i, 0x10000 <= i < 0x658d8 -> mem (Z_to_bv 64 i) = None.
Hypothesis HEX : rdn RSEGS mem (Z_to_bv 64 0x658d8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x66a30)).
Hypothesis IM1b : forall i, 0x658e0 <= i < 0x659d0 -> mem (Z_to_bv 64 i) = None.
Hypothesis GOT : rdn RSEGS mem (Z_to_bv 64 0x659d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x97e70)).
Hypothesis IM2 : forall i, 0x659d8 <= i < 0x66000 -> mem (Z_to_bv 64 i) = None.
Hypothesis IMF : forall i, 0x66e28 <= i < 0x66f10 -> mem (Z_to_bv 64 i) = None.
Variable can : Z.
Hypothesis CAN64 : 0 <= can < 2^64.
Hypothesis CAN : rdn RSEGS mem (Z_to_bv 64 0x97e70) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).

Let E := pfE regs sp 0 can.

#[using="SPAL SPLO SPHI STK IM1 HEX IM1b GOT IM2 IMF CAN64 CAN"] Lemma p1_know_ok : know_ok RSEGS E mem p1_kn.
Proof.
pose proof (u64_range sp) as Hsp.
assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
assert (E0 : ev E 0 = sp) by reflexivity.
assert (E2 : ev E 2 = Z_to_bv 64 can) by reflexivity.
unfold p1_kn. repeat (apply Forall_cons); [ .. | apply Forall_nil ].
- apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. exact SPAL.
- apply krange_intro. cbn [edenot]. rewrite E0. lia.
- apply (kwr_of_stk_ok RSEGS E mem (EVar 0) sp 1536); [exact E0 | exact STK | lia].
- apply kimg_intro; [lia | lia | exact IM1].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact HEX].
- apply kimg_intro; [lia | lia | exact IM1b].
- eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0)); [reflexivity | reflexivity | lia | lia | rewrite Z0; lia | rewrite Z0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | rewrite Z0; exact GOT].
- apply kimg_intro; [lia | lia | exact IM2].
- apply kimg_intro; [lia | lia | exact IMF].
-
cbn [kentry_ok]. split; [lia|]. split; [apply flat_intro; cbn [edenot a_base a_off]; rewrite ?Z0; lia|].
rewrite adenot_lit0. cbn [edenot]. rewrite E2. exact CAN.
- cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia.
split; [lia|]. intros d k Hd Hk. apply data_store_ok; lia.
Qed.

End Entry.

Lemma p1_regions_flatE : forall (E : env) (sp : word), ev E 0 = sp ->
0x7fff00000000 <= bv_unsigned sp -> bv_unsigned sp <= 0x7fffffffffff ->
regions_flat E p1_regions /\ regions_lt E p1_regions.
Proof.
intros E sp HE SPLO SPHI. pose proof (u64_range sp).
split; intros r Hr; unfold p1_regions in Hr; cbn [In] in Hr; unfold flat, estart;
destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd a_base a_off edenot]; rewrite ?u64_lit by lia;
rewrite ?HE; lia.
Qed.

Lemma p1_frame : forall (E : env) (sp : word) base log (x : word),
ev E 0 = sp -> 0x7fff00000000 <= bv_unsigned sp -> bv_unsigned sp <= 0x7fffffffffff ->
log_covered p1_regions log = true ->
~ (bv_unsigned sp - 1536 <= bv_unsigned x < bv_unsigned sp) ->
~ (0x66e28 <= bv_unsigned x < 0x66f10) -> ~ (0x98350 <= bv_unsigned x < 0x98750) ->
mem_denot E base log x = base x.
Proof.
intros E sp base log x HE SPLO SPHI Hc N1 N2 N3.
destruct (p1_regions_flatE E sp HE SPLO SPHI) as [RF RL].
apply (mem_denot_frame E base p1_regions log x Hc RF RL).
pose proof (u64_range sp). pose proof (u64_range x).
unfold p1_regions. cbn [map rdenot outside fst snd]. unfold in_rng, estart. cbn [a_base a_off edenot]. rewrite HE.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite !Z.add_0_l. rewrite !u_small by lia. repeat split; try exact I; lia.
Qed.

Lemma R_wb : sc_wb p1_res = ELit 0x98350. Proof. reflexivity. Qed.
Lemma R_wp : sc_wp p1_res = ELit 0x98351. Proof. reflexivity. Qed.
Lemma R_s : sc_s p1_res = ELit 0x10d33. Proof. reflexivity. Qed.
Lemma R_l : sc_l p1_res = ELit 1. Proof. reflexivity. Qed.
Lemma R_sp : sc_sp p1_res = EAlu Instr.ALU_ADD (EVar 0) (ELit (-1088)). Proof. reflexivity. Qed.
Lemma R_fd : sc_fd p1_res = 1%Z. Proof. reflexivity. Qed.
Lemma R_f : sc_f p1_res = 0x66e28%Z. Proof. reflexivity. Qed.
Lemma R_ret : sc_ret p1_res = 0x553f4%Z. Proof. reflexivity. Qed.
Lemma R_bufp : sc_bufp p1_res = ELit 0x98350. Proof. reflexivity. Qed.
Lemma R_bufsz : sc_bufsz p1_res = ELit 1024. Proof. reflexivity. Qed.
Lemma R_sr : sc_sr p1_res = p1_srC0. Proof. reflexivity. Qed.
Lemma R_kn : sc_kn p1_res = p1_knC0. Proof. reflexivity. Qed.

Section AmbP.
Context {AMB : Amb}.
#[using="Type"] Theorem printf1_ok : forall usp0, printf1_stmt usp0.
Proof.
intros usp0. unfold printf1_stmt. intros until K. cbv zeta. intros [Hh Hl] FD1 OUTC IMG ST MI SPB SPA Htp KNIL HK0. subst tp.
destruct IMG as (IM1 & HEX & IM1b & IM2 & GOT & CAN).
set (sp := Z_to_bv 64 (usp0 - 208)).
assert (U : bv_unsigned sp = usp0 - 208) by (subst sp; apply unsigned_lit; lia).
set (R := mkR (Z_to_bv 64 PRINTF_RET) sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
set (can := bv_unsigned rc_canary).
assert (CAN64 : 0 <= can < 2^64) by (subst can; pose proof (u64_range rc_canary) as RC; lia).
set (vals := pf_vals R sp 0 can).
assert (HL : length vals = 35%nat) by reflexivity.
pose proof (pf_regs_ok R sp 0 can (UWOb.g1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
(UWOb.g2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
(UWOb.g11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)) as HR.
assert (STK : stk_ok RSEGS m sp 1536).
{ replace 1536 with (bv_unsigned sp - (usp0 - 208 - 1536)) by (rewrite U; lia). apply UWOb.stk_ok_of_stk. rewrite U. exact ST. }
pose proof (p1_know_ok R m sp ltac:(rewrite U; replace (usp0 - 208) with (usp0 + (-13) * 16) by lia; rewrite Z.mod_add by lia; exact SPA)
ltac:(rewrite U; lia) ltac:(rewrite U; lia) STK IM1 (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ HEX) IM1b
(QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ GOT) IM2 OUTC can CAN64
ltac:(subst can; rewrite Z_to_bv_bv_unsigned; exact (QuJV.Mq0.bytes_at_rdn0 rsegs m _ _ CAN))) as HK.
change (pfE R sp 0 can) with (Env (vals_ev vals) (blobs_ev [])) in HR, HK.
change (realizes RSEGS (mkCfg (@mkst F fc R (Z_to_bv 64 0x20fdc) m (seg_rom RSEGS)) md) (t_emit (W 1 (zero_lines 1)) K)).

run_block_gen FUEL P1STOPS scr0 35%nat true.

eapply (rz_ioctl_winsz RSEGS _ (Z_to_bv 64 349136) _ md ECALLW (Z_to_bv 64 1));
[ vm_compute; reflexivity | apply is_ecall_ECALLW | exact Hh | exact Hl
| regv HR (17%bv : reg); reflexivity
| regv HR (10%bv : reg); reflexivity
| rewrite u_small by lia; lia
| exact FD1
| regv HR (11%bv : reg); reflexivity
| ].
rewrite v_addi_pc4 by lia. change (349136 + 4)%Z with 0x553d4%Z.
lazymatch type of HR with regs_ok ?E0 ?sr ?Rc =>
pose proof (regs_set_a0 E0 sr Rc (errno_ret ENOTTY) (ELit 18446744073709551591) HR ltac:(apply bv_eq; reflexivity)) as HR1 end.
clear HR. rename HR1 into HR.

run_block_gen FUEL P1STOPS scr0 35%nat true.

lazymatch type of HR with regs_ok _ ?sr _ => change sr with p1_srB in HR end.
lazymatch type of HK with know_ok _ _ _ ?kn => change kn with p1_knB in HK end.
change (t_emit (W 1 (zero_lines 1)) K)
with (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd p1_res))) ([Z_to_bv 8 48] ++ [Z_to_bv 8 10])) K).
eapply (stdio_call_sound_post (fF:=F) (fC:=fc) vals (blobs_ev []) p1_srB p1_knB _ _ md p1_res [Z_to_bv 8 48] [Z_to_bv 8 10] K HR HK
ltac:(rewrite HL; exact p1_res_eq));
rewrite ?R_wb, ?R_wp, ?R_l, ?R_s, ?R_fd, ?R_sp, ?R_bufp, ?R_bufsz; cbn [edenot].
- rewrite !u_small by lia. lia.
- rewrite !u_small by lia. lia.
- rewrite !u_small by lia. reflexivity.
- rewrite !u_small by lia. reflexivity.
- cbn. lia.
- left. rewrite alu_add_lit. change (ev _ 0) with sp. rewrite U. rewrite !u_small by lia. lia.
- left. rewrite alu_add_lit. change (ev _ 0) with sp. rewrite U. rewrite !u_small by lia. lia.
- rewrite !u_small by lia. lia.
- rewrite u_small by lia. krd HK 623440%Z 1%nat Hrd. rewrite Hrd. reflexivity.
- rewrite (kimg_rdn RSEGS _ _ p1_knB ltac:(let i := kidx p1_knB (is_kimg_cov 0x10d33 1) in exact i) _ _ 0x10d33 1 HK eq_refl) by lia.
exact nl_img.
- exact FD1.
- exact Hh.
- exact Hl.
- exact KNIL.
-
intros R2 M2 HR2 HK2 HPOST _. rewrite R_sr in HR2. rewrite R_kn in HK2. rewrite R_ret.
rewrite ?R_f, ?R_bufp, ?R_bufsz in HPOST. cbn [edenot] in HPOST. rewrite ?alu_add_lit in HPOST.
change (ev _ 0) with sp in HPOST. rewrite ?U in HPOST. rewrite ?u_small in HPOST by lia.
clear HR HK.
set (vals2 := vals ++ junk_vals R2) in *.
assert (HL2 : length vals2 = 67%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (QV : forall i, (i < 35)%nat -> vals_ev vals2 i = vals_ev vals i)
by (intros i Hi; subst vals2; apply vals_ev_app_l; rewrite HL; exact Hi).
clearbody vals2. rename HR2 into HR. rename HK2 into HK.
run_block_gen FUEL P1STOPS scr0 67%nat true.

lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc ?pc ?Mc ?rom) _) _ =>
change (mkst Rc pc Mc rom) with (QEpW.MS Rc F pc fc None Mc rom) end.
apply (realizes_canon rsegs). rewrite canonR_getr. rewrite !(reg_val _ _ _ _ HR).
lazymatch type of HR with regs_ok _ ?SR _ =>
repeat match goal with |- context [sr_get SR ?r] => let e := eval vm_compute in (sr_get SR r) in change (sr_get SR r) with e end end.
cbn [edenot ev eb].
rewrite (QV 0%nat), (QV 6%nat), (QV 7%nat), (QV 11%nat), (QV 12%nat), (QV 21%nat), (QV 22%nat), (QV 23%nat), (QV 24%nat),
(QV 25%nat), (QV 26%nat), (QV 27%nat), (QV 28%nat), (QV 29%nat), (QV 30%nat) by lia.
change (vals_ev vals 0) with sp. change (vals_ev vals 6) with gp. change (vals_ev vals 7) with (Z_to_bv 64 0x77c00).
change (vals_ev vals 11) with s0. change (vals_ev vals 12) with s1.
change (vals_ev vals 21) with s2. change (vals_ev vals 22) with s3. change (vals_ev vals 23) with s4. change (vals_ev vals 24) with s5.
change (vals_ev vals 25) with s6. change (vals_ev vals 26) with s7. change (vals_ev vals 27) with s8. change (vals_ev vals 28) with s9.
change (vals_ev vals 29) with s10. change (vals_ev vals 30) with s11.

lazymatch goal with |- realizes _ (mkCfg (QEpW.MS _ _ _ _ _ ?Mc _) _) _ => rename Mc into M3 end.
assert (E20 : ev {| ev := vals_ev vals2; eb := blobs_ev [] |} 0 = sp) by (cbn [ev]; rewrite (QV 0%nat) by lia; reflexivity).
assert (EQ : forall x : word, ~ (usp0 - 208 - 1536 <= bv_unsigned x < usp0 - 208) ->
~ (0x66e28 <= bv_unsigned x < 0x66f10) -> ~ (0x98350 <= bv_unsigned x < 0x98750) -> M3 x = m x).
{ intros x N1 N2 N3. pose proof (u64_range x).
rewrite EQM1. rewrite (p1_frame _ sp M2 p1_logC x E20) by (rewrite ?U; first [exact p1_covC | lia]).
rewrite (swp_agree _ _ _ _ _ _ HPOST x) by lia.
rewrite EQM0. rewrite (p1_frame (Env (vals_ev vals) (blobs_ev [])) sp M p1_logB x (@eq_refl _ sp)) by (rewrite ?U; first [exact p1_covB | lia]).
rewrite EQM. rewrite (p1_frame (Env (vals_ev vals) (blobs_ev [])) sp m p1_logA x (@eq_refl _ sp)) by (rewrite ?U; first [exact p1_covA | lia]).
reflexivity. }
assert (GR : mem_grows m M3).
{ rewrite EQM1. eapply mem_grows_trans; [| apply mem_denot_grows].
eapply mem_grows_trans; [| exact (swp_grows _ _ _ _ _ _ HPOST)].
rewrite EQM0. eapply mem_grows_trans; [| apply mem_denot_grows].
rewrite EQM. apply mem_denot_grows. }
subst sp. eapply HK0.
+ intros x OUT. apply EQ; unfold PFW in OUT; cbn [QWxq.outside] in OUT; lia.
+ exact (wmono_of_grows _ _ GR).
+ eapply mem_inv_of_agree; [exact MI|]. intros x Hx. apply EQ; lia.
+ eapply stk_grows; [exact ST | exact GR | lia].
+ constructor; unfold Um90.Mq0.cell.
* krd HK 0x66e28%Z 4%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e30%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e38%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e48%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e50%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e60%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e70%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e80%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66e88%Z 8%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66ea0%Z 4%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66eb4%Z 4%nat H1. rewrite H1. vm_compute. reflexivity.
* krd HK 0x66eb8%Z 4%nat H1. rewrite H1. vm_compute. reflexivity.
* reflexivity.
Qed.
End AmbP.
