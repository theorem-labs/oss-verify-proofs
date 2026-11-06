(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.

Definition is_mkR (R : bvmap 5 word) : Prop :=
exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

Lemma is_mkR_set : forall R (k : reg) v, is_mkR R -> is_x0 k = false -> is_mkR (bvmap_set k v R).
Proof.
intros R k v (x1&x2&x3&x4&x5&x6&x7&x8&x9&x10&x11&x12&x13&x14&x15&x16&x17&x18&x19&x20&x21&x22&x23&x24&x25&x26&x27&x28&x29&x30&x31&->) Hk.
pose proof (bv_unsigned_in_range 5 k) as Hr. unfold bv_modulus in Hr. cbn in Hr.
unfold is_x0 in Hk. apply Z.eqb_neq in Hk.
assert (Ek : k = Z_to_bv 5 (bv_unsigned k)) by (apply bv_eq; rewrite Z_to_bv_small; [reflexivity | unfold bv_modulus; cbn; lia]).
rewrite Ek. set (n := bv_unsigned k) in *. clearbody n. clear Ek k.
unfold is_mkR.
assert (H : forall z, (1 <= z <= 31)%Z -> z = n ->
exists y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
bvmap_set (Z_to_bv 5 z) v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
= mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31).
{ intros z Hz _.
destruct (Z.eq_dec z 1) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 2) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 3) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 4) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 5) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 6) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 7) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 8) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 9) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 10) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 11) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 12) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 13) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 14) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 15) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 16) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 17) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 18) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 19) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 20) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 21) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 22) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 23) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 24) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 25) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 26) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 27) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 28) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 29) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 30) as [->|]; [repeat eexists; reflexivity|].
destruct (Z.eq_dec z 31) as [->|]; [repeat eexists; reflexivity|].
lia. }
exact (H n ltac:(lia) eq_refl).
Qed.

Fixpoint eff_all (P : core -> Prop) (t : eff) : Prop :=
match t with
| EDone c => P c
| ELoad n a k => forall v, eff_all P (k v)
| EStore n a v k => eff_all P k
| _ => True
end.

Definition mkRc (c : core) : Prop := is_mkR (c_regs c).

Lemma mkRc_rset : forall r v c, mkRc c -> mkRc (rset r v c).
Proof.
intros r v c H. unfold rset. destruct (is_x0 r) eqn:E; [exact H|].
unfold mkRc, with_regs in *. cbn. apply is_mkR_set; assumption.
Qed.
Lemma mkRc_fset : forall r v c, mkRc c -> mkRc (fset r v c).
Proof. intros r v [R F p f s] H. exact H. Qed.
Lemma mkRc_with_pc : forall v c, mkRc c -> mkRc (with_pc v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma mkRc_with_fcsr : forall v c, mkRc c -> mkRc (with_fcsr v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma mkRc_with_resv : forall v c, mkRc c -> mkRc (with_resv v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma mkRc_accrue : forall fl c, mkRc c -> mkRc (accrue fl c).
Proof. intros fl [R F p f s] H. exact H. Qed.
Lemma mkRc_fwrite : forall fmt r v c, mkRc c -> mkRc (fwrite fmt r v c).
Proof. intros fmt r v [R F p f s] H. unfold fwrite. cbn. destruct fmt; exact H. Qed.
Lemma mkRc_inval_resv : forall a c, mkRc c -> mkRc (inval_resv a c).
Proof. intros a [R F p f s] H. unfold inval_resv. cbn. destruct s as [r|]; [destruct (Z.eqb _ _)|]; exact H. Qed.
Lemma mkRc_if : forall (b : bool) c1 c2, mkRc c1 -> mkRc c2 -> mkRc (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

Local Ltac solve_mkRc H :=
repeat first [ apply mkRc_rset | apply mkRc_fset | apply mkRc_with_pc
| apply mkRc_with_fcsr | apply mkRc_with_resv | apply mkRc_accrue
| apply mkRc_fwrite | apply mkRc_inval_resv | apply mkRc_if
| match goal with |- mkRc (match ?X with _ => _ end) => destruct X end ];
exact H.

Local Ltac all_struct H :=
repeat first
[ lazymatch goal with
| |- eff_all _ (EDone _) => cbn [eff_all]; solve_mkRc H
| |- mkRc _ => solve_mkRc H
| |- eff_all _ (EIllegal _) => exact I
| |- eff_all _ (EDefinedIllegal _) => exact I
| |- eff_all _ (EEcall _) => exact I
| |- eff_all _ (EEbreak _) => exact I
| |- eff_all _ (EFault _) => exact I
| |- eff_all _ (ELoad _ _ _) => cbn [eff_all]; intros ?
| |- eff_all _ (EStore _ _ _ _) => cbn [eff_all]
| |- eff_all _ (match ?X with _ => _ end) => destruct X
| |- eff_all _ (match ?X with _ => _ end _) => destruct X
| |- eff_all _ (if ?X then _ else _) => destruct X
end ].

Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_mkRc : forall sz i c, mkRc c -> eff_all mkRc (exec sz i c).
Proof.
intros sz i [R F pc fc rv] H.
destruct i; unfold_exec; all_struct H.
Qed.

Lemma interp_eff_accesses_all : forall segs P t m rep,
eff_all P t ->
RiscvSemantics.interp_eff_accesses segs t m = MachineOk rep ->
P (fst (@access_value _ rep)).
Proof.
intros segs P t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m rep HA HI; cbn in HI.
- injection HI as <-. exact HA.
- discriminate HI.
- discriminate HI.
- discriminate HI.
- discriminate HI.
- discriminate HI.
- destruct (ov_read_bytes segs m a (RiscvSemantics.width_bytes n)) as [bs|]; [|discriminate HI].
destruct (RiscvSemantics.interp_eff_accesses segs (k _) m) as [rep'| |] eqn:E; try discriminate HI.
injection HI as <-. cbn. eapply IH; [apply HA | exact E].
- destruct (store_ok segs m a (RiscvSemantics.width_bytes n)); [|discriminate HI].
destruct (RiscvSemantics.interp_eff_accesses segs k _) as [rep'| |] eqn:E; try discriminate HI.
injection HI as <-. cbn. eapply IH; [exact HA | exact E].
Qed.

Lemma decode_exec_is_mkR : forall segs ms w rep,
is_mkR (ms_regs ms) -> RiscvSemantics.decode_exec_accesses segs ms w = MachineOk rep ->
is_mkR (ms_regs (@access_value _ rep)).
Proof.
intros segs [R0 F0 pc0 sv0 rv0 fc0 m0 ro0] w rep HR HS. cbn in HR.
unfold RiscvSemantics.decode_exec_accesses in HS. cbn in HS.
destruct (is_ecall w).
- injection HS as <-. cbn. exact HR.
- destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate HS].
destruct (RiscvSemantics.interp_eff_accesses _ _ m0) as [rep'| |] eqn:E; try discriminate HS.
destruct (@access_value _ rep') as [c m'] eqn:Ev.
injection HS as <-. cbn.
match type of E with RiscvSemantics.interp_eff_accesses _ (exec _ _ ?cc) _ = _ =>
pose proof (interp_eff_accesses_all segs mkRc _ _ _ (exec_mkRc (Z_to_bv 64 isz) i cc (HR : mkRc cc)) E) as X end.
rewrite Ev in X. exact X.
Qed.

Lemma fetch_failure_not_ok : forall segs m a st,
RiscvSemantics.fetch_failure segs m a = MachineOk st -> False.
Proof.
intros segs m a st H. unfold RiscvSemantics.fetch_failure in H.
destruct (negb _); [discriminate H|].
cbv zeta in H. destruct (_ || _ || _)%bool; discriminate H.
Qed.

Lemma step_is_mkR : forall segs ms ms',
is_mkR (ms_regs ms) -> RiscvSemantics.step segs ms = MachineOk ms' -> is_mkR (ms_regs ms').
Proof.
intros segs ms ms' HR HS.
unfold RiscvSemantics.step, RiscvSemantics.step_accesses, RiscvSemantics.drop_access_report in HS.
assert (D : forall w, match RiscvSemantics.decode_exec_accesses segs ms w with
| MachineOk r => MachineOk (@access_value _ r)
| MachineFault => MachineFault | MachineUnmodeled => MachineUnmodeled end = MachineOk ms' ->
is_mkR (ms_regs ms')).
{ intros w Hw. destruct (RiscvSemantics.decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate Hw.
injection Hw as <-. eapply decode_exec_is_mkR; [exact HR | exact E]. }
destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (D w HS)|].
destruct (RiscvSemantics.fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (D w HS)|].
destruct (RiscvSemantics.fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (D w HS)|].
destruct (RiscvSemantics.fetch_failure segs (ms_mem ms) (ms_pc ms)) as [st| |] eqn:E; try discriminate HS.
exfalso. exact (fetch_failure_not_ok _ _ _ _ E).
Qed.

Lemma hmsteps_is_mkR : forall segs ms ms',
QsRG.msteps segs ms ms' -> is_mkR (ms_regs ms) -> is_mkR (ms_regs ms').
Proof.
intros segs ms ms' H. induction H as [ms|ms ms1 ms2 Hsvc Hstep Hrest IH]; intros HR; [exact HR|].
apply IH. eapply step_is_mkR; [exact HR | exact Hstep].
Qed.

Lemma hmsteps_cmsteps : forall segs ms ms', QsRG.msteps segs ms ms' -> QbrW.msteps segs ms ms'.
Proof.
intros segs ms ms' H. induction H as [ms|ms ms1 ms2 Hsvc Hstep Hrest IH].
- apply QbrW.msteps_refl.
- eapply QbrW.msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

Lemma evt_hmsteps : forall segs Q ms ms', QsRG.msteps segs ms ms' -> evt segs Q ms' -> evt segs Q ms.
Proof.
intros segs Q ms ms' H (msf & Hs & HQ). exists msf. split; [|exact HQ].
eapply QbrW.msteps_trans; [apply hmsteps_cmsteps; exact H | exact Hs].
Qed.

Definition rv (E : env) (sr : list expr) (n : Z) : word := edenot E (sr_get sr (Z_to_bv 5 n)).

Lemma mkR_of_regs_ok : forall E sr R,
is_mkR R -> regs_ok E sr R ->
R = mkR (rv E sr 1) (rv E sr 2) (rv E sr 3) (rv E sr 4) (rv E sr 5) (rv E sr 6) (rv E sr 7) (rv E sr 8)
(rv E sr 9) (rv E sr 10) (rv E sr 11) (rv E sr 12) (rv E sr 13) (rv E sr 14) (rv E sr 15) (rv E sr 16)
(rv E sr 17) (rv E sr 18) (rv E sr 19) (rv E sr 20) (rv E sr 21) (rv E sr 22) (rv E sr 23) (rv E sr 24)
(rv E sr 25) (rv E sr 26) (rv E sr 27) (rv E sr 28) (rv E sr 29) (rv E sr 30) (rv E sr 31).
Proof.
intros E sr R (x1&x2&x3&x4&x5&x6&x7&x8&x9&x10&x11&x12&x13&x14&x15&x16&x17&x18&x19&x20&x21&x22&x23&x24&x25&x26&x27&x28&x29&x30&x31&->) HR.
unfold rv.
assert (G : forall n, (1 <= n <= 31)%Z ->
getr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) (Z_to_bv 5 n)
= edenot E (sr_get sr (Z_to_bv 5 n))) by (intros n _; apply HR).
pose proof (G 1%Z ltac:(lia)) as G1. pose proof (G 2%Z ltac:(lia)) as G2. pose proof (G 3%Z ltac:(lia)) as G3.
pose proof (G 4%Z ltac:(lia)) as G4. pose proof (G 5%Z ltac:(lia)) as G5. pose proof (G 6%Z ltac:(lia)) as G6.
pose proof (G 7%Z ltac:(lia)) as G7. pose proof (G 8%Z ltac:(lia)) as G8. pose proof (G 9%Z ltac:(lia)) as G9.
pose proof (G 10%Z ltac:(lia)) as G10. pose proof (G 11%Z ltac:(lia)) as G11. pose proof (G 12%Z ltac:(lia)) as G12.
pose proof (G 13%Z ltac:(lia)) as G13. pose proof (G 14%Z ltac:(lia)) as G14. pose proof (G 15%Z ltac:(lia)) as G15.
pose proof (G 16%Z ltac:(lia)) as G16. pose proof (G 17%Z ltac:(lia)) as G17. pose proof (G 18%Z ltac:(lia)) as G18.
pose proof (G 19%Z ltac:(lia)) as G19. pose proof (G 20%Z ltac:(lia)) as G20. pose proof (G 21%Z ltac:(lia)) as G21.
pose proof (G 22%Z ltac:(lia)) as G22. pose proof (G 23%Z ltac:(lia)) as G23. pose proof (G 24%Z ltac:(lia)) as G24.
pose proof (G 25%Z ltac:(lia)) as G25. pose proof (G 26%Z ltac:(lia)) as G26. pose proof (G 27%Z ltac:(lia)) as G27.
pose proof (G 28%Z ltac:(lia)) as G28. pose proof (G 29%Z ltac:(lia)) as G29. pose proof (G 30%Z ltac:(lia)) as G30.
pose proof (G 31%Z ltac:(lia)) as G31.
cbn [getr bv_eqb Z.eqb bv_unsigned Z_to_bv] in *.
unfold getr in *.
repeat match goal with H : (if ?b then _ else _) = _ |- _ => let bb := eval vm_compute in b in change b with bb in H; cbv iota in H end.
rewrite <- G1, <- G2, <- G3, <- G4, <- G5, <- G6, <- G7, <- G8, <- G9, <- G10, <- G11, <- G12, <- G13, <- G14, <- G15, <- G16,
<- G17, <- G18, <- G19, <- G20, <- G21, <- G22, <- G23, <- G24, <- G25, <- G26, <- G27, <- G28, <- G29, <- G30, <- G31.
reflexivity.
Qed.

Definition mkRv (E : env) (sr : list expr) : bvmap 5 word :=
mkR (rv E sr 1) (rv E sr 2) (rv E sr 3) (rv E sr 4) (rv E sr 5) (rv E sr 6) (rv E sr 7) (rv E sr 8)
(rv E sr 9) (rv E sr 10) (rv E sr 11) (rv E sr 12) (rv E sr 13) (rv E sr 14) (rv E sr 15) (rv E sr 16)
(rv E sr 17) (rv E sr 18) (rv E sr 19) (rv E sr 20) (rv E sr 21) (rv E sr 22) (rv E sr 23) (rv E sr 24)
(rv E sr 25) (rv E sr 26) (rv E sr 27) (rv E sr 28) (rv E sr 29) (rv E sr 30) (rv E sr 31).

Lemma is_mkR_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
is_mkR (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. repeat eexists. Qed.

Lemma is_mkR_mkRv : forall E sr, is_mkR (mkRv E sr).
Proof. intros. apply is_mkR_mkR. Qed.

Theorem symb_block : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
(E : env) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) R Q,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
carry (s_log ss') kn [] = (kn', scs2, hs2) ->
is_mkR R ->
regs_ok E sr R -> know_ok segs E M kn ->
scs_denot segs M E scs -> scs_denot segs M E scs2 ->
(regs_ok E (s_regs ss') (mkRv E (s_regs ss')) ->
know_ok segs E (mem_denot E M (s_log ss')) kn' ->
log_flat E (s_log ss') ->
evt segs Q (MS (mkRv E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None
(mem_denot E M (s_log ss')) (QsRG.Mq0.seg_rom segs))) ->
evt segs Q (MS R F (Z_to_bv 64 pc) fc None M (QsRG.Mq0.seg_rom segs)).
Proof.
intros segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M F fc R Q
Hex Hc Hmk HR HK Hsc Hsc2 Hcont.
destruct (@run_sound F fc segs fuel stops scr pc sr kn nx ss' scs scr' E M (QsRG.Mq0.seg_rom segs) R Hex HR HK Hsc)
as (R' & HR' & Hlf & Hms).
pose proof (hmsteps_is_mkR _ _ _ Hms Hmk) as Hmk'. cbn [ms_regs mkst] in Hmk'.
pose proof (mkR_of_regs_ok E (s_regs ss') R' Hmk' HR') as ER'.
change (mkst R (Z_to_bv 64 pc) M (QsRG.Mq0.seg_rom segs)) with
(MS R F (Z_to_bv 64 pc) fc None M (QsRG.Mq0.seg_rom segs)) in Hms.
change (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E M (s_log ss')) (QsRG.Mq0.seg_rom segs)) with
(MS R' F (Z_to_bv 64 (s_pc ss')) fc None (mem_denot E M (s_log ss')) (QsRG.Mq0.seg_rom segs)) in Hms.
eapply evt_hmsteps; [exact Hms|].
fold (mkRv E (s_regs ss')) in ER'. rewrite ER'.
apply Hcont.
- rewrite <- ER'. exact HR'.
- eapply carry_after; eassumption.
- exact Hlf.
Qed.

Corollary symb_block_mkR : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
(E : env) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32)
x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 Q,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
carry (s_log ss') kn [] = (kn', scs2, hs2) ->
regs_ok E sr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) ->
know_ok segs E M kn ->
scs_denot segs M E scs -> scs_denot segs M E scs2 ->
(regs_ok E (s_regs ss') (mkRv E (s_regs ss')) ->
know_ok segs E (mem_denot E M (s_log ss')) kn' ->
log_flat E (s_log ss') ->
evt segs Q (MS (mkRv E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None
(mem_denot E M (s_log ss')) (QsRG.Mq0.seg_rom segs))) ->
evt segs Q (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None M (QsRG.Mq0.seg_rom segs)).
Proof. intros. eapply symb_block; try eassumption. apply is_mkR_mkR. Qed.
