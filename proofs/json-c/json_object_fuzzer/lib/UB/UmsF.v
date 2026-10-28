(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qpox QsV0 QBxa QSjk QMz4 QO3A Q7m0 QSpR QuJV QCPB QH7x QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ Um90 UWQV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR UG24 U9ch UleT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH QBxa.Mq4 QSjk.Mq0 QBxa.Mq1 QMz4 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.Mq0 QqES.
Import U1oC.
Import QBxa.Mq5 Q9ox.Mq2 QSpR.Mq0.
Import UFeQ.Mq0 Um90 UWQV.Mq0.
Import QUeZ.
Import Um90.Mq0.
Import QBxa.Mq0 QBxa.Mq2.
Import UJvR.Mq0 UJvR.Mq1 UG24.Mq1 U9ch.Mq0 UleT.Mq0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition STOPS_H : list Z := (0x520b4 :: STOPS)%Z.
Definition runH (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_H scr ss [].

Definition hssA0 : sym_state := SS 0x20d3c srOOM0 [] knRE0 39.
Definition hrA := Eval vm_compute in runH scr0 hssA0.
Definition hsrA : list expr := Eval vm_compute in s_regs (fst (fst hrA)).
Definition hknA : list kentry := Eval vm_compute in kn_after hrA knRE0.
Definition hlogA : list sentry := Eval vm_compute in s_log (fst (fst hrA)).
Definition hssA0' : sym_state := SS 0x20d58 srOOM0 [] knRE0 39.
Definition hrA' := Eval vm_compute in runH scr0 hssA0'.
Definition hsrA' : list expr := Eval vm_compute in s_regs (fst (fst hrA')).

Definition hresB : stdio_res :=
Eval vm_compute in match stdio_call 39 hsrA hknA with Some r => r
| None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition hresB' : stdio_res :=
Eval vm_compute in match stdio_call 39 hsrA' hknA with Some r => r
| None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Lemma hresB_eq : stdio_call 39 hsrA hknA = Some hresB.   Proof. vm_compute. reflexivity. Qed.
Lemma hresB'_eq : stdio_call 39 hsrA' hknA = Some hresB'. Proof. vm_compute. reflexivity. Qed.

Definition hsrB0 : list expr := Eval vm_compute in sc_sr hresB.
Definition hknB0 : list kentry := Eval vm_compute in sc_kn hresB.
Definition hssB0 : sym_state := SS 0x550e0 hsrB0 [] hknB0 71.
Definition hrB := Eval vm_compute in runH scr0 hssB0.
Definition hsrB : list expr := Eval vm_compute in s_regs (fst (fst hrB)).

Lemma msg_short_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x12fd7) 31 = Some msg_short.
Proof. vm_compute. reflexivity. Qed.
Lemma msg_overrun_img : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x110c0) 31 = Some msg_overrun.
Proof. vm_compute. reflexivity. Qed.

Tactic Notation "run_blkH" constr(scr) constr(NX) := run_block_gen FUEL STOPS_H scr NX true.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section HdrMsg.
Context {AMB : Amb}.
Variable sp0 : word.
Variable BL : list (list byte).
Variable model : Model.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].
Hypothesis Hfd2 : fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

Record hdr_post (M M' : word -> option byte) : Prop := {
hp_agree : forall x : word,
~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0 - 128)%Z ->
~ (0x66d38 + 8 <= bv_unsigned x < 0x66d38 + 24)%Z ->
~ (0x66d38 + 32 <= bv_unsigned x < 0x66d38 + 48)%Z ->
~ (0x66d38 + 56 <= bv_unsigned x < 0x66d38 + 64)%Z ->
~ (0x66d38 + 136 <= bv_unsigned x < 0x66d38 + 140)%Z ->
M' x = M x;
hp_grows : mem_grows M M';
hp_wend  : cell M' (0x66d38 + 32) 8 0x98348;
hp_wpos  : cell M' (0x66d38 + 40) 8 0x98348;
hp_wbase : cell M' (0x66d38 + 56) 8 0x98348;

hp_rpos  : cell M' (0x66d38 + 8) 8 0;
hp_rend  : cell M' (0x66d38 + 16) 8 0 }.

#[using="Hvsp Hh Hlazy Hfd2 SPlo SPhi"] Lemma hdr_sym : forall (pc : Z) (msg : list byte) vals R M K,
((pc = 0x20d3c /\ msg = msg_short) \/ (pc = 0x20d58 /\ msg = msg_overrun))%Z ->
length vals = 39%nat -> vals_ev vals 0 = sp0 ->
regs_ok (ENV BL vals) srOOM0 R -> know_ok RSEGS (ENV BL vals) M knRE0 ->
K [] ->
(forall R' M',
getr R' 10 = vals_ev vals 15 -> getr R' 1 = Z_to_bv 64 0x20d80 ->
getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R' 3 = Z_to_bv 64 0x10800 -> getr R' 4 = Z_to_bv 64 0x77c00 ->
getr R' 8 = vals_ev vals 14 -> getr R' 9 = vals_ev vals 15 ->
getr R' 18 = vals_ev vals 24 -> getr R' 19 = vals_ev vals 25 -> getr R' 20 = vals_ev vals 26 ->
getr R' 21 = vals_ev vals 27 -> getr R' 22 = vals_ev vals 28 -> getr R' 23 = vals_ev vals 29 ->
getr R' 24 = vals_ev vals 30 -> getr R' 25 = vals_ev vals 31 -> getr R' 26 = vals_ev vals 32 ->
getr R' 27 = vals_ev vals 33 ->
hdr_post M M' ->
realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x520b4) M' (seg_rom RSEGS)) model) K) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
(t_emit (W 2 msg) K).
Proof.
intros pc msg vals R M K Hpc HL P0 HR HK HKnil HCONT.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.

assert (STEP : forall T,
(forall R1 M1, regs_ok (ENV BL vals) (if Z.eqb pc 0x20d3c then hsrA else hsrA') R1 ->
know_ok RSEGS (ENV BL vals) M1 hknA -> M1 = mem_denot (ENV BL vals) M hlogA ->
realizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 0x551dc) M1 (seg_rom RSEGS)) model) T) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model) T).
{ intros T HT. destruct Hpc as [[-> _] | [-> _]].
- run_blkH scr0 39%nat. apply (HT _ _ HR HK EQM).
- run_blkH scr0 39%nat. apply (HT _ _ HR HK EQM). }
apply STEP. clear STEP HR HK. intros R1 M1 HR1 HK1 EQM1.

assert (RES : exists res s_lit, stdio_call (length vals) (if Z.eqb pc 0x20d3c then hsrA else hsrA') hknA = Some res
/\ sc_ret res = 0x550e0%Z /\ sc_f res = 0x66d38%Z /\ sc_fd res = 2%Z /\ sc_l res = ELit 31
/\ sc_wb res = ELit 0x98348 /\ sc_wp res = ELit 0x98348 /\ sc_s res = ELit s_lit
/\ sc_sr res = hsrB0 /\ sc_kn res = hknB0 /\ sc_sp res = sc_sp hresB
/\ sc_bufp res = ELit 0x98348 /\ sc_bufsz res = ELit 0
/\ rdn RSEGS (fun _ => None) (Z_to_bv 64 s_lit) 31 = Some msg /\ (0x10000 <= s_lit /\ s_lit + 31 <= 0x66000)%Z).
{ rewrite HL. destruct Hpc as [[-> ->] | [-> ->]]; cbn [Z.eqb Pos.eqb].
- exists hresB, 0x12fd7%Z. split; [exact hresB_eq|].
repeat split; try (vm_compute; reflexivity); try apply msg_short_img; cbn; lia.
- exists hresB', 0x110c0%Z. split; [exact hresB'_eq|].
repeat split; try (vm_compute; reflexivity); try apply msg_overrun_img; cbn; lia. }
destruct RES as (res & s_lit & Hres & Rret & Rf & Rfd & Rl & Rwb & Rwp & Rs & Rsr & Rkn & Rsp & Rbufp & Rbufsz & Rimg & Rsrng).
assert (Hmsglen : length msg = 31%nat).
{ destruct Hpc as [[_ ->] | [_ ->]]; reflexivity. }
unfold W. rewrite <- (app_nil_l msg). rewrite <- Rfd.
eapply (stdio_call_sound_post vals (blobs_ev BL) _ hknA R1 M1 model res [] msg K HR1 HK1 Hres);
rewrite ?Rwb, ?Rwp, ?Rl, ?Rs, ?Rfd, ?Rsp; cbn [edenot].
- lia.
- rewrite u_small by lia. lia.
- reflexivity.
- rewrite u_small by lia. rewrite Hmsglen. reflexivity.
- rewrite Hmsglen. cbn. lia.
- left. cbn [sc_sp hresB]. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
rewrite P0. rewrite !u_small by lia. lia.
- left. cbn [sc_sp hresB]. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
rewrite P0. rewrite !u_small by lia. lia.
- rewrite !u_small by lia. lia.
- reflexivity.
- rewrite Hmsglen.
rewrite (kimg_rdn RSEGS (ENV BL vals) M1 hknA ltac:(let i := kidx hknA (is_kimg_cov 0x110c0 31) in exact i)
_ _ s_lit 31 HK1 eq_refl) by lia.
exact Rimg.
- exact Hfd2.
- exact Hh.
- exact Hlazy.
- exact HKnil.
-
intros R2 M2 HR2 HK2 HPOST Ha0. rewrite Rsr in HR2. rewrite Rkn in HK2. rewrite Rret.
set (vals2 := vals ++ junk_vals R2) in *.
assert (HL2 : length vals2 = 71%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (QV : forall i, (i < 39)%nat -> vals_ev vals2 i = vals_ev vals i).
{ intros i Hi. subst vals2. apply vals_ev_app_l. rewrite HL. exact Hi. }
change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR2, HK2.
clearbody vals2.
rename HR2 into HR. rename HK2 into HK.
run_blkH scr0 71%nat.
apply HCONT.
all: try (regv HR0 (10 : reg) || idtac).
+ regv HR (10 : reg). change (edenot (ENV BL vals2) (EVar 15)) with (vals_ev vals2 15). apply QV. lia.
+ regv HR (1 : reg). reflexivity.
+ regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite Q0. try (f_equal; lia).
+ regv HR (3 : reg). reflexivity.
+ regv HR (4 : reg). reflexivity.
+ regv HR (8 : reg). change (edenot (ENV BL vals2) (EVar 14)) with (vals_ev vals2 14). apply QV. lia.
+ regv HR (9 : reg). change (edenot (ENV BL vals2) (EVar 15)) with (vals_ev vals2 15). apply QV. lia.
+ regv HR (18 : reg). change (edenot (ENV BL vals2) (EVar 24)) with (vals_ev vals2 24). apply QV. lia.
+ regv HR (19 : reg). change (edenot (ENV BL vals2) (EVar 25)) with (vals_ev vals2 25). apply QV. lia.
+ regv HR (20 : reg). change (edenot (ENV BL vals2) (EVar 26)) with (vals_ev vals2 26). apply QV. lia.
+ regv HR (21 : reg). change (edenot (ENV BL vals2) (EVar 27)) with (vals_ev vals2 27). apply QV. lia.
+ regv HR (22 : reg). change (edenot (ENV BL vals2) (EVar 28)) with (vals_ev vals2 28). apply QV. lia.
+ regv HR (23 : reg). change (edenot (ENV BL vals2) (EVar 29)) with (vals_ev vals2 29). apply QV. lia.
+ regv HR (24 : reg). change (edenot (ENV BL vals2) (EVar 30)) with (vals_ev vals2 30). apply QV. lia.
+ regv HR (25 : reg). change (edenot (ENV BL vals2) (EVar 31)) with (vals_ev vals2 31). apply QV. lia.
+ regv HR (26 : reg). change (edenot (ENV BL vals2) (EVar 32)) with (vals_ev vals2 32). apply QV. lia.
+ regv HR (27 : reg). change (edenot (ENV BL vals2) (EVar 33)) with (vals_ev vals2 33). apply QV. lia.
+
rewrite EQM. cbn [mem_denot].
rewrite Rf in HPOST. pose proof HPOST as HPOST0. destruct HPOST as [PA PG PW1 PW2 PW3].
assert (SU : bv_unsigned (edenot (Env (vals_ev vals) (blobs_ev BL)) (sc_sp hresB)) = (bv_unsigned sp0 - 192)%Z).
{ cbn [sc_sp hresB]. rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV].
rewrite P0. rewrite u_small by lia. lia. }
rewrite SU in PA.
constructor.
* intros x X1 X2 X3 X4 X5. pose proof (u64_range x) as Hx.
rewrite (PA x) by lia. rewrite EQM1. unfold hlogA. cbn [mem_denot].
unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. rewrite (u_small 0) by lia. cbn [Z.add].
repeat (rewrite wbytes_outside;
[ | rewrite ?length_N_to_le_bytes; unorm; cbn; lia
| rewrite ?length_N_to_le_bytes; unorm; cbn; lia ]).
reflexivity.
* eapply mem_grows_trans; [|exact PG]. rewrite EQM1. unfold hlogA. cbn [mem_denot].
repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
* unfold cell. rewrite Rbufp, Rbufsz in PW1. cbn [edenot] in PW1. rewrite PW1. f_equal.
* unfold cell. rewrite Rbufp in PW2. cbn [edenot] in PW2. exact PW2.
* unfold cell. rewrite Rbufp in PW3. cbn [edenot] in PW3. exact PW3.
* unfold cell. eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ HPOST0); [ | rewrite u_small by lia; lia | rewrite SU; rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia ].
rewrite EQM1. unfold hlogA. cbn [mem_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. rewrite (u_small 0) by lia. cbn [Z.add].
do 3 (rewrite rdn_wbytes_out; [ | rewrite ?length_N_to_le_bytes; unorm; cbn; lia | rewrite ?length_N_to_le_bytes; unorm; cbn; lia | rewrite ?length_N_to_le_bytes; unorm; cbn; lia ]).
apply rdn_wbytes_hit8; rewrite ?length_N_to_le_bytes; unorm; cbn; lia.
* unfold cell. eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ HPOST0); [ | rewrite u_small by lia; lia | rewrite SU; rewrite u_small by lia; lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia ].
rewrite EQM1. unfold hlogA. cbn [mem_denot]. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. rewrite (u_small 0) by lia. cbn [Z.add].
do 2 (rewrite rdn_wbytes_out; [ | rewrite ?length_N_to_le_bytes; unorm; cbn; lia | rewrite ?length_N_to_le_bytes; unorm; cbn; lia | rewrite ?length_N_to_le_bytes; unorm; cbn; lia ]).
apply rdn_wbytes_hit8; rewrite ?length_N_to_le_bytes; unorm; cbn; lia.
Qed.

Variables (tid : Z) (c : Z) (R : bvmap 5 word) (M : word -> option byte).
Hypothesis Rsp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128).
Hypothesis Rgp : getr R 3 = Z_to_bv 64 0x10800.
Hypothesis Rtp : getr R 4 = Z_to_bv 64 0x77c00.
Hypothesis Mstack : stack_writable M sp0.
Hypothesis Mimg : Forall (fun iv => img_clear M (fst iv) (snd iv)) re_ivs.
Hypothesis Mtid : cell M 0x77b58 4 tid.
Hypothesis Htid : (0 < tid < 2 ^ 22)%Z.
Hypothesis Mself : cell M 0x77b38 8 0x77b38.
Hypothesis Mcanary : cell M 0x97e70 8 c.
Hypothesis Mpagesz : cell M 0x97ec0 8 4096.

#[using="BL Hvsp Hh Hlazy Hfd2 SPlo SPhi tid c Rsp Rgp Rtp Mstack Mimg Mtid Htid Mself Mcanary Mpagesz"] Theorem ref_hdr_msg : forall (pc : Z) (msg : list byte) K,
((pc = 0x20d3c /\ msg = msg_short) \/ (pc = 0x20d58 /\ msg = msg_overrun))%Z ->
K [] ->
(forall R' M',
getr R' 10 = getr R 9 -> getr R' 1 = Z_to_bv 64 0x20d80 ->
getr R' 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R' 3 = Z_to_bv 64 0x10800 -> getr R' 4 = Z_to_bv 64 0x77c00 ->
getr R' 8 = getr R 8 -> getr R' 9 = getr R 9 ->
getr R' 18 = getr R 18 -> getr R' 19 = getr R 19 -> getr R' 20 = getr R 20 -> getr R' 21 = getr R 21 ->
getr R' 22 = getr R 22 -> getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 ->
getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
hdr_post M M' ->
realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 0x520b4) M' (seg_rom RSEGS)) model) K) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) model)
(t_emit (W 2 msg) K).
Proof.
intros pc msg K Hpc HKnil HCONT.
pose proof SPlo. pose proof SPhi.
assert (EVJ : forall i, (i < 32)%nat -> vals_ev (valsOOM sp0 tid c R) (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. exact (evOOM_junk sp0 BL tid c R i Hi). }
eapply (hdr_sym pc msg (valsOOM sp0 tid c R) R M K Hpc (valsOOM_len sp0 tid c R) eq_refl
(regs_okOOM sp0 BL Hvsp tid c R Rsp Rgp Rtp)
(know_okOOM sp0 BL Hvsp tid c R M Mstack Mimg Mtid Htid Mself Mcanary Mpagesz)
HKnil).
intros R' M' G10 G1 G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HP.
apply HCONT; try assumption.
all: first [ rewrite G10 | rewrite G8 | rewrite G9 | rewrite G18 | rewrite G19 | rewrite G20 | rewrite G21
| rewrite G22 | rewrite G23 | rewrite G24 | rewrite G25 | rewrite G26 | rewrite G27 ];
lazymatch goal with |- vals_ev _ ?n = _ =>
change n with (6 + (n - 6))%nat; rewrite EVJ by lia; f_equal; apply bv_eq; reflexivity end.
Qed.
End HdrMsg.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 QRjH QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq5.
Import Udbv UWQV.Mq0 UJvR.Mq0 UleT U1oC.Mq2 U1zM.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.
Context {SL : SrcLim}.

Section Branch.
Context {AMB : Amb}.
Variable sp0 : word.
Variables a0s path : list byte.
Variable envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.
Hypothesis Hva : valid_argv [a0s; path].
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 [a0s; path] envv tid regs0 mem0.
Hypothesis Hfit : entry_stack_fits sp0 [a0s; path] envv.

#[using="regs0 Hva Hve Hvsp ME Hfit"] Theorem open_err_branch_cannot_open :
U1zM.open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
Proof.
intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
apply (UleT.ref_open_fail_errno sp0 a0s path envv tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp ME Hfit
e vals R M (openat_errnos_range e He) HL P0 P38 P2 HR HK Habove).
Qed.
End Branch.

End FPGEN1.

End Mq1.

From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeDN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeDN. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMOs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMOs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqHD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqHD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFOH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFOH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUeZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUeZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJvR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJvR.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG24. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U9ch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U9ch.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG24.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG24.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UleT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UleT.Mq2.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section Usage.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av envv : list (list byte).
Variable tid : word.
Variable regs0 : bvmap 5 word.
Variable mem0 : word -> option byte.
Variable brk : word.
Variable mbase : word.
Variable fs0 : Fs.
Variable stdin0 : InputStream.

Variable lim : Z.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv tid regs0 mem0.
Hypothesis Hargc : length av <> 2%nat.

Hypothesis Hfit : entry_stack_fits sp0 av envv.

Definition model0 : Model :=
with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 lim (mkProcInputC av envv fs0 stdin0)).

Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

#[using="Type"] Lemma model0_halted : m_halted model0 = None. Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_lazy : m_vm_lazy model0 = []. Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_fd2 : fd_lookup (m_fds model0) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
#[using="Type"] Lemma model0_fs : m_fs model0 = fs0. Proof. reflexivity. Qed.

#[using="AMB sp0 envv tid regs0 mem0 Hva ME Hargc Hfit"] Lemma a0s_nonul : ~ In (Z_to_bv 8 0) (hd [] av).
Proof.
destruct Hva as ([H1 _] & _ & _ & Hn & _). destruct av as [|a0s rest]; [cbn in H1; lia|].
inversion Hn; subst. assumption.
Qed.

#[using="AMB tid regs0 mem0 Hva Hve Hvsp ME Hargc Hfit SPlo SPhi"] Lemma a0s_fits : (bv_unsigned (p0N sp0 av envv) + Z.of_nat (length (hd [] av)) + 1 <= 0x800000000000)%Z.
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
assert (Hlen : (1 <= length av)%nat) by (destruct Hva as [[H1 _] _]; lia).
unfold p0N. rewrite (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(lia)).
pose proof Hfit as HF. unfold entry_stack_fits, entry_stack_span, sp_window_hi in HF.
pose proof (total_arg_bytes_nonneg envv) as He.
destruct av as [|a0 rest]; [cbn in Hlen; lia|].
pose proof (total_arg_bytes_nonneg rest) as Hr.
cbn [firstn hd]. change (total_arg_bytes_nat []) with 0%nat.
unfold cat_struct_size, auxv_size. cbn [length total_arg_bytes fold_right] in HF. unfold auxv_size in HF.
fold (total_arg_bytes rest) in HF. cbn [length]. lia.
Qed.

#[using="AMB sp0 envv tid regs0 mem0 Hva ME Hargc Hfit"] Lemma hd_nth : hd [] av = nth 0 av [].
Proof. destruct av; reflexivity. Qed.

#[using="Hvsp SPlo SPhi"] Lemma umemcpy1_denot : forall vals M, vals_ev vals 0 = sp0 ->
mem_denot (ENV vals) M u_logM1 = wbytes M (Z_to_bv 64 (bv_unsigned sp0 - 560)) PRE7.
Proof.
intros vals M P0. pose proof SPlo. pose proof SPhi.
rewrite <- PRE7_word. cbn [mem_denot u_logM1].
unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0.
f_equal; f_equal; lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hargc Hfit SPlo SPhi"] Theorem ref_usage :
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_usage (hd [] av)) fs0).
Proof.
pose proof SPlo as Hlo. pose proof SPhi as Hhi.
assert (Hlen : (1 <= length av <= 1024)%nat) by (destruct Hva as [[H1 H2] _]; lia).
assert (HR : regs_ok (EN sp0 av envv tid regs0) sr_mainN regs0) by (eapply main_regs_okN; eassumption).
assert (HK : know_ok RSEGS (EN sp0 av envv tid regs0) mem0 kn_mainN) by (eapply main_know_okN; eassumption).
assert (Hac : ev (EN sp0 av envv tid regs0) 16 = argcN av) by (eapply evN_argc; eassumption).
change (EN sp0 av envv tid regs0) with (ENV (valsN sp0 av envv tid regs0)) in HR, HK, Hac.
set (vals := valsN sp0 av envv tid regs0) in *.
assert (HL : length vals = 39%nat) by (subst vals; apply valsN_length).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0N sp0 av envv) by reflexivity.
cbn [ev ENV] in Hac.
assert (STR := fun k Hk => main_strN sp0 av envv tid regs0 mem0 Hva Hve Hvsp ME k Hk) || idtac.
edestruct (main_strN sp0 av envv tid regs0 mem0) as (Sr & Slo & Shi & Slen & t8 & Ht8); try eassumption.
1:{ instantiate (1 := 0%nat). lia. }
rewrite <- hd_nth in Sr, Slen, Ht8. set (a0s := hd [] av) in *.
pose proof (u64_range (cat_argv_ptr sp0 av envv 0)) as Hppr.
clearbody vals.
pose proof model0_halted as Hh.

run_blk_keep u_scrA 39%nat.
{ unfold sc_denot. cbn [branch_taken edenot ev ENV]. rewrite Hac.
unfold bv_eqb. rewrite (u_argcN av Hva). change (bv_unsigned (Z_to_bv 64 2)) with 2%Z.
apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M x = mem0 x).
{ intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x99000);
[vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
clear EQM.

set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x110af) 7 = Some PRE7).
{ rewrite (kimg_rdn RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x110af 7) in exact i)
_ _ 0x110af 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
assert (Hdst : store_ok RSEGS M dst 7 = true).
{ pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
_ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
assert (MC : mcH M dst (Z_to_bv 64 0x110af) 7 PRE7).
{ constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
- exact Hsrc.
- exact Hdst. }
lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
assert (A1 : getr Rc 1 = (0x55024 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
assert (A10 : getr Rc 10 = dst)
by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
assert (A11 : getr Rc 11 = Z_to_bv 64 0x110af) by (regv HR (11 : reg); reflexivity);
assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
destruct (ref_memcpy M dst (Z_to_bv 64 0x110af) 7 _ (seg_rom RSEGS) MC Rc (0x55024 : word)
ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
clear A1 A10 A11 A12
end.
replace (Z_to_bv 64 390200) with (0x5f438 : word) by (apply bv_eq; reflexivity).
eapply rz_msteps; [exact Hh | exact model0_lazy | exact Hms |]. clear Hms.
replace (0x55024 : word) with (Z_to_bv 64 0x55024) by (apply bv_eq; reflexivity).
lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M dst PRE7) u_knB0).
{ subst dst. rewrite <- (umemcpy1_denot vals M P0).
eapply (carry_after RSEGS (ENV vals) M u_logM1 u_knA [] u_knB0 [] []);
[vm_compute; reflexivity | | exact HK | constructor].
cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
clear HK.
pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M dst PRE7) u_knB0
ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
clear HK2.
set (vals1 := vals ++ junk_vals R2) in *.
assert (HL1 : length vals1 = 71%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
assert (Q1 : vals_ev vals1 1 = p0N sp0 av envv) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
clearbody vals1.
change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
rewrite <- model0_fs.
eapply (us_tail sp0 model0 Hvsp model0_halted model0_lazy model0_fd2 a0s (p0N sp0 av envv) t8 vals1); try eassumption.
- apply a0s_nonul.
- unfold p0N. lia.
- pose proof a0s_fits as HFp. fold a0s in HFp. unfold p0N in HFp |- *. clearbody a0s. lia.
- unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
- unfold p0N. rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hargc Hfit SPlo SPhi"] Corollary ref_usage_w :
realizes RSEGS (mkCfg (mkst regs0 (0x20b84 : word) mem0 (seg_rom RSEGS)) model0)
(t_die (msg_usage (hd [] av)) fs0).
Proof.
replace (0x20b84 : word) with (Z_to_bv 64 0x20b84) by (apply bv_eq; reflexivity). apply ref_usage.
Qed.

End Usage.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
