(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QsRG Qnhz Qrxj QRjH Qpox QsV0 Q9ox QBxa Qn1e QiVh QMz4 QO3A Q7m0 QSpR QuJV QCPB QH7x QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv UFOH UFeQ UWQV U1oC U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qpox QsV0 QRjH Q9ox.Mq2 QBxa.Mq4 Qn1e.Mq1 QiVh Qn1e QBxa.Mq0 QMz4 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QqES.
Import Udbv UFOH.Mq0 UFeQ.
Import QSpR.Mq3.
Import UWQV.Mq0.
Import QSpR.Mq1 QBxa.Mq6.
Import U1oC.Mq2 U1zM.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section L.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable tid : word.
Hypothesis Hva : valid_argv av.
Hypothesis Hlo : (sp_window_lo <= bv_unsigned sp0)%Z.
Hypothesis Hhi : (bv_unsigned sp0 <= sp_window_hi)%Z.

#[using="Hva"] Lemma D_main_locale : forall segs,
rdn segs (D_main sp0 av ev tid) (Z_to_bv 64 0x77bd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x97ec8)).
Proof.
intros segs. pose proof (u64_range tid). pose proof (len_av av Hva). unfold sp_window_lo, sp_window_hi in *.
unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.
End L.

Definition entry_stack_b (spi : nat) (lo : Z) (e : sentry) : bool :=
match e with
| SE (SA (EVar i) k) w _ => (Nat.eqb i spi) && (lo <=? k)%Z && (k + Z.of_nat w <=? 0)%Z
| _ => false
end.

Lemma mem_denot_below : forall E M log spi lo (x : word),
forallb (entry_stack_b spi lo) log = true ->
(0 <= bv_unsigned (ev E spi) + lo)%Z ->
(bv_unsigned x < bv_unsigned (ev E spi) + lo)%Z ->
mem_denot E M log x = M x.
Proof.
intros E M log spi lo x Hb H0 Hx.
induction log as [|[[b k] w v] rest IH]; [reflexivity|].
cbn [forallb] in Hb. apply andb_prop in Hb as [He Hrest].
destruct b as [z|i| | | | | |]; cbn [entry_stack_b] in He; try discriminate.
apply andb_prop in He as [He1 He3]. apply andb_prop in He1 as [He1 He2].
apply Nat.eqb_eq in He1. subst i. apply Z.leb_le in He2. apply Z.leb_le in He3.
pose proof (u64_range (ev E spi)) as Hs. pose proof (u64_range x) as Hxr.
cbn [mem_denot]. rewrite wbytes_outside.
- apply IH. exact Hrest.
- rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
- rewrite length_N_to_le_bytes. left. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
Qed.

Lemma logA_stack : forallb (entry_stack_b 0 (-8388608)) logA = true.
Proof. vm_compute. reflexivity. Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qpox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpox. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsV0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsV0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9ox.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9ox.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QiVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qn1e.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn1e. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udbv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1oC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1oC.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1zM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1zM.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Tactic Notation "run_block" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX false.
Tactic Notation "run_block_keep" constr(scr) constr(NX) := run_block_gen FUEL STOPS scr NX true.

Section Open.
Context {fF : FPF} {fC : FPC}.
Context {AMB : Amb}.
Context {SL : SrcLim}.
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
Hypothesis Hbrk : valid_brk RSEGS brk.
Hypothesis Hpne : path <> [].
Hypothesis Hplen : (length path <= 4095)%nat.

Notation ENV := (U1zM.ENV a0s path).
Notation model0 := (U1zM.model0 sp0 a0s path envv tid brk mbase fs0 stdin0).
Notation model1g := (U1zM.model1g sp0 tid brk mbase fs0 stdin0).
Notation above_sp0 := (U1zM.above_sp0 sp0 mem0).

Hypothesis HKA : open_err_branch sp0 a0s path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).

Definition open_ok_branch (fd3 : FdEntry) (KB : TSet) : Prop :=
forall vals R M,
length vals = 39%nat -> vals_ev vals 0 = sp0 ->
vals_ev vals 1 = p0 sp0 a0s path envv -> vals_ev vals 2 = p1 sp0 a0s path envv ->
vals_ev vals 3 = auxvp sp0 a0s path envv -> vals_ev vals 4 = rnd sp0 a0s path envv -> vals_ev vals 5 = tid ->
vals_ev vals 38 = ssp_canary ->
regs_ok (ENV vals) srB0 R -> know_ok RSEGS (ENV vals) M knA -> above_sp0 M ->
M = mem_denot (ENV vals) mem0 logA ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x6086c) M (seg_rom RSEGS)) (model1g fd3)) KB.

#[using="Hva Hve Hvsp Htid ME Hpne Hplen HKA"] Lemma open_seg : forall KB,
(path <> QBxa.Mq5.dot_path -> forall fdata, fs_lookup fs0 path = Some fdata -> open_ok_branch (FdFile path (Z_to_bv 64 0)) KB) ->
(path = QBxa.Mq5.dot_path -> open_ok_branch FdDir KB) ->
(path <> QBxa.Mq5.dot_path -> exists fdata, fs_lookup fs0 path = Some fdata) ->
realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x20b84) mem0 (seg_rom RSEGS)) model0)
(t_alt2 (t_die (msg_cannot_open path) fs0) KB).
Proof.
intros KB HKfile HKdot Hfs.
pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi.
unfold sp_window_lo, sp_window_hi in *.
pose proof (main_regs_ok sp0 a0s path envv tid regs0 mem0 Hvsp Htid ME) as HR.
pose proof (main_know_ok sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp Htid ME) as HK.
change (E0 sp0 a0s path envv tid regs0) with (ENV (vals0 sp0 a0s path envv tid regs0)) in HR, HK.
set (vals := vals0 sp0 a0s path envv tid regs0) in *.
assert (HL : length vals = 39%nat) by (subst vals; unfold vals0; rewrite !length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0 sp0 a0s path envv) by reflexivity.
assert (P2 : vals_ev vals 2 = p1 sp0 a0s path envv) by reflexivity.
assert (P3 : vals_ev vals 3 = auxvp sp0 a0s path envv) by reflexivity.
assert (P4 : vals_ev vals 4 = rnd sp0 a0s path envv) by reflexivity.
assert (P5t : vals_ev vals 5 = tid) by reflexivity.
assert (P38 : vals_ev vals 38 = ssp_canary) by reflexivity.
destruct (main_str sp0 a0s path envv tid regs0 mem0 Hva Hve Hvsp ME 1%nat ltac:(lia)) as (Sr & Slo & Shi & Slen).
cbn [nth] in Sr, Slo, Shi, Slen.
clearbody vals.

run_block_keep scr0 39%nat.
assert (Sr' : rdn RSEGS M (p1 sp0 a0s path envv) (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
{ rewrite EQM. unfold p1. rewrite (rdn_mem_denot_above RSEGS (ENV vals) mem0 _ 0%nat 0x99000);
[exact Sr | vm_compute; reflexivity | cbn [ev U1zM.ENV]; rewrite P0; lia | cbn [ev U1zM.ENV]; rewrite P0; lia | lia
| pose proof (u64_range (cat_argv_ptr sp0 [a0s; path] envv 1)); lia]. }
assert (HA : above_sp0 M).
{ intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) mem0 _ 0%nat 0x99000);
[vm_compute; reflexivity | cbn [ev U1zM.ENV]; rewrite P0; lia | cbn [ev U1zM.ENV]; rewrite P0; lia | lia]. }

assert (KAok : forall e, In e openat_errnos ->
realizes RSEGS (mkCfg (mkst (regupd R 10 (errno_ret e)) (v_addi (Z_to_bv 64 0x60868) 4) M (seg_rom RSEGS)) model0)
(t_die (msg_cannot_open path) fs0)).
{ intros e He. rewrite v_addi_pc4 by lia. change (0x60868 + 4)%Z with 0x6086c%Z.
lazymatch type of HR with regs_ok _ ?sr ?Rc =>
pose proof (env_app_regs vals [errno_ret e] _ sr Rc ltac:(rewrite HL; vm_compute; reflexivity) HR) as HR2 end.
lazymatch type of HK with know_ok _ _ ?Mc ?kn =>
pose proof (env_app_know RSEGS vals [errno_ret e] _ Mc kn ltac:(rewrite HL; vm_compute; reflexivity) HK) as HK2 end.
change (Env (vals_ev (vals ++ [errno_ret e])) (blobs_ev (blobs0 a0s path))) with (ENV (vals ++ [errno_ret e])) in HR2, HK2.
eapply (HKA e (vals ++ [errno_ret e])); try eassumption.
+ rewrite length_app, HL. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P0.
+ rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P1.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P2.
+ rewrite vals_ev_app_l by (rewrite HL; lia). exact P5t.
+ apply regs_set_a0; [exact HR2|]. cbn [edenot ev U1zM.ENV].
rewrite <- HL, <- (Nat.add_0_r (length vals)). rewrite vals_ev_app_r. reflexivity. }
pose proof (regs_set_a0 (ENV vals) _ _ (Z_to_bv 64 3) (ELit 3) HR eq_refl) as HR3.
assert (EDOT : Uapi.dot_path = QBxa.Mq5.dot_path) by reflexivity.
destruct (list_eq_dec (fun x y : byte => bv_eq_dec _ x y) path QBxa.Mq5.dot_path) as [Hdot|Hndot].
-
eapply (rz_openat_dot RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
+ vm_compute. reflexivity.
+ reflexivity.
+ reflexivity.
+ regv HR (17 : reg). reflexivity.
+ regv HR (10 : reg). apply bv_eq. reflexivity.
+ regv HR (12 : reg). vm_compute. reflexivity.
+ rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
+  rewrite EDOT, <- Hdot. split; [exact Hplen|]. split; [apply (U1zM.path_nonul a0s path Hva)|].
regv HR (11 : reg). cbn [edenot ev U1zM.ENV]. rewrite P2. exact Sr'.
+ exact KAok.
+ rewrite v_addi_pc4 by lia. change (0x60868 + 4)%Z with 0x6086c%Z.
rewrite m0_fds. rewrite alloc_fd_fds0.
change (with_fds (fd_insert (U1zM.fds0) (Z_to_bv 64 3) FdDir) model0) with (model1g FdDir).
eapply (HKdot Hdot vals); eassumption.
-
destruct (Hfs Hndot) as [fdata Hfile].
eapply (rz_openat_file RSEGS _ _ _ model0 ECALLW); try apply is_ecall_ECALLW.
+ vm_compute. reflexivity.
+ reflexivity.
+ reflexivity.
+ regv HR (17 : reg). reflexivity.
+ regv HR (10 : reg). apply bv_eq. reflexivity.
+ regv HR (12 : reg). vm_compute. reflexivity.
+ rewrite m0_fds. rewrite alloc_fd_fds0. apply fd_lookup_fds0_3.
+  split; [exact Hplen|]. split; [apply (U1zM.path_nonul a0s path Hva)|].
regv HR (11 : reg). cbn [edenot ev U1zM.ENV]. rewrite P2. exact Sr'.
+ exact Hpne.
+ apply (U1zM.path_noslash a0s path tid Hva Htid).
+ apply (U1zM.path_not_dirref a0s path tid Hva Htid). rewrite <- ?EDOT. exact Hndot.
+ rewrite m0_fs. exact Hfile.
+ exact KAok.
+ rewrite v_addi_pc4 by lia. change (0x60868 + 4)%Z with 0x6086c%Z.
rewrite m0_fds. rewrite alloc_fd_fds0.
change (with_fds (fd_insert (U1zM.fds0) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 0))) model0)
with (model1g (FdFile path (Z_to_bv 64 0))).
eapply (HKfile Hndot fdata Hfile vals); eassumption.
Qed.
End Open.
