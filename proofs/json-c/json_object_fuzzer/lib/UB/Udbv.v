(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJyS. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq6.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uhzw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uhzw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq8. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90.Mq9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1SW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1SW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULxO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULxO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5hz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5hz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UoL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UoL3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuT1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuT1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require USPu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import USPu. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UU2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UU2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8LG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8LG.
Import ListNotations.
Open Scope bv_scope.

#[local] Existing Instance fp0F.
#[local] Existing Instance fp0C.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

Lemma with_tid_halted_c : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_tid_lazy_c : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. reflexivity. Qed.

Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
let J6 := J_tls sp0 (J_aux sp0 av ev (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
(Z_to_bv 64 0x506a0) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x97e90)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
(Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x506a8)))
(Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
(Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x5089c)))
(Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))
(Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))
(Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x507ec)))
(Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x62688)).

Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
(regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
me_ra  : getr regs 1 = Z_to_bv 64 0x508ac;
me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
me_tp  : getr regs 4 = Z_to_bv 64 0x77c00;
me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
me_s1  : getr regs 9 = argcN av;
me_a0  : getr regs 10 = argcN av;
me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
me_s2  : getr regs 18 = Z_to_bv 64 0x20b84;
me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
me_mem : exists (J : word -> option byte) (s1v : word),
wfJ sp0 J /\ J = J_main sp0 av ev s1v
/\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd) J (D_main sp0 av ev tid)
}.

Section Assembly.
Context {AMB : Amb}.
Variable sp : word.
Variables argv envp : list (list byte).
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hvsp : valid_sp sp.

Variable P : machine_state -> Model -> Prop.
Hypothesis P_bwd : forall model, m_halted model = None -> m_vm_lazy model = [] ->
bwd rsegs (fun st => P st model).

Hypothesis P_set_tid : forall regs (pc : word) mem model w,
fetch_word rsegs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
P (mkst (regupd regs 10 tid) (v_addi pc 4) mem (seg_rom rsegs)) (with_tid tid model)) ->
P (mkst regs pc mem (seg_rom rsegs)) model.

#[using="Hvsp"] Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof. destruct Hvsp as [H _]. exact H. Qed.
#[using="Hvsp"] Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
#[using="Hvsp"] Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

Ltac side Hva Hve HG :=
first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
| apply wfJ_const
| lazymatch goal with |- getr _ _ = _ =>
gres; first [ assumption | reflexivity | bveq
| match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
first [reflexivity | f_equal; lia | bveq] end ] end
| idtac ].

#[using="Hva Hve Hvsp P_bwd P_set_tid J0"] Theorem startup_sec : forall (model : Model),
m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
(forall tid regs mem,
(0 < bv_unsigned tid < 2^22)%Z ->
main_entry sp argv envp tid regs mem ->
P (mkst regs (0x20b84 : word) mem (seg_rom rsegs)) (with_tid tid model)) ->
P (mkst (regs_init sp) (0x20a38 : word) (wrap_mem RPH sp argv envp a_uid a_hwcap a_rnd) (seg_rom rsegs)) model.
Proof.
intros model Hh Hlazy Ht0 HK.
pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. pose proof Hal as Hal'.
pose proof (u64_range sp) as Hsp.
set (RZ := fun st : machine_state => P st model).
assert (HG : bwd rsegs RZ) by (apply P_bwd; [exact Hh | exact Hlazy]).
rewrite cmem_init.
change (P ?st model) with (RZ st).

destruct (p1_run sp argv envp Hva Hve Hlo' Hhi' Hal' (seg_rom SEGS) J0 (wfJ_const sp _))
as [regs1 (R1 & A1 & A2 & A3 & A4 & A8 & A9 & A10 & A11 & A12 & A18 & Az)].
eapply HG; [exact R1|].

assert (A1' : getr regs1 1 = (0x505bc : word)) by (rewrite A1; apply bv_eq; reflexivity).
destruct (memset304_run regs1 (cmem sp (wrap_mem RPH sp argv envp a_uid a_hwcap a_rnd) (J1 sp argv J0) (fun _ => None))
(seg_rom SEGS) (Z_to_bv 64 (bv_unsigned sp - 368)) (0x505bc : word) A1')
as [regs2 [mem2 (R2 & M2 & G2)]].
{ unfold ret_ok. apply bv_eq. vm_compute. reflexivity. }
{ exact A10. } { exact A11. } { exact A12. }
{ rewrite u_Z2bv by lia. rewrite <- Zminus_mod_idemp_l.
replace (bv_unsigned sp mod 8)%Z with 0%Z; [reflexivity|].
symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2%Z; reflexivity). rewrite Hal'. reflexivity. }
{ rewrite u_Z2bv by lia. lia. }
{ apply store_ok_cmem_win; [unfold J1; repeat apply wfJ_wbytes; apply wfJ_const | region_side | region_side]. }
eapply HG; [exact R2|]. subst mem2.
rewrite wbytes_cmem_win by region_side.

carry G2 A2 (2:reg) B2. carry G2 A8 (8:reg) B8. carry G2 A9 (9:reg) B9. carry G2 A10 (10:reg) B10.
carry G2 A3 (3:reg) B3.
eapply (p3_run sp argv envp) with (G := RZ); try side Hva Hve HG.
{ unfold J1; repeat apply wfJ_wbytes; apply wfJ_const. }
intros regs3 C1 C2 C10 C18 G3.
carry G3 B3 (3:reg) C3. carry G3 B8 (8:reg) C8.
assert (Cz : forall r : reg, In r [5; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs3 r = Z_to_bv 64 0).
{ intros r Hr. rewrite (G3 r), (G2 r); [apply Az; exact Hr | |];
clear -Hr; cbn [In] in Hr; intros HH; cbn [In] in HH;
repeat (destruct Hr as [<-|Hr]; [repeat (destruct HH as [HH|HH]; [apply bv_eq in HH; cbv in HH; discriminate HH|]); exact HH |]); exact Hr. }
pose proof (Cz 19 ltac:(in_list)) as Z19. pose proof (Cz 20 ltac:(in_list)) as Z20.
pose proof (Cz 21 ltac:(in_list)) as Z21. pose proof (Cz 22 ltac:(in_list)) as Z22.
pose proof (Cz 23 ltac:(in_list)) as Z23. pose proof (Cz 24 ltac:(in_list)) as Z24.
pose proof (Cz 25 ltac:(in_list)) as Z25. pose proof (Cz 26 ltac:(in_list)) as Z26.
pose proof (Cz 27 ltac:(in_list)) as Z27.

change (J1 sp argv J0) with (J_lsm sp argv J0).
eapply (tls_c1 sp J0 argv envp) with (G := RZ) (x9v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4a; intros.
eapply (tls_c2 sp J0 argv envp) with (G := RZ) (x9v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4b; intros.
eapply (tls_c3 sp J0 argv envp) with (G := RZ) (x9v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4c; intros.
eapply (tls_c4a sp J0 argv envp) with (G := RZ) (x9v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4d; intros.
eapply (tls_c4b sp J0 argv envp) with (G := RZ) (x9v := getr regs3 9) (tid := Z_to_bv 64 0); try side Hva Hve HG.
intros regs4; intros.

unfold RZ at 1.
eapply (P_set_tid regs4 (0x50b0c : word) _ model W_4ed84 F_4ed84 E_4ed84);
[exact Hh | exact Hlazy | assumption | exact Ht0 |].
intros tid Htid.
replace (v_addi (0x50b0c : word) 4) with (0x50b10 : word) by (apply bv_eq; reflexivity).
set (model' := with_tid tid model).
assert (Hh' : m_halted model' = None) by (unfold model'; rewrite with_tid_halted_c; exact Hh).
assert (Hlazy' : m_vm_lazy model' = []) by (unfold model'; rewrite with_tid_lazy_c; exact Hlazy).
set (RZ' := fun st : machine_state => P st model').
assert (HG' : bwd rsegs RZ') by (apply P_bwd; [exact Hh' | exact Hlazy']).
change (P ?st model') with (RZ' st).
assert (Htid' : (0 < bv_unsigned tid < 2^22)%Z) by (unfold PID_MAX_ENVELOPE in Htid; lia).
eapply (tls_c5 sp J0 argv envp) with (G := RZ') (x9v := getr regs3 9); try side Hva Hve HG'.
intros regs5; intros.
eapply (fin_c6 sp J0 argv envp) with (G := RZ') (x9v := getr regs3 9); try side Hva Hve HG'.
intros regs6; intros.
eapply (fin_c7 sp J0 argv envp) with (G := RZ') (x9v := getr regs3 9); try side Hva Hve HG'.
intros regs7; intros.
eapply (fin_c8 sp J0 argv envp) with (G := RZ') (x9v := getr regs3 9); try side Hva Hve HG'.
intros regs8; intros.
eapply (fin_c9 sp J0 argv envp) with (G := RZ') (x9v := getr regs3 9); try side Hva Hve HG'.
intros regs9 M1 M2 M3 M4 M8 M9 M10 M11 M12 M18 M19 M20 M21 M22 M23 M24 M25 M26 M27 G9.
unfold RZ'. apply (HK tid regs9). { exact Htid'. }
split; try assumption.
- intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [assumption|]). destruct Hr.
- eexists _, (getr regs3 9). split; [|split; [reflexivity|]].
+ unfold J_main, J_tls, J_aux, J_lsm. repeat apply wfJ_wbytes. apply wfJ_const.
+ unfold J_main, J_tls, D_main, D_fd, D_ssp, D_tls, D_tlsA, D_tlsB. reflexivity.
Qed.

End Assembly.

Theorem startup : forall (P : machine_state -> Model -> Prop),
(forall model, m_halted model = None -> m_vm_lazy model = [] -> bwd rsegs (fun st => P st model)) ->
(forall regs (pc : word) mem model w,
fetch_word rsegs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
P (mkst (regupd regs 10 tid) (v_addi pc 4) mem (seg_rom rsegs)) (with_tid tid model)) ->
P (mkst regs pc mem (seg_rom rsegs)) model) ->
forall sp brk mbase rnd lim inp (Hsp : valid_sp sp),
valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
(forall tid regs mem,
(0 < bv_unsigned tid < 2^22)%Z ->
@main_entry (amb_of inp rnd sp Hsp) sp (in_argv inp) (in_envp inp) tid regs mem ->
P (mkst regs (0x20b84 : word) mem (seg_rom rsegs))
(with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) ->
P (cfg_ms (init_config rsegs rpc rph sp brk mbase rnd lim inp))
(cfg_model (init_config rsegs rpc rph sp brk mbase rnd lim inp)).
Proof.
intros P P_bwd P_set_tid sp brk mbase rnd lim inp Hsp Hva Hve HK.
unfold init_config. cbn [cfg_ms cfg_model].
rewrite init_mkst.
replace (Z_to_bv 64 (Z.of_N Ubsan.M.init_pc)) with (0x20a38 : word) by (apply bv_eq; reflexivity).
fold (regs_init sp).
apply (@startup_sec (amb_of inp rnd sp Hsp) sp (in_argv inp) (in_envp inp) Hva Hve Hsp P P_bwd P_set_tid);
[reflexivity | reflexivity | reflexivity | exact HK].
Qed.

Section Consumers.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av ev : list (list byte).
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis ME : main_entry sp0 av ev tid regs mem.

#[using="tid regs ME"] Lemma main_entry_rdn_above : forall segs (a : word) n,
(bv_unsigned sp0 <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd) a n.
Proof.
intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply rdn_cmem_above; assumption.
Qed.

#[using="tid regs ME"] Lemma main_entry_mem_above : forall (a : word),
(bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev a_uid a_hwcap a_rnd a.
Proof.
intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply cmem_at_above. exact Ha.
Qed.

#[using="AMB av ev tid regs ME"] Lemma main_entry_store_ok_win : forall segs (a : word) n,
(bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
store_ok segs mem a n = true.
Proof.
intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
Qed.

#[using="regs ME"] Lemma main_entry_mem_data : forall (a : word),
(bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
mem a = D_main sp0 av ev tid a.
Proof.
intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply cmem_at_data. unfold win_lo. exact Ha.
Qed.

#[using="regs ME"] Lemma main_entry_rdn_data : forall segs (a : word) n,
(bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
rdn segs mem a n = rdn segs (D_main sp0 av ev tid) a n.
Proof.
intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
apply rdn_cmem_data. unfold win_lo. exact Ha.
Qed.
End Consumers.
