(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz Qrxj QEVk QSjk QRjH QiVh Qn1e QsV0 QBxa QSpR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90 UMOs UFOH UWQV U1SW USPu UU2A U8LG UZSc UsN4 UlKb U39n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QEVk.Mq0 QSjk.Mq0 QRjH.Mq4 QRjH.Mq3 QiVh.Mq0 Qn1e.Mq1 QRjH.Mq1 QsV0 QRjH QBxa.Mq4 QBxa.Mq5 QSpR.Mq0.
Import Um90 Um90.Mq1 Um90.Mq2 UMOs.Mq0 UMOs.Mq1 UFOH UWQV U1SW USPu UU2A U8LG UZSc UsN4 UlKb U39n.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

#[using="Type"] Theorem ref_exit_clean :
forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
exit_common regs mem sp tp code tid wp2 rp2 ->
file_clean mem 0x66e28 wp1 rp1 ->
m_halted model = None -> m_vm_lazy model = [] ->
realizes RSEGS (mkCfg (mkst regs (0x50e6c : word) mem (seg_rom RSEGS)) model)
(t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
destruct EC.

destruct ec_atx as [armed ATX]. pose proof (proj1 ec_glob) as Gnl0.
destruct (w1 armed regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.

destruct (w2 regs1 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: lazymatch goal with |- realizes _ _ _ => idtac | _ => destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; first [store_ok_peel; exact ec_sok | rdn_solve] end.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.

destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3a regs2 (mem_w2 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
1:{ unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; rdn_solve. }
1:{ repeat split; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve. }
1:{ repeat split; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.

eapply rz_exit_at; [exact F_4ee68 | exact E_4ee68 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

#[using="Type"] Theorem ref_exit_flush :
forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
(wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
exit_common regs mem sp tp code tid wp2 rp2 ->
stdout_pending mem wb wp bufp bufsz rp1 can pending ->
m_halted model = None -> m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
realizes RSEGS (mkCfg (mkst regs (0x50e6c : word) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.

destruct ec_atx as [armed ATX]. pose proof (proj1 ec_glob) as Gnl0.
destruct (w1 armed regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
try assumption.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.

destruct (w2 regs1 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) (seg_rom RSEGS) sp code (getr regs1 9))
as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
all: lazymatch goal with |- realizes _ _ _ => idtac | _ => destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; first [store_ok_peel; exact ec_sok | rdn_solve] end.
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.

destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
destruct (w3b1 regs2 (mem_w2 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9))
(seg_rom RSEGS) sp code wb wp)
as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
1:{ unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; store_ok_peel; exact ec_sok. }
1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; rdn_solve. }
1:{ repeat split; unfold mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve. }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.

replace (Z_to_bv 64 0x54e2c) with (0x54e2c : word) in R3ra by (apply bv_eq; reflexivity).
unfold W. rewrite <- (app_nil_r pending).
set (mem3 := mem_w3a (mem_w2 (mem_w1 armed mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) code tid) sp code (getr regs1 9)) sp code).
eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x66e28 wb wp 1
(Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x54e2c : word) pending []);
[ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
| lia | lia
|
subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; sok_stack ec_sok
| lia | lia
|  split; subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve
|  split; subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; rdn_solve
| lia | exact Hfd | exact Hh | exact Hlazy
| lia | lia | exact LEN
| cbn [length]; u_norm; reflexivity
| cbn [length]; lia
| lia | u_norm; lia | u_norm; lia
| subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; repeat rdn_peel1; exact BYTES
| reflexivity
| apply ret_ok_even; reflexivity
| apply t_emit_has_nil
| ].
intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
rewrite R3s0 in Q8.
destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; destruct armed; cbn [mem_w1]; unfold mem_w1A, mem_w1I, mem_w1c; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
eapply rz_exit_at; [exact F_4ee68 | exact E_4ee68 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

#[using="Type"] Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

#[using="Type"] Theorem ref_exit : forall regs mem model code pending,
exit_pre regs mem model code pending ->
realizes RSEGS (mkCfg (mkst regs (0x50e6c : word) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
- eapply rz_conseq; [ | apply t_emit_nil_exit ].
eapply ref_exit_clean; eassumption.
- eapply ref_exit_flush; eassumption.
Qed.

#[using="Type"] Corollary ref_exit_Z : forall regs mem model code pending,
exit_pre regs mem model code pending ->
realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x50e6c) mem (seg_rom RSEGS)) model)
(t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
intros. replace (Z_to_bv 64 0x50e6c) with (0x50e6c : word) by (apply bv_eq; reflexivity).
apply ref_exit; assumption.
Qed.
End FPGEN1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq0.
From Stdlib Require NArith.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.Riscv Require Sem.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJyS QO3A Q7m0 QuJV QCPB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ Udbv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QRjH.Mq3 Qn1e QRjH.Mq0 QRjH.Mq2 QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QBxa.Mq2 QBxa.Mq6 QSpR.Mq3.
Import UFeQ Udbv UFOH.Mq0 UWQV.Mq0.
Import QH7x.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section MainEntryN.
Context {AMB : Amb}.
Variable sp0 : word.
Variables av envv : list (list byte).
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp envv.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av envv tid regs mem.

Definition p0N : word := cat_argv_ptr sp0 av envv 0.
Definition auxvpN : word := auxv_w sp0 av envv.
Definition rndN : word := at_random_ptr sp0 av envv.

Definition valsN : list word := [sp0; p0N; p0N; auxvpN; rndN; tid] ++ junk_vals regs ++ [ssp_canary].
Definition EN : env := Env (vals_ev valsN) (blobs_ev []).

Definition sr_mainN : list expr :=
[ELit 0; ELit 0x508ac; spx (-48); ELit 0x10800; ELit 0x77c00; EVar 11; EVar 12; EVar 13;
spx 8; EVar 15; EVar 16; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
EVar 22; EVar 23; ELit 0x20b84; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_stackN : list kentry :=
[KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
KWr (SA (EVar 0) (-8388608)) 8388608;
KWord (SA (EVar 0) 8) 8 (EVar 1);
KRange (EVar 1) 0x7fff80000000 0x800000400000].

Definition kn_mainN : list kentry := kn_stackN ++ kn_image.

Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

#[using="sp0 Hva"] Lemma len_avN : (1 <= length av <= 1024)%nat.
Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

#[using="Type"] Lemma evN_junk : forall i, (i < 32)%nat -> ev EN (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof.
intros i Hi. unfold EN. cbn [ev]. unfold valsN.
change (6 + i)%nat with (length [sp0; p0N; p0N; auxvpN; rndN; tid] + i)%nat.
unfold vals_ev. rewrite app_nth2_plus. rewrite app_nth1 by (unfold junk_vals; rewrite length_map, length_seq; exact Hi).
unfold junk_vals.
rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
Qed.

#[using="Type"] Lemma spxN_val : forall k, edenot EN (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev EN 0) with sp0.
apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

Ltac reg_caseN :=
cbn [nth sr_mainN all_regs];
first [ rewrite spxN_val
| lazymatch goal with |- _ = edenot _ (EVar ?n) =>
change (edenot EN (EVar n)) with (ev EN n);
first [ rewrite (evN_junk (n - 6)) by lia; reflexivity | idtac ]
| |- _ => cbn [edenot] end ];
first [ reflexivity
| exact (me_ra _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ ME)
| exact (me_s2 _ _ _ _ _ _ ME)
| rewrite (me_sp _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
| rewrite (me_s0 _ _ _ _ _ _ ME); reflexivity
| rewrite (me_a1 _ _ _ _ _ _ ME); reflexivity
| apply (me_szero _ _ _ _ _ _ ME); cbn; tauto
| idtac ].

#[using="mem Hvsp Htid ME Hlo Hhi"] Theorem main_regs_okN : regs_ok EN sr_mainN regs.
Proof.
pose proof Hlo. pose proof Hhi.
apply regs_ok_by_index.
intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_caseN.
Qed.

#[using="AMB tid regs Hva Hve Hvsp ME Hlo Hhi"] Lemma main_strN : forall k, (k < length av)%nat ->
rdn RSEGS mem (cat_argv_ptr sp0 av envv k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
/\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr sp0 av envv k))%Z
/\ (bv_unsigned (cat_argv_ptr sp0 av envv k) <= bv_unsigned sp0 + 2107576)%Z
/\ (Z.of_nat (length (nth k av [])) <= 131071)%Z
/\ (exists t8, rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 av envv k) + Z.of_nat (length (nth k av []))))
8 = Some t8).
Proof.
intros k Hk'. pose proof Hlo. pose proof Hhi.
pose proof (lay_bsb_nw RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_hi; lia)) as Hnw.
destruct (argv_ptr_bounds_at sp0 av envv Hva Hve ltac:(unfold sp_window_hi; lia) k Hk') as [B1 B2].
pose proof (u_cat_argv_ptr sp0 av envv Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
pose proof (struct_av_bound av envv Hva Hve) as Hsb.
pose proof (total_arg_bytes_firstn_le k av) as Hf.
pose proof (argv_str_len av Hva k Hk') as Hlen.
pose proof (rdn_wmem_stack RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd) as Hw. unfold wmem in Hw.
repeat split.
- rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by lia.
rewrite Hw by lia. apply read_argv_cstr_k; [exact Hk' | exact Hnw].
- exact B1.
- lia.
- exact Hlen.
- destruct (read_word_stack RPH RSEGS sp0 av envv k (length (nth k av [])) a_uid a_hwcap a_rnd Hk' ltac:(lia) Hnw) as (t8 & Hl8 & Hr8).
exists t8. rewrite w_add_nat in Hr8.
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
rewrite Hw by (rewrite u_small by lia; lia). exact Hr8.
Qed.

#[using="Type"] Lemma keN0 : ev EN 0 = sp0. Proof. reflexivity. Qed.
#[using="Type"] Lemma keN1 : ev EN 1 = p0N. Proof. reflexivity. Qed.
#[using="Type"] Lemma keN3 : ev EN 3 = auxvpN. Proof. reflexivity. Qed.
#[using="Type"] Lemma keN5 : ev EN 5 = tid. Proof. reflexivity. Qed.
#[using="Type"] Lemma keN38 : ev EN 38 = ssp_canary. Proof. reflexivity. Qed.

#[using="Hva Hve Hvsp ME Hlo Hhi Hal"] Lemma know_stackN : know_ok RSEGS EN mem kn_stackN.
Proof.
pose proof Hlo. pose proof Hhi. pose proof Hal. pose proof len_avN as Hlen.
destruct (main_strN 0%nat ltac:(lia)) as (_ & B1 & B2 & _ & _).
unfold kn_stackN, know_ok.
repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?keN0, ?keN1;
unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?keN0.
- split; [lia | exact Hal].
- lia.
- split; [lia|]. intros d m Hd Hm.
apply (main_entry_store_ok_win sp0 av envv tid regs mem ME); rewrite u_small by lia; unfold stack_max_size; lia.
- split; [lia|]. split; [lia|].
unfold adenot. cbn [a_base a_off edenot]. rewrite keN0. unfold v_addi.
rewrite (main_entry_rdn_above sp0 av envv tid regs mem ME) by (rewrite u_small by lia; lia).
pose proof (read_argv_ptr_w RSEGS RPH sp0 av envv a_uid a_hwcap a_rnd Hva Hve ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat ltac:(lia)) as Hr.
unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
rewrite Hr. rewrite n_to_le_8_spec. reflexivity.
- unfold p0N. lia.
Qed.

#[using="Hvsp Hlo Hhi"] Lemma D_main_auxvpN : forall segs,
rdn segs (D_main sp0 av envv tid) (Z_to_bv 64 0x97e98) 8
= Some (word_to_le_bytes 8 auxvpN).
Proof.
intros segs. pose proof (u64_range tid). pose proof Hlo. pose proof Hhi.
unfold auxvpN, D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
apply rdn_wbytes_hit8. unorm; lia.
Qed.

#[using="Type"] Lemma wseg_dataN : wseg_ok RSEGS (Z_to_bv 64 0x66000) 0x33000 = true.

Proof. exact (@UWQV.Mq0.wseg_data). Qed.

#[using="sp0 Hvsp Hlo"] Lemma range_disjoint_subN : forall lo n c i, range_disjoint_b lo n c = true ->
(lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> range_disjoint_b i 1 c = true.
Proof.
intros lo n [c w] i H Hlo' Hhi'. unfold range_disjoint_b in *. cbn [fst snd] in *.
apply orb_true_iff in H. apply orb_true_iff. rewrite !Z.leb_le in *. cbn [Z.of_nat Pos.of_succ_nat]. lia.
Qed.

#[using="sp0 Hvsp Hlo"] Lemma missb_subN : forall lo n i, D_main_missb lo n = true ->
(lo <= i)%Z -> (i + 1 <= lo + Z.of_nat n)%Z -> D_main_missb i 1 = true.
Proof.
intros lo n i H Hlo' Hhi'. unfold D_main_missb in *.
apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3.
apply andb_true_iff; split; [apply andb_true_iff; split|]; [| apply Z.leb_le; lia | apply Z.leb_le; cbn [Z.of_nat Pos.of_succ_nat]; lia].
apply forallb_forall. intros c Hc. apply (range_disjoint_subN lo n); [|lia|lia].
apply (proj1 (forallb_forall _ _) H1). exact Hc.
Qed.

#[using="Hva Hvsp ME Hlo Hhi"] Lemma kimg_okN : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x99000)%Z ->
kentry_ok RSEGS EN mem (KImg lo hi).
Proof.
intros lo hi Hb Hle Hhi'. pose proof Hlo as HLO. pose proof Hhi as HHI.
assert (Hlo0 : (0 <= lo)%Z).
{ unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _]. apply andb_true_iff in Hb as [_ Hb].
apply Z.leb_le in Hb. exact Hb. }
cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
rewrite (main_entry_mem_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia).
apply (D_main_none sp0 av envv tid i Hva); [lia | lia |].
apply (missb_subN lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
Qed.

Ltac kimgN := apply kimg_okN; [vm_compute; reflexivity | lia | lia].

Ltac kw_preN :=
split; [lia|]; split; [lia|];
unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
Ltac kw_dataN L :=
kw_preN;
rewrite (main_entry_rdn_data sp0 av envv tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
rewrite (L RSEGS); try reflexivity.
Ltac kw_memN L := kw_preN; rewrite (L RSEGS); try reflexivity.

#[using="Hva Hvsp Htid ME Hlo Hhi"] Lemma know_imageN : know_ok RSEGS EN mem kn_image.
Proof.
pose proof Hlo as HLO. pose proof Hhi as HHI. pose proof (u64_range tid) as Ht.
unfold kn_image, know_ok.
repeat apply Forall_cons; try apply Forall_nil;
try kimgN;
cbn [kentry_ok a_base a_off edenot]; rewrite ?keN3, ?keN5, ?keN38; unfold flat, estart, elenZ; cbn [a_base a_off edenot];
rewrite ?(u_small 0) by lia; cbn [Z.add].
-  split; [lia|]. intros d m Hd Hm.
eapply (store_ok_window RSEGS mem (Z_to_bv 64 0x66000) (Z_to_bv 64 (0x66000 + d)) 0x33000 m 0x66000 0x99000);
[reflexivity | reflexivity | cbn; lia | apply wseg_dataN | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
- kw_dataN (D_main_self sp0 av envv tid).
- kw_memN (main_entry_tid sp0 av envv tid HLO regs mem ME).
- kw_dataN (D_main_canary sp0 av envv tid).
- kw_memN (main_entry_guard sp0 av envv tid HLO regs mem ME).
- kw_dataN D_main_auxvpN.
- kw_dataN (D_main_pagesize sp0 av envv tid Hva).
-  lia.
Qed.

#[using="Hva Hve Hvsp Htid ME Hlo Hhi Hal"] Theorem main_know_okN : know_ok RSEGS EN mem kn_mainN.
Proof.
unfold kn_mainN, know_ok. apply Forall_app; split; [apply know_stackN | apply know_imageN].
Qed.

#[using="Type"] Lemma valsN_length : length valsN = 39%nat.
Proof. unfold valsN. rewrite !length_app, junk_vals_length. reflexivity. Qed.

#[using="mem ME"] Lemma evN_argc : ev EN 16 = argcN av.
Proof. change 16%nat with (6 + 10)%nat. rewrite (evN_junk 10) by lia. exact (me_a0 _ _ _ _ _ _ ME). Qed.
End MainEntryN.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OssFuzzTheorems.json_c.json_object_fuzzer.images.Ubsan.
Import QJyS QsRG.Mq0 Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x QBxa.Mq3.
Import UWQV.Mq0.

Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition kn_exec : list kentry := kn_main.

Definition STOPS : list Z := [0x5f438; 0x5f9b8; 0x5fe24; 0x5f33c; 0x21024; 0x53a78; 0x50e6c; 0x551dc]%Z.

Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].

Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
fst (fst (carry (s_log (fst (fst r))) kn [])).

Definition NV0 : nat := 39%nat.

Definition ssA0 : sym_state := SS 0x20b84 sr_main [] kn_exec NV0.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_exec.
Definition logA : list sentry := Eval vm_compute in s_log (fst (fst rA)).

Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0x6086c srB0 [] knA NV0.

End FPGEN1.
End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqES. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSjk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSjk.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UFeQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UFeQ.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um90.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um90. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWQV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWQV.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition SC_KEPT : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Record stdio_res : Type := SCR_ {
sc_f : Z;
sc_fd : Z;
sc_ret : Z;
sc_wb : expr;
sc_wp : expr;
sc_bufp : expr;
sc_bufsz : expr;
sc_s : expr;
sc_l : expr;
sc_sp : expr;
sc_sr : list expr;
sc_kn : list kentry
}.

Definition lit_even_ret (e : expr) : option Z :=
match e with
| ELit r => if ((r mod 2 =? 0) && (0 <=? r) && (r <? two64))%bool then Some r else None
| _ => None
end.

Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
match K with
| KImg lo hi =>
if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
| _ => [K]
end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
| ELit f, Some ret =>
match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
kread RSEGS kn (ELit 0) 0x659d0 8, kread RSEGS kn (ELit 0) 0x97e70 8 with
| Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some _ =>
let sp := nth 2 sr (ELit 0) in
let '(qb, k0) := split_lit sp in
let qk := (k0 - 112)%Z in
match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
| Some _, Some (blo, bhi) =>
if ((0x66000 <=? f) && (f + 232 <=? 0x97e70)
&& ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0x97e70)
&& (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
&& expr_vars_lt nv bufp && expr_vars_lt nv bufsz
&& sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
then
let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
let k1 := kn_frame k0 qb qk 112 in
let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
(sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
(KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
:: KWord (SA (ELit 0) (f + 40)) 8 bufp
:: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
else None
| _, _ => None
end
| _, _, _, _, _, _, _ => None
end
| _, _ => None
end.

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

#[using="Type"] Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

#[using="Type"] Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence. Qed.

#[using="Type"] Lemma know_ok_frame3 : forall E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3,
know_ok RSEGS E M kn ->
flat E (SA b1 o1) n1 -> flat E (SA b2 o2) n2 -> flat E (SA b3 o3) n3 ->
(forall x : word,
~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + n1)%Z ->
~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + n2)%Z ->
~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + n3)%Z ->
M' x = M x) ->
mem_grows M M' ->
know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3).
Proof.
intros E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3 HK F1 F2 F3 Hout Hg.
set (a1 := estart E (SA b1 o1)) in *. set (a2 := estart E (SA b2 o2)) in *. set (a3 := estart E (SA b3 o3)) in *.
set (M1 := fun x : word => if (inr a2 n2 x || inr a3 n3 x)%bool then M x else M' x).
set (M2 := fun x : word => if inr a3 n3 x then M x else M' x).
assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + n1 <= bv_unsigned x)%Z -> M1 x = M x).
{ intros x Hx. unfold M1. destruct (inr a2 n2 x) eqn:E2; [reflexivity|]. destruct (inr a3 n3 x) eqn:E3; [reflexivity|].
cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
assert (G1 : mem_grows M M1).
{ intros x Hx. unfold M1. destruct (inr a2 n2 x || inr a3 n3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + n2 <= bv_unsigned x)%Z -> M2 x = M1 x).
{ intros x Hx. unfold M1, M2. destruct (inr a3 n3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
destruct (inr a2 n2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
assert (G2 : mem_grows M1 M2).
{ intros x Hx. unfold M1, M2 in *. destruct (inr a3 n3 x); [rewrite orb_true_r in Hx; exact Hx|].
destruct (inr a2 n2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + n3 <= bv_unsigned x)%Z -> M' x = M2 x).
{ intros x Hx. unfold M2. destruct (inr a3 n3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
assert (G3 : mem_grows M2 M').
{ intros x Hx. unfold M2 in Hx. destruct (inr a3 n3 x); [exact (Hg x Hx) | exact Hx]. }
eapply know_ok_frame; [| exact F3 | exact O3 | exact G3].
eapply know_ok_frame; [| exact F2 | exact O2 | exact G2].
eapply know_ok_frame; [exact HK | exact F1 | exact O1 | exact G1].
Qed.

#[using="Type"] Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros A P x H. constructor; [exact H | constructor]. Qed.

#[using="Type"] Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one'; exact HKK).
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one'; exact HKK|].
apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Himg).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one'. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
- destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one'. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.

#[using="Type"] Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.

#[using="Type"] Lemma flat_abs0 : forall E off n, (0 <= off)%Z -> (0 <= n)%Z -> (off + n <= 2 ^ 64)%Z -> (off < 2 ^ 64)%Z ->
flat E (SA (ELit 0) off) n.
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.

#[using="Type"] Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
intros E e b k H.
assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
{ intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
unfold split_lit in H.
destruct e; try (injection H as <- <-; apply G).
- injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
- lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

#[using="Type"] Lemma split_lit_vars : forall n e b k, split_lit e = (b, k) -> expr_vars_lt n e = true -> expr_vars_lt n b = true.
Proof.
intros n e b k H Hv. unfold split_lit in H.
destruct e; try (injection H as <- <-; first [reflexivity | exact Hv]).
lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

#[using="Type"] Lemma kindex_some : forall p kn i j, kindex p kn i = Some j ->
exists K, nth_error kn (j - i) = Some K /\ p K = true /\ (i <= j)%nat.
Proof.
intros p kn. induction kn as [|K rest IH]; intros i j H; cbn [kindex] in H; [discriminate|].
destruct (p K) eqn:HP.
- injection H as <-. exists K. rewrite Nat.sub_diag. cbn. auto.
- destruct (IH (S i) j H) as (K' & Hn & HP' & Hle). exists K'.
replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error]. repeat split; try assumption. lia.
Qed.

#[using="Type"] Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

#[using="Type"] Lemma sr_get_nat : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
intros sr n Hn. unfold sr_get.
assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.

#[using="Type"] Lemma length_sr_upd : forall sr n e, (n < length sr)%nat -> length (sr_upd sr n e) = length sr.
Proof.
intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
destruct n; cbn [sr_upd length]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.

#[using="Type"] Lemma nth_sr_upd_same : forall sr n e, (n < length sr)%nat -> nth n (sr_upd sr n e) (ELit 0) = e.
Proof.
intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
destruct n; cbn [sr_upd nth]; [reflexivity|]. apply IH. lia.
Qed.

#[using="Type"] Lemma nth_sr_upd_other : forall sr n m e, n <> m -> nth m (sr_upd sr n e) (ELit 0) = nth m sr (ELit 0).
Proof.
intros sr. induction sr as [|h t IH]; intros n m e Hne.
- revert m Hne. induction n as [|n IHn]; intros m Hne; cbn [sr_upd].
+ destruct m; [lia | destruct m; reflexivity].
+ destruct m; [reflexivity|]. cbn [nth]. rewrite IHn by lia. destruct m; reflexivity.
- destruct n; destruct m; cbn [sr_upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.

#[using="Type"] Lemma length_sr_after_call_j : forall sr kept nv, length (sr_after_call_j sr kept nv) = 32%nat.
Proof. intros. unfold sr_after_call_j. rewrite length_map, length_seq. reflexivity. Qed.

#[using="Type"] Theorem stdio_call_sound :
forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
(R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
(pending extra : list byte) (K : TSet),
let E := Env (vals_ev vals) ebs in
regs_ok E sr R -> know_ok RSEGS E M kn ->
stdio_call (length vals) sr kn = Some res ->
let wb := bv_unsigned (edenot E (sc_wb res)) in
let wp := bv_unsigned (edenot E (sc_wp res)) in
let s := edenot E (sc_s res) in
let l := edenot E (sc_l res) in
let su := bv_unsigned (edenot E (sc_sp res)) in
(wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS M s (length extra) = Some extra ->
fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
m_halted model = None -> m_vm_lazy model = [] ->
K [] ->
(forall R' M',
regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x551dc) M (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
destruct (kread RSEGS kn (ELit 0) 0x659d0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
destruct (kread RSEGS kn (ELit 0) 0x97e70 8) as [canv|] eqn:Hcan; [|discriminate].
destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
intros Hwbwp Hwpts Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hh Hlz HKnil HCONT.
set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.

apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
apply andb_prop in Hcond as [Hf0 Hf232].
apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.

assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
{ unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
{ intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
assert (R1 : getr R 1 = Z_to_bv 64 ret).
{ replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
assert (R10 : getr R 10 = Z_to_bv 64 f).
{ replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
rewrite H10. reflexivity. }
assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
{ replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R11 : getr R 11 = s).
{ replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R12 : getr R 12 = l).
{ replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
set (sp := edenot E (nth 2 sr (ELit 0))) in *.
pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
{ subst su. rewrite Hsqd. apply u64_lit. lia. }
pose proof (u64_range sp) as Hspr2. fold su in Hspr2.

destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
{ unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }

assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
{ intros off n A B C. apply flat_abs0; lia. }
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x659d0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x97e70 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
fold wp in Hwpr. fold wb in Hwbr.

replace (Z_to_bv 64 0x551dc) with (0x551dc%bv : word) by (apply bv_eq; reflexivity).
eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
pending extra K).
- rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
- exact R10.
- exact R11.
- exact R12.
- exact R1.
- lia.
- lia.
- exact Wst'.
- lia.
- lia.
- constructor.
+ rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rfd. cbn [edenot]. reflexivity.
+ exact Rbufp.
+ exact Rbufsz.
- split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
- apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
- exact Hfdlk.
- exact Hh.
- exact Hlz.
- lia.
- lia.
- exact Hlenp.
- exact Hlene.
- exact H30.
- exact Dw.
- exact Ds.
- exact Hsl.
- exact Rpend.
- exact Rextra.
- apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
- exact HKnil.
-
intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
apply HCONT.
+
assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
{ apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
- intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
(split; [lia|]);
lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
| replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
| replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
| replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
| replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
| replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
| replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
| replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
| replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
| replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
| replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
| replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
| replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
| replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
| replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
| replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
end.
- unfold SC_KEPT. cbn [In]. lia. }
apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
[ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
intros i Hi. rewrite length_sr_after_call_j in Hi.
destruct (Nat.eq_dec i 10) as [->|Hne].
* rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
* rewrite nth_sr_upd_other by lia. reflexivity.
+
destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
assert (HK3 : know_ok RSEGS E' M'
(kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
(ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
{ assert (Eqb : edenot E' qb = edenot E qb).
{ symmetry. apply (edenot_agree (length vals)); [exact Hag|].
apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
- unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
- intros x N1 N2 N3. apply Pagree.
+ unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
+ unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
+ unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
subst E'.
repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
* rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
* rewrite Xb. exact Pwpos.
* rewrite Xb. exact Pwbase.
Qed.

#[using="Type"] Theorem stdio_call_sound_post :
forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
(R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
(pending extra : list byte) (K : TSet),
let E := Env (vals_ev vals) ebs in
regs_ok E sr R -> know_ok RSEGS E M kn ->
stdio_call (length vals) sr kn = Some res ->
let wb := bv_unsigned (edenot E (sc_wb res)) in
let wp := bv_unsigned (edenot E (sc_wp res)) in
let s := edenot E (sc_s res) in
let l := edenot E (sc_l res) in
let su := bv_unsigned (edenot E (sc_sp res)) in
(wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
(wp - wb = Z.of_nat (length pending))%Z ->
(bv_unsigned l = Z.of_nat (length extra))%Z ->
(Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
(wp <= su - 112 \/ su <= wb)%Z ->
(bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
(bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
rdn RSEGS M s (length extra) = Some extra ->
fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
m_halted model = None -> m_vm_lazy model = [] ->
K [] ->
(forall R' M',
regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
getr R' 10 = l ->
realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x551dc) M (seg_rom RSEGS)) model)
(t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
destruct (kread RSEGS kn (ELit 0) 0x659d0 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
destruct (kread RSEGS kn (ELit 0) 0x97e70 8) as [canv|] eqn:Hcan; [|discriminate].
destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
intros Hwbwp Hwpts Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hh Hlz HKnil HCONT.
set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.

apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
apply andb_prop in Hcond as [Hf0 Hf232].
apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.

assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
{ unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
{ intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
assert (R1 : getr R 1 = Z_to_bv 64 ret).
{ replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
assert (R10 : getr R 10 = Z_to_bv 64 f).
{ replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
rewrite H10. reflexivity. }
assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
{ replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R11 : getr R 11 = s).
{ replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
assert (R12 : getr R 12 = l).
{ replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
set (sp := edenot E (nth 2 sr (ELit 0))) in *.
pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
{ subst su. rewrite Hsqd. apply u64_lit. lia. }
pose proof (u64_range sp) as Hspr2. fold su in Hspr2.

destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
{ unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }

assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
{ intros off n A B C. apply flat_abs0; lia. }
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x659d0 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x97e70 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
fold wp in Hwpr. fold wb in Hwbr.

replace (Z_to_bv 64 0x551dc) with (0x551dc%bv : word) by (apply bv_eq; reflexivity).
eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
pending extra K).
- rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
- exact R10.
- exact R11.
- exact R12.
- exact R1.
- lia.
- lia.
- exact Wst'.
- lia.
- lia.
- constructor.
+ rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
+ rewrite Rfd. cbn [edenot]. reflexivity.
+ exact Rbufp.
+ exact Rbufsz.
- split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
- apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
- exact Hfdlk.
- exact Hh.
- exact Hlz.
- lia.
- lia.
- exact Hlenp.
- exact Hlene.
- exact H30.
- exact Dw.
- exact Ds.
- exact Hsl.
- exact Rpend.
- exact Rextra.
- apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
- exact HKnil.
-
intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
apply HCONT; [ | | exact HPOST | exact G10].
+
assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
{ apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
- intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
(split; [lia|]);
lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
| replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
| replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
| replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
| replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
| replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
| replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
| replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
| replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
| replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
| replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
| replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
| replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
| replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
| replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
| replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
end.
- unfold SC_KEPT. cbn [In]. lia. }
apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
[ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
intros i Hi. rewrite length_sr_after_call_j in Hi.
destruct (Nat.eq_dec i 10) as [->|Hne].
* rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
* rewrite nth_sr_upd_other by lia. reflexivity.
+
destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
assert (HK3 : know_ok RSEGS E' M'
(kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
(ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
{ assert (Eqb : edenot E' qb = edenot E qb).
{ symmetry. apply (edenot_agree (length vals)); [exact Hag|].
apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
- unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
- intros x N1 N2 N3. apply Pagree.
+ unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
+ unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
+ unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
subst E'.
repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
* rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
* rewrite Xb. exact Pwpos.
* rewrite Xb. exact Pwbase.
Qed.
End FPGEN1.

