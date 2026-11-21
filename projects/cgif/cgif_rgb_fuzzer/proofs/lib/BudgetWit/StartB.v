(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from YO3p.v: its realizes lemmas (src2_start_gen, src2_start) and its tactics restated over BudgetWit.Rzb.rzb. *)
(* Modified by Theorem Labs, 2026-11: made again from the LPS 727298f3 YO3p.v: the section is over the run's ProcInput, the entry and the launch premises, YO3p's section lemmas are bound to its closed lemmas (the ews rewrites typed over E_stR), the run's CONFIG_RSEQ flag is split only where a state must compute, and the register splices peel their update lists with explicit cons and nil steps; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1a YK1b YK15 YK0o YQ0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YL02 YO3u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH05 YO3s.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib.BudgetWit Require Import Rzb RunB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.

(** * The start of the process over [rzb]

    [YO3p.src2_start_gen] and [YO3p.src2_start] take the process from
    [init_config] through musl's [_start_c] and [__libc_start_main] to the call of
    [main], as a [YK15.realizes] proof.  This file restates both over
    [BudgetWit.Rzb.rzb] ([realizes] with a budget check at each node):

    - [src2_start_gen_b] mirrors [YO3p.src2_start_gen];
    - [src2_start_b] mirrors [YO3p.src2_start].

    The statements are YO3p's with [realizes] written [rzb]; the binders are the
    same and in the same order (section [f] has YO3p's section variables, its
    notations for the run's projections and its [E_stR]).  The proofs are YO3p's
    with these renames: [rz_msteps] is [Rzb.rzb_msteps], [rz_set_tid_first] is
    [RunB.rzb_set_tid_first], and the goal patterns match [rzb] for [realizes].
    The runs are taken by [RunB]'s copies of [sym_run_with] and [sym_run_to_with].
    Those lemmas build each [rzb] node with its [budget_ok]; no node is built in
    this file, so no statement has a new hypothesis.

    Tactics of YO3p copied here under their own names: [sym_spliceL] (its body
    names [rz_msteps], here [rzb_msteps]), and [reg_of] and [sym_add_chunk_sem]
    (bodies unchanged; YO3p defines them inside its section [f]).

    YO3p's section [f] lemmas that the proof of [src2_start_gen] uses
    ([runs_main_init], [alias_memset_ok], [alias_envp_ok], [ews1], [ews2], [ews4],
    [ews5], [ews7], [ews8], [envp_block_reads], [argv0_reads]) are YO3p's own: each
    is bound here by a [Let] to YO3p's closed lemma at this section's variables
    ([yo3p] feeds them in declaration order and skips the ones a lemma does not
    take), so the proof text names them as YO3p's does. *)

Section f.
(* The start-up proof reasons about one RUN [inp] at the entry [mkEntry sp brk
   mbase rnd] the launch admits ([Hlau]).  The names below are NOTATIONS for
   the run's projections, not [Let]s, so every lemma of [YQ0a] stated over
   [in_argv inp], [ed_top rnd], ... matches them syntactically.  [rs] is the
   run's CONFIG_RSEQ flag, never a literal: the proof splits on it only where a
   symbolic state has to compute. *)
Variable inp : ProcInput.
Variables mbase sp brk : word.
Variable rnd : EntryDraw.
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
Local Notation xf := (in_execfn inp) (only parsing).
Local Notation rs := (kb_rseq (in_kernel inp)) (only parsing).
Local Notation top := (ed_top rnd) (only parsing).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Ltac yo3p L := let H := fresh "L" in pose proof L as H;
try specialize (H inp); try specialize (H mbase); try specialize (H sp); try specialize (H brk);
try specialize (H rnd); try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve);
try specialize (H Hvl); try specialize (H Hlau);
exact H.
Let E_stR (t : word) : env := E_st sp inp mbase t rnd.
Let runs_main_init := ltac:(yo3p @YO3p.runs_main_init).
Let alias_memset_ok := ltac:(yo3p @YO3p.alias_memset_ok).
Let alias_envp_ok := ltac:(yo3p @YO3p.alias_envp_ok).
(* The [ews*] are stated over [E_stR], as in YO3p, so that [rewrite] meets the goal's own
   spelling (the closed lemmas spell the environment as a beta-redex). *)
Let ews1 : forall t, bv_unsigned (ew (E_stR t) 1) = z_argv (bv_unsigned top) argv envp xf 0
:= ltac:(yo3p @YO3p.ews1).
Let ews2 : forall t, bv_unsigned (ew (E_stR t) 2)
= z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (length (nth 0 argv [])) + 1
:= ltac:(yo3p @YO3p.ews2).
Let ews4 : forall t, bv_unsigned (ew (E_stR t) 4) = z_envp (bv_unsigned sp) argv
:= ltac:(yo3p @YO3p.ews4).
Let ews5 : forall t, bv_unsigned (ew (E_stR t) 5) = z_auxv (bv_unsigned sp) argv envp
:= ltac:(yo3p @YO3p.ews5).
Let ews7 : forall t, bv_unsigned (ew (E_stR t) 7)
= z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (progname_off (nth 0 argv []))
:= ltac:(yo3p @YO3p.ews7).
Let ews8 : forall t, ew (E_stR t) 8 = t := ltac:(yo3p @YO3p.ews8).
Let envp_block_reads := ltac:(yo3p @YO3p.envp_block_reads).
Let argv0_reads := ltac:(yo3p @YO3p.argv0_reads).
Ltac sym_spliceL HS Hms k E' Hagree upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rzb_msteps; [assumption | assumption | exact Hms | ];
rewrite Hshape in HS; clear Hshape;
unshelve epose proof (st_ok_set_regs segs k E E' ss _ regs' _ pc' _ upd HS Hagree _ _ _ _ _);
[ vm_compute; reflexivity
| reflexivity
| vm_compute; reflexivity
|
|
| clear HS Hms;
match goal with Hn : st_ok _ _ (set_regs_pc _ _ _) _ |- _ => rename Hn into HS end;
sym_norm HS ]
end end.
Ltac reg_of HS r H :=
pose proof (st_ok_reg src2segs _ _ _ r HS) as H;
eval_sr_get_in H; cbn [sv_denot] in H; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in H.
Ltac sym_add_chunk_sem HS b c :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let r := eval vm_compute in (add_chunk_sem (ss_mem ss) b c) in
lazymatch r with
| Some (?rs', ?cs) =>
let H := fresh "Hadd" in let HS' := fresh "HS'" in
assert (H : add_chunk_sem (ss_mem ss) b c = Some (rs', cs)) by (vm_compute; reflexivity);
unshelve epose proof (st_ok_add_chunk_sem segs E ss ms b c rs' cs HS H _) as HS';
[ cbn [base_val ms_mem]
| clear H HS; rename HS' into HS;
lazymatch type of HS with st_ok _ _ ?ss2 _ =>
let ss3 := eval vm_compute in ss2 in change (st_ok segs E ss3 ms) in HS end ]
| None => fail "sym_add_chunk_sem: chunk not inside a region of that base"
end
end.
Lemma src2_start_gen_b : forall (two : bool) model T,
(if two then (2 <= length argv)%nat else True) ->
m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src2segs (E_main sp inp argv envp xf tid rnd) (ss_main two rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp top argv envp xf rnd) ->
rzb src2segs (mkCfg ms (with_tid tid model)) T) ->
rzb src2segs (mkCfg (init_machine_state src2segs Plain_init_pc Plain_phdrs sp mbase rnd inp) model) T.
Proof.
intros two model T Htwo Hh Hlz Htid K.
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. unfold z_xfn in L. unfold SP_LO, SP_HI in L.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
(* the ported lemma takes the RUN and twelve datom premises.  [xd_run] is the
   witness for all twelve - seven by [reflexivity], the eight cache words by
   [xd_run_cw] - so nothing here is pinned and nothing is restated. *)
pose proof (src2_init_st_ok inp mbase sp brk rnd (xw_main sp top argv envp xf (Z_to_bv 64 0) rnd) (xd_run inp sp mbase rnd) two
Hsp Hva Hve Hvl Hlau eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
(fun i Hi => xd_run_cw inp sp mbase rnd i Hi) Htwo) as HS.
change (st_ok src2segs (E_stR (Z_to_bv 64 0)) (src2_ss0 two rs)
(init_machine_state src2segs Plain_init_pc Plain_phdrs sp mbase rnd inp)) in HS.
apply (st_ok_add_alias src2segs _ _ _ (fst alias_memset) (snd alias_memset)) in HS; [|apply alias_memset_ok].
apply (st_ok_add_alias src2segs _ _ _ (fst alias_envp) (snd alias_envp)) in HS; [|apply alias_envp_ok].
change (st_ok src2segs (E_stR (Z_to_bv 64 0)) (ss_start two rs)
(init_machine_state src2segs Plain_init_pc Plain_phdrs sp mbase rnd inp)) in HS.
pose proof (runs_main_init two Plain_init_pc Htwo) as HR.
(* [E_st] and [E_main] read the run's CONFIG_RSEQ flag inside, so this split
   reaches [ss_start], [ss_main] and [L] - the places that need it concrete -
   and leaves the environments, and the [ews*] rewrites over them, alone.
   [HS] and [K] are reverted first: [destruct] on a term abstracts it in the
   goal only, and a state left with the flag opaque cannot compute. *)
revert HS K. destruct two; destruct (kb_rseq (in_kernel inp)); intros HS K.
all: sym_run_with src2tbl_ok HS.
all: idtac "PHASE B".
all: reg_of HS (9%bv:reg) H9.
all: lazymatch goal with |- rzb _ (mkCfg ?ms _) _ =>
destruct (envp_block_reads (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 0 _ _ HR eq_refl))
as (Hnz & Hz & Hnw);
destruct (src2_envp_count (length envp) (ms_regs ms) (ms_mem ms) (seg_rom src2segs) _ H9 Hnz Hz Hnw)
as (regs1 & Hms & R10 & R9 & Rfr) end.
all: lazymatch type of HS with st_ok _ ?E _ _ =>
sym_spliceL HS Hms 9%nat E (env_agree_refl 9%nat E) upd_envp end;
[ sym_splice_frame Rfr
(* [upd_envp] is a [Definition]: unfold it so the list is a literal cons chain, peel each entry
   with [Forall_cons] and close the nil tail with [Forall_nil]; [constructor] chooses between the
   two by unifying against the unexpanded name. *)
| unfold upd_envp;
repeat (apply Forall_cons;
[ split;
[ reflexivity
| cbn [fst snd sv_denot];
first [ exact R10
| rewrite R9, Z.add_0_r, ews4, ews5; apply (f_equal (Z_to_bv 64)); lia ] ]
| ]);
apply Forall_nil
| ].
all: clear H9 Hnz Hz Hnw R10 R9 Rfr.
all: idtac "PHASE C".
all: sym_run_to_with src2tbl_ok HS 0x16b08; clear regs1.
all: idtac "PHASE D".
all: reg_of HS (8%bv:reg) H8; reg_of HS (10%bv:reg) H10.
all: pose proof (z_argv_bounds inp rnd 0 ltac:(lia)) as B0.
all: pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 0 ltac:(lia)) as F0; unfold SP_HI in F0.
all: lazymatch goal with |- rzb _ (mkCfg ?ms _) _ =>
destruct (src2_progname_scan (nth 0 argv []) _ (ms_mem ms) (seg_rom src2segs) (ms_regs ms)
(argv_no_nul inp Hva 0 ltac:(lia))
ltac:(rewrite ews1; lia)
ltac:(left; rewrite ews1; unfold PROGNAME; lia)
H8 H10
(argv0_reads (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 1 _ _ HR eq_refl)))
as (regs2 & Hms & R11 & R12 & R13 & Rfr) end.
all: pose proof (st_ok_mkst src2segs _ _ _ HS eq_refl) as Hshape;
rewrite Hshape; (eapply rzb_msteps; [exact Hh | exact Hlz | exact Hms | ]);
rewrite Hshape in HS; clear Hshape Hms.
all: lazymatch goal with |- rzb _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes _ _ ?bs =>
lazymatch type of HS with st_ok _ ?E ?ss (mkst _ _ ?m _) =>
let rs' := eval vm_compute in (opt_mem (store_region (ss_mem ss) None 0x51f98 8 (CVal 8 (SOff 7 0)))) in
assert (HCB : forall i, 0 <= i < Z.of_nat (length bs) ->
cbyte src2segs E (base_val E None + 0x51f98) (CVal 8 (SOff 7 0)) i = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite length_N_to_le_bytes in Hi;
change (CVal 8 (SOff 7 0)) with (CVal (N.of_nat 8) (SOff 7 0));
rewrite (st_bytes_cbyte src2segs E) by lia;
unfold word_to_le_bytes; rewrite Z_to_le_bytes_st; do 2 f_equal;
cbn [sv_denot]; rewrite Z.add_0_r, ews7, ews1; reflexivity
| ];
pose proof (proj2 (swrite_sound src2segs E m (ss_mem ss) None 0x51f98 (CVal 8 (SOff 7 0)) bs rs'
(st_ok_mem_ok src2segs E ss _ HS)
ltac:(rewrite length_N_to_le_bytes; vm_compute; reflexivity)
ltac:(rewrite length_N_to_le_bytes; lia)
ltac:(rewrite length_N_to_le_bytes; reflexivity) HCB)) as HM;
change (mem_ok src2segs E m' rs') in HM;
unshelve epose proof (st_ok_set_regs_mem src2segs 9%nat E E ss _ regs2 _ 0x16b2c m m' rs' upd_progname
HS (env_agree_refl 9%nat E) _ _ _ _ HM) as HS';
[ vm_compute; reflexivity
| reflexivity
| sym_splice_frame Rfr
| unfold upd_progname;
repeat (apply Forall_cons;
[ split;
[ reflexivity
| cbn [fst snd sv_denot];
first [ rewrite R11, Z.add_0_r, ews2, ews1; reflexivity
| exact R12
| exact R13 ] ]
| ]);
apply Forall_nil
| clear HS HM HCB; rename HS' into HS;
apply (runs_at_wbytes_below (bv_unsigned sp) m _ (Z_to_bv 64 PROGNAME) bs) in HR;
[ | rewrite length_N_to_le_bytes; change (bv_unsigned (Z_to_bv 64 PROGNAME)) with PROGNAME;
unfold PROGNAME; lia ] ]
end end end.
all: clear H8 H10 R11 R12 R13 Rfr.
(* atom 7, the progname pointer, takes the strings-window fact [str_fact]:
   it lies inside argv[0], so below [SP_HI - 9] by [z_argv_fits] *)
all: sym_add_fact HS 7%nat str_fact;
[ unfold str_fact, SP_LO, SP_HI, K_stack; cbn [af_lo af_hi af_al2]; rewrite ews7;
pose proof (progname_off_le (nth 0 argv []));
change (2^0) with 1; rewrite Z.mod_1_r; lia
| ].
all: clear B0 F0.
all: idtac "PHASE E".
all: sym_run_with src2tbl_ok HS; clear regs2.
all: idtac "PHASE F".
all: lazymatch type of HS with st_ok_ecall _ ?E ?ss _ =>
sym_ecall_open HS; cbn [ms_mem pend_at] in HR;
lazymatch goal with Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
eapply rzb_set_tid_first; [exact Hh | exact Hlz | rewrite (Hregs 17%bv); reflexivity | exact Htid | ];
intros tid Htid8; rewrite PID_MAX_ENVELOPE_val in Htid8;
assert (HA8 : env_agree 8%nat E (E_stR tid))
by (split; [intros n Hn; do 8 (destruct n as [|n]; [reflexivity|]); lia | reflexivity]);
pose proof (st_ok_resume_mem src2segs 8%nat E (E_stR tid) ss regs mem (SOff 8 0) tid (ss_mem ss)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))
Hregs HA8 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)
(mem_ok_agree src2segs 8%nat _ _ mem (ss_mem ss) HA8 ltac:(vm_compute; reflexivity) Hmem)
(facts_ok_add_atom _ _ 8%nat tid_fact
(facts_ok_agree 8%nat _ _ (ss_facts ss) HA8 ltac:(vm_compute; reflexivity) HG)
ltac:(unfold afact_ok, tid_fact; cbn [af_lo af_hi af_al2]; rewrite ews8;
change (2^0) with 1; rewrite Z.mod_1_r; lia))) as HS;
clear Hregs Hmem HG HA8; sym_norm HS;
assert (Hh' : m_halted (with_tid tid model) = None) by exact Hh;
assert (Hlz' : m_vm_lazy (with_tid tid model) = []) by exact Hlz
end
end.
all: idtac "PHASE G".
all: sym_run_to_with src2tbl_ok HS 0x17390.
all: sym_add_chunk_sem HS (@None nat) guard_data_chunk;
[ intros HCS; apply (guard_data_chunk_ok src2segs _ _ 0 GUARD RAND_DATOM);
[ cbn; lia
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS) ]
| ].
all: sym_run_to_with src2tbl_ok HS 0x17394.
all: sym_add_chunk_sem HS (@None nat) canary_chunk;
[ intros HCS; apply (canary_chunk_ok src2segs _ _ 0 GUARD RAND_DATOM CANARY_ATOM);
[ cbn; lia
| reflexivity
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS)
| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HCS))) ]
| ].
all: idtac "PHASE H".
all: sym_run_to_with src2tbl_ok HS 0x12ad4.
all: idtac "PHASE I".
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_head src2segs E ss ms keep_zero) in HS;
apply (st_ok_prune src2segs E _ ms [] [0%nat]) in HS end.
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_all src2segs E ss ms keep_main) in HS;
apply (st_ok_agree_pd src2segs (fun _ => true) (not_in START_DATOMS) _ (E_main sp inp argv envp xf tid rnd)) in HS;
[ | apply E_st_main_agree | vm_compute; reflexivity ] end.
all: sym_norm HS.
all: exact (K ms tid Htid8 HS HR).
Qed.
End f.
Theorem src2_start_b : forall (two : bool) sp brk mbase rnd lim inp T,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
(if two then (2 <= length (in_argv inp))%nat else True) ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src2segs (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) (ss_main two (kb_rseq (in_kernel inp))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) rnd) ->
rzb src2segs (mkCfg ms (with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd))
(init_model (segments_reserved src2segs) brk mbase sp lim inp)))) T) ->
rzb src2segs (init_config src2segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) T.
Proof.
intros two sp brk mbase rnd lim inp T Hsp Hva Hve Hvl Hlau Htwo K.
unfold init_config.
apply (src2_start_gen_b inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau two);
[exact Htwo | reflexivity | reflexivity | reflexivity | exact K].
Qed.
