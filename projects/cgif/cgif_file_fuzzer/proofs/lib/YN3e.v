(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch premises entry_launch_ok_va and valid_input; the run's CONFIG_RSEQ flag; the start-up stack anchored at its top; AT_EXECFN; the launch's group id; the vDSO's mappings and steps): changed CANARY_ATOM, xw_main, E_main, E_st, E_st_main_agree, alias_envp, ss_start, runs_main and 31 more; added xd_full, START_DATOMS, ss_main_tt, ss_main_tf, ss_main_ft, ss_main_ff, inp, mbase and 21 more; removed xd_st, envp_words, envp_block, length_envp_words, length_envp_block, Hfits, uid; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u YN3q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH01 YN3h.
From OSSVerify.cgif.cgif_file_fuzzer.images Require Import Plain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zmod_elim x M :=
let q := fresh "q" in let r := fresh "r" in
let Hq := fresh "Hdm" in let Hr := fresh "Hmb" in
pose proof (Z.div_mod x M ltac:(lia)) as Hq;
pose proof (Z.mod_pos_bound x M ltac:(lia)) as Hr;
remember (x / M) as q eqn:Heqq; clear Heqq;
remember (x mod M) as r eqn:Heqr; clear Heqr.
Lemma negw_and3_zero : forall u : Z, u mod 16 = 0 ->
zalu64 ALU_AND (zalu32 ALU_SUB 0 (u + -368)) 3 = 0.
Proof.
intros u Hu.
unfold zalu64, zalu32, zcanon, zu32, M64, M32. cbn [zalu_raw].
rewrite (Z.mod_small 3), (Z.mod_small 0) by lia.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
zmod_elim u 16.
zmod_elim (u + -368) (2^32).
zmod_elim (0 - r0 + 2 ^ 31) (2^32).
zmod_elim (r1 - 2 ^ 31) (2^64).
zmod_elim r2 (2^64).
zmod_elim r3 (2^2).
rewrite Z.mod_small by lia. lia.
Qed.
Definition CANARY_ATOM : nat := 9%nat.
(* The strings block is anchored at the entry draw's [ed_top], not at [sp], and the launch
   execfn is one of its tenants: that is the whole of [YP08.z_argv]'s new argument list
   (YP08.v:200-203) and of [YP08.E0]'s (YP08.v:209-210). *)
Definition xw_main (argv envp : list (list byte)) (efn : list byte) (tid : word) (rnd : EntryDraw) (n : nat) : word :=
match n with
| 7%nat => Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) argv envp efn 0
+ Z.of_nat (progname_off (nth 0 argv [])))
| 8%nat => tid
| 9%nat => canary_word (rand_bytes rnd)
| _ => Z_to_bv 64 0
end.
Definition xd_main (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d RAND_DATOM then rand_bytes rnd else [].
(* The startup environment answers every datom [YH01.src0_init_st_ok] pins, which is now
   seven: GID, EHDR, MINSIG and EXECFN are the four this revision added. *)
Definition xd_full (inp : ProcInput) (sp : word) (mbase : word) (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d UID_DATOM then uid_bytes (in_uid inp)
else if Nat.eqb d HWCAP_DATOM then hwcap_bytes (in_hwcap inp)
else if Nat.eqb d RAND_DATOM then rand_bytes rnd
else if Nat.eqb d GID_DATOM then gid_bytes (in_gid inp)
else if Nat.eqb d EHDR_DATOM then ehdr_bytes inp sp mbase
else if Nat.eqb d MINSIG_DATOM then minsig_bytes inp sp mbase
else if Nat.eqb d EXECFN_DATOM then execfn_ptr_bytes (ed_top rnd) (in_execfn inp)
else [].
Definition START_DATOMS : list nat :=
[UID_DATOM; HWCAP_DATOM; GID_DATOM; EHDR_DATOM; MINSIG_DATOM; EXECFN_DATOM].
(* [inp] is carried, rather than the bare [kb_rseq] flag, so that a case split on the run's
   own rseq flag reaches [ss_main] and leaves these two environments alone. *)
Definition E_main (sp : word) (inp : ProcInput) (argv envp : list (list byte)) (efn : list byte)
(tid : word) (rnd : EntryDraw) : env :=
E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) argv envp efn (xw_main argv envp efn tid rnd) (xd_main rnd).
Definition E_st (sp : word) (inp : ProcInput) (mbase : word) (tid : word) (rnd : EntryDraw) : env :=
E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp)
(xw_main (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) (xd_full inp sp mbase rnd).
Lemma E_st_main_agree : forall sp inp mbase tid rnd,
env_agree_pd (fun _ => true) (not_in START_DATOMS)
(E_st sp inp mbase tid rnd)
(E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd).
Proof.
intros. split; [intros; reflexivity|].
intros d Hd. unfold not_in, START_DATOMS in Hd. cbn [existsb] in Hd. rewrite orb_false_r in Hd.
apply negb_true_iff in Hd.
apply orb_false_iff in Hd as [Hd1 Hd]. apply orb_false_iff in Hd as [Hd2 Hd].
apply orb_false_iff in Hd as [Hd3 Hd]. apply orb_false_iff in Hd as [Hd4 Hd].
apply orb_false_iff in Hd as [Hd5 Hd6].
unfold E_st, E_main, E0; cbn [ed].
destruct d as [|[|d]]; [reflexivity|reflexivity|].
unfold xd_full, xd_main. rewrite Hd1, Hd2.
destruct (Nat.eqb (S (S d)) RAND_DATOM); [reflexivity|].
rewrite Hd3, Hd4, Hd5, Hd6. reflexivity.
Qed.
Definition alias_memset : sv * sv :=
(SAlu ALU_AND (SAluw ALU_SUB (SLit 0) (SOff 0 (-368))) (SLit 3), SLit 0).
Definition alias_envp : sv * sv :=
(SAlu ALU_ADD (SOff 0 16) (SAlu ALU_SLL (SOff 3 0) (SLit 3)), SOff 4 0).
(* [src0_ss0] gained the run's own [kb_rseq] flag (YH01.v:24): the auxv block, and with it
   the head of the entry stack, is one pair longer when it is set, so the symbolic start
   state -- and every state computed from it -- is indexed by that flag as well as by [two]. *)
Definition ss_start (rs two : bool) : sstate :=
add_alias (add_alias (src0_ss0 rs two)
(fst alias_memset) (snd alias_memset))
(fst alias_envp) (snd alias_envp).
(* [rs] is the run's CONFIG_RSEQ flag: the last element is the key words of the auxv pairs
   from 26 up to AT_NULL ([YP08.auxv_tail_runs]), the words the two flags do not share.
   Every state from [ss_canon] on holds for both flags and drops them, so they travel
   here, beside the state, to the first malloc ([YL0n.src0_malloc1]). *)
Definition runs_main (rs two : bool) (sp top : word) (argv envp : list (list byte)) (efn : list byte)
: list (Z * list byte) :=
(z_envp (bv_unsigned sp) argv, envp_block top argv envp efn)
:: (z_argv (bv_unsigned top) argv envp efn 0, nth 0 argv [] ++ [NUL])
:: (if two then [(z_argv (bv_unsigned top) argv envp efn 1, nth 1 argv [] ++ [NUL])] else [])
++ (z_strs (bv_unsigned top) argv envp efn, stack_tail argv envp efn)
:: auxv_tail_runs rs (z_auxv (bv_unsigned sp) argv envp).
Definition opt_mem (o : option smem) : smem := match o with Some rs => rs | None => [] end.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition keep_zero (c : chunk) : bool :=
match c_val c with CZero n => 4096 <=? n | _ => false end.
Definition upd_envp : list (reg * sv) := [(10%bv : reg, SLit 0); (9%bv : reg, SOff 5 0)].
Definition upd_progname : list (reg * sv) := [(11%bv : reg, SOff 2 0); (12%bv : reg, SLit 47); (13%bv : reg, SLit 0)].
Definition tid_fact : afact := mkAF 1 4194303 0.
Definition GUARD : Z := 0x503f8.
Definition guard_data_chunk : chunk := mkChunk GUARD (CData RAND_DATOM 0 8).
Definition canary_chunk : chunk := mkChunk GUARD (CVal 8 (SOff CANARY_ATOM 0)).
Definition is_canary_val (cv : cval) : bool :=
match cv with CVal 8 (SOff n 0) => Nat.eqb n CANARY_ATOM | _ => false end.
Definition keep_main (c : chunk) : bool :=
cval_atoms_pd (fun _ => true) (not_in START_DATOMS) (c_val c)
&& negb ((GUARD <=? c_off c) && (c_off c <? GUARD + 8) && negb (is_canary_val (c_val c))).
Definition main_state (rs two : bool) : sstate :=
let s1 := run_ (ss_start rs two) in
let s2 := set_regs_pc s1 upd_envp 0x153bc in
let s3 := runto_ 0x1545c s2 in
let s4 := add_atom (mkSS 0x15480 (sr_sets (ss_regs s3) upd_progname)
(opt_mem (store_region (ss_mem s3) None 0x50408 8 (CVal 8 (SOff 7 0))))
(* Atom 7 is the progname pointer, a pointer INTO the strings block, so its fact is
   [str_fact] (YP08.v:313), not the pointer-block [ptr_fact 0] (YP08.v:312).  Same
   alignment (0), different ceiling: the top-anchored layout bounds this atom by
   [SP_HI - 10] and no better (see the derivation at :533), so [SP_HI - 16] is false for
   it while [SP_HI - 9] holds.  Atoms 1 and 2 -- the other two strings pointers -- already
   carry [str_fact] in YP08's own table (YP08.v:316-317). *)
None (ss_facts s3)) 7 str_fact in
let s5 := run_ s4 in
let s6 := resume s5 (SOff 8 0) (ss_mem s5)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts s5))
(f_conds (ss_facts s5)) (f_alias (ss_facts s5))) in
let s7 := runto_ 0x15ce4 s6 in
let s8 := add_chunk_ None guard_data_chunk s7 in
let s9 := runto_ 0x15ce8 s8 in
let s10 := add_chunk_ None canary_chunk s9 in
let s11 := runto_ 0x12930 s10 in
let s12 := prune (mkSS (ss_pc s11) (ss_regs s11) (clean_head keep_zero (ss_mem s11)) (ss_resv s11) (ss_facts s11))
[] [0%nat] in
mkSS (ss_pc s12) (ss_regs s12) (clean_all keep_main (ss_mem s12)) (ss_resv s12) (ss_facts s12).
Definition ss_main_tt : sstate := Eval vm_compute in (main_state true true).
Definition ss_main_tf : sstate := Eval vm_compute in (main_state true false).
Definition ss_main_ft : sstate := Eval vm_compute in (main_state false true).
Definition ss_main_ff : sstate := Eval vm_compute in (main_state false false).
Definition ss_main_t (rs : bool) : sstate := if rs then ss_main_tt else ss_main_ft.
Definition ss_main_f (rs : bool) : sstate := if rs then ss_main_tf else ss_main_ff.
Definition ss_main (rs two : bool) : sstate := if two then ss_main_t rs else ss_main_f rs.
Lemma bytes_at_app : forall m a l1 l2,
YP03.bytes_at m a l1 -> YP03.bytes_at m (a + Z.of_nat (length l1)) l2 ->
YP03.bytes_at m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hg].
- rewrite nth_error_app1 by exact Hl. apply H1. exact Hl.
- rewrite nth_error_app2 by exact Hg.
replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia.
apply H2. lia.
Qed.
Lemma after_slash_le : forall s i acc, (acc <= i)%nat -> (after_slash s i acc <= i + length s)%nat.
Proof.
induction s as [|b s IH]; intros i acc H; cbn [after_slash length]; [lia|].
specialize (IH (S i) (if bv_eqb b SLASH then S i else acc)).
destruct (bv_eqb b SLASH); lia.
Qed.
Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intros s. unfold progname_off. pose proof (after_slash_le s 0 0 ltac:(lia)). lia. Qed.
Lemma runs_at_wbytes_below : forall spv m l (a : word) bs,
runs_at spv m l -> bv_unsigned a + Z.of_nat (length bs) <= spv -> runs_at spv (wbytes m a bs) l.
Proof.
intros spv m l a bs H Hle. unfold runs_at in *. rewrite Forall_forall in *.
intros [a' bs'] Hin. specialize (H _ Hin). cbn in *. destruct H as (H1 & H2 & H3).
split; [exact H1|]. split; [exact H2|]. intros j Hj. rewrite wbytes_above; [apply H3; exact Hj|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range a). rewrite Z.mod_small by lia. lia.
Qed.
Section f.
(* Mirrors [YP08]'s own section header (YP08.v:477-501) and [YH01.src0_init_st_ok]: the run is
   indexed by the whole [ProcInput] and by the entry draw.  [entry_stack_fits] is REPLACED by
   the three premises the new initial-state theorem asks for ([valid_launch],
   [entry_launch_ok_va], [valid_input]); it no longer determines the stack image. *)
Variable inp : ProcInput.
Variable mbase : word.
Variable sp : word.
Variable brk : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Hypothesis Hvi : valid_input inp.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation efn := (in_execfn inp).
#[local] Notation krs := (kb_rseq (in_kernel inp)).
#[local] Notation top := (ed_top rnd).
#[local] Notation zsp := (bv_unsigned sp).
#[local] Notation ztop := (bv_unsigned (ed_top rnd)).
(* [YP08]'s section discharges over its own variable list, in its own order; [eapply] lets
   unification choose the instance, so no call below hard-codes a discharged arity. *)
Lemma LF :
z_envp zsp argv = zsp + 16 + 8 * Z.of_nat (length argv)
/\ z_auxv zsp argv envp = z_envp zsp argv + 8 * Z.of_nat (length envp) + 8
/\ z_rand zsp krs argv envp = z_auxv zsp argv envp + AUXV_BYTES krs + 8 * Z.of_nat (block_items argv envp mod 2)
/\ z_rand zsp krs argv envp + 16 <= z_strs ztop argv envp efn
/\ z_argv ztop argv envp efn 0 = z_strs ztop argv envp efn
/\ z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp)
+ Z.of_nat (length efn) + 1 + 8 = ztop
/\ ztop <= SP_HI
/\ SP_LO <= zsp <= SP_HI.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
eapply YP08.layout_facts; eassumption.
Qed.
Lemma SB : zsp <= z_strs ztop argv envp efn
/\ z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp)
+ Z.of_nat (length efn) + 1 + 8 = ztop.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
eapply YP08.str_bounds; eassumption.
Qed.
Lemma ZAB : forall k, (k < length argv)%nat ->
z_strs ztop argv envp efn <= z_argv ztop argv envp efn k
/\ z_argv ztop argv envp efn k + Z.of_nat (length (nth k argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros k Hk. eapply YP08.z_argv_bounds; eassumption.
Qed.
Lemma ZEB : forall k, (k < length envp)%nat ->
z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) <= z_envs ztop argv envp efn k
/\ z_envs ztop argv envp efn k + Z.of_nat (length (nth k envp [])) + 1 <= z_execfn ztop argv envp efn.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros k Hk. eapply YP08.z_envs_bounds; eassumption.
Qed.
Lemma STE : z_strs ztop argv envp efn + Z.of_nat (length (stack_tail argv envp efn)) = ztop.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
eapply YP08.stack_tail_end; eassumption.
Qed.
Lemma ANN : forall k, (k < length argv)%nat -> ~ In NUL (nth k argv []).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros k Hk. eapply YP08.argv_no_nul; eassumption.
Qed.
Lemma UEP : forall k, (k < length envp)%nat ->
nth k (fst (string_addrs (cat_env_base top argv envp efn) envp)) (Z_to_bv 64 0)
= Z_to_bv 64 (z_envs ztop argv envp efn k).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros k Hk. eapply YP08.u_envp_ptr; eassumption.
Qed.
Lemma runs_main_init : forall (two : bool) (pc : N),
(if two then (2 <= length argv)%nat else True) ->
runs_at zsp (ms_mem (init_machine_state src0segs pc Plain_phdrs sp mbase rnd inp))
(runs_main krs two sp top argv envp efn).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros two pc Htwo. rewrite init_mkst. cbn [ms_mem mkst].
pose proof LF as L. pose proof SB as S. pose proof STE as T.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
unfold SP_LO, SP_HI in *.
unfold runs_main. cbn [app]. apply Forall_cons; [|apply Forall_cons; [| apply Forall_app; split]].
- cbn [fst snd]. rewrite length_envp_block.
split; [lia|]. split; [lia|]. unfold envp_block, envp_words. rewrite flat_map_app. apply bytes_at_app.
+ eapply YP08.m0_envp_ptrs; eassumption.
+ rewrite length_flat_map_le8, length_string_addrs_fst. cbn [flat_map]. rewrite app_nil_r.
replace (z_envp zsp argv + Z.of_nat (8 * length envp))
with (z_auxv zsp argv envp - 8) by lia.
eapply YP08.m0_envp_null; eassumption.
- cbn [fst snd]. pose proof (ZAB 0 ltac:(lia)) as B.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. eapply YP08.m0_argv_str; first [eassumption | lia].
- destruct two; [|constructor]. apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (ZAB 1 ltac:(lia)) as B.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. eapply YP08.m0_argv_str; first [eassumption | lia].
- apply Forall_cons.
{ cbn [fst snd]. split; [lia|]. split; [lia|]. eapply YP08.m0_tail; eassumption. }
lazymatch goal with |- Forall (fun ab => _ /\ _ /\ YP03.bytes_at ?m _ _) _ =>
assert (TB : Forall (fun ab => bytes_at m (fst ab) (snd ab)) (auxv_tail_runs krs (z_auxv zsp argv envp)))
by (eapply YP08.m0_auxv_tail; eassumption) end.
rewrite Forall_forall in TB |- *. intros [a bs] Hin. split; [|split; [|exact (TB _ Hin)]]; cbn [fst snd];
revert Hin L; destruct (kb_rseq (in_kernel inp)); intros Hin L;
first [change (AUXV_BYTES true) with 464 in L | change (AUXV_BYTES false) with 432 in L];
cbn [auxv_tail_runs In] in Hin; repeat destruct Hin as [Hin|Hin]; try contradiction;
injection Hin as Ha Hb; subst a bs; cbn [length word_le8]; lia.
Qed.
Lemma ew0_st : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 0) = zsp.
Proof using Hsp Hva Hve Hvl Hlau Hvi. intros t. reflexivity. Qed.
Lemma ew3_st : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 3) = Z.of_nat (length argv).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. unfold E_st. eapply YP08.ew3; eassumption.
Qed.
Lemma ew4_st : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 4) = z_envp zsp argv.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. unfold E_st. eapply YP08.ew4; eassumption.
Qed.
Lemma alias_memset_ok : forall t,
sv_denot (E_st sp inp mbase t rnd) (fst alias_memset)
= sv_denot (E_st sp inp mbase t rnd) (snd alias_memset).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. cbn [fst snd alias_memset sv_denot].
rewrite zalu32_sound, zalu64_sound. f_equal. apply negw_and3_zero.
rewrite (ew0_st t). exact (proj2 (proj2 Hsp)).
Qed.
Lemma alias_envp_ok : forall t,
sv_denot (E_st sp inp mbase t rnd) (fst alias_envp)
= sv_denot (E_st sp inp mbase t rnd) (snd alias_envp).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. cbn [fst snd alias_envp sv_denot].
rewrite !zalu64_sound. rewrite (ew0_st t), (ew3_st t), (ew4_st t).
pose proof LF as L. pose proof (proj1 Hva) as HA.
unfold SP_LO, SP_HI in L.
apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !Z.add_0_r. rewrite !(Z.mod_small _ (2^64)) by lia. lia.
Qed.
Lemma ewm1 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 1)
= z_argv ztop argv envp efn 0.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. pose proof LF as L.
assert (H1 : bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 1) = z_strs ztop argv envp efn)
by (unfold E_main; eapply YP08.ew1; eassumption).
rewrite H1. lia.
Qed.
Lemma ewm2 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 2)
= z_argv ztop argv envp efn 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. pose proof LF as L.
assert (H2 : bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 2)
= z_strs ztop argv envp efn + Z.of_nat (length (nth 0 argv [])) + 1)
by (unfold E_main; eapply YP08.ew2; eassumption).
rewrite H2. lia.
Qed.
Lemma ewm4 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 4) = z_envp zsp argv.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. unfold E_main. eapply YP08.ew4; eassumption.
Qed.
Lemma ewm5 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 5) = z_auxv zsp argv envp.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. unfold E_main. eapply YP08.ew5; eassumption.
Qed.
Lemma ewm6 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 6) = z_rand zsp krs argv envp.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. unfold E_main. eapply YP08.ew6; eassumption.
Qed.
Lemma ewm7 : forall t, bv_unsigned (ew (E_main sp inp argv envp efn t rnd) 7)
= z_argv ztop argv envp efn 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros t. cbn [ew E_main E0 xw_main].
pose proof LF as L. pose proof SB as S. pose proof (proj1 Hva) as HA.
pose proof (ZAB 0 ltac:(lia)) as B. pose proof (progname_off_le (nth 0 argv [])).
unfold SP_LO, SP_HI in *. apply u_Z2bv; lia.
Qed.
Lemma ewm8 : forall t, ew (E_main sp inp argv envp efn t rnd) 8 = t.
Proof using Hsp Hva Hve Hvl Hlau Hvi. intros t. reflexivity. Qed.
Lemma ewm9 : forall t, ew (E_main sp inp argv envp efn t rnd) CANARY_ATOM = canary_word (rand_bytes rnd).
Proof using Hsp Hva Hve Hvl Hlau Hvi. intros t. reflexivity. Qed.
Lemma edm7 : forall t, ed (E_main sp inp argv envp efn t rnd) RAND_DATOM = rand_bytes rnd.
Proof using Hsp Hva Hve Hvl Hlau Hvi. intros t. reflexivity. Qed.
Lemma ews1 : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 1) = z_argv ztop argv envp efn 0.
Proof using Hsp Hva Hve Hvl Hlau Hvi. exact ewm1. Qed.
Lemma ews2 : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 2)
= z_argv ztop argv envp efn 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof using Hsp Hva Hve Hvl Hlau Hvi. exact ewm2. Qed.
Lemma ews4 : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 4) = z_envp zsp argv.
Proof using Hsp Hva Hve Hvl Hlau Hvi. exact ewm4. Qed.
Lemma ews5 : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 5) = z_auxv zsp argv envp.
Proof using Hsp Hva Hve Hvl Hlau Hvi. exact ewm5. Qed.
Lemma ews7 : forall t, bv_unsigned (ew (E_st sp inp mbase t rnd) 7)
= z_argv ztop argv envp efn 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof using Hsp Hva Hve Hvl Hlau Hvi. exact ewm7. Qed.
Lemma ews8 : forall t, ew (E_st sp inp mbase t rnd) 8 = t.
Proof using Hsp Hva Hve Hvl Hlau Hvi. intros t. reflexivity. Qed.
Lemma envp_block_reads : forall m t,
YP03.bytes_at m (z_envp zsp argv) (envp_block top argv envp efn) ->
(forall i, (i < length envp)%nat -> exists bs,
rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp inp mbase t rnd) 4) + 8 * Z.of_nat i)) 8 = Some bs
/\ bytes_le_to_Z bs <> 0)
/\ (exists bs, rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp inp mbase t rnd) 4)
+ 8 * Z.of_nat (length envp))) 8 = Some bs
/\ bytes_le_to_Z bs = 0)
/\ bv_unsigned (ew (E_st sp inp mbase t rnd) 4) + 8 * Z.of_nat (length envp) + 8 < 2^64.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros m t HB. rewrite ews4.
pose proof LF as L. pose proof SB as S. pose proof (proj1 Hve) as HE. pose proof (proj1 Hva) as HA.
unfold SP_LO, SP_HI in *.
assert (HW : forall k, (k < length envp + 1)%nat ->
rdn src0segs m (Z_to_bv 64 (z_envp zsp argv + 8 * Z.of_nat k)) 8
= Some (word_le8 (nth k (envp_words top argv envp efn) (Z_to_bv 64 0)))).
{ intros k Hk. apply (bytes_at_rdn src0segs m _ (word_le8 _)).
apply (bytes_at_le8_nth m _ (envp_words top argv envp efn) k HB). rewrite length_envp_words. exact Hk. }
split; [|split; [|lia]].
- intros i Hi. eexists. split; [apply HW; lia|].
unfold envp_words. rewrite app_nth1 by (rewrite length_string_addrs_fst; exact Hi).
rewrite (UEP i Hi).
rewrite n_to_le_8_spec, bytes_le_to_Z_8.
pose proof (ZEB i Hi). unfold z_execfn in *. rewrite u_Z2bv by lia. lia.
- eexists. split; [apply HW; lia|].
unfold envp_words. rewrite app_nth2 by (rewrite length_string_addrs_fst; lia).
rewrite length_string_addrs_fst, Nat.sub_diag. reflexivity.
Qed.
Lemma argv0_reads : forall m t,
YP03.bytes_at m (z_argv ztop argv envp efn 0) (nth 0 argv [] ++ [NUL]) ->
forall j, (j <= length (nth 0 argv []))%nat ->
rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp inp mbase t rnd) 1) + Z.of_nat j)) 1
= Some [nth j (nth 0 argv [] ++ [NUL]) NUL].
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros m t HB j Hj. rewrite ews1. apply (proj2 (rdn_mbytes src0segs m 1 _ [_])).
split; [reflexivity|]. intros i Hi. destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
rewrite (bytes_at_mbyte src0segs m _ _ j HB) by (rewrite length_app; cbn; lia).
apply nth_error_nth'. rewrite length_app; cbn; lia.
Qed.
Ltac sym_spliceL HS Hms k E' Hagree upd :=
lazymatch type of HS with st_ok ?segs ?E ?ss ?ms =>
lazymatch type of Hms with msteps _ _ (mkst ?regs' (Z_to_bv 64 ?pc') _ _) =>
let Hshape := fresh "Hshape" in
pose proof (st_ok_mkst segs E ss ms HS eq_refl) as Hshape;
rewrite Hshape; eapply rz_msteps; [assumption | assumption | exact Hms | ];
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
pose proof (st_ok_reg src0segs _ _ _ r HS) as H;
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
Lemma src0_start_gen : forall (two : bool) model T,
(if two then (2 <= length argv)%nat else True) ->
m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_main sp inp argv envp efn tid rnd) (ss_main krs two) ms ->
runs_at zsp (ms_mem ms) (runs_main krs two sp top argv envp efn) ->
realizes src0segs (mkCfg ms (with_tid tid model)) T) ->
realizes src0segs (mkCfg (init_machine_state src0segs Plain_init_pc Plain_phdrs sp mbase rnd inp) model) T.
Proof using Hsp Hva Hve Hvl Hlau Hvi.
intros two model T Htwo Hh Hlz Htid K.
pose proof LF as L. pose proof SB as S. unfold SP_LO, SP_HI in *.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
pose proof (src0_init_st_ok inp mbase sp brk rnd
(xw_main argv envp efn (Z_to_bv 64 0) rnd) (xd_full inp sp mbase rnd) two
Hsp Hva Hve Hvl Hlau Hvi eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Htwo) as HS.
change (st_ok src0segs (E_st sp inp mbase (Z_to_bv 64 0) rnd) (src0_ss0 krs two)
(init_machine_state src0segs Plain_init_pc Plain_phdrs sp mbase rnd inp)) in HS.
apply (st_ok_add_alias src0segs _ _ _ (fst alias_memset) (snd alias_memset)) in HS; [|apply alias_memset_ok].
apply (st_ok_add_alias src0segs _ _ _ (fst alias_envp) (snd alias_envp)) in HS; [|apply alias_envp_ok].
change (st_ok src0segs (E_st sp inp mbase (Z_to_bv 64 0) rnd) (ss_start krs two)
(init_machine_state src0segs Plain_init_pc Plain_phdrs sp mbase rnd inp)) in HS.
pose proof (runs_main_init two Plain_init_pc Htwo) as HR.
(* [E_st] and [E_main] hide the rseq flag behind [inp], so this split reaches [ss_start] and
   [ss_main] -- the only places that need it concrete to compute -- and nothing else.  Two
   placements below are LOAD-BEARING, not tidiness: [L] (the only flag-carrying fact here, its
   [z_rand]/[AUXV_BYTES] atoms keyed to [kb_rseq]) is posed ABOVE the split so it specialises
   with the goal, and every [rewrite] under the split names an [ews*] whose statement is
   flag-free.  Give [E_st]/[E_main] the bare flag instead of [inp], or push [L] into the
   branches, and those rewrites stop matching syntactically while [apply] still works. *)
destruct two; destruct (kb_rseq (in_kernel inp)).
all: sym_run_with src0tbl_ok HS.
all: idtac "PHASE B".
all: reg_of HS (9%bv:reg) H9.
all: lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
destruct (envp_block_reads (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 0 _ _ HR eq_refl))
as (Hnz & Hz & Hnw);
destruct (src0_envp_count (length envp) (ms_regs ms) (ms_mem ms) (seg_rom src0segs) _ H9 Hnz Hz Hnw)
as (regs1 & Hms & R10 & R9 & Rfr) end.
all: lazymatch type of HS with st_ok _ ?E _ _ =>
sym_spliceL HS Hms 9%nat E (env_agree_refl 9%nat E) upd_envp end;
[ sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot];
[ exact R10 | rewrite R9, Z.add_0_r, ews4, ews5; apply (f_equal (Z_to_bv 64)); lia ]
| ].
all: clear H9 Hnz Hz Hnw R10 R9 Rfr.
all: idtac "PHASE C".
all: sym_run_to_with src0tbl_ok HS 0x1545c; clear regs1.
all: idtac "PHASE D".
all: reg_of HS (8%bv:reg) H8; reg_of HS (10%bv:reg) H10.
all: pose proof (ZAB 0 ltac:(lia)) as B0.
all: lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
destruct (src0_progname_scan (nth 0 argv []) _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms)
(ANN 0 ltac:(lia))
ltac:(rewrite ews1; lia)
ltac:(left; rewrite ews1; unfold PROGNAME; lia)
H8 H10
(argv0_reads (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 1 _ _ HR eq_refl)))
as (regs2 & Hms & R11 & R12 & R13 & Rfr) end.
all: pose proof (st_ok_mkst src0segs _ _ _ HS eq_refl) as Hshape;
rewrite Hshape; (eapply rz_msteps; [exact Hh | exact Hlz | exact Hms | ]);
rewrite Hshape in HS; clear Hshape Hms.
all: lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes _ _ ?bs =>
lazymatch type of HS with st_ok _ ?E ?ss (mkst _ _ ?m _) =>
let rs' := eval vm_compute in (opt_mem (store_region (ss_mem ss) None 0x50408 8 (CVal 8 (SOff 7 0)))) in
assert (HCB : forall i, 0 <= i < Z.of_nat (length bs) ->
cbyte src0segs E (base_val E None + 0x50408) (CVal 8 (SOff 7 0)) i = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite length_N_to_le_bytes in Hi;
change (CVal 8 (SOff 7 0)) with (CVal (N.of_nat 8) (SOff 7 0));
rewrite (st_bytes_cbyte src0segs E) by lia;
unfold word_to_le_bytes; rewrite Z_to_le_bytes_st; do 2 f_equal;
cbn [sv_denot]; rewrite Z.add_0_r, ews7, ews1; reflexivity
| ];
pose proof (proj2 (swrite_sound src0segs E m (ss_mem ss) None 0x50408 (CVal 8 (SOff 7 0)) bs rs'
(st_ok_mem_ok src0segs E ss _ HS)
ltac:(rewrite length_N_to_le_bytes; vm_compute; reflexivity)
ltac:(rewrite length_N_to_le_bytes; lia)
ltac:(rewrite length_N_to_le_bytes; reflexivity) HCB)) as HM;
change (mem_ok src0segs E m' rs') in HM;
unshelve epose proof (st_ok_set_regs_mem src0segs 9%nat E E ss _ regs2 _ 0x15480 m m' rs' upd_progname
HS (env_agree_refl 9%nat E) _ _ _ _ HM) as HS';
[ vm_compute; reflexivity
| reflexivity
| sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot];
[ rewrite R11, Z.add_0_r, ews2, ews1; reflexivity | exact R12 | exact R13 ]
| clear HS HM HCB; rename HS' into HS;
apply (runs_at_wbytes_below zsp m _ (Z_to_bv 64 PROGNAME) bs) in HR;
[ | rewrite length_N_to_le_bytes; change (bv_unsigned (Z_to_bv 64 PROGNAME)) with PROGNAME;
unfold PROGNAME; lia ] ]
end end end.
all: clear H8 H10 R11 R12 R13 Rfr.
(* The strings are top-anchored now, so the window for atom 7 comes from [str_bounds] and
   [z_argv_bounds], not from the old sp-relative [block_fits] -- and with that window
   [ptr_fact 0] is NOT PROVABLE, which is what [lia] was reporting as "No applicable
   tactic" (the same vocabulary YA02.v:256-262 records for a false [lia] goal in this
   tree).  Measured: atom 7 is [z_argv ztop argv envp efn 0 + progname_off (nth 0 argv
   [])], so by [ZAB 0] it is at most [z_strs + total_arg_bytes_nat argv - 1], and by [SB]
   that equals [ztop - total_arg_bytes_nat envp - length efn - 10], hence at most
   [SP_HI - 10] by [LF]'s [ztop <= SP_HI] -- with both tails EMPTY that is exactly
   SP_HI - 10, six bytes above [ptr_fact]'s [SP_HI - 16].  [SP_HI - 16] is [ptr_fact]'s
   window because it is the POINTER-block window (YP08.v:312; atoms 4, 5 and 6 of
   YP08.v:319-321 take it, all 16-aligned).  Atom 7 is a STRINGS pointer, exactly like
   atoms 1 and 2 (YP08.v:316-317), whose fact is [str_fact = mkAF SP_LO (SP_HI - 9) 0]
   (YP08.v:313) -- the same alignment, the strings window, and the bound the layout
   actually gives, with one byte to spare.  The plan at :131 carries the same correction;
   the two must agree because [ss_main_*] is [vm_compute]d from it. *)
all: sym_add_fact HS 7%nat str_fact;
[ unfold str_fact, SP_LO, SP_HI, K_stack; cbn [af_lo af_hi af_al2]; rewrite ews7;
pose proof LF as LFw; pose proof SB as SBw; pose proof (proj1 Hva) as HAw;
pose proof (ZAB 0 ltac:(lia)) as ZAw; pose proof (progname_off_le (nth 0 argv []));
unfold SP_LO, SP_HI in *;
change (2^0) with 1; rewrite Z.mod_1_r; lia
| ].
all: clear B0.
all: idtac "PHASE E".
all: sym_run_with src0tbl_ok HS; clear regs2.
all: idtac "PHASE F".
all: lazymatch type of HS with st_ok_ecall _ ?E ?ss _ =>
sym_ecall_open HS; cbn [ms_mem pend_at] in HR;
lazymatch goal with Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
eapply rz_set_tid_first; [exact Hh | exact Hlz | rewrite (Hregs 17%bv); reflexivity | exact Htid | ];
intros tid Htid8; rewrite PID_MAX_ENVELOPE_val in Htid8;
assert (HA8 : env_agree 8%nat E (E_st sp inp mbase tid rnd))
by (split; [intros n Hn; do 8 (destruct n as [|n]; [reflexivity|]); lia | reflexivity]);
pose proof (st_ok_resume_mem src0segs 8%nat E (E_st sp inp mbase tid rnd) ss regs mem (SOff 8 0) tid (ss_mem ss)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))
Hregs HA8 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)
(mem_ok_agree src0segs 8%nat _ _ mem (ss_mem ss) HA8 ltac:(vm_compute; reflexivity) Hmem)
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
all: sym_run_to_with src0tbl_ok HS 0x15ce4.
all: sym_add_chunk_sem HS (@None nat) guard_data_chunk;
[ intros HCS; apply (guard_data_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM);
[ cbn; lia
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS) ]
| ].
all: sym_run_to_with src0tbl_ok HS 0x15ce8.
all: sym_add_chunk_sem HS (@None nat) canary_chunk;
[ intros HCS; apply (canary_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM CANARY_ATOM);
[ cbn; lia
| reflexivity
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS)
| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HCS))) ]
| ].
all: idtac "PHASE H".
all: sym_run_to_with src0tbl_ok HS 0x12930.
all: idtac "PHASE I".
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_head src0segs E ss ms keep_zero) in HS;
apply (st_ok_prune src0segs E _ ms [] [0%nat]) in HS end.
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_all src0segs E ss ms keep_main) in HS;
apply (st_ok_agree_pd src0segs (fun _ => true) (not_in START_DATOMS) _
(E_main sp inp argv envp efn tid rnd)) in HS;
[ | apply E_st_main_agree | vm_compute; reflexivity ] end.
all: sym_norm HS.
- change (st_ok src0segs (E_main sp inp argv envp efn tid rnd) (ss_main true true) ms) in HS.
exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp inp argv envp efn tid rnd) (ss_main false true) ms) in HS.
exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp inp argv envp efn tid rnd) (ss_main true false) ms) in HS.
exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp inp argv envp efn tid rnd) (ss_main false false) ms) in HS.
exact (K ms tid Htid8 HS HR).
Qed.
End f.
Theorem src0_start : forall (two : bool) sp brk mbase rnd lim inp T,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> valid_input inp ->
(if two then (2 <= length (in_argv inp))%nat else True) ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd)
(ss_main (kb_rseq (in_kernel inp)) two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms)
(runs_main (kb_rseq (in_kernel inp)) two sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) ->
(* [init_config] wraps the model in [with_vdso (vdso_run_init (ed_vdso mi_draw))] at this
   revision (75d69e00:theories/LinuxProcessSem/Run.v:1426-1430, the ONE writer of that
   field), so the caller's obligation [K] is about THAT model, not the bare [init_model].
   [src0_start_gen] below already quantifies over the model and is applied to the goal's
   own one, so this line is what makes [exact K] at :638 meet it. *)
realizes src0segs (mkCfg ms (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
(init_model (segments_reserved src0segs) brk mbase sp lim inp)))) T) ->
realizes src0segs (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) T.
Proof.
intros two sp brk mbase rnd lim inp T Hsp Hva Hve Hvl Hlau Hvi Htwo K.
unfold init_config.
apply (src0_start_gen inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau Hvi two);
[exact Htwo | reflexivity | reflexivity | reflexivity | exact K].
Qed.
