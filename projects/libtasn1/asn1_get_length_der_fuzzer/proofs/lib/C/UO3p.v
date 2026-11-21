(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Trevor Hansen, 2026-11: hex addresses and numbers for the binaries of libtasn1/asn1_get_length_der_fuzzer, and module names. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the change of the same file of cgif/cgif_rgb_fuzzer with its addresses relocated to this unit's binaries and one copied comment reworded, and the start-up proof stated over the run with the launch premises, the CONFIG_RSEQ-indexed states and the vDSO draw of the initial model; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YK11 YK0i YK0j YK14 YK1a YK1b YK15 YK0o YQ0k.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import YQ0j YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ0a YQ05 YL02 YO3u.
From OSSVerify.Proofs.libtasn1.asn1_get_length_der_fuzzer.lib.C Require Import UH04 UH05 UO3s.
From OSSVerify.libtasn1.asn1_get_length_der_fuzzer.images Require Import Ubsan.
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
(* lpsrev #38: YQ0a's layout layer re-based — z_argv/z_strs take the
   execfn string [xf] and are measured from [ed_top rnd], not from [sp]. Donor for the
   consumer form, statement and proof: this tree's own UH05.v:36-43 (green at 75d69e00 —
   this file imports it, so it compiled before this file failed). *)
Definition xw_main (sp top : word) (argv envp : list (list byte)) (xf : list byte) (tid : word) (rnd : EntryDraw) (n : nat) : word :=
match n with
| 7%nat => Z_to_bv 64 (z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (progname_off (nth 0 argv [])))
| 8%nat => tid
| 9%nat => canary_word (rand_bytes rnd)
| _ => Z_to_bv 64 0
end.
Definition xd_main (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d RAND_DATOM then rand_bytes rnd else [].
(* The ported [ubs2_init_st_ok] (UH05.v) demands TWELVE datom values of its
   [xd]: UID, HWCAP and RAND as before, and the five families this revision
   added to the auxv.

   The five missing families all come off the RUN, which is what makes this a
   threading and not a pin: GID from [in_gid inp], SYSI and MSS from
   [launch_auxv inp sp mbase], XFN from [ed_top rnd] and [in_execfn inp], and the
   eight cache words from [la_cache (launch_auxv inp sp mbase)].  Nothing here
   reads [kb_rseq] or any other free kernel field.

   The cache words are ONE indexed branch, not eight: [CW_DATOM i = (11 + i)%nat]
   (YQ0a.v:244) over a closed eight-element [cache_list] (:246-247), so the
   range test [11 <= d < 19] recovers [i = d - 11].  The numbering is disjoint
   by construction - UID 4, HWCAP 6, RAND 7, GID 8, SYSI 9, XFN 10, CW 11..18,
   MSS 19 - so the chain of tests below cannot shadow a later case.

   Donor: YQ0a.v:705-723, which takes exactly these twelve as hypotheses on an
   abstract [xd] and proves [ed_uid]/[ed_gid]/… by [exact].  This definition is
   the witness that discharges them. *)
Definition xd_run (inp : ProcInput) (sp : word) (mbase : word) (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d UID_DATOM then uid_bytes (in_uid inp)
else if Nat.eqb d HWCAP_DATOM then hwcap_bytes (in_hwcap inp)
else if Nat.eqb d RAND_DATOM then rand_bytes rnd
else if Nat.eqb d GID_DATOM then word_le8 (in_gid inp)
else if Nat.eqb d SYSI_DATOM then word_le8 (la_sysinfo_ehdr (launch_auxv inp sp mbase))
else if Nat.eqb d XFN_DATOM then word_le8 (at_execfn_ptr (ed_top rnd) (in_execfn inp))
else if Nat.eqb d MSS_DATOM then word_le8 (la_minsigstksz (launch_auxv inp sp mbase))
else if ((11 <=? d)%nat && (d <? 19)%nat)%bool
then word_le8 (nth (d - 11) (cache_list (la_cache (launch_auxv inp sp mbase))) (Z_to_bv 64 0))
else [].
Lemma xd_run_cw : forall inp sp mbase rnd i, (i < 8)%nat ->
xd_run inp sp mbase rnd (CW_DATOM i)
= word_le8 (nth i (cache_list (la_cache (launch_auxv inp sp mbase))) (Z_to_bv 64 0)).
Proof.
intros inp sp mbase rnd i Hi. unfold xd_run, CW_DATOM.
do 8 (destruct i as [|i]; [reflexivity|]). cbn in Hi. lia.
Qed.
(* The datoms the start-up environment answers and the main environment does
   not: every launch value of the auxv but AT_RANDOM's bytes.  [keep_main]
   drops the chunks that read them, so [ss_main] needs none of them. *)
Definition START_DATOMS : list nat :=
[UID_DATOM; HWCAP_DATOM; GID_DATOM; SYSI_DATOM; XFN_DATOM; MSS_DATOM] ++ map CW_DATOM (seq 0 8).
(* Both environments take the RUN [inp] and read its CONFIG_RSEQ flag
   [kb_rseq (in_kernel inp)] inside, so a case split on that flag reaches the
   symbolic states, which need it concrete to compute, and leaves these two
   environments - and every [ews*]/[ewm*] rewrite stated over them - alone. *)
Definition E_main (sp : word) (inp : ProcInput) (argv envp : list (list byte)) (xf : list byte)
(tid : word) (rnd : EntryDraw) : env :=
E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) argv envp xf
(xw_main sp (ed_top rnd) argv envp xf tid rnd) (xd_main rnd).
Definition E_st (sp : word) (inp : ProcInput) (mbase : word) (tid : word) (rnd : EntryDraw) : env :=
E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp)
(xw_main sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) (xd_run inp sp mbase rnd).
Lemma E_st_main_agree : forall sp inp mbase tid rnd,
env_agree_pd (fun _ => true) (not_in START_DATOMS)
(E_st sp inp mbase tid rnd) (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd).
Proof.
intros. split; [intros; reflexivity|].
(* [vm_compute] runs only on the closed membership test [Hd]: on the goal it
   would normalise the launch's auxv values ([launch_auxv inp sp mbase], open in
   [inp]) in full.  The goal is closed by lazy conversion instead. *)
intros d Hd. unfold E_st, E_main, E0; cbn [ed].
do 20 (destruct d as [|d]; [vm_compute in Hd; first [discriminate | reflexivity] |]).
cbn [xd_run xd_main Nat.eqb Nat.leb Nat.ltb andb]. reflexivity.
Qed.
Definition alias_memset : sv * sv :=
(SAlu ALU_AND (SAluw ALU_SUB (SLit 0) (SOff 0 (-368))) (SLit 3), SLit 0).
Definition alias_envp : sv * sv :=
(SAlu ALU_ADD (SOff 0 16) (SAlu ALU_SLL (SOff 3 0) (SLit 3)), SOff 4 0).
(* ubs2_ss0 gained the rseq flag (UH05.v:23: the start-up layout depends on kb_rseq,
   27 or 29 auxv pairs), so every symbolic start state is now indexed by [rs] too. *)
Definition ss_start (two rs : bool) : sstate :=
add_alias (add_alias (ubs2_ss0 two rs)
(fst alias_memset) (snd alias_memset))
(fst alias_envp) (snd alias_envp).
Definition envp_words (top : word) (argv envp : list (list byte)) (xf : list byte) : list word :=
fst (string_addrs (cat_env_base top argv envp xf) envp) ++ [Z_to_bv 64 0].
Definition envp_block (top : word) (argv envp : list (list byte)) (xf : list byte) : list byte :=
flat_map word_le8 (envp_words top argv envp xf).
Definition runs_main (two : bool) (sp top : word) (argv envp : list (list byte)) (xf : list byte) (rnd : EntryDraw) : list (Z * list byte) :=
(z_envp (bv_unsigned sp) argv, envp_block top argv envp xf)
:: (z_argv (bv_unsigned top) argv envp xf 0, nth 0 argv [] ++ [NUL])
:: (if two then [(z_argv (bv_unsigned top) argv envp xf 1, nth 1 argv [] ++ [NUL])] else [])
(* stack_tail is now (av ev xf) and NO LONGER ENDS IN rand_bytes: YQ0a.v:384-385 is
   flatten_strings av ++ flatten_strings ev ++ xf ++ [NUL] ++ repeat 0 8. The random
   block moved INTO the head (z_rand = zsp + block_head_size rs av ev - 16), so the
   image order changed and this entry is strings-to-top, not strings-then-random. *)
++ [(z_strs (bv_unsigned top) argv envp xf, stack_tail argv envp xf)].
Definition opt_mem (o : option smem) : smem := match o with Some rs => rs | None => [] end.
Definition run_ (ss : sstate) : sstate := fst (sym_runN ubs2segs ubs2tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN ubs2segs ubs2tbl FUEL pc ss).
Definition keep_zero (c : chunk) : bool :=
match c_val c with CZero n => 4096 <=? n | _ => false end.
Definition upd_envp : list (reg * sv) := [(10%bv : reg, SLit 0); (9%bv : reg, SOff 5 0)].
Definition upd_progname : list (reg * sv) := [(11%bv : reg, SOff 2 0); (12%bv : reg, SLit 47); (13%bv : reg, SLit 0)].
Definition tid_fact : afact := mkAF 1 4194303 0.
(* Atom 7 is the progname pointer, a pointer INTO the strings block, which the
   revision anchors at the top of the entry stack: [YQ0a.z_argv_fits] bounds it
   by [SP_HI - 9] and no better, so the pointer-block fact [ptr_fact 0]
   ([SP_HI - 16]) is false for it.  This is its strings-window fact. *)
Definition str_fact : afact := mkAF SP_LO (SP_HI - 9) 0.
Definition GUARD : Z := 0x4d468.
Definition guard_data_chunk : chunk := mkChunk GUARD (CData RAND_DATOM 0 8).
Definition canary_chunk : chunk := mkChunk GUARD (CVal 8 (SOff CANARY_ATOM 0)).
Definition is_canary_val (cv : cval) : bool :=
match cv with CVal 8 (SOff n 0) => Nat.eqb n CANARY_ATOM | _ => false end.
Definition keep_main (c : chunk) : bool :=
cval_atoms_pd (fun _ => true) (not_in START_DATOMS) (c_val c)
&& negb ((GUARD <=? c_off c) && (c_off c <? GUARD + 8) && negb (is_canary_val (c_val c))).
(* #38: [ubs2_ss0] gained the CONFIG_RSEQ flag (UH05.v:23 - 27 or 29 auxv
   pairs) and [ss_start] at :75 was widened to pass it, but THIS consumer was
   not, which is the `ss_start two has type bool -> sstate` error.  Threading
   it, never pinning: [ss_start two false] would compile instantly and would
   narrow the unit to the rseq-off case, which is a statement change by the
   back door - the unit's published statement quantifies over [kb_rseq]. *)
Definition main_state (two rs : bool) : sstate :=
let s1 := run_ (ss_start two rs) in
let s2 := set_regs_pc s1 upd_envp 0x12bd0 in
let s3 := runto_ 0x12c70 s2 in
let s4 := add_atom (mkSS 0x12c94 (sr_sets (ss_regs s3) upd_progname)
(opt_mem (store_region (ss_mem s3) None 0x4d478 8 (CVal 8 (SOff 7 0))))
None (ss_facts s3)) 7 str_fact in
let s5 := run_ s4 in
let s6 := resume s5 (SOff 8 0) (ss_mem s5)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts s5))
(f_conds (ss_facts s5)) (f_alias (ss_facts s5))) in
let s7 := runto_ 0x134f8 s6 in
let s8 := add_chunk_ None guard_data_chunk s7 in
let s9 := runto_ 0x134fc s8 in
let s10 := add_chunk_ None canary_chunk s9 in
let s11 := runto_ 0x125b4 s10 in
let s12 := prune (mkSS (ss_pc s11) (ss_regs s11) (clean_head keep_zero (ss_mem s11)) (ss_resv s11) (ss_facts s11))
[] [0%nat] in
mkSS (ss_pc s12) (ss_regs s12) (clean_all keep_main (ss_mem s12)) (ss_resv s12) (ss_facts s12).
(* #38, Main's CHAIN-DUP ruling: the reduced chain is instantiated at both
   CONFIG_RSEQ values and selected by the run's own flag.  The [two] dimension
   is pre-existing and orthogonal, so this is the approved rseq DOUBLING of an
   already-doubled chain, not a new four-way cost.  MEASURED before writing:
   the whole [ss_main] cone is 90 `Eval vm_compute` lines over 10 files
   (control: 2,464 tree-wide over 289), so the doubling is ~90 lines - the same
   order as the [mem_am0] fixture chain, and an order of magnitude below the
   cgif_file twin's.  [ss_main_t]/[ss_main_f] are DELETED rather than kept as
   rseq-pinned aliases (rule 12f), so every consumer that has not been threaded
   fails at compile time instead of silently compiling the rseq-on case. *)
Definition ss_main_tt : sstate := Eval vm_compute in (main_state true true).
Definition ss_main_tf : sstate := Eval vm_compute in (main_state true false).
Definition ss_main_ft : sstate := Eval vm_compute in (main_state false true).
Definition ss_main_ff : sstate := Eval vm_compute in (main_state false false).
Definition ss_main (two rs : bool) : sstate :=
if two then (if rs then ss_main_tt else ss_main_tf)
else (if rs then ss_main_ft else ss_main_ff).
Lemma bytes_at_app : forall m a l1 l2,
YQ04.bytes_at m a l1 -> YQ04.bytes_at m (a + Z.of_nat (length l1)) l2 ->
YQ04.bytes_at m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hg].
- rewrite nth_error_app1 by exact Hl. apply H1. exact Hl.
- rewrite nth_error_app2 by exact Hg.
replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia.
apply H2. lia.
Qed.
Lemma length_envp_words : forall top argv envp xf, length (envp_words top argv envp xf) = (length envp + 1)%nat.
Proof. intros. unfold envp_words. rewrite length_app, length_string_addrs_fst. reflexivity. Qed.
Lemma length_envp_block : forall top argv envp xf, length (envp_block top argv envp xf) = (8 * length envp + 8)%nat.
Proof. intros. unfold envp_block. rewrite length_flat_map_le8, length_envp_words. lia. Qed.
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
Lemma runs_main_init : forall (two : bool) pc,
(if two then (2 <= length argv)%nat else True) ->
runs_at (bv_unsigned sp) (ms_mem (init_machine_state ubs2segs pc Ubsan_phdrs sp mbase rnd inp))
(runs_main two sp top argv envp xf rnd).
Proof.
intros two pc Htwo. rewrite init_mkst. cbn [ms_mem mkst].
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. unfold SP_LO, SP_HI in L.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
unfold runs_main. cbn [app]. apply Forall_cons; [|apply Forall_cons; [| apply Forall_app; split]].
- cbn [fst snd]. rewrite length_envp_block.
split; [lia|]. split; [lia|]. unfold envp_block, envp_words. rewrite flat_map_app. apply bytes_at_app.
+ unfold cat_env_base, cat_string_base. apply (m0_envp_ptrs Ubsan_phdrs inp pc mbase sp brk rnd Hsp Hlau).
+ rewrite length_flat_map_le8, length_string_addrs_fst. cbn [flat_map]. rewrite app_nil_r.
replace (z_envp (bv_unsigned sp) argv + Z.of_nat (8 * length envp))
with (z_auxv (bv_unsigned sp) argv envp - 8) by lia.
apply (m0_envp_null Ubsan_phdrs inp pc mbase sp brk rnd Hsp Hlau).
- cbn [fst snd]. pose proof (z_argv_bounds inp rnd 0 ltac:(lia)) as B.
pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 0 ltac:(lia)) as F. unfold SP_HI in F.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. apply (m0_argv_str Ubsan_phdrs inp pc mbase sp brk rnd Hsp Hlau 0). lia.
- destruct two; [|constructor]. apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (z_argv_bounds inp rnd 1 ltac:(lia)) as B.
pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 1 ltac:(lia)) as F. unfold SP_HI in F.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. apply (m0_argv_str Ubsan_phdrs inp pc mbase sp brk rnd Hsp Hlau 1). lia.
- apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (stack_tail_end inp rnd) as B.
split; [lia|]. split; [lia|]. apply (m0_tail Ubsan_phdrs inp pc mbase sp brk rnd Hsp Hlau).
Qed.
Let E_stR (t : word) : env := E_st sp inp mbase t rnd.
Lemma alias_memset_ok : forall t,
sv_denot (E_stR t) (fst alias_memset) = sv_denot (E_stR t) (snd alias_memset).
Proof.
intros t. cbn [fst snd alias_memset sv_denot].
rewrite zalu32_sound, zalu64_sound. f_equal. apply negw_and3_zero.
unfold E_stR, E_st. rewrite (ew0 inp sp rnd). exact (proj2 (proj2 Hsp)).
Qed.
Lemma alias_envp_ok : forall t,
sv_denot (E_stR t) (fst alias_envp) = sv_denot (E_stR t) (snd alias_envp).
Proof.
intros t. cbn [fst snd alias_envp sv_denot]. unfold E_stR, E_st.
rewrite !zalu64_sound. rewrite (ew0 inp sp rnd), (ew3 inp sp rnd Hva), (ew4 inp mbase sp brk rnd Hsp Hlau).
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. pose proof (proj1 Hva) as HA.
unfold z_xfn in L. unfold SP_LO, SP_HI in L.
apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !Z.add_0_r. rewrite !(Z.mod_small _ (2^64)) by lia. lia.
Qed.
Lemma ewm1 : forall t, bv_unsigned (ew (E_main sp inp argv envp xf t rnd) 1) = z_argv (bv_unsigned top) argv envp xf 0.
Proof.
intros t. pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L.
unfold E_main. rewrite (ew1 inp mbase sp brk rnd Hsp Hlau). lia.
Qed.
Lemma ewm2 : forall t, bv_unsigned (ew (E_main sp inp argv envp xf t rnd) 2)
= z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof.
intros t. pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L.
unfold E_main. rewrite (ew2 inp mbase sp brk rnd Hsp Hva Hlau). lia.
Qed.
Lemma ewm4 : forall t, bv_unsigned (ew (E_main sp inp argv envp xf t rnd) 4) = z_envp (bv_unsigned sp) argv.
Proof. intros t. exact (ew4 inp mbase sp brk rnd Hsp Hlau _ _). Qed.
Lemma ewm5 : forall t, bv_unsigned (ew (E_main sp inp argv envp xf t rnd) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. intros t. exact (ew5 inp mbase sp brk rnd Hsp Hlau _ _). Qed.
Lemma ewm7 : forall t, bv_unsigned (ew (E_main sp inp argv envp xf t rnd) 7)
= z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof.
intros t. cbn [ew E_main E0 xw_main].
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. pose proof (proj1 Hva) as HA.
pose proof (z_argv_bounds inp rnd 0 ltac:(lia)) as B.
pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 0 ltac:(lia)) as F.
pose proof (progname_off_le (nth 0 argv [])).
unfold SP_LO, SP_HI in L, F. apply u_Z2bv; lia.
Qed.
Lemma ews1 : forall t, bv_unsigned (ew (E_stR t) 1) = z_argv (bv_unsigned top) argv envp xf 0.
Proof. exact ewm1. Qed.
Lemma ews2 : forall t, bv_unsigned (ew (E_stR t) 2)
= z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof. exact ewm2. Qed.
Lemma ews4 : forall t, bv_unsigned (ew (E_stR t) 4) = z_envp (bv_unsigned sp) argv.
Proof. exact ewm4. Qed.
Lemma ews5 : forall t, bv_unsigned (ew (E_stR t) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. exact ewm5. Qed.
Lemma ews7 : forall t, bv_unsigned (ew (E_stR t) 7)
= z_argv (bv_unsigned top) argv envp xf 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof. exact ewm7. Qed.
Lemma ews8 : forall t, ew (E_stR t) 8 = t.
Proof. intros t. reflexivity. Qed.
Lemma envp_block_reads : forall m t,
YQ04.bytes_at m (z_envp (bv_unsigned sp) argv) (envp_block top argv envp xf) ->
(forall i, (i < length envp)%nat -> exists bs,
rdn ubs2segs m (Z_to_bv 64 (bv_unsigned (ew (E_stR t) 4) + 8 * Z.of_nat i)) 8 = Some bs
/\ bytes_le_to_Z bs <> 0)
/\ (exists bs, rdn ubs2segs m (Z_to_bv 64 (bv_unsigned (ew (E_stR t) 4)
+ 8 * Z.of_nat (length envp))) 8 = Some bs
/\ bytes_le_to_Z bs = 0)
/\ bv_unsigned (ew (E_stR t) 4) + 8 * Z.of_nat (length envp) + 8 < 2^64.
Proof.
intros m t HB. rewrite ews4.
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. pose proof (proj1 Hve) as HE.
unfold z_xfn in L. unfold SP_LO, SP_HI in L.
assert (HW : forall k, (k < length envp + 1)%nat ->
rdn ubs2segs m (Z_to_bv 64 (z_envp (bv_unsigned sp) argv + 8 * Z.of_nat k)) 8
= Some (word_le8 (nth k (envp_words top argv envp xf) (Z_to_bv 64 0)))).
{ intros k Hk. apply (bytes_at_rdn ubs2segs m _ (word_le8 _)).
apply (bytes_at_le8_nth m _ (envp_words top argv envp xf) k HB). rewrite length_envp_words. exact Hk. }
split; [|split; [|lia]].
- intros i Hi. eexists. split; [apply HW; lia|].
unfold envp_words. rewrite app_nth1 by (rewrite length_string_addrs_fst; exact Hi).
unfold cat_env_base, cat_string_base.
rewrite (u_envp_ptr inp mbase sp brk rnd Hsp Hlau i Hi).
rewrite n_to_le_8_spec, bytes_le_to_Z_8.
pose proof (z_envs_bounds inp rnd i Hi). pose proof (z_envs_fits inp mbase sp brk rnd Hsp Hlau i Hi) as F.
unfold SP_HI in F. rewrite u_Z2bv by lia. lia.
- eexists. split; [apply HW; lia|].
unfold envp_words. rewrite app_nth2 by (rewrite length_string_addrs_fst; lia).
rewrite length_string_addrs_fst, Nat.sub_diag. reflexivity.
Qed.
Lemma argv0_reads : forall m t,
YQ04.bytes_at m (z_argv (bv_unsigned top) argv envp xf 0) (nth 0 argv [] ++ [NUL]) ->
forall j, (j <= length (nth 0 argv []))%nat ->
rdn ubs2segs m (Z_to_bv 64 (bv_unsigned (ew (E_stR t) 1) + Z.of_nat j)) 1
= Some [nth j (nth 0 argv [] ++ [NUL]) NUL].
Proof.
intros m t HB j Hj. rewrite ews1. apply (proj2 (rdn_mbytes ubs2segs m 1 _ [_])).
split; [reflexivity|]. intros i Hi. destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r.
rewrite (bytes_at_mbyte ubs2segs m _ _ j HB) by (rewrite length_app; cbn; lia).
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
pose proof (st_ok_reg ubs2segs _ _ _ r HS) as H;
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
Lemma ubs2_start_gen : forall (two : bool) model T,
(if two then (2 <= length argv)%nat else True) ->
m_halted model = None -> m_vm_lazy model = [] -> m_tid model = None ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok ubs2segs (E_main sp inp argv envp xf tid rnd) (ss_main two rs) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp top argv envp xf rnd) ->
realizes ubs2segs (mkCfg ms (with_tid tid model)) T) ->
realizes ubs2segs (mkCfg (init_machine_state ubs2segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp) model) T.
Proof.
intros two model T Htwo Hh Hlz Htid K.
pose proof (layout_facts inp mbase sp brk rnd Hsp Hlau) as L. unfold z_xfn in L. unfold SP_LO, SP_HI in L.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
(* the ported lemma takes the RUN and twelve datom premises.  [xd_run] is the
   witness for all twelve - seven by [reflexivity], the eight cache words by
   [xd_run_cw] - so nothing here is pinned and nothing is restated. *)
pose proof (ubs2_init_st_ok inp mbase sp brk rnd (xw_main sp top argv envp xf (Z_to_bv 64 0) rnd) (xd_run inp sp mbase rnd) two
Hsp Hva Hve Hvl Hlau eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
(fun i Hi => xd_run_cw inp sp mbase rnd i Hi) Htwo) as HS.
change (st_ok ubs2segs (E_stR (Z_to_bv 64 0)) (ubs2_ss0 two rs)
(init_machine_state ubs2segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp)) in HS.
apply (st_ok_add_alias ubs2segs _ _ _ (fst alias_memset) (snd alias_memset)) in HS; [|apply alias_memset_ok].
apply (st_ok_add_alias ubs2segs _ _ _ (fst alias_envp) (snd alias_envp)) in HS; [|apply alias_envp_ok].
change (st_ok ubs2segs (E_stR (Z_to_bv 64 0)) (ss_start two rs)
(init_machine_state ubs2segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp)) in HS.
pose proof (runs_main_init two Ubsan_init_pc Htwo) as HR.
(* [E_st] and [E_main] read the run's CONFIG_RSEQ flag inside, so this split
   reaches [ss_start], [ss_main] and [L] - the places that need it concrete -
   and leaves the environments, and the [ews*] rewrites over them, alone.
   [HS] and [K] are reverted first: [destruct] on a term abstracts it in the
   goal only, and a state left with the flag opaque cannot compute. *)
revert HS K. destruct two; destruct (kb_rseq (in_kernel inp)); intros HS K.
all: sym_run_with ubs2tbl_ok HS.
all: idtac "PHASE B".
all: reg_of HS (9%bv:reg) H9.
all: lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
destruct (envp_block_reads (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 0 _ _ HR eq_refl))
as (Hnz & Hz & Hnw);
destruct (ubs2_envp_count (length envp) (ms_regs ms) (ms_mem ms) (seg_rom ubs2segs) _ H9 Hnz Hz Hnw)
as (regs1 & Hms & R10 & R9 & Rfr) end.
all: lazymatch type of HS with st_ok _ ?E _ _ =>
sym_spliceL HS Hms 9%nat E (env_agree_refl 9%nat E) upd_envp end;
[ sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot];
[ exact R10 | rewrite R9, Z.add_0_r, ews4, ews5; apply (f_equal (Z_to_bv 64)); lia ]
| ].
all: clear H9 Hnz Hz Hnw R10 R9 Rfr.
all: idtac "PHASE C".
all: sym_run_to_with ubs2tbl_ok HS 0x12c70; clear regs1.
all: idtac "PHASE D".
all: reg_of HS (8%bv:reg) H8; reg_of HS (10%bv:reg) H10.
all: pose proof (z_argv_bounds inp rnd 0 ltac:(lia)) as B0.
all: pose proof (z_argv_fits inp mbase sp brk rnd Hsp Hlau 0 ltac:(lia)) as F0; unfold SP_HI in F0.
all: lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
destruct (ubs2_progname_scan (nth 0 argv []) _ (ms_mem ms) (seg_rom ubs2segs) (ms_regs ms)
(argv_no_nul inp Hva 0 ltac:(lia))
ltac:(rewrite ews1; lia)
ltac:(left; rewrite ews1; unfold PROGNAME; lia)
H8 H10
(argv0_reads (ms_mem ms) (Z_to_bv 64 0) (runs_at_nth _ (ms_mem ms) _ 1 _ _ HR eq_refl)))
as (regs2 & Hms & R11 & R12 & R13 & Rfr) end.
all: pose proof (st_ok_mkst ubs2segs _ _ _ HS eq_refl) as Hshape;
rewrite Hshape; (eapply rz_msteps; [exact Hh | exact Hlz | exact Hms | ]);
rewrite Hshape in HS; clear Hshape Hms.
all: lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?m' _) _) _ =>
lazymatch m' with wbytes _ _ ?bs =>
lazymatch type of HS with st_ok _ ?E ?ss (mkst _ _ ?m _) =>
let rs' := eval vm_compute in (opt_mem (store_region (ss_mem ss) None 0x4d478 8 (CVal 8 (SOff 7 0)))) in
assert (HCB : forall i, 0 <= i < Z.of_nat (length bs) ->
cbyte ubs2segs E (base_val E None + 0x4d478) (CVal 8 (SOff 7 0)) i = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite length_N_to_le_bytes in Hi;
change (CVal 8 (SOff 7 0)) with (CVal (N.of_nat 8) (SOff 7 0));
rewrite (st_bytes_cbyte ubs2segs E) by lia;
unfold word_to_le_bytes; rewrite Z_to_le_bytes_st; do 2 f_equal;
cbn [sv_denot]; rewrite Z.add_0_r, ews7, ews1; reflexivity
| ];
pose proof (proj2 (swrite_sound ubs2segs E m (ss_mem ss) None 0x4d478 (CVal 8 (SOff 7 0)) bs rs'
(st_ok_mem_ok ubs2segs E ss _ HS)
ltac:(rewrite length_N_to_le_bytes; vm_compute; reflexivity)
ltac:(rewrite length_N_to_le_bytes; lia)
ltac:(rewrite length_N_to_le_bytes; reflexivity) HCB)) as HM;
change (mem_ok ubs2segs E m' rs') in HM;
unshelve epose proof (st_ok_set_regs_mem ubs2segs 9%nat E E ss _ regs2 _ 0x12c94 m m' rs' upd_progname
HS (env_agree_refl 9%nat E) _ _ _ _ HM) as HS';
[ vm_compute; reflexivity
| reflexivity
| sym_splice_frame Rfr
| repeat constructor; cbn [fst snd sv_denot];
[ rewrite R11, Z.add_0_r, ews2, ews1; reflexivity | exact R12 | exact R13 ]
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
all: sym_run_with ubs2tbl_ok HS; clear regs2.
all: idtac "PHASE F".
all: lazymatch type of HS with st_ok_ecall _ ?E ?ss _ =>
sym_ecall_open HS; cbn [ms_mem pend_at] in HR;
lazymatch goal with Hregs : regs_ok _ _ ?regs, Hmem : mem_ok _ _ ?mem _, HG : facts_ok _ _ |- _ =>
eapply rz_set_tid_first; [exact Hh | exact Hlz | rewrite (Hregs 17%bv); reflexivity | exact Htid | ];
intros tid Htid8; rewrite PID_MAX_ENVELOPE_val in Htid8;
assert (HA8 : env_agree 8%nat E (E_stR tid))
by (split; [intros n Hn; do 8 (destruct n as [|n]; [reflexivity|]); lia | reflexivity]);
pose proof (st_ok_resume_mem ubs2segs 8%nat E (E_stR tid) ss regs mem (SOff 8 0) tid (ss_mem ss)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))
Hregs HA8 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Z.add_0_r; apply Z_to_bv_bv_unsigned)
(mem_ok_agree ubs2segs 8%nat _ _ mem (ss_mem ss) HA8 ltac:(vm_compute; reflexivity) Hmem)
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
all: sym_run_to_with ubs2tbl_ok HS 0x134f8.
all: sym_add_chunk_sem HS (@None nat) guard_data_chunk;
[ intros HCS; apply (guard_data_chunk_ok ubs2segs _ _ 0 GUARD RAND_DATOM);
[ cbn; lia
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS) ]
| ].
all: sym_run_to_with ubs2tbl_ok HS 0x134fc.
all: sym_add_chunk_sem HS (@None nat) canary_chunk;
[ intros HCS; apply (canary_chunk_ok ubs2segs _ _ 0 GUARD RAND_DATOM CANARY_ATOM);
[ cbn; lia
| reflexivity
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS)
| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HCS))) ]
| ].
all: idtac "PHASE H".
all: sym_run_to_with ubs2tbl_ok HS 0x125b4.
all: idtac "PHASE I".
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_head ubs2segs E ss ms keep_zero) in HS;
apply (st_ok_prune ubs2segs E _ ms [] [0%nat]) in HS end.
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_all ubs2segs E ss ms keep_main) in HS;
apply (st_ok_agree_pd ubs2segs (fun _ => true) (not_in START_DATOMS) _ (E_main sp inp argv envp xf tid rnd)) in HS;
[ | apply E_st_main_agree | vm_compute; reflexivity ] end.
all: sym_norm HS.
all: exact (K ms tid Htid8 HS HR).
Qed.
End f.
Theorem ubs2_start : forall (two : bool) sp brk mbase rnd lim inp T,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
(if two then (2 <= length (in_argv inp))%nat else True) ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok ubs2segs (E_main sp inp (in_argv inp) (in_envp inp) (in_execfn inp) tid rnd) (ss_main two (kb_rseq (in_kernel inp))) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) rnd) ->
realizes ubs2segs (mkCfg ms (with_tid tid (with_vdso (vdso_run_init (ed_vdso rnd))
(init_model (segments_reserved ubs2segs) brk mbase sp lim inp)))) T) ->
realizes ubs2segs (init_config ubs2segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) T.
Proof.
intros two sp brk mbase rnd lim inp T Hsp Hva Hve Hvl Hlau Htwo K.
unfold init_config.
apply (ubs2_start_gen inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau two);
[exact Htwo | reflexivity | reflexivity | reflexivity | exact K].
Qed.
