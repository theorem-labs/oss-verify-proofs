(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3e.v, with its module paths and addresses changed. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the CONFIG_RSEQ-sized auxiliary vector; the vvar/vDSO pair in the initial model and its reservations; the launch's ProcInput, mmap base and entry draw; a lemma name made explicit; the launch's string area with the exec file name); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YH00 YH01 YN3h.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require YO0d.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Ubsan.
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
Definition xw_main (inp : ProcInput) (rnd : EntryDraw) (tid : word) (n : nat) : word :=
match n with
| 7%nat => Z_to_bv 64 (z_argv (bv_unsigned (ed_top rnd)) (in_argv inp) (in_envp inp) (in_execfn inp) 0
                       + Z.of_nat (progname_off (nth 0 (in_argv inp) [])))
| 8%nat => tid
| 9%nat => canary_word (rand_bytes rnd)
| _ => Z_to_bv 64 0
end.
Definition xd_main (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d RAND_DATOM then rand_bytes rnd else [].
Definition xd_st (inp : ProcInput) (sp : word) (mbase : word) (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d UID_DATOM then uid_bytes (in_uid inp)
else if Nat.eqb d HWCAP_DATOM then hwcap_bytes (in_hwcap inp)
else if Nat.eqb d RAND_DATOM then rand_bytes rnd
else if Nat.eqb d GID_DATOM then gid_bytes (in_gid inp)
else if Nat.eqb d EHDR_DATOM then ehdr_bytes inp sp mbase
else if Nat.eqb d EXECFN_DATOM then execfn_ptr_bytes (ed_top rnd) (in_execfn inp) else [].
Definition E_main (sp : word) (inp : ProcInput) (tid : word) (rnd : EntryDraw) : env :=
E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) (xw_main inp rnd tid) (xd_main rnd).
Definition E_st (sp : word) (inp : ProcInput) (mbase : word) (rnd : EntryDraw) (tid : word) : env :=
E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) (xw_main inp rnd tid) (xd_st inp sp mbase rnd).
(** The data atoms the start-up reads and main does not: the credentials, hwcap, the vDSO base and the
    AT_EXECFN pointer. *)
Definition FORGET : list nat := [UID_DATOM; HWCAP_DATOM; GID_DATOM; EHDR_DATOM; EXECFN_DATOM].
Lemma E_st_main_agree : forall sp inp mbase rnd tid,
env_agree_pd (fun _ => true) (not_in FORGET) (E_st sp inp mbase rnd tid) (E_main sp inp tid rnd).
Proof.
intros. split; [intros; reflexivity|].
intros d Hd. unfold not_in, FORGET in Hd. cbn [existsb] in Hd. rewrite orb_false_r in Hd.
apply negb_true_iff in Hd. apply orb_false_iff in Hd as [Hd1 Hd].
apply orb_false_iff in Hd as [Hd2 Hd]. apply orb_false_iff in Hd as [Hd3 Hd].
apply orb_false_iff in Hd as [Hd4 Hd5].
unfold E_st, E_main, E0; cbn [ed].
destruct d as [|[|d]]; [reflexivity|reflexivity|].
unfold xd_st, xd_main. rewrite Hd1, Hd2.
destruct (Nat.eqb (S (S d)) RAND_DATOM); [reflexivity|].
rewrite Hd3, Hd4, Hd5. reflexivity.
Qed.
Definition alias_memset : sv * sv :=
(SAlu ALU_AND (SAluw ALU_SUB (SLit 0) (SOff 0 (-368))) (SLit 3), SLit 0).
Definition alias_envp : sv * sv :=
(SAlu ALU_ADD (SOff 0 16) (SAlu ALU_SLL (SOff 3 0) (SLit 3)), SOff 4 0).
Definition ss_start (rs two : bool) : sstate :=
add_alias (add_alias (src0_ss0 rs two)
(fst alias_memset) (snd alias_memset))
(fst alias_envp) (snd alias_envp).
Definition envp_words (inp : ProcInput) (rnd : EntryDraw) : list word :=
fst (string_addrs (cat_env_base (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp)) (in_envp inp)) ++ [Z_to_bv 64 0].
Definition envp_block (inp : ProcInput) (rnd : EntryDraw) : list byte :=
flat_map word_le8 (envp_words inp rnd).
(** The auxv words the start-up leaves on the stack, as mallocng's [auxv_pre] reads them: the type
    word of each pair the kernel's rseq flag selects, and the AT_RANDOM pointer. *)
Definition runs_auxv (sp : word) (inp : ProcInput) : list (Z * list byte) :=
let zsp := bv_unsigned sp in let av := in_argv inp in let ev := in_envp inp in
let rs := kb_rseq (in_kernel inp) in
map (fun k => (z_auxv zsp av ev + 16 * Z.of_nat k, word_le8 (Z_to_bv 64 (nth k (YO0d.auxv_types rs) 0))))
  (seq 0 (length (YO0d.auxv_types rs)))
++ [(z_auxv zsp av ev + 16 * Z.of_nat YO0d.AUXV_RAND_K + 8, word_le8 (Z_to_bv 64 (z_rand zsp rs av ev)))].
Lemma nth_auxv_words_key : forall la ph e u g h ar ef k,
(k < length (YO0d.auxv_types (la_rseq la)))%nat ->
nth (2 * k) (auxv_words (auxv_entries la ph e u g h ar ef)) (Z_to_bv 64 0)
= Z_to_bv 64 (nth k (YO0d.auxv_types (la_rseq la)) 0).
Proof.
intros la ph e u g h ar ef k Hk. unfold auxv_entries. cbv zeta.
destruct (la_rseq la); cbn [YO0d.auxv_types length app] in Hk;
do 29 (destruct k as [|k]; [reflexivity|]); lia.
Qed.
Lemma nth_auxv_words_rand : forall la ph e u g h ar ef,
nth (2 * YO0d.AUXV_RAND_K + 1) (auxv_words (auxv_entries la ph e u g h ar ef)) (Z_to_bv 64 0) = ar.
Proof. intros. unfold auxv_entries, YO0d.AUXV_RAND_K. cbv zeta. destruct (la_rseq la); reflexivity. Qed.
Lemma length_auxv_types_count : forall rs, length (YO0d.auxv_types rs) = auxv_count rs.
Proof. intros [|]; reflexivity. Qed.
Definition runs_main (two : bool) (sp : word) (inp : ProcInput) (rnd : EntryDraw) : list (Z * list byte) :=
let ztop := bv_unsigned (ed_top rnd) in
let av := in_argv inp in let ev := in_envp inp in let efn := in_execfn inp in
(z_envp (bv_unsigned sp) av, envp_block inp rnd)
:: (z_argv ztop av ev efn 0, nth 0 av [] ++ [NUL])
:: (if two then [(z_argv ztop av ev efn 1, nth 1 av [] ++ [NUL])] else [])
++ [(z_strs ztop av ev efn, stack_tail av ev efn)] ++ runs_auxv sp inp.
Definition opt_mem (o : option smem) : smem := match o with Some rs => rs | None => [] end.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition keep_zero (c : chunk) : bool :=
match c_val c with CZero n => 4096 <=? n | _ => false end.
Definition upd_envp : list (reg * sv) := [(10%bv : reg, SLit 0); (9%bv : reg, SOff 5 0)].
Definition upd_progname : list (reg * sv) := [(11%bv : reg, SOff 2 0); (12%bv : reg, SLit 47); (13%bv : reg, SLit 0)].
Definition tid_fact : afact := mkAF 1 4194303 0.
Definition GUARD : Z := 0x4e8f0.
Definition guard_data_chunk : chunk := mkChunk GUARD (CData RAND_DATOM 0 8).
Definition canary_chunk : chunk := mkChunk GUARD (CVal 8 (SOff CANARY_ATOM 0)).
Definition is_canary_val (cv : cval) : bool :=
match cv with CVal 8 (SOff n 0) => Nat.eqb n CANARY_ATOM | _ => false end.
Definition keep_main (c : chunk) : bool :=
cval_atoms_pd (fun _ => true) (not_in FORGET) (c_val c)
&& negb ((GUARD <=? c_off c) && (c_off c <? GUARD + 8) && negb (is_canary_val (c_val c))).
Definition main_state (rs two : bool) : sstate :=
let s1 := run_ (ss_start rs two) in
let s2 := set_regs_pc s1 upd_envp 0x13d34 in
let s3 := runto_ 0x13dd4 s2 in
let s4 := add_atom (mkSS 0x13df8 (sr_sets (ss_regs s3) upd_progname)
(opt_mem (store_region (ss_mem s3) None 0x4e900 8 (CVal 8 (SOff 7 0))))
None (ss_facts s3)) 7 str_fact in
let s5 := run_ s4 in
let s6 := resume s5 (SOff 8 0) (ss_mem s5)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts s5))
(f_conds (ss_facts s5)) (f_alias (ss_facts s5))) in
let s7 := runto_ 0x1460c s6 in
let s8 := add_chunk_ None guard_data_chunk s7 in
let s9 := runto_ 0x14610 s8 in
let s10 := add_chunk_ None canary_chunk s9 in
let s11 := runto_ 0x12920 s10 in
let s12 := prune (mkSS (ss_pc s11) (ss_regs s11) (clean_head keep_zero (ss_mem s11)) (ss_resv s11) (ss_facts s11))
[] [0%nat] in
mkSS (ss_pc s12) (ss_regs s12) (clean_all keep_main (ss_mem s12)) (ss_resv s12) (ss_facts s12).
(** [forget_rs]: the one place the two auxv layouts differ at main is the auxv region itself, 464 bytes
    with the two AT_RSEQ pairs or 432 without, both ending in AT_NULL (measured on [main_state rs two]
    for both values of rs: every register, fact and other region is the same). The start-up has read
    the whole vector by then and main does not read it again, so the region is cut to the 26 pairs
    every launch carries, [0, 416), and its chunks to those inside; both layouts then reach the same
    state. Sound because it only shrinks a region ([st_ok_submem]). *)
Definition auxv_shrinkable (r : region) : bool :=
match r_base r with Some 5%nat => true | _ => false end
&& Z.eqb (r_lo r) 0 && Z.leb 416 (r_hi r) && Z.leb (r_whi r) (r_wlo r).
Definition shrink_auxv (r : region) : region :=
if auxv_shrinkable r
then mkRegion (r_base r) 0 416 (r_wlo r) (r_whi r)
       (List.filter (fun c => Z.leb (c_off c + c_len c) 416) (r_chunks r))
else r.
Definition forget_rs (s : sstate) : sstate :=
mkSS (ss_pc s) (ss_regs s) (map shrink_auxv (ss_mem s)) (ss_resv s) (ss_facts s).
Lemma subregion_shrink_auxv : forall r, subregion (shrink_auxv r) r.
Proof.
intros r. unfold shrink_auxv. destruct (auxv_shrinkable r) eqn:E; [|apply subregion_refl].
unfold auxv_shrinkable in E. rewrite !andb_true_iff in E. destruct E as [[[_ Hlo] Hhi] Hw].
apply Z.eqb_eq in Hlo. apply Z.leb_le in Hhi. apply Z.leb_le in Hw.
unfold subregion; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; exact Hw|].
intros c Hc. apply filter_In in Hc. exact (proj1 Hc).
Qed.
Lemma submem_map_shrink : forall l, submem (map shrink_auxv l) l.
Proof.
induction l as [|r l IH]; cbn [map]; [constructor|].
apply submem_keep; [apply subregion_shrink_auxv | exact IH].
Qed.
Lemma region_wf_shrink_auxv : forall r, region_wf r = true -> region_wf (shrink_auxv r) = true.
Proof.
intros r H. unfold shrink_auxv. destruct (auxv_shrinkable r) eqn:E; [|exact H].
unfold auxv_shrinkable in E. rewrite !andb_true_iff in E. destruct E as [[[_ Hlo] _] Hw].
apply Z.eqb_eq in Hlo. apply Z.leb_le in Hw.
unfold region_wf in H |- *; cbn [r_lo r_hi r_wlo r_whi r_chunks].
apply andb_prop in H as [_ Hc].
apply andb_true_intro. split; [apply andb_true_intro; split|].
- apply Z.leb_le. lia.
- apply orb_true_iff. left. apply Z.leb_le. exact Hw.
- apply forallb_forall. intros c Hin. apply filter_In in Hin as [Hin Hle].
  pose proof (proj1 (forallb_forall _ _) Hc c Hin) as Hci.
  unfold chunk_inside in Hci |- *; cbn [r_lo r_hi].
  rewrite Hlo in Hci.
  apply andb_prop in Hci as [Hci H3]. apply andb_prop in Hci as [H1 _].
  apply andb_true_intro. split; [apply andb_true_intro; split|]; [exact H1 | exact Hle | exact H3].
Qed.
Lemma regions_wf_map_shrink : forall l, regions_wf l = true -> regions_wf (map shrink_auxv l) = true.
Proof.
induction l as [|r l IH]; cbn [map regions_wf]; intros H; [reflexivity|].
apply andb_prop in H as [H1 H2]. rewrite (region_wf_shrink_auxv r H1), (IH H2). reflexivity.
Qed.
Lemma st_ok_forget_rs : forall E s ms, st_ok src0segs E s ms -> st_ok src0segs E (forget_rs s) ms.
Proof.
intros E s ms HS. unfold forget_rs.
apply (st_ok_submem src0segs E s ms); [exact HS | apply submem_map_shrink |].
apply regions_wf_map_shrink. destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _). exact (proj1 HM).
Qed.
(** The state at main does not depend on the kernel's rseq flag once the start-up's reads of the
    auxv tail are forgotten ([forget_rs]); [main_state_rs] checks that for both values. *)
Definition main_state_u (rs two : bool) : sstate := forget_rs (main_state rs two).
Definition ss_main_t : sstate := Eval vm_compute in (main_state_u true true).
Definition ss_main_f : sstate := Eval vm_compute in (main_state_u true false).
Definition ss_main (two : bool) : sstate := if two then ss_main_t else ss_main_f.
Section e.
Local Set Default Proof Using "All".
Variable inp : ProcInput.
Variable mbase sp brk : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
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
Lemma length_envp_words : length (envp_words inp rnd) = (length envp + 1)%nat.
Proof. unfold envp_words. rewrite length_app, length_string_addrs_fst. reflexivity. Qed.
Lemma length_envp_block : length (envp_block inp rnd) = (8 * length envp + 8)%nat.
Proof. unfold envp_block. rewrite length_flat_map_le8, length_envp_words. lia. Qed.
Lemma runs_main_init : forall (two : bool),
(if two then (2 <= length argv)%nat else True) ->
runs_at (bv_unsigned sp) (ms_mem (init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp))
(runs_main two sp inp rnd).
Proof.
intros two Htwo. rewrite init_mkst. cbn [ms_mem mkst].
pose proof (layout_facts src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) as L. pose proof (auxv_bytes_range (kb_rseq (in_kernel inp))) as AR.
pose proof (top_le src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) as TL. pose proof (str_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) as SB.
unfold SP_LO, SP_HI in *.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
match goal with |- runs_at _ ?M0 _ =>
assert (AUX : Forall (fun ab => bv_unsigned sp <= fst ab /\ fst ab + Z.of_nat (length (snd ab)) <= 2 ^ 64
  /\ YP03.bytes_at M0 (fst ab) (snd ab)) (runs_auxv sp inp)) end.
{ pose proof (auxv_bytes_count (kb_rseq (in_kernel inp))) as AC.
  pose proof (length_auxv_types_count (kb_rseq (in_kernel inp))) as LC.
  pose proof (YO0d.auxv_types_len_ge (kb_rseq (in_kernel inp))) as LG.
  unfold runs_auxv. cbv zeta. apply Forall_app. split.
  - apply Forall_forall. intros [a bs] Hin. apply in_map_iff in Hin as (k & Hk & Hin). injection Hk as <- <-.
    apply in_seq in Hin. cbn [fst snd].
    assert (H2k : (2 * k < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat) by lia.
    pose proof (m0_auxv_word src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau (2 * k) H2k) as W. unfold auxv_wordlist in W.
    rewrite nth_auxv_words_key in W
      by (change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)); lia).
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)) in W.
    unfold word_le8 at 1. cbn [length].
    split; [lia|]. split; [lia|].
    replace (z_auxv (bv_unsigned sp) argv envp + 16 * Z.of_nat k)
      with (z_auxv (bv_unsigned sp) argv envp + 8 * Z.of_nat (2 * k)) by lia. exact W.
  - apply Forall_cons; [|constructor]. cbn [fst snd].
    assert (H49 : (2 * YO0d.AUXV_RAND_K + 1 < 2 * auxv_count (kb_rseq (in_kernel inp)))%nat)
      by (unfold YO0d.AUXV_RAND_K; lia).
    pose proof (m0_auxv_word src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau _ H49) as W. unfold auxv_wordlist in W.
    rewrite nth_auxv_words_rand in W.
    change (la_rseq (launch_auxv inp sp mbase)) with (kb_rseq (in_kernel inp)) in W.
    rewrite (at_random_ptr_val src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) in W.
    unfold word_le8 at 1. cbn [length]. unfold YO0d.AUXV_RAND_K in *.
    split; [lia|]. split; [lia|].
    replace (z_auxv (bv_unsigned sp) argv envp + 16 * Z.of_nat 24 + 8)
      with (z_auxv (bv_unsigned sp) argv envp + 8 * Z.of_nat (2 * 24 + 1)) by lia. exact W. }
unfold runs_main. cbv zeta. cbn [app]. apply Forall_cons; [|apply Forall_cons; [| apply Forall_app; split]].
- cbn [fst snd]. rewrite length_envp_block.
split; [lia|]. split; [unfold z_auxv in *; lia|]. unfold envp_block, envp_words. rewrite flat_map_app. apply bytes_at_app.
+ exact (m0_envp_ptrs src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
+ rewrite length_flat_map_le8, length_string_addrs_fst. cbn [flat_map]. rewrite app_nil_r.
replace (z_envp (bv_unsigned sp) argv + Z.of_nat (8 * length envp))
with (z_auxv (bv_unsigned sp) argv envp - 8) by (unfold z_auxv; lia).
exact (m0_envp_null src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
- cbn [fst snd]. pose proof (z_argv_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 0 ltac:(lia)) as B.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. apply (m0_argv_str src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 0). lia.
- destruct two; [|constructor]. apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (z_argv_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia)) as B.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. apply (m0_argv_str src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1). lia.
- apply Forall_cons; [|exact AUX]. cbn [fst snd].
pose proof (stack_tail_end src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) as B.
split; [lia|]. split; [lia|]. exact (m0_tail src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
End e.
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
Lemma runs_main_auxv : forall spv m two sp inp rnd,
runs_at spv m (runs_main two sp inp rnd) -> runs_at spv m (runs_auxv sp inp).
Proof.
intros spv m two sp inp rnd H. unfold runs_at, runs_main in *. cbv zeta in H.
apply Forall_inv_tail, Forall_inv_tail in H.
apply Forall_app in H as [_ H]. apply Forall_app in H as [_ H]. exact H.
Qed.
Lemma word_mem_of_le8 : forall m a (w : word),
YP03.bytes_at m a (word_le8 w) -> YO0d.word_mem src0segs m a (bv_unsigned w).
Proof.
intros m a w H k Hk.
rewrite (YP08.bytes_at_mbyte src0segs m a (word_le8 w) k H) by (unfold word_le8; cbn [length]; lia).
rewrite word_le8_nth by exact Hk. f_equal. symmetry.
unfold YO0f.le_byte, byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned.
pose proof (u64_range w).
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small (bv_unsigned w)) by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma auxv_types_range : forall rs k, 0 <= nth k (YO0d.auxv_types rs) 0 < 2 ^ 64.
Proof. intros [|] k; (do 30 (destruct k as [|k]; [cbn; lia|])); destruct k; cbn; lia. Qed.
(** The auxv words of [runs_auxv], as mallocng's [auxv_pre] reads them. *)
Lemma runs_auxv_words : forall spv m sp inp,
runs_at spv m (runs_auxv sp inp) ->
(forall k, (k < length (YO0d.auxv_types (kb_rseq (in_kernel inp))))%nat ->
  YO0d.word_mem src0segs m (z_auxv (bv_unsigned sp) (in_argv inp) (in_envp inp) + 16 * Z.of_nat k)
    (nth k (YO0d.auxv_types (kb_rseq (in_kernel inp))) 0))
/\ YO0d.word_mem src0segs m (z_auxv (bv_unsigned sp) (in_argv inp) (in_envp inp) + 16 * Z.of_nat YO0d.AUXV_RAND_K + 8)
     (bv_unsigned (Z_to_bv 64 (z_rand (bv_unsigned sp) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp)))).
Proof.
intros spv m sp inp H. unfold runs_at, runs_auxv in H. cbv zeta in H.
apply Forall_app in H as [H1 H2]. split.
- intros k Hk. rewrite Forall_forall in H1.
  assert (Hin : In k (seq 0 (length (YO0d.auxv_types (kb_rseq (in_kernel inp)))))) by (apply in_seq; lia).
  destruct (H1 _ (in_map _ _ k Hin)) as (_ & _ & Hb). cbn [fst snd] in Hb.
  pose proof (word_mem_of_le8 _ _ _ Hb) as W.
  rewrite Z_to_bv_unsigned in W. unfold bv_wrap in W. change (bv_modulus 64) with (2 ^ 64) in W.
  rewrite Z.mod_small in W by apply auxv_types_range. exact W.
- apply Forall_inv in H2. destruct H2 as (_ & _ & Hb). cbn [fst snd] in Hb.
  exact (word_mem_of_le8 _ _ _ Hb).
Qed.
Lemma ss_start_rs : forall r b two, r = b -> ss_start r two = ss_start b two.
Proof. intros r b two ->. reflexivity. Qed.
Section f.
Local Set Default Proof Using "All".
Variable inp : ProcInput.
Variable mbase sp brk : word.
Variable rnd : EntryDraw.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp.
Local Notation argv := (in_argv inp) (only parsing).
Local Notation envp := (in_envp inp) (only parsing).
Local Notation efn := (in_execfn inp) (only parsing).
Local Notation krs := (kb_rseq (in_kernel inp)) (only parsing).
Local Notation top := (ed_top rnd) (only parsing).
Local Notation zsp := (bv_unsigned sp) (only parsing).
Local Notation ztop := (bv_unsigned (ed_top rnd)) (only parsing).
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
Proof.
exact (YP08.layout_facts src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma SB : zsp <= z_strs ztop argv envp efn
/\ z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp)
+ Z.of_nat (length efn) + 1 + 8 = ztop.
Proof.
exact (YP08.str_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma ZAB : forall k, (k < length argv)%nat ->
z_strs ztop argv envp efn <= z_argv ztop argv envp efn k
/\ z_argv ztop argv envp efn k + Z.of_nat (length (nth k argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv).
Proof.
exact (YP08.z_argv_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma ZEB : forall k, (k < length envp)%nat ->
z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) <= z_envs ztop argv envp efn k
/\ z_envs ztop argv envp efn k + Z.of_nat (length (nth k envp [])) + 1 <= z_execfn ztop argv envp efn.
Proof.
exact (YP08.z_envs_bounds src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma STE : z_strs ztop argv envp efn + Z.of_nat (length (stack_tail argv envp efn)) = ztop.
Proof.
exact (YP08.stack_tail_end src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma ANN : forall k, (k < length argv)%nat -> ~ In NUL (nth k argv []).
Proof.
exact (YP08.argv_no_nul src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma UEP : forall k, (k < length envp)%nat ->
nth k (fst (string_addrs (cat_env_base top argv envp efn) envp)) (Z_to_bv 64 0)
= Z_to_bv 64 (z_envs ztop argv envp efn k).
Proof.
exact (YP08.u_envp_ptr src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau).
Qed.
Lemma alias_memset_ok : forall t,
sv_denot (E_st sp inp mbase rnd t) (fst alias_memset) = sv_denot (E_st sp inp mbase rnd t) (snd alias_memset).
Proof.
intros t. cbn [fst snd alias_memset sv_denot].
rewrite zalu32_sound, zalu64_sound. f_equal. apply negw_and3_zero.
unfold E_st. rewrite (ew0 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _). exact (proj2 (proj2 Hsp)).
Qed.
Lemma alias_envp_ok : forall t,
sv_denot (E_st sp inp mbase rnd t) (fst alias_envp) = sv_denot (E_st sp inp mbase rnd t) (snd alias_envp).
Proof.
intros t. cbn [fst snd alias_envp sv_denot]. unfold E_st.
rewrite !zalu64_sound. rewrite (ew0 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _), (ew3 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _), (ew4 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _).
pose proof (layout_facts src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau) as L. pose proof (auxv_bytes_range (kb_rseq (in_kernel inp))) as ARb. pose proof (proj1 Hva) as HA.
unfold SP_LO, SP_HI in L.
apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !Z.add_0_r. rewrite !(Z.mod_small _ (2^64)) by lia. lia.
Qed.
Lemma ewm1 : forall t, bv_unsigned (ew (E_main sp inp t rnd) 1) = z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0.
Proof.
intros t. pose proof LF as L.
unfold E_main. rewrite (ew1 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _). lia.
Qed.
Lemma ewm2 : forall t, bv_unsigned (ew (E_main sp inp t rnd) 2)
= z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof.
intros t. pose proof LF as L.
unfold E_main. rewrite (ew2 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _). lia.
Qed.
Lemma ewm4 : forall t, bv_unsigned (ew (E_main sp inp t rnd) 4) = z_envp (bv_unsigned sp) argv.
Proof. intros t. exact (ew4 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _). Qed.
Lemma ewm5 : forall t, bv_unsigned (ew (E_main sp inp t rnd) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. intros t. exact (ew5 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _). Qed.
Lemma ewm6 : forall t, bv_unsigned (ew (E_main sp inp t rnd) 6) = z_rand zsp krs argv envp.
Proof. intros t. exact (YP08.ew6 src0segs Ubsan_phdrs inp mbase Ubsan_init_pc sp brk rnd Hsp Hva Hve Hvl Hlau 1 ltac:(lia) _ _). Qed.
Lemma ewm7 : forall t, bv_unsigned (ew (E_main sp inp t rnd) 7)
= z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof.
intros t. cbn [ew E_main E0 xw_main].
pose proof LF as L. pose proof SB as S. pose proof (proj1 Hva) as HA.
pose proof (ZAB 0 ltac:(lia)) as B. pose proof (progname_off_le (nth 0 argv [])).
unfold SP_LO, SP_HI in *. apply u_Z2bv; lia.
Qed.
Lemma ewm8 : forall t, ew (E_main sp inp t rnd) 8 = t.
Proof. intros t. reflexivity. Qed.
Lemma ewm9 : forall t, ew (E_main sp inp t rnd) CANARY_ATOM = canary_word (rand_bytes rnd).
Proof. intros t. reflexivity. Qed.
Lemma edm7 : forall t, ed (E_main sp inp t rnd) RAND_DATOM = rand_bytes rnd.
Proof. intros t. reflexivity. Qed.
Lemma ews1 : forall t, bv_unsigned (ew (E_st sp inp mbase rnd t) 1) = z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0.
Proof. exact ewm1. Qed.
Lemma ews2 : forall t, bv_unsigned (ew (E_st sp inp mbase rnd t) 2)
= z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof. exact ewm2. Qed.
Lemma ews4 : forall t, bv_unsigned (ew (E_st sp inp mbase rnd t) 4) = z_envp (bv_unsigned sp) argv.
Proof. exact ewm4. Qed.
Lemma ews5 : forall t, bv_unsigned (ew (E_st sp inp mbase rnd t) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. exact ewm5. Qed.
Lemma ews7 : forall t, bv_unsigned (ew (E_st sp inp mbase rnd t) 7)
= z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof. exact ewm7. Qed.
Lemma ews8 : forall t, ew (E_st sp inp mbase rnd t) 8 = t.
Proof. intros t. reflexivity. Qed.
Lemma envp_block_reads : forall m t,
YP03.bytes_at m (z_envp (bv_unsigned sp) argv) (envp_block inp rnd) ->
(forall i, (i < length envp)%nat -> exists bs,
rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp inp mbase rnd t) 4) + 8 * Z.of_nat i)) 8 = Some bs
/\ bytes_le_to_Z bs <> 0)
/\ (exists bs, rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp inp mbase rnd t) 4)
+ 8 * Z.of_nat (length envp))) 8 = Some bs
/\ bytes_le_to_Z bs = 0)
/\ bv_unsigned (ew (E_st sp inp mbase rnd t) 4) + 8 * Z.of_nat (length envp) + 8 < 2^64.
Proof.
intros m t HB. rewrite ews4.
pose proof LF as L. pose proof SB as S. pose proof (proj1 Hve) as HE. pose proof (proj1 Hva) as HA.
unfold SP_LO, SP_HI in *.
assert (HW : forall k, (k < length envp + 1)%nat ->
rdn src0segs m (Z_to_bv 64 (z_envp (bv_unsigned sp) argv + 8 * Z.of_nat k)) 8
= Some (word_le8 (nth k (envp_words inp rnd) (Z_to_bv 64 0)))).
{ intros k Hk. apply (bytes_at_rdn src0segs m _ (word_le8 _)).
apply (bytes_at_le8_nth m _ (envp_words inp rnd) k HB). rewrite (length_envp_words inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau). exact Hk. }
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
YP03.bytes_at m (z_argv (bv_unsigned (ed_top rnd)) argv envp (in_execfn inp) 0) (nth 0 argv [] ++ [NUL]) ->
forall j, (j <= length (nth 0 argv []))%nat ->
rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp inp mbase rnd t) 1) + Z.of_nat j)) 1
= Some [nth j (nth 0 argv [] ++ [NUL]) NUL].
Proof.
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
st_ok src0segs (E_main sp inp tid rnd) (ss_main two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp inp rnd) ->
realizes src0segs (mkCfg ms (with_tid tid model)) T) ->
realizes src0segs (mkCfg (init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp) model) T.
Proof.
intros two model T Htwo Hh Hlz Htid K.
pose proof LF as L. pose proof SB as S. unfold SP_LO, SP_HI in *.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
pose proof (src0_init_st_ok inp mbase sp brk rnd (xw_main inp rnd (Z_to_bv 64 0)) (xd_st inp sp mbase rnd) two
Hsp Hva Hve Hvl Hlau eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Htwo) as HS.
change (st_ok src0segs (E_st sp inp mbase rnd (Z_to_bv 64 0)) (src0_ss0 (kb_rseq (in_kernel inp)) two)
(init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp)) in HS.
apply (st_ok_add_alias src0segs _ _ _ (fst alias_memset) (snd alias_memset)) in HS; [|apply alias_memset_ok].
apply (st_ok_add_alias src0segs _ _ _ (fst alias_envp) (snd alias_envp)) in HS; [|apply alias_envp_ok].
change (st_ok src0segs (E_st sp inp mbase rnd (Z_to_bv 64 0)) (ss_start (kb_rseq (in_kernel inp)) two)
(init_machine_state src0segs Ubsan_init_pc Ubsan_phdrs sp mbase rnd inp)) in HS.
pose proof (runs_main_init inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau two Htwo) as HR.
(* The four start-up runs: the kernel's rseq flag only selects the auxv's length in the symbolic state;
   the environment E keeps it symbolic. *)
destruct (Sumbool.sumbool_of_bool (kb_rseq (in_kernel inp))) as [Ers|Ers];
rewrite (ss_start_rs _ _ two Ers) in HS; destruct two.
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
all: sym_run_to_with src0tbl_ok HS 0x13dd4; clear regs1.
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
let rs' := eval vm_compute in (opt_mem (store_region (ss_mem ss) None 0x4e900 8 (CVal 8 (SOff 7 0)))) in
assert (HCB : forall i, 0 <= i < Z.of_nat (length bs) ->
cbyte src0segs E (base_val E None + 0x4e900) (CVal 8 (SOff 7 0)) i = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite length_N_to_le_bytes in Hi;
change (CVal 8 (SOff 7 0)) with (CVal (N.of_nat 8) (SOff 7 0));
rewrite (st_bytes_cbyte src0segs E) by lia;
unfold word_to_le_bytes; rewrite Z_to_le_bytes_st; do 2 f_equal;
cbn [sv_denot]; rewrite Z.add_0_r, ews7, ews1; reflexivity
| ];
pose proof (proj2 (swrite_sound src0segs E m (ss_mem ss) None 0x4e900 (CVal 8 (SOff 7 0)) bs rs'
(st_ok_mem_ok src0segs E ss _ HS)
ltac:(rewrite length_N_to_le_bytes; vm_compute; reflexivity)
ltac:(rewrite length_N_to_le_bytes; lia)
ltac:(rewrite length_N_to_le_bytes; reflexivity) HCB)) as HM;
change (mem_ok src0segs E m' rs') in HM;
unshelve epose proof (st_ok_set_regs_mem src0segs 9%nat E E ss _ regs2 _ 0x13df8 m m' rs' upd_progname
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
assert (HA8 : env_agree 8%nat E (E_st sp inp mbase rnd tid))
by (split; [intros n Hn; do 8 (destruct n as [|n]; [reflexivity|]); lia | reflexivity]);
pose proof (st_ok_resume_mem src0segs 8%nat E (E_st sp inp mbase rnd tid) ss regs mem (SOff 8 0) tid (ss_mem ss)
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
all: sym_run_to_with src0tbl_ok HS 0x1460c.
all: sym_add_chunk_sem HS (@None nat) guard_data_chunk;
[ intros HCS; apply (guard_data_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM);
[ cbn; lia
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS) ]
| ].
all: sym_run_to_with src0tbl_ok HS 0x14610.
all: sym_add_chunk_sem HS (@None nat) canary_chunk;
[ intros HCS; apply (canary_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM CANARY_ATOM);
[ cbn; lia
| reflexivity
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS)
| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HCS))) ]
| ].
all: idtac "PHASE H".
all: sym_run_to_with src0tbl_ok HS 0x12920.
all: idtac "PHASE I".
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_head src0segs E ss ms keep_zero) in HS;
apply (st_ok_prune src0segs E _ ms [] [0%nat]) in HS end.
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_all src0segs E ss ms keep_main) in HS;
apply (st_ok_agree_pd src0segs (fun _ => true) (not_in FORGET) _ (E_main sp inp tid rnd)) in HS;
[ | apply E_st_main_agree | vm_compute; reflexivity ] end.
all: sym_norm HS.
all: apply st_ok_forget_rs in HS; sym_norm HS.
- change (st_ok src0segs (E_main sp inp tid rnd) (ss_main true) ms) in HS. exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp inp tid rnd) (ss_main false) ms) in HS. exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp inp tid rnd) (ss_main true) ms) in HS. exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp inp tid rnd) (ss_main false) ms) in HS. exact (K ms tid Htid8 HS HR).
Qed.
End f.
Theorem src0_start : forall (two : bool) sp brk mbase rnd lim inp T,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
(if two then (2 <= length (in_argv inp))%nat else True) ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_main sp inp tid rnd) (ss_main two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp inp rnd) ->
realizes src0segs (mkCfg ms (with_tid tid (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
  (init_model (segments_reserved src0segs) brk mbase sp lim inp)))) T) ->
realizes src0segs (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk mbase rnd lim inp) T.
Proof.
intros two sp brk mbase rnd lim inp T Hsp Hva Hve Hvl Hlau Htwo K.
unfold init_config.
apply (src0_start_gen inp mbase sp brk rnd Hsp Hva Hve Hvl Hlau two);
[exact Htwo | reflexivity | reflexivity | reflexivity | exact K].
Qed.
