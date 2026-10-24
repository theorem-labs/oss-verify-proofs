(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH01 YN3h.
From OssFuzzTheorems.zlib.checksum_fuzzer.images Require Import Plain.
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
Definition xw_main (sp : word) (argv envp : list (list byte)) (tid : word) (rnd : EntryDraw) (n : nat) : word :=
match n with
| 7%nat => Z_to_bv 64 (z_argv (bv_unsigned sp) argv envp 0 + Z.of_nat (progname_off (nth 0 argv [])))
| 8%nat => tid
| 9%nat => canary_word (rand_bytes rnd)
| _ => Z_to_bv 64 0
end.
Definition xd_main (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d RAND_DATOM then rand_bytes rnd else [].
Definition xd_st (uid hw : word) (rnd : EntryDraw) (d : nat) : list byte :=
if Nat.eqb d UID_DATOM then uid_bytes uid
else if Nat.eqb d HWCAP_DATOM then hwcap_bytes hw
else if Nat.eqb d RAND_DATOM then rand_bytes rnd else [].
Definition E_main (sp : word) (argv envp : list (list byte)) (tid : word) (rnd : EntryDraw) : env :=
E0 sp argv envp (xw_main sp argv envp tid rnd) (xd_main rnd).
Definition E_st (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (tid : word) : env :=
E0 sp argv envp (xw_main sp argv envp tid rnd) (xd_st uid hw rnd).
Lemma E_st_main_agree : forall sp argv envp uid hw rnd tid,
env_agree_pd (fun _ => true) (not_in [UID_DATOM; HWCAP_DATOM]) (E_st sp argv envp uid hw rnd tid) (E_main sp argv envp tid rnd).
Proof.
intros. split; [intros; reflexivity|].
intros d Hd. unfold not_in in Hd. cbn [existsb] in Hd. rewrite orb_false_r in Hd.
apply negb_true_iff in Hd. apply orb_false_iff in Hd as [Hd1 Hd2].
unfold E_st, E_main, E0, xd_st, xd_main; cbn [ed]. rewrite Hd1, Hd2.
destruct d as [|[|d]]; reflexivity.
Qed.
Definition alias_memset : sv * sv :=
(SAlu ALU_AND (SAluw ALU_SUB (SLit 0) (SOff 0 (-368))) (SLit 3), SLit 0).
Definition alias_envp : sv * sv :=
(SAlu ALU_ADD (SOff 0 16) (SAlu ALU_SLL (SOff 3 0) (SLit 3)), SOff 4 0).
Definition ss_start (two : bool) : sstate :=
add_alias (add_alias (src0_ss0 two)
(fst alias_memset) (snd alias_memset))
(fst alias_envp) (snd alias_envp).
Definition envp_words (sp : word) (argv envp : list (list byte)) : list word :=
fst (string_addrs (cat_env_base sp argv envp) envp) ++ [Z_to_bv 64 0].
Definition envp_block (sp : word) (argv envp : list (list byte)) : list byte :=
flat_map word_le8 (envp_words sp argv envp).
Definition runs_main (two : bool) (sp : word) (argv envp : list (list byte)) (rnd : EntryDraw) : list (Z * list byte) :=
(z_envp (bv_unsigned sp) argv, envp_block sp argv envp)
:: (z_argv (bv_unsigned sp) argv envp 0, nth 0 argv [] ++ [NUL])
:: (if two then [(z_argv (bv_unsigned sp) argv envp 1, nth 1 argv [] ++ [NUL])] else [])
++ [(z_strs (bv_unsigned sp) argv envp, stack_tail argv envp rnd)].
Definition opt_mem (o : option smem) : smem := match o with Some rs => rs | None => [] end.
Definition run_ (ss : sstate) : sstate := fst (sym_runN src0segs src0tbl FUEL ss).
Definition runto_ (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL pc ss).
Definition keep_zero (c : chunk) : bool :=
match c_val c with CZero n => 4096 <=? n | _ => false end.
Definition upd_envp : list (reg * sv) := [(10%bv : reg, SLit 0); (9%bv : reg, SOff 5 0)].
Definition upd_progname : list (reg * sv) := [(11%bv : reg, SOff 2 0); (12%bv : reg, SLit 47); (13%bv : reg, SLit 0)].
Definition tid_fact : afact := mkAF 1 4194303 0.
Definition GUARD : Z := 0x4fd20.
Definition guard_data_chunk : chunk := mkChunk GUARD (CData RAND_DATOM 0 8).
Definition canary_chunk : chunk := mkChunk GUARD (CVal 8 (SOff CANARY_ATOM 0)).
Definition is_canary_val (cv : cval) : bool :=
match cv with CVal 8 (SOff n 0) => Nat.eqb n CANARY_ATOM | _ => false end.
Definition keep_main (c : chunk) : bool :=
cval_atoms_pd (fun _ => true) (not_in [UID_DATOM; HWCAP_DATOM]) (c_val c)
&& negb ((GUARD <=? c_off c) && (c_off c <? GUARD + 8) && negb (is_canary_val (c_val c))).
Definition main_state (two : bool) : sstate :=
let s1 := run_ (ss_start two) in
let s2 := set_regs_pc s1 upd_envp 0x152e8 in
let s3 := runto_ 0x15388 s2 in
let s4 := add_atom (mkSS 0x153ac (sr_sets (ss_regs s3) upd_progname)
(opt_mem (store_region (ss_mem s3) None 0x4fd30 8 (CVal 8 (SOff 7 0))))
None (ss_facts s3)) 7 (ptr_fact 0) in
let s5 := run_ s4 in
let s6 := resume s5 (SOff 8 0) (ss_mem s5)
(mkFacts ((8%nat, tid_fact) :: f_atoms (ss_facts s5))
(f_conds (ss_facts s5)) (f_alias (ss_facts s5))) in
let s7 := runto_ 0x15cd4 s6 in
let s8 := add_chunk_ None guard_data_chunk s7 in
let s9 := runto_ 0x15cd8 s8 in
let s10 := add_chunk_ None canary_chunk s9 in
let s11 := runto_ 0x13d50 s10 in
let s12 := prune (mkSS (ss_pc s11) (ss_regs s11) (clean_head keep_zero (ss_mem s11)) (ss_resv s11) (ss_facts s11))
[] [0%nat] in
mkSS (ss_pc s12) (ss_regs s12) (clean_all keep_main (ss_mem s12)) (ss_resv s12) (ss_facts s12).
Definition ss_main_t : sstate := Eval vm_compute in (main_state true).
Definition ss_main_f : sstate := Eval vm_compute in (main_state false).
Definition ss_main (two : bool) : sstate := if two then ss_main_t else ss_main_f.
Section e.
Variable sp : word.
Variable argv envp : list (list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
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
Lemma length_envp_words : length (envp_words sp argv envp) = (length envp + 1)%nat.
Proof. unfold envp_words. rewrite length_app, length_string_addrs_fst. reflexivity. Qed.
Lemma length_envp_block : length (envp_block sp argv envp) = (8 * length envp + 8)%nat.
Proof. unfold envp_block. rewrite length_flat_map_le8, length_envp_words. lia. Qed.
Lemma runs_main_init : forall (two : bool) pc uid hw rnd,
(if two then (2 <= length argv)%nat else True) ->
runs_at (bv_unsigned sp) (ms_mem (init_machine_state src0segs pc Plain_phdrs sp rnd argv envp uid hw))
(runs_main two sp argv envp rnd).
Proof.
intros two pc uid hw rnd Htwo. rewrite init_mkst. cbn [ms_mem mkst].
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
unfold runs_main. cbn [app]. apply Forall_cons; [|apply Forall_cons; [| apply Forall_app; split]].
- cbn [fst snd]. rewrite length_envp_block.
split; [lia|]. split; [lia|]. unfold envp_block, envp_words. rewrite flat_map_app. apply bytes_at_app.
+ apply (m0_envp_ptrs Plain_phdrs sp argv envp Hsp Hva Hve).
+ rewrite length_flat_map_le8, length_string_addrs_fst. cbn [flat_map]. rewrite app_nil_r.
replace (z_envp (bv_unsigned sp) argv + Z.of_nat (8 * length envp))
with (z_auxv (bv_unsigned sp) argv envp - 8) by lia.
apply (m0_envp_null Plain_phdrs sp argv envp Hsp Hva Hve).
- cbn [fst snd]. pose proof (z_argv_bounds sp argv envp 0 ltac:(lia)) as B.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. apply (m0_argv_str Plain_phdrs sp argv envp Hsp Hva Hve uid hw rnd 0). lia.
- destruct two; [|constructor]. apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (z_argv_bounds sp argv envp 1 ltac:(lia)) as B.
rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. apply (m0_argv_str Plain_phdrs sp argv envp Hsp Hva Hve uid hw rnd 1). lia.
- apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (stack_tail_end sp argv envp rnd) as B.
pose proof (z_rand_end sp argv envp Hsp Hva Hve) as B'.
split; [lia|]. split; [lia|]. apply (m0_tail Plain_phdrs sp argv envp Hsp Hva Hve).
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
Section f.
Variable sp : word.
Variable argv envp : list (list byte).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfits : entry_stack_fits sp argv envp.
Variable uid hw : word.
Variable rnd : EntryDraw.
Lemma alias_memset_ok : forall t,
sv_denot (E_st sp argv envp uid hw rnd t) (fst alias_memset) = sv_denot (E_st sp argv envp uid hw rnd t) (snd alias_memset).
Proof.
intros t. cbn [fst snd alias_memset sv_denot].
rewrite zalu32_sound, zalu64_sound. f_equal. apply negw_and3_zero.
unfold E_st. rewrite (ew0 sp argv envp). exact (proj2 (proj2 Hsp)).
Qed.
Lemma alias_envp_ok : forall t,
sv_denot (E_st sp argv envp uid hw rnd t) (fst alias_envp) = sv_denot (E_st sp argv envp uid hw rnd t) (snd alias_envp).
Proof.
intros t. cbn [fst snd alias_envp sv_denot]. unfold E_st.
rewrite !zalu64_sound. rewrite (ew0 sp argv envp), (ew3 sp argv envp Hva), (ew4 sp argv envp Hsp Hva Hve).
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L. pose proof (proj1 Hva) as HA.
unfold SP_LO, SP_HI in L.
apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
change (Z.land (3 mod 2 ^ 64) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
rewrite !Z.add_0_r. rewrite !(Z.mod_small _ (2^64)) by lia. lia.
Qed.
Lemma ewm1 : forall t, bv_unsigned (ew (E_main sp argv envp t rnd) 1) = z_argv (bv_unsigned sp) argv envp 0.
Proof.
intros t. pose proof (layout_facts sp argv envp Hsp Hva Hve) as L.
unfold E_main. rewrite (ew1 sp argv envp Hsp Hva Hve). lia.
Qed.
Lemma ewm2 : forall t, bv_unsigned (ew (E_main sp argv envp t rnd) 2)
= z_argv (bv_unsigned sp) argv envp 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof.
intros t. pose proof (layout_facts sp argv envp Hsp Hva Hve) as L.
unfold E_main. rewrite (ew2 sp argv envp Hsp Hva Hve). lia.
Qed.
Lemma ewm4 : forall t, bv_unsigned (ew (E_main sp argv envp t rnd) 4) = z_envp (bv_unsigned sp) argv.
Proof. intros t. exact (ew4 sp argv envp Hsp Hva Hve _ _). Qed.
Lemma ewm5 : forall t, bv_unsigned (ew (E_main sp argv envp t rnd) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. intros t. exact (ew5 sp argv envp Hsp Hva Hve _ _). Qed.
Lemma ewm7 : forall t, bv_unsigned (ew (E_main sp argv envp t rnd) 7)
= z_argv (bv_unsigned sp) argv envp 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof.
intros t. cbn [ew E_main E0 xw_main].
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L. pose proof (proj1 Hva) as HA.
pose proof (z_argv_bounds sp argv envp 0 ltac:(lia)) as B. pose proof (progname_off_le (nth 0 argv [])).
unfold SP_LO, SP_HI in L. apply u_Z2bv; lia.
Qed.
Lemma ewm8 : forall t, ew (E_main sp argv envp t rnd) 8 = t.
Proof. intros t. reflexivity. Qed.
Lemma ewm9 : forall t, ew (E_main sp argv envp t rnd) CANARY_ATOM = canary_word (rand_bytes rnd).
Proof. intros t. reflexivity. Qed.
Lemma edm7 : forall t, ed (E_main sp argv envp t rnd) RAND_DATOM = rand_bytes rnd.
Proof. intros t. reflexivity. Qed.
Lemma ews1 : forall t, bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 1) = z_argv (bv_unsigned sp) argv envp 0.
Proof. exact ewm1. Qed.
Lemma ews2 : forall t, bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 2)
= z_argv (bv_unsigned sp) argv envp 0 + Z.of_nat (length (nth 0 argv [])) + 1.
Proof. exact ewm2. Qed.
Lemma ews4 : forall t, bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 4) = z_envp (bv_unsigned sp) argv.
Proof. exact ewm4. Qed.
Lemma ews5 : forall t, bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 5) = z_auxv (bv_unsigned sp) argv envp.
Proof. exact ewm5. Qed.
Lemma ews7 : forall t, bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 7)
= z_argv (bv_unsigned sp) argv envp 0 + Z.of_nat (progname_off (nth 0 argv [])).
Proof. exact ewm7. Qed.
Lemma ews8 : forall t, ew (E_st sp argv envp uid hw rnd t) 8 = t.
Proof. intros t. reflexivity. Qed.
Lemma envp_block_reads : forall m t,
YP03.bytes_at m (z_envp (bv_unsigned sp) argv) (envp_block sp argv envp) ->
(forall i, (i < length envp)%nat -> exists bs,
rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 4) + 8 * Z.of_nat i)) 8 = Some bs
/\ bytes_le_to_Z bs <> 0)
/\ (exists bs, rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 4)
+ 8 * Z.of_nat (length envp))) 8 = Some bs
/\ bytes_le_to_Z bs = 0)
/\ bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 4) + 8 * Z.of_nat (length envp) + 8 < 2^64.
Proof.
intros m t HB. rewrite ews4.
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L. pose proof (proj1 Hve) as HE.
unfold SP_LO, SP_HI in L.
assert (HW : forall k, (k < length envp + 1)%nat ->
rdn src0segs m (Z_to_bv 64 (z_envp (bv_unsigned sp) argv + 8 * Z.of_nat k)) 8
= Some (word_le8 (nth k (envp_words sp argv envp) (Z_to_bv 64 0)))).
{ intros k Hk. apply (bytes_at_rdn src0segs m _ (word_le8 _)).
apply (bytes_at_le8_nth m _ (envp_words sp argv envp) k HB). rewrite length_envp_words. exact Hk. }
split; [|split; [|lia]].
- intros i Hi. eexists. split; [apply HW; lia|].
unfold envp_words. rewrite app_nth1 by (rewrite length_string_addrs_fst; exact Hi).
rewrite (u_envp_ptr sp argv envp Hsp Hva Hve i Hi).
rewrite n_to_le_8_spec, bytes_le_to_Z_8.
pose proof (z_envs_bounds sp argv envp i Hi). rewrite u_Z2bv by lia. lia.
- eexists. split; [apply HW; lia|].
unfold envp_words. rewrite app_nth2 by (rewrite length_string_addrs_fst; lia).
rewrite length_string_addrs_fst, Nat.sub_diag. reflexivity.
Qed.
Lemma argv0_reads : forall m t,
YP03.bytes_at m (z_argv (bv_unsigned sp) argv envp 0) (nth 0 argv [] ++ [NUL]) ->
forall j, (j <= length (nth 0 argv []))%nat ->
rdn src0segs m (Z_to_bv 64 (bv_unsigned (ew (E_st sp argv envp uid hw rnd t) 1) + Z.of_nat j)) 1
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
st_ok src0segs (E_main sp argv envp tid rnd) (ss_main two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp argv envp rnd) ->
realizes src0segs (mkCfg ms (with_tid tid model)) T) ->
realizes src0segs (mkCfg (init_machine_state src0segs Plain_init_pc Plain_phdrs sp rnd argv envp uid hw) model) T.
Proof.
intros two model T Htwo Hh Hlz Htid K.
pose proof (layout_facts sp argv envp Hsp Hva Hve) as L. unfold SP_LO, SP_HI in L.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HE.
pose proof (src0_init_st_ok sp argv envp uid hw rnd (xw_main sp argv envp (Z_to_bv 64 0) rnd) (xd_st uid hw rnd) two
Hsp Hva Hve Hfits eq_refl eq_refl eq_refl Htwo) as HS.
change (st_ok src0segs (E_st sp argv envp uid hw rnd (Z_to_bv 64 0)) (src0_ss0 two)
(init_machine_state src0segs Plain_init_pc Plain_phdrs sp rnd argv envp uid hw)) in HS.
apply (st_ok_add_alias src0segs _ _ _ (fst alias_memset) (snd alias_memset)) in HS; [|apply alias_memset_ok].
apply (st_ok_add_alias src0segs _ _ _ (fst alias_envp) (snd alias_envp)) in HS; [|apply alias_envp_ok].
change (st_ok src0segs (E_st sp argv envp uid hw rnd (Z_to_bv 64 0)) (ss_start two)
(init_machine_state src0segs Plain_init_pc Plain_phdrs sp rnd argv envp uid hw)) in HS.
pose proof (runs_main_init sp argv envp Hsp Hva Hve two Plain_init_pc uid hw rnd Htwo) as HR.
destruct two.
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
all: sym_run_to_with src0tbl_ok HS 0x15388; clear regs1.
all: idtac "PHASE D".
all: reg_of HS (8%bv:reg) H8; reg_of HS (10%bv:reg) H10.
all: pose proof (z_argv_bounds sp argv envp 0 ltac:(lia)) as B0.
all: lazymatch goal with |- realizes _ (mkCfg ?ms _) _ =>
destruct (src0_progname_scan (nth 0 argv []) _ (ms_mem ms) (seg_rom src0segs) (ms_regs ms)
(argv_no_nul argv Hva 0 ltac:(lia))
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
let rs' := eval vm_compute in (opt_mem (store_region (ss_mem ss) None 0x4fd30 8 (CVal 8 (SOff 7 0)))) in
assert (HCB : forall i, 0 <= i < Z.of_nat (length bs) ->
cbyte src0segs E (base_val E None + 0x4fd30) (CVal 8 (SOff 7 0)) i = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite length_N_to_le_bytes in Hi;
change (CVal 8 (SOff 7 0)) with (CVal (N.of_nat 8) (SOff 7 0));
rewrite (st_bytes_cbyte src0segs E) by lia;
unfold word_to_le_bytes; rewrite Z_to_le_bytes_st; do 2 f_equal;
cbn [sv_denot]; rewrite Z.add_0_r, ews7, ews1; reflexivity
| ];
pose proof (proj2 (swrite_sound src0segs E m (ss_mem ss) None 0x4fd30 (CVal 8 (SOff 7 0)) bs rs'
(st_ok_mem_ok src0segs E ss _ HS)
ltac:(rewrite length_N_to_le_bytes; vm_compute; reflexivity)
ltac:(rewrite length_N_to_le_bytes; lia)
ltac:(rewrite length_N_to_le_bytes; reflexivity) HCB)) as HM;
change (mem_ok src0segs E m' rs') in HM;
unshelve epose proof (st_ok_set_regs_mem src0segs 9%nat E E ss _ regs2 _ 0x153ac m m' rs' upd_progname
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
all: sym_add_fact HS 7%nat (ptr_fact 0);
[ unfold ptr_fact, SP_LO, SP_HI, K_stack; cbn [af_lo af_hi af_al2]; rewrite ews7;
pose proof (progname_off_le (nth 0 argv [])); pose proof (rand_off_bound argv envp Hva Hve);
pose proof (block_fits sp argv envp Hfits) as HBF; unfold SP_HI in HBF;
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
assert (HA8 : env_agree 8%nat E (E_st sp argv envp uid hw rnd tid))
by (split; [intros n Hn; do 8 (destruct n as [|n]; [reflexivity|]); lia | reflexivity]);
pose proof (st_ok_resume_mem src0segs 8%nat E (E_st sp argv envp uid hw rnd tid) ss regs mem (SOff 8 0) tid (ss_mem ss)
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
all: sym_run_to_with src0tbl_ok HS 0x15cd4.
all: sym_add_chunk_sem HS (@None nat) guard_data_chunk;
[ intros HCS; apply (guard_data_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM);
[ cbn; lia
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS) ]
| ].
all: sym_run_to_with src0tbl_ok HS 0x15cd8.
all: sym_add_chunk_sem HS (@None nat) canary_chunk;
[ intros HCS; apply (canary_chunk_ok src0segs _ _ 0 GUARD RAND_DATOM CANARY_ATOM);
[ cbn; lia
| reflexivity
| exact (Forall_inv (Forall_inv_tail HCS))
| exact (Forall_inv HCS)
| exact (Forall_inv (Forall_inv_tail (Forall_inv_tail HCS))) ]
| ].
all: idtac "PHASE H".
all: sym_run_to_with src0tbl_ok HS 0x13d50.
all: idtac "PHASE I".
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_head src0segs E ss ms keep_zero) in HS;
apply (st_ok_prune src0segs E _ ms [] [0%nat]) in HS end.
all: lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
apply (st_ok_clean_all src0segs E ss ms keep_main) in HS;
apply (st_ok_agree_pd src0segs (fun _ => true) (not_in [UID_DATOM; HWCAP_DATOM]) _ (E_main sp argv envp tid rnd)) in HS;
[ | apply E_st_main_agree | vm_compute; reflexivity ] end.
all: sym_norm HS.
- change (st_ok src0segs (E_main sp argv envp tid rnd) (ss_main true) ms) in HS. exact (K ms tid Htid8 HS HR).
- change (st_ok src0segs (E_main sp argv envp tid rnd) (ss_main false) ms) in HS. exact (K ms tid Htid8 HS HR).
Qed.
End f.
Theorem src0_start : forall (two : bool) sp brk mbase rnd lim inp T,
valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
(if two then (2 <= length (in_argv inp))%nat else True) ->
(forall ms tid, 0 < bv_unsigned tid < 4194304 ->
st_ok src0segs (E_main sp (in_argv inp) (in_envp inp) tid rnd) (ss_main two) ms ->
runs_at (bv_unsigned sp) (ms_mem ms) (runs_main two sp (in_argv inp) (in_envp inp) rnd) ->
realizes src0segs (mkCfg ms (with_tid tid (init_model (segments_reserved src0segs) brk mbase sp lim inp))) T) ->
realizes src0segs (init_config src0segs Plain_init_pc Plain_phdrs sp brk mbase rnd lim inp) T.
Proof.
intros two sp brk mbase rnd lim inp T Hsp Hva Hve Hfits Htwo K.
unfold init_config.
apply (src0_start_gen sp (in_argv inp) (in_envp inp) Hsp Hva Hve Hfits (in_uid inp) (in_hwcap inp) rnd two);
[exact Htwo | reflexivity | reflexivity | reflexivity | exact K].
Qed.
