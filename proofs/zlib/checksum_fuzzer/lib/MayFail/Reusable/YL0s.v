(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0s.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN35.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN34.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0r.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition add0 (x : sv) : sv := SAlu ALU_ADD x (SLit 0).
Definition sv_cl00 : sv := add0 (add0 sv_cl).
Definition sv_pl : sv := SAlu ALU_ADD (SAlu ALU_SUB (SOff 27 0) sv_cl) (SLit (-6)).
Definition sv_pl00 : sv := add0 (add0 sv_pl).
Definition sv_calls : sv := SAlu ALU_ADD (SAlu ALU_AND (SData 2 2 1) (SLit 3)) (SLit 1).
Lemma U_range : forall E x, 0 <= U E x < M64.
Proof. intros E x. unfold U, M64. apply u64_range. Qed.
Lemma U_add0 : forall E x, U E (add0 x) = U E x.
Proof.
intros E x. unfold add0. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0.
rewrite Z.add_0_r. apply zcanon_id. apply U_range.
Qed.
Section c.
Variables (E : env) (data : list byte) (d0 d1 : byte) (rest : list byte).
Hypothesis Hd : ed E 2 = data.
Hypothesis Ed : data = d0 :: d1 :: rest.
Hypothesis H26 : bv_unsigned (ew E 27) = Z.of_nat (length data).
Hypothesis HL : 6 + config_len data <= Z.of_nat (length data) < 2 ^ 62.
Lemma U_cl' : U E sv_cl = config_len data.
Proof. rewrite Ed. apply U_cl. rewrite Hd, Ed. reflexivity. Qed.
Lemma U_cl00 : U E sv_cl00 = config_len data.
Proof. unfold sv_cl00. rewrite !U_add0. apply U_cl'. Qed.
Lemma U_pl : U E sv_pl = payload_len data.
Proof.
pose proof (config_len_bound data) as Hcl.
unfold sv_pl, payload_len, HDR_MIN, dlen. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SOff, U_cl', U_SLit, H26, Z.add_0_r.
rewrite (zcanon_id (Z.of_nat (length data))) by (unfold M64; lia).
rewrite (zcanon_id (Z.of_nat (length data) - config_len data)) by (unfold M64; lia).
unfold zcanon at 2. unfold M64.
replace ((-6) mod 2 ^ 64) with (2 ^ 64 - 6) by reflexivity.
unfold zcanon, M64. replace (Z.of_nat (length data) - config_len data + (2 ^ 64 - 6)) with ((Z.of_nat (length data) - 6 - config_len data) + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma U_pl00 : U E sv_pl00 = payload_len data.
Proof. unfold sv_pl00. rewrite !U_add0. apply U_pl. Qed.
Lemma denot_pl000 : sv_denot E (add0 sv_pl00) = Z_to_bv 64 (payload_len data).
Proof. rewrite (denot_lit_U E _), U_add0, U_pl00. reflexivity. Qed.
Lemma U_calls : config_len data <> 0 -> U E sv_calls = Z.of_nat (calls data).
Proof.
intros Hcl. unfold sv_calls, calls, cfg_byte. rewrite (proj2 (Z.eqb_neq _ _) Hcl).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (zcanon 3) with 3. change (zcanon 1) with 1.
assert (Hb2 : U E (SData 2 2 1) = dbyte data 2).
{ unfold U. cbn [sv_denot]. unfold data_word. rewrite Hd. unfold dbyte.
pose proof (config_len_bound data) as Hb.
destruct rest as [|d2 rest']; [rewrite Ed in HL, Hb; cbn [length] in HL; lia|].
rewrite Ed. change (bytes_le_to_Z _) with (Z.lor (bv_unsigned d2) (Z.shiftl 0 8)).
change (nth 2 (d0 :: d1 :: d2 :: rest') (Z_to_bv 8 0)) with d2.
rewrite Z.shiftl_0_l, Z.lor_0_r. pose proof (u8_range d2). apply unsigned_lit_small. lia. }
rewrite Hb2. pose proof (u8_range (nth 2 data (Z_to_bv 8 0))) as Hr. unfold dbyte in *.
change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
pose proof (Z.mod_pos_bound (bv_unsigned (nth 2 data (Z_to_bv 8 0))) 4 ltac:(lia)).
rewrite (zcanon_id (_ mod 4)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End c.
Lemma wr_app : forall ch l1 l2 T, t_eq (wr ch (l1 ++ l2) T) (wr ch l1 (wr ch l2 T)).
Proof. intros. unfold wr. rewrite map_app. apply t_eq_sym. apply YK0k.t_emit_app. Qed.
Lemma lines_S : forall n, concat (repeat line0 (S n)) = line0 ++ concat (repeat line0 n).
Proof. intros. reflexivity. Qed.
Lemma t_emit_congr : forall l T T', t_eq T T' -> t_eq (t_emit l T) (t_emit l T').
Proof.
intros l T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
Qed.
Definition payload_leaf (b0 : sptr) (cap0 : Z) (r : option sptr * astate) : dleaf * astate :=
match fst r with
| None => (DL_payload_fail, snd r)
| Some q => (DL_run b0 cap0 (Some q), snd r)
end.
Lemma frame_of_havoc : forall k E ws rs m m',
mem_atoms_lt k rs = true -> frame_of E rs m m' -> frame_of (havoc E k ws) rs m m'.
Proof.
intros k E ws rs m m' Hat HF x Hx. apply HF. intros (r & Hin & Hr). apply Hx.
exists r. split; [exact Hin|].
unfold mem_atoms_lt in Hat. pose proof (proj1 (forallb_forall _ _) Hat r Hin) as Hr'.
unfold region_atoms_lt in Hr'. apply andb_prop in Hr' as [Hb _].
rewrite (base_val_agree k E (havoc E k ws) (r_base r) (env_agree_havoc E k ws) Hb). exact Hr.
Qed.
End a.
Ltac drv_printf0 HS Hch k ret HF :=
lazymatch type of HS with st_ok _ ?E ?ss ?ms =>
lazymatch type of Hch with fdchan (Z_to_bv 64 1) ?ch ?model =>
let r := eval vm_compute in (pf0_check k ss ret) in
lazymatch r with
| Some (?s5, ?zs) =>
let Hck := fresh "Hck" in
assert (Hck : pf0_check k ss ret = Some (s5, zs)) by (vm_compute; reflexivity);
apply (realizes_printf0_by_run E ss ms model ch k ret s5 zs _ HS ltac:(assumption) ltac:(assumption) Hck Hch);
clear Hck HS;
let ms' := fresh "ms" in let ws := fresh "ws" in
intros ms' ws HS HF; cbn [ms_mem mkst pend_at] in HF;
apply (frame_of_havoc k E ws (ss_mem ss)) in HF; [| vm_compute; reflexivity]
| None => fail "drv_printf0: pf0_check failed on this state"
end
end end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition setreg_ (r : reg) (v : sv) (ss : sstate) : sstate :=
mkSS (ss_pc ss) (sr_set (ss_regs ss) r v) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition drop_base (n : nat) (l : list (nat * YP09.region)) : list (nat * YP09.region) :=
filter (fun p => negb (obase_eqb (r_base (snd p)) (Some n))) l.
Definition cond_CL0 : acond := mkAC BC_EQ sv_cl00 (SLit 0).
Definition cond_CL1 : acond := mkAC BC_NE sv_cl00 (SLit 0).
Definition cond_PL0 : acond := mkAC BC_EQ sv_pl00 (SLit 0).
Definition cond_PL1 : acond := mkAC BC_NE sv_pl00 (SLit 0).
Definition sB0 : sstate := Eval vm_compute in (run_ ssP0).
Definition sB1 : sstate := Eval vm_compute in (run_ ssP1).
Definition sQ0 : sstate := Eval vm_compute in (run_ (add_cond sB0 cond_CL0)).
Definition sQ1 : sstate := Eval vm_compute in (run_ (add_cond sB1 cond_CL1)).
Definition sQ1k (k : Z) : sstate := Eval vm_compute in (setreg_ 21%bv (SLit k) sQ1).
Lemma sBQ_facts :
ss_pc sB0 = src0_A_target_run + 0x48 /\ ss_pc sB1 = src0_A_target_run + 0x48 /\ ss_pc sQ0 = src0_A_target_run + 0xa4 /\ ss_pc sQ1 = src0_A_target_run + 0x58 /\
sr_get (ss_regs sQ0) 21%bv = SLit 1 /\ sr_get (ss_regs sQ1) 21%bv = sv_calls /\
sr_get (ss_regs sQ0) 8%bv = sv_pl00 /\ sr_get (ss_regs sQ1) 8%bv = sv_pl00.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition run_env (E : env) (data : list byte) (buf : Z) : Prop :=
ed E 2 = data /\ bv_unsigned (ew E 14) = buf /\ bv_unsigned (ew E 27) = Z.of_nat (length data) /\
bv_unsigned (ew E 47) = buf + 2 + config_len data /\ hdr_anch E.
Lemma run_env_agree : forall k E E' data buf, (48 <= k)%nat -> env_agree k E E' -> run_env E data buf -> run_env E' data buf.
Proof.
intros k E E' data buf Hk [HA HD] (H1 & H2 & H3 & H4 & H5). unfold run_env.
rewrite HD, !HA by lia. repeat split; try assumption.
apply (hdr_anch_ext E E' H5). intros n Hn. apply HA. lia.
Qed.
Lemma run_env_anch : forall E data buf, run_env E data buf -> hdr_anch E.
Proof. intros E data buf H. exact (proj2 (proj2 (proj2 (proj2 H)))). Qed.
Lemma run_env_havoc : forall E data buf k ws, (48 <= k)%nat -> run_env E data buf -> run_env (havoc E k ws) data buf.
Proof. intros E data buf k ws Hk H. eapply run_env_agree; [exact Hk | apply env_agree_havoc | exact H]. Qed.
Lemma run_env_post : forall E data buf k regs g, (48 <= k)%nat -> run_env E data buf -> run_env (post_env E k regs g) data buf.
Proof. intros E data buf k regs g Hk H. eapply run_env_agree; [exact Hk | apply post_env_agree | exact H]. Qed.
Definition md_inv (fs : Fs) (md : Model) : Prop :=
fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) md /\ fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md /\ m_fs md = fs.
Lemma md_inv_vm : forall fs md vm, md_inv fs md -> md_inv fs (with_vmmaps vm md).
Proof. intros fs md vm ([H1 H1'] & [H2 H2'] & H3). unfold md_inv, fdchan. autorewrite with model. repeat split; assumption. Qed.
Lemma md_inv_ex : forall fs md md', md_inv fs md -> (exists vm, md' = with_vmmaps vm md) -> md_inv fs md'.
Proof. intros fs md md' H [vm ->]. apply md_inv_vm. exact H. Qed.
Lemma md_inv_ch1 : forall fs md, md_inv fs md -> fdchan (Z_to_bv 64 1) ch_stdout md.
Proof. intros fs md (H1 & H2 & H3). exact H1. Qed.
Lemma md_inv_fs : forall fs md, md_inv fs md -> m_fs md = fs.
Proof. intros fs md (H1 & H2 & H3). exact H3. Qed.
Lemma blocks_same_ptr : forall B MR (LAWS : MR_laws B MR) L A m md p q n n',
MR L A m md -> In (p, n) (user_blocks A) -> In (q, n') (user_blocks A) -> 0 < n -> 0 < n' ->
ptr_addr L p = ptr_addr L q -> n = n'.
Proof.
intros B MR LAWS L A m md p q n n' HMR Hp Hq Hn Hn' Heq.
destruct (Z.eq_dec n n') as [|Hne]; [assumption|]. exfalso.
pose proof (mr_blocks_disjoint B MR LAWS L A m md HMR) as HD. unfold blocks in HD.
revert HD Hp Hq. induction (user_blocks A) as [|b bl IH]; intros HD Hp Hq; [destruct Hp|].
cbn [map pairwise] in HD. destruct HD as [Hhd Htl].
destruct Hp as [->|Hp]; destruct Hq as [Hq'|Hq].
- apply Hne. congruence.
- specialize (Hhd (ptr_addr L q, n') ltac:(apply in_map_iff; exists (q, n'); auto)). unfold ranges_disjoint in Hhd. cbn [fst snd] in Hhd. lia.
- subst b. specialize (Hhd (ptr_addr L p, n) ltac:(apply in_map_iff; exists (p, n); auto)). unfold ranges_disjoint in Hhd. cbn [fst snd] in Hhd. lia.
- apply IH; assumption.
Qed.
Lemma blocks_distinct_addr : forall B MR (LAWS : MR_laws B MR) L A m md p q n n',
MR L A m md -> In (p, n) (user_blocks A) -> In (q, n') (user_blocks A) -> 0 < n -> 0 < n' ->
p <> q -> ptr_addr L p <> ptr_addr L q.
Proof.
intros B MR LAWS L A m md p q n n' HMR Hp Hq Hn Hn' Hne Heq.
pose proof (mr_blocks_disjoint B MR LAWS L A m md HMR) as HD. unfold blocks in HD.
revert HD Hp Hq. induction (user_blocks A) as [|b bl IH]; intros HD Hp Hq; [destruct Hp|].
cbn [map pairwise] in HD. destruct HD as [Hhd Htl].
destruct Hp as [->|Hp]; destruct Hq as [Hq'|Hq].
- apply Hne. congruence.
- specialize (Hhd (ptr_addr L q, n') ltac:(apply in_map_iff; exists (q, n'); auto)). unfold ranges_disjoint in Hhd. cbn [fst snd] in Hhd. lia.
- subst b. specialize (Hhd (ptr_addr L p, n) ltac:(apply in_map_iff; exists (p, n); auto)). unfold ranges_disjoint in Hhd. cbn [fst snd] in Hhd. lia.
- apply IH; assumption.
Qed.
Definition renv (E : env) (data : list byte) (buf q : Z) : Prop :=
run_env E data buf /\ bv_unsigned (ew E 52) = q.
Lemma renv_agree : forall k E E' data buf q, (53 <= k)%nat -> env_agree k E E' -> renv E data buf q -> renv E' data buf q.
Proof.
intros k E E' data buf q Hk HA [H1 H2]. split; [eapply run_env_agree; [| exact HA | exact H1]; lia|].
rewrite (proj1 HA) by lia. exact H2.
Qed.
Lemma renv_havoc : forall E data buf q k ws, (53 <= k)%nat -> renv E data buf q -> renv (havoc E k ws) data buf q.
Proof. intros E data buf q k ws Hk H. eapply renv_agree; [exact Hk | apply env_agree_havoc | exact H]. Qed.
Lemma renv_post : forall E data buf q k regs g, (53 <= k)%nat -> renv E data buf q -> renv (post_env E k regs g) data buf q.
Proof. intros E data buf q k regs g Hk H. eapply renv_agree; [exact Hk | apply post_env_agree | exact H]. Qed.
Definition RA_ME : Z := Eval vm_compute in (src0_A_target_run + 0x64).
Definition RA_MC : Z := Eval vm_compute in (src0_A_target_run + 0x78).
Definition RA_LIB : Z := Eval vm_compute in (src0_A_target_run + 0xcc).
Definition RET_PF : Z := Eval vm_compute in (src0_A_target_run + 0xdc).
Definition RA_FQ : Z := Eval vm_compute in (src0_A_target_run + 0xf8).
Definition LIBPC : Z := Eval vm_compute in src0_A_LLVMFuzzerTestOneInput.
Definition EMPTY : Z := Eval vm_compute in src0_D_aef_aligned_copy_empty.
Definition cond_CMt : acond := mkAC BC_LT sv_b1s (SLit 0).
Definition cond_CMf : acond := mkAC BC_GE sv_b1s (SLit 0).
Definition blkq_fact : afact := mkAF 4096 CEIL_MAX 4.
End d.
Ltac anch_ew :=
repeat first [ reflexivity
| rewrite ew_havoc_old by lia
| rewrite ew_ewset_other by lia
| rewrite (proj1 (post_env_agree _ _ _ _)) by lia ].
Ltac drv_anch ::= first
[ assumption
| match goal with
| H : hdr_anch ?E |- stack_anchored ?E _ => apply H; vm_compute; reflexivity
| H : run_env ?E _ _ |- stack_anchored ?E _ => apply (run_env_anch _ _ _ H); vm_compute; reflexivity
| H : renv ?E _ _ _ |- stack_anchored ?E _ => apply (run_env_anch _ _ _ (proj1 H)); vm_compute; reflexivity
| H : run_env ?E0 _ _ |- stack_anchored ?E _ =>
apply (hdr_anch_ext E0 E (run_env_anch _ _ _ H)); [ intros; anch_ew | vm_compute; reflexivity ]
| H : renv ?E0 _ _ _ |- stack_anchored ?E _ =>
apply (hdr_anch_ext E0 E (run_env_anch _ _ _ (proj1 H))); [ intros; anch_ew | vm_compute; reflexivity ]
| H : hdr_anch ?E0 |- stack_anchored ?E _ =>
apply (hdr_anch_ext E0 E H); [ intros; anch_ew | vm_compute; reflexivity ]
end ].
Ltac renv_sync HS HRE :=
lazymatch type of HS with
| st_ok _ (havoc ?E ?k ?ws) _ _ =>
first [apply (renv_havoc E _ _ _ k ws) in HRE | apply (run_env_havoc E _ _ k ws) in HRE]; [| lia]
| st_ok _ (post_env ?E ?k ?regs ?g) _ _ =>
first [apply (renv_post E _ _ _ k regs g) in HRE | apply (run_env_post E _ _ k regs g) in HRE]; [| lia]
end.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section BQ.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Variables (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr) (MDc : Model).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis Hok : 6 + config_len data <= dlen data.
Hypothesis HLc : dlen data < cap0.
Theorem src0_P_to_Q : forall E ms T,
run_env E data (ptr_addr L' b0) ->
st_ok src0segs E (if config_len data =? 0 then ssP0 else ssP1) ms ->
aa_MR API L' A' (ms_mem ms) MDc ->
(forall ms', st_ok src0segs E (if config_len data =? 0 then sQ0 else sQ1) ms' ->
aa_MR API L' A' (ms_mem ms') MDc ->
realizes src0segs (mkCfg ms' MDc) T) ->
realizes src0segs (mkCfg ms MDc) T.
Proof.
intros E ms T HE HS HMR K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
destruct HE as (HEd & HE13 & HE26 & HE46 & HAN). unfold dlen in *.
destruct (list_len2 data ltac:(pose proof (config_len_bound data); lia)) as (d0 & d1 & rest & Ed).
let v := eval cbv [sv_cl00 add0 sv_cl sv_b1s] in sv_cl00 in
assert (Hcl00 : U E v = config_len data) by (eapply U_cl00; eauto).
destruct (Z.eqb_spec (config_len data) 0) as [Hz | Hnz].
- drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sB0 msx) in HS end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_eq_U, Hcl00, U_SLit, Hz. reflexivity. }
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sQ0 msx) in HS end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
exact (K _ HS HMR).
- drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sB1 msx) in HS end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_eq_U, Hcl00, U_SLit. change (zcanon 0) with 0. apply Z.eqb_neq. exact Hnz. }
drv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E sQ1 msx) in HS end.
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
exact (K _ HS HMR).
Qed.
Theorem src0_Q_calls : forall E ms,
run_env E data (ptr_addr L' b0) -> config_len data <> 0 ->
st_ok src0segs E sQ1 ms -> st_ok src0segs E (sQ1k (Z.of_nat (calls data))) ms.
Proof.
intros E ms (HEd & HE13 & HE26 & HE46 & HAN) Hnz HS.
unfold dlen in *.
destruct (list_len2 data ltac:(pose proof (config_len_bound data); lia)) as (d0 & d1 & rest & Ed).
unfold sQ1k.
match goal with |- st_ok _ _ ?ssx _ => let v := eval vm_compute in (setreg_ 21%bv (SLit (Z.of_nat (calls data))) sQ1) in change ssx with v end.
change (st_ok src0segs E (setreg_ 21%bv (SLit (Z.of_nat (calls data))) sQ1) ms).
unfold setreg_. apply (st_ok_regs src0segs E sQ1 ms _ HS).
intros r. destruct (decide (r = 21%bv)) as [->|Hne].
- rewrite sr_get_set_same by reflexivity. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 sBQ_facts)))))).
rewrite (denot_lit_U E sv_calls), (U_calls E data d0 d1 rest HEd Ed) by (lia || exact Hnz).
cbn [sv_denot]. first [reflexivity | f_equal; pose proof (calls_bound data); unfold zcanon, M64; rewrite Z.mod_small by lia; reflexivity].
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
End BQ.
End e.
