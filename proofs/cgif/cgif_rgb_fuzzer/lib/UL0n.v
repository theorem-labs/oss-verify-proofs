(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK0o YK0q YQ0k YN06 YN02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ0d YQ05 YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e YP07.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH05 UH07 UH06 UO3p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO04 YL05 YL01 UL06 YL0b YL0c YL02 YL08 YL09 YL00 YL03 YL0a YL07 UL0g UL0i UL0p.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition sP : sstate := Eval vm_compute in (run_ (add_cond ss_h1 cond_OK)).
Definition A_P : nat := 47.
Definition R46 : YQ0b.region := YQ0b.mkRegion (Some 47%nat) 0 4 0 0 [mkChunk 0 (CData 3 0 4)].
Definition R13h (h : Z) : YQ0b.region := block_region 14 h [mkChunk 0 (CData 2 0 h)].
Definition fact_P : afact := mkAF 4098 CEIL_MAX 0.
Definition ssP (h : Z) : sstate :=
mkSS (ss_pc sP) (sr_set (ss_regs sP) 10%bv (SOff 47 0))
(R46 :: R13h h :: tl (ss_mem sP)) None
(mkFacts ((47%nat, fact_P) :: f_atoms (ss_facts sP)) (f_conds (ss_facts sP)) (f_alias (ss_facts sP))).
Definition ssP0 : sstate := Eval vm_compute in (ssP 2).
Definition ssP1 : sstate := Eval vm_compute in (ssP 3).
Lemma sP_facts : ss_pc sP = ubs2_A_main + 0x128 /\ sr_get (ss_regs sP) 10%bv = SAlu ALU_ADD (SOff 14 2) sv_cl /\
hd_error (ss_mem sP) = Some (block_region 14 6 [mkChunk 0 (CData 2 0 6)]) /\
ss_atoms_pd (fun n => negb (Nat.eqb n 47)) (not_in [3%nat]) sP = true /\
sep_check ubs2_msyms (ss_facts sP) (tl (ss_mem sP)) = true /\ ss_resv sP = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition E_P (E : env) (data : list byte) (p : Z) : env :=
ewset (edset E 3 (skipn (Z.to_nat (2 + config_len data)) data)) 47 (Z_to_bv 64 p).
Lemma E_P_agree : forall E data p, env_agree_pd (fun n => negb (Nat.eqb n 47)) (not_in [3%nat]) E (E_P E data p).
Proof.
intros E data p. split.
- intros n Hn. unfold E_P, ewset, edset. cbn [ew]. destruct (Nat.eqb_spec n 47); [subst; discriminate | reflexivity].
- intros d Hd. unfold E_P, ewset, edset. cbn [ed]. unfold not_in in Hd. cbn in Hd.
destruct (Nat.eqb_spec d 3); [subst; discriminate | reflexivity].
Qed.
Lemma E_P_old : forall E data p n, n <> 47%nat -> ew (E_P E data p) n = ew E n.
Proof. intros. unfold E_P. rewrite ew_ewset_other by assumption. reflexivity. Qed.
Lemma E_P_46 : forall E data p, 0 <= p < 2 ^ 64 -> bv_unsigned (ew (E_P E data p) 47) = p.
Proof.
intros. unfold E_P. rewrite ew_ewset_same, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. lia.
Qed.
Lemma E_P_ed3 : forall E data p, ed (E_P E data p) 3 = skipn (Z.to_nat (2 + config_len data)) data.
Proof. intros. reflexivity. Qed.
Lemma E_P_ed : forall E data p d, d <> 3%nat -> ed (E_P E data p) d = ed E d.
Proof. intros E data p d Hd. unfold E_P, ewset, edset. cbn [ed]. destruct (Nat.eqb_spec d 3); [contradiction | reflexivity]. Qed.
Section P.
Variable API : AllocAPI ubs2_msyms.
Hypothesis AX : AllocExtra ubs2_msyms (aa_MR API).
Variables (data : list byte) (cap0 : Z) (L' : layout) (A' : astate) (b0 : sptr) (E2 : env) (md : Model).
Hypothesis Hub : user_blocks A' = [(b0, cap0)].
Hypothesis Hcap0 : 65536 <= cap0 <= 67108864.
Hypothesis HE : hdr_env E2 data (ptr_addr L' b0).
Hypothesis HAN : hdr_anch E2.
Let pP : Z := ptr_addr L' b0 + 2 + config_len data.
Let E3 : env := E_P E2 data pP.
Lemma E2_ed2 : ed E2 2 = data.
Proof. exact (proj1 HE). Qed.
Lemma E3_ed2 : ed E3 2 = data.
Proof. unfold E3. rewrite E_P_ed by lia. apply E2_ed2. Qed.
Theorem ubs2_to_P : forall ms2 T,
6 + config_len data <= dlen data -> dlen data < cap0 ->
st_ok ubs2segs E2 ss_h1 ms2 ->
aa_MR API L' A' (ms_mem ms2) md ->
blk_data ubs2_msyms (ms_mem ms2) (ptr_addr L' b0) data ->
(forall ms3, st_ok ubs2segs E3 (if config_len data =? 0 then ssP0 else ssP1) ms3 ->
aa_MR API L' A' (ms_mem ms3) md ->
blk_data ubs2_msyms (ms_mem ms3) (ptr_addr L' b0) data ->
realizes ubs2segs (mkCfg ms3 md) T) ->
realizes ubs2segs (mkCfg ms2 md) T.
Proof.
intros ms2 T Hok HLc HS0 HMR HD K.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (b0, cap0) (user_blocks A')) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L' A' (ms_mem ms2) md b0 cap0 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
unfold dlen in Hok, HLc. pose proof (config_len_bound data) as Hcl.
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YN05.alloc_ceiling_val; lia).
destruct (list_len2 data ltac:(lia)) as (d0 & d1 & rest & Ed).
pose proof (proj1 (proj2 HE)) as E13. pose proof (proj2 (proj2 HE)) as E26.
assert (HS : st_ok ubs2segs E2 (add_cond ss_h1 cond_OK) ms2).
{ apply (st_ok_add_cond_neg ubs2segs E2 ss_h1 ms2 BC_LTU (SOff 27 0) sv_cl6 HS0).
rewrite branch_ltu_U, (U_cl6 E2 d0 d1 rest) by (rewrite E2_ed2; exact Ed).
rewrite U_SOff, E26, Z.add_0_r, zcanon_id by (unfold M64 in *; lia).
apply Z.ltb_ge. rewrite <- Ed. lia. }
clear HS0.
drv_run_with ubs2tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok ubs2segs E2 sP msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
pose proof (blk_data_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX L' A' m0 m1 _ E2 (ss_facts sP) ubs2_keep rs0 b0 cap0 (ptr_addr L' b0) data HMR
ltac:(destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HG0); exact HG0) ltac:(drv_anch) ltac:(vm_compute; reflexivity) HF Hin ltac:(lia) ltac:(lia)) as HD';
specialize (HD' HD); clear HD; rename HD' into HD end.
drv_mr (MR_after_frame ubs2_msyms (aa_MR API) (aa_laws API) AX) ubs2_keep E2 HS HF HMR.
lazymatch type of HS with st_ok _ _ _ ?msx => apply (K msx); [| exact HMR | exact HD] end.
destruct sP_facts as (Hpc & Ha0P & Hhd & Hpd & Hsep & Hrv).
assert (HpP : 0 <= pP < 2 ^ 64) by (unfold pP; lia).
apply (st_ok_agree_pd ubs2segs _ _ E2 E3 sP _ HS (E_P_agree E2 data pP)) in Hpd. clear HS. rename Hpd into HS.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (HS' : st_ok ubs2segs E3 (ssP (if config_len data =? 0 then 2 else 3)) ltac:(lazymatch type of H7 with regs_ok _ _ (ms_regs ?m) => exact m end)).
2:{ destruct (config_len data =? 0); [change ssP0 with (ssP 2) | change ssP1 with (ssP 3)]; exact HS'. }
unfold st_ok, ssP. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [rewrite H4, Hrv; reflexivity|].
split; [exact H5|]. split; [exact H6|]. split; [| split].
-
intros r. destruct (decide (r = 10%bv)) as [->|Hne].
+ rewrite sr_get_set_same by reflexivity. rewrite (H7 10%bv), Ha0P.
rewrite (denot_lit_U E3 (SOff 47 0)), (denot_lit_U E3 (SAlu ALU_ADD (SOff 14 2) sv_cl)). f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, (U_cl E3 d0 d1 rest) by (rewrite E3_ed2; exact Ed).
unfold E3. rewrite E_P_46 by exact HpP. rewrite E_P_old by lia. rewrite E13.
rewrite <- Ed. unfold pP. rewrite (zcanon_id (ptr_addr L' b0 + 2)) by (unfold M64 in *; lia).
rewrite !zcanon_id by (unfold M64 in *; lia). lia.
+ rewrite sr_get_set_other by exact Hne. apply H7.
-
change (ss_mem sP) with (block_region 14 6 [mkChunk 0 (CData 2 0 6)] :: tl (ss_mem sP)) in H8.
set (tail := tl (ss_mem sP)) in *.
assert (E13' : bv_unsigned (ew E3 14) = ptr_addr L' b0) by (unfold E3; rewrite E_P_old by lia; exact E13).
assert (HM1 : mem_ok ubs2segs E3 (ms_mem ms) (R13h (if config_len data =? 0 then 2 else 3) :: tail)).
{ eapply (mem_ok_head_replace ubs2_msyms); [exact H8 | reflexivity | cbn; lia | | | cbn; lia | |].
- unfold R13h, block_region. cbn [r_hi]. destruct (config_len data =? 0); lia.
- unfold R13h, block_region. cbn [r_lo r_hi]. destruct (config_len data =? 0); lia.
- unfold R13h, block_region. cbn. destruct (config_len data =? 0); reflexivity.
- unfold R13h, block_region. cbn [r_chunks r_base base_val]. rewrite E13'. constructor; [| constructor].
eapply (chunk_ok_cdata0 ubs2_msyms); [exact E3_ed2 | destruct (config_len data =? 0); lia |].
intros i Hi. apply HD. destruct (config_len data =? 0); lia. }
eapply (mem_ok_cons ubs2_msyms); [exact HM1 | reflexivity | |].
+
unfold region_ok, R46. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. unfold E3 at 1 2 3. rewrite E_P_46 by exact HpP.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [| constructor].
eapply (chunk_ok_cdata0 ubs2_msyms); [apply E_P_ed3 | rewrite length_skipn; lia |].
intros i Hi. unfold E3. rewrite E_P_46 by exact HpP. unfold pP.
replace (ptr_addr L' b0 + 2 + config_len data + i) with (ptr_addr L' b0 + (2 + config_len data + i)) by lia.
rewrite (HD (2 + config_len data + i)) by lia.
rewrite nth_error_skipn. f_equal. lia.
+
intros r' [<- | Hr'].
* unfold extent_disjoint, R46, R13h, block_region. cbn [r_base r_lo r_hi base_val]. rewrite E13'.
unfold E3. rewrite E_P_46 by exact HpP. unfold pP. right. destruct (Z.eqb_spec (config_len data) 0); lia.
* eapply (sep_check_disjoint ubs2_msyms (aa_MR API) (aa_laws API) AX E3 _ (ss_facts sP) L' A' md b0 cap0 tail R46 47);
[exact H9 | | exact HMR | exact Hin | reflexivity | cbn; lia | | | vm_compute; discriminate | exact Hsep | exact Hr'].
-- apply (hdr_anch_ext E2 E3 HAN); [| vm_compute; reflexivity]. intros n Hn. unfold E3. apply E_P_old. lia.
-- cbn [r_lo R46]. unfold E3. rewrite E_P_46 by exact HpP. unfold pP. lia.
-- cbn [r_hi R46]. unfold E3. rewrite E_P_46 by exact HpP. unfold pP. lia.
-
apply facts_ok_add_atom; [exact H9|]. unfold afact_ok, fact_P. cbn [af_lo af_hi af_al2].
unfold E3. rewrite E_P_46 by exact HpP. unfold pP. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
pose proof YN05.alloc_ceiling_val. lia.
Qed.
End P.
End a.
