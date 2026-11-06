From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0a YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN03 YN02 YN2b YN25 YN26 YN0b YN07 YN0a YN09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition c_lo : acond := mkAC BC_NE (SAlu ALU_AND (SOff aBITS 0) (SLit 3072)) (SLit 3072).
Definition c_hi : acond := mkAC BC_EQ (SAlu ALU_AND (SOff aBITS 0) (SLit 3072)) (SLit 3072).
Definition az_cond (k : kcase) : acond := match k with K3b => c_hi | _ => c_lo end.
Definition nowin (r : YP09.region) : YP09.region := YP09.mkRegion (r_base r) (r_lo r) (r_hi r) 0 0 (r_chunks r).
Definition ss_az0 (k : kcase) (r : rcase) : sstate :=
mkSS src0_A_malloc_allzerop regs_init (map nowin (free_mem k r)) None (free_facts k r).
Definition ss_az (k : kcase) (r : rcase) : sstate := add_cond (ss_az0 k r) (az_cond k).
Definition AZ_RET (k : kcase) : Z :=
match k with
| K3b => src0_A_malloc_allzerop + 0x120
| K3a => src0_A_malloc_allzerop + 0x154
| _ => src0_A_malloc_allzerop + 0x174
end.
Definition az_a0 (k : kcase) : sv :=
match k with
| K3b => SLit 1
| K3a => SAlu ALU_SLTU (SOff aMP (-16)) (SAlu ALU_SLL (SOff aSCL 0) (SLit 4))
| _ => SLit 0
end.
Definition keep_ok (l : list sv) : bool :=
forallb (fun n => ((10 <=? n) && (n <=? 16))%nat || sv_eqb (nth n l (SLit 0)) (nth n regs_init (SLit 0))) (seq 0%nat 32%nat).
Definition SSAZ (k : kcase) (r : rcase) : sstate := fst (sym_run_toN src0segs src0tbl FUEL (AZ_RET k) (ss_az k r)).
Definition az_ok (k : kcase) (r : rcase) : bool :=
let p := sym_run_toN src0segs src0tbl FUEL (AZ_RET k) (ss_az k r) in
match snd p with RS_running => true | _ => false end && (ss_pc (fst p) =? AZ_RET k) &&
keep_ok (ss_regs (fst p)) && sv_eqb (nth 10 (ss_regs (fst p)) (SLit 0)) (az_a0 k) &&
match ss_resv (fst p) with None => true | Some _ => false end.
Lemma az_ok_all : forall k r, az_ok k r = true.
Proof using. intros k r. destruct k, r; vm_compute; reflexivity. Qed.
Lemma az_facts : forall k r,
run_to_ok (AZ_RET k) (ss_az k r) (SSAZ k r) /\ keep_ok (ss_regs (SSAZ k r)) = true /\
nth 10 (ss_regs (SSAZ k r)) (SLit 0) = az_a0 k /\ ss_resv (SSAZ k r) = None.
Proof using.
intros k r. pose proof (az_ok_all k r) as H. unfold az_ok, SSAZ in *.
destruct (sym_run_toN src0segs src0tbl FUEL (AZ_RET k) (ss_az k r)) as [s st] eqn:E. cbn [fst snd] in *.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2].
destruct st; try discriminate H1.
split; [split; [exact E | apply Z.eqb_eq; exact H2] |].
split; [exact H3|]. split; [apply sv_eqb_eq; exact H4|].
destruct (ss_resv s); [discriminate H5 | reflexivity].
Qed.
Lemma keep_get : forall l (i : reg), keep_ok l = true -> (bv_unsigned i < 10 \/ 16 < bv_unsigned i) ->
sr_get l i = sr_get regs_init i.
Proof using.
intros l i H Hi. unfold sr_get. destruct (bv_eqb i 0); [reflexivity|].
unfold keep_ok in H. rewrite forallb_forall in H.
pose proof (u5_range i) as Hr.
specialize (H (ridx i) ltac:(apply in_seq; unfold ridx; lia)).
apply orb_prop in H as [H|H].
- exfalso. apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.leb_le in H2. unfold ridx in *. lia.
- apply sv_eqb_eq. exact H.
Qed.
Lemma region_ok_nowin : forall E m x, region_ok src0segs E m x -> region_ok src0segs E m (nowin x).
Proof using.
intros E m x (H1 & H2 & _ & H4). unfold nowin, region_ok; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks].
split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; lia | exact H4].
Qed.
Lemma all_disjoint_nowin : forall E x l, all_disjoint E x l -> all_disjoint E (nowin x) (map nowin l).
Proof using.
intros E x l. induction l as [|y l IH]; cbn [all_disjoint map]; [tauto|].
intros [Hd Hl]. split; [exact Hd | exact (IH Hl)].
Qed.
Lemma pairwise_nowin : forall E l, pairwise_disjoint E l -> pairwise_disjoint E (map nowin l).
Proof using.
intros E l. induction l as [|x l IH]; cbn [pairwise_disjoint map]; [tauto|].
intros [Ha Hp]. split; [apply all_disjoint_nowin; exact Ha | exact (IH Hp)].
Qed.
Lemma in_wrange_nowin : forall E l a, ~ in_wrange E (map nowin l) a.
Proof using.
intros E l a (x & Hin & Hx). apply in_map_iff in Hin as (y & <- & _).
unfold nowin in Hx. cbn [r_wlo r_whi r_base] in Hx. lia.
Qed.
Lemma land3072_chk : forallb (fun l => forallb (fun s => Bool.eqb (Z.land (l + 32 + 64 * s) 3072 =? 3072) (48 <=? s))
(zseq 0 64)) (zseq 0 32) = true.
Proof using. vm_compute. reflexivity. Qed.
Lemma land3072 : forall last sc ml, 0 <= last < 32 -> 0 <= sc < 64 -> 0 <= ml ->
(Z.land (bits_enc last sc ml) 3072 =? 3072) = (48 <=? sc).
Proof using.
intros last sc ml H1 H2 H3.
assert (K : 3072 = Z.land (Z.ones 12) 3072) by reflexivity.
assert (E : Z.land (bits_enc last sc ml) 3072 = Z.land (last + 32 + 64 * sc) 3072).
{ transitivity (Z.land (Z.land (bits_enc last sc ml) (Z.ones 12)) 3072).
- rewrite <- Z.land_assoc, <- K. reflexivity.
- rewrite Z.land_ones by lia. f_equal. change (2 ^ 12) with 4096. unfold bits_enc.
replace (last + 32 + 64 * sc + 4096 * ml) with ((last + 32 + 64 * sc) + ml * 4096) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite E. pose proof land3072_chk as C. rewrite forallb_forall in C.
specialize (C last (proj2 (In_zseq 0 32 last) ltac:(lia))). rewrite forallb_forall in C.
specialize (C sc (proj2 (In_zseq 0 64 sc) ltac:(lia))). apply Bool.eqb_prop in C. exact C.
Qed.
Lemma az_cond_ok : forall k r v m, free_pre k r v m -> acond_ok (EV (xvf v)) (az_cond k).
Proof using.
intros k r v m FP. pose proof (fp_k _ _ _ _ FP) as K.
pose proof (bits_facts _ _ _ _ FP) as (B & L1 & L2 & L3 & L4).
assert (HL : bv_unsigned (sv_denot (EV (xvf v)) (SAlu ALU_AND (SOff aBITS 0) (SLit 3072))) = Z.land (fv_bits v) 3072).
{ den. rewrite alu64_and, !lit64_small by lin. reflexivity. }
assert (HR : bv_unsigned (sv_denot (EV (xvf v)) (SLit 3072)) = 3072) by reflexivity.
pose proof (land3072 (fv_last v) (fv_sc v) (fv_ml v) ltac:(lia) ltac:(lia) ltac:(lia)) as E. rewrite <- B in E.
destruct k; unfold az_cond, c_lo, c_hi, acond_ok; cbn [ac_c ac_a ac_b]; rewrite ?branch_ne, ?branch_eq, HL, HR, E.
- destruct K as (_ & Hs & _). apply negb_true_iff, Z.leb_gt. lia.
- destruct K as (_ & Hs & _). apply negb_true_iff, Z.leb_gt. lia.
- destruct K as (_ & Hs & _). apply negb_true_iff, Z.leb_gt. lia.
- destruct K as (_ & Hs & _). rewrite Hs. reflexivity.
Qed.
Lemma az_entry : forall k r v m, free_pre k r v m ->
st_ok src0segs (EV (xvf v)) (ss_az k r) (mkst (fv_regs v) (Z_to_bv 64 src0_A_malloc_allzerop) m (seg_rom src0segs)).
Proof using.
intros k r v m FP.
pose proof (free_entry_st_ok k r v m FP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9).
assert (HS : st_ok src0segs (EV (xvf v)) (ss_az0 k r)
(mkst (fv_regs v) (Z_to_bv 64 src0_A_malloc_allzerop) m (seg_rom src0segs))).
{ split; [exact H1|]. split; [reflexivity|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [| exact H9].
split; [destruct k, r; vm_compute; reflexivity|]. split.
- apply Forall_map. eapply Forall_impl; [| exact Hok]. intros x Hx. apply region_ok_nowin. exact Hx.
- apply pairwise_nowin. exact Hpd. }
pose proof (az_cond_ok k r v m FP) as HC. unfold ss_az.
destruct k; unfold az_cond, c_lo, c_hi in *; apply st_ok_add_cond; first [exact HS | exact HC].
Qed.
Definition az_true (k : kcase) (v : fvals) : Prop :=
match k with K3b => True | K3a => 4096 * fv_ml v - 16 < 16 * fv_scl v | _ => False end.
Lemma fetch_az_ret : forall k, fetch_word src0segs (Z_to_bv 64 (AZ_RET k)) = Some (0x00008067%bv : bv 32).
Proof using. intros k. destruct k; apply fetch_lit; vm_compute; reflexivity. Qed.
Lemma decode_az_ret : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof using. vm_refl_bv. Qed.
Lemma az_a0_true : forall k r v m, free_pre k r v m ->
sv_denot (EV (xvf v)) (az_a0 k) <> Z_to_bv 64 0 -> az_true k v.
Proof using.
intros k r v m FP Hnz. pose proof (fp_k _ _ _ _ FP) as K. destruct k; cbn [az_a0 az_true] in *.
- apply Hnz. reflexivity.
- apply Hnz. reflexivity.
- destruct (Z_lt_le_dec (4096 * fv_ml v - 16) (16 * fv_scl v)) as [H|H]; [exact H|].
exfalso. apply Hnz. weq. den. rewrite alu64_sltu, alu64_sll, !lit64_small by lin.
change (4 mod 64) with 4. unfold sll64, sltu. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite (Z.mod_small (fv_scl v * 16)) by lin.
destruct (4096 * fv_ml v + -16 <? fv_scl v * 16) eqn:Elt; [apply Z.ltb_lt in Elt; lia | reflexivity].
- exact I.
Qed.
Theorem az_SR : forall k r v m md, free_pre k r v m -> YK0s.ret_ok (getr (fv_regs v) 1) ->
m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg (mkst (fv_regs v) (Z_to_bv 64 src0_A_malloc_allzerop) m (seg_rom src0segs)) md)
(fun c' => exists regs', c' = mkCfg (mkst regs' (getr (fv_regs v) 1) m (seg_rom src0segs)) md /\
(forall i : reg, (bv_unsigned i < 10 \/ 16 < bv_unsigned i) -> getr regs' i = getr (fv_regs v) i) /\
(getr regs' 10 <> Z_to_bv 64 0 -> az_true k v)).
Proof using.
intros k r v m md FP Hra Hh Hlz.
destruct (az_facts k r) as (Hrun & Hkeep & Ha0 & Hrv).
eapply SR_bind; [exact (SR_run_to (AZ_RET k) _ _ _ _ md (az_entry k r v m FP) Hrun Hh Hlz)|].
intros c' (ms1 & -> & HS1 & HF1).
assert (Hm1 : ms_mem ms1 = m).
{ apply FunctionalExtensionality.functional_extensionality. intros x.
exact (HF1 x (in_wrange_nowin _ (free_mem k r) _)). }
destruct Hrun as [_ Hpc].
rewrite (st_ok_mkst src0segs _ _ _ HS1 Hrv), Hm1, Hpc.
assert (KEEP : forall i : reg, (bv_unsigned i < 10 \/ 16 < bv_unsigned i) -> getr (ms_regs ms1) i = getr (fv_regs v) i).
{ intros i Hi. rewrite (st_ok_reg src0segs _ _ _ i HS1), (free_regs_ok v i). f_equal. apply keep_get; assumption. }
assert (A0 : getr (ms_regs ms1) 10 = sv_denot (EV (xvf v)) (az_a0 k)).
{ rewrite (st_ok_reg src0segs _ _ _ 10%bv HS1). rewrite <- Ha0. reflexivity. }
assert (R1e : getr (ms_regs ms1) 1 = getr (fv_regs v) 1) by (apply KEEP; left; reflexivity).
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
{ eapply step_jalr_x0; [apply fetch_az_ret | reflexivity | exact decode_az_ret | exact R1e]. }
cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hra. rewrite Hra.
apply SR_ret. exists (ms_regs ms1). split; [reflexivity|]. split; [exact KEEP|].
intros Hnz. rewrite A0 in Hnz. exact (az_a0_true k r v m FP Hnz).
Qed.
Lemma az_true_allzero : forall A g am idx fr regs L a glen, WF A -> usedX [] A g am -> 0 <= idx <= am_last am ->
ss_fr (nth_slot am idx) = Some fr ->
az_true (kcase_of am) (fv_of regs L g am idx fr a glen) -> allzero_block A (frame_ptr am idx fr) = true.
Proof using.
intros A g am idx fr regs L a glen HW Hu Hidx Hfr Ht.
unfold allzero_block. rewrite (find_frame_in_spec [] None U0 A HW g am idx fr Hu Hidx Hfr).
pose proof (proj1 (usedX_MT _ _ _ _ Hu)) as Mg. unfold MT in Mg. rewrite Mg.
pose proof (inv_groups HW g am Hu) as (_ & _ & _ & Gcl & _).
assert (Hsc : am_sc am = 63 \/ 0 <= am_sc am < 48) by (destruct Gcl as [(C & _)|(C & _)]; [left|right]; exact C).
unfold kcase_of, az_true, fv_of in Ht. cbn [fv_ml fv_scl] in Ht.
destruct (am_sc am =? 63) eqn:E63.
- apply Z.eqb_eq in E63. rewrite E63. reflexivity.
- apply Z.eqb_neq in E63.
destruct (am_maplen am =? 0) eqn:Eml; [destruct Ht|].
destruct (am_last am =? 0) eqn:El; [|destruct Ht].
apply orb_true_iff. right. apply Z.ltb_lt. unfold stride_of. rewrite El, Eml. cbn [andb negb].
unfold scl_of in Ht. replace (am_sc am <? 48) with true in Ht by (symmetry; apply Z.ltb_lt; lia).
unfold class_size, UNIT. lia.
Qed.
End a.
