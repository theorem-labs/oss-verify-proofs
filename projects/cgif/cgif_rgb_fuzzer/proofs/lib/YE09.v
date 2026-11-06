(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8v YE1o YE1p YE07 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition A_fwrite {imgk : img} : Z := (0x97a04 + D_10ec).
Definition FW_STK : Z := 176.
Definition F_STDERR {imgk : img} : Z := (0xa6750 + D_10f0).
Definition STDERR_BUF {imgk : img} : Z := (0x5fd858 + D_10c0).
Definition A_GOT_canary {imgk : img} : Z := (0xa2e10 + D_10f0).
Definition A_canary {imgk : img} : Z := (0x5fd190 + D_10c0).
Definition FILE_SZ : Z := 232.
Definition stderr_fields {imgk : img} : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, (0x96d9c + D_10ec)); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, (0x96ee8 + D_10ec)); (80, 8%N, (0x96ee0 + D_10ec)); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 2);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stderr_fields_after {imgk : img} : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, (0x96d9c + D_10ec)); (32, 8%N, STDERR_BUF); (40, 8%N, STDERR_BUF); (48, 8%N, 0);
(56, 8%N, STDERR_BUF); (64, 8%N, 0); (72, 8%N, (0x96ee8 + D_10ec)); (80, 8%N, (0x96ee0 + D_10ec)); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0);
(112, 8%N, 0); (120, 8%N, 2); (128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition file_is {imgk : img} (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem tfxsegs m (F_STDERR + o) (N.to_nat n) v end) flds.
Definition stderr_pristine {imgk : img} : (word -> option byte) -> Prop := file_is stderr_fields.
Definition stderr_written {imgk : img} : (word -> option byte) -> Prop := file_is stderr_fields_after.
Definition fw_file_chunks {imgk : img} : list YQ0b.chunk :=
map (fun f => match f with (o, n, v) => YQ0b.mkChunk (F_STDERR + o) (CVal n (SLit v)) end) stderr_fields.
Definition fw_regions {imgk : img} : smem :=
[ YQ0b.mkRegion (Some 2%nat) (- FW_STK) 0 (- FW_STK) 0 [];
YQ0b.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ) fw_file_chunks;
YQ0b.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YQ0b.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YQ0b.mkRegion None A_canary (A_canary + 8) 0 0 [YQ0b.mkChunk A_canary (CVal 8 (SOff 32 0))] ].
Definition fw_sr {imgk : img} : list sv := sr_set sr_atoms (13%bv : bv 5) (SLit F_STDERR).
Definition fw_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
Definition ss_fwrite {imgk : img} : sstate := mkSS A_fwrite fw_sr fw_regions None fw_facts.
Definition fw_len : sv := SMd M_MUL (SOff 12 0) (SOff 11 0).
Definition fw_vl1 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD fw_len (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0).
Definition ss_fw_br {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL ss_fwrite)))).
Definition fw_cond : acond := mkAC BC_LTU (SLit 0) (SAlu ALU_ADD (SAlu ALU_ADD fw_len (SLit 0)) (SLit 0)).
Definition ss_fw_ecall {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL (add_cond ss_fw_br fw_cond))))).
Definition ss_fw_after {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (wl_after ss_fw_ecall 0 (- FW_STK) 33))).
Definition ss_fw_br2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL ss_fw_after)))).
Definition fw_cond2 : acond :=
mkAC BC_EQ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD fw_len (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0)) fw_len.
Definition ss_fw_ret {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tfxmusl_tbl FUEL (add_cond ss_fw_br2 fw_cond2))))).
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis TL : TfxSyms B.
Hypothesis LAWS : AR_laws tfxsegs B.
Lemma fwrite_entry : forall (W : world tfxsegs) regs mem cval,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - FW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 13 = w64 F_STDERR ->
stderr_pristine (mrestrict (w_H W) mem) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
st_ok tfxsegs (Ereg regs [Z_to_bv 64 cval]) ss_fwrite
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_fwrite) mem (seg_rom tfxsegs))).
Proof.
intros W regs mem cval Hsp1 Hsp2 Hal Hpres H13 HF Hgot Hcan Hcv. rewrite restrict_mkst_fx. unfold ss_fwrite.
set (E := Ereg regs [Z_to_bv 64 cval]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs [Z_to_bv 64 cval]) with E.
-   unfold fw_sr. img_apply regs_ok_pin; [img_try (img_apply regs_ok_Ereg) | img_try (intros Hx; discriminate Hx) | img_try (rewrite H13; img_refl)].
- img_case; vm_compute. all: img_refl.
- unfold fw_regions. repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (region_ok_stack tfxsegs E _ 2 (spZ regs) (- FW_STK)); [img_try (img_exact E2) | img_try (unfold FW_STK; img_lia) | img_lia |].
intros a Ha. img_apply apresent_writable. img_apply Hpres. unfold FW_STK in *. img_lia.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold F_STDERR, FILE_SZ. split; [img_lia|]. split; [img_lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
img_apply (store_ok_all tfxsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDERR));
[img_try (rewrite unsigned_lit_small by (unfold F_STDERR; img_lia); unfold F_STDERR; cbn; img_lia)
| img_try (img_apply store_ok_wseg; (img_case; vm_compute); img_refl)
| img_try (rewrite !unsigned_lit_small by (unfold F_STDERR in *; img_lia); unfold F_STDERR in *; cbn; img_lia)].
* unfold fw_file_chunks, stderr_fields. cbn [map].
unfold stderr_pristine, file_is, stderr_fields in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold STDERR_BUF; img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; unfold F_STDERR, STDERR_BUF in *; assumption)]).
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_GOT_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0); [img_refl | img_try (unfold A_canary; img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_exact Hgot.
+ unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold A_canary. split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ cval); [| img_try (img_zside) | img_try (img_zside) | img_try (rewrite Z.add_0_l; img_exact Hcan)].
cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- img_apply pairwise_disjoint_of_extents. unfold fw_regions, extent_of_region.
cbn [map YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite E2.
unfold F_STDERR, FILE_SZ, A_GOT_canary, A_canary, FW_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)].
cbn [fw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
img_change (2 ^ 4) with 16. repeat split; try img_lia.
Qed.
Lemma U_add0 : forall E v, U E (SAlu ALU_ADD v (SLit 0)) = U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. img_change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (U_range E v). img_apply zcanon_id. img_lia.
Qed.
Lemma U_add0l : forall E v, U E (SAlu ALU_ADD (SLit 0) v) = U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. img_change (zcanon 0) with 0. rewrite Z.add_0_l.
pose proof (U_range E v). img_apply zcanon_id. img_lia.
Qed.
Definition le_bytes (n : nat) (v : Z) : list Z := map (fun k => le_byte v n k) (seq 0 n).
Lemma val_mem_of_lit : forall E m rs a n v,
mem_ok tfxsegs E m rs -> lit_buf tfxsegs rs (SLit a) n = Some (le_bytes n v) -> val_mem tfxsegs m a n v.
Proof.
intros E m rs a n v HM Hl k Hk.
pose proof (lit_buf_sound tfxsegs E m rs (SLit a) n _ HM Hl) as Hr. cbn [sv_denot] in Hr.
apply (proj1 (rdn_mbytes tfxsegs m n a _)) in Hr as [_ Hr].
rewrite (Hr k Hk). unfold le_bytes. rewrite !nth_error_map.
rewrite (nth_error_nth' (seq 0 n) 0%nat) by (img_try (rewrite length_seq; img_exact Hk)). rewrite seq_nth by img_exact Hk. img_refl.
Qed.
Fixpoint cells_cover (flds : list (Z * N * Z)) (lo hi : Z) : bool :=
match flds with
| [] => lo =? hi
| (o, n, _) :: r => (o =? lo) && cells_cover r (o + Z.of_N n) hi
end.
Lemma file_is_readable : forall flds m lo hi,
file_is flds m -> cells_cover flds lo hi = true ->
forall a, F_STDERR + lo <= a < F_STDERR + hi -> exists b, mbyte tfxsegs m a = Some b.
Proof.
induction flds as [|[[o n] v] r IH]; intros m lo hi HF Hc a Ha; cbn [cells_cover] in Hc.
- apply Z.eqb_eq in Hc. img_lia.
- apply andb_prop in Hc as [Ho Hc]. apply Z.eqb_eq in Ho. (subst o; cbv beta).
pose proof (Forall_inv HF) as H1. cbn beta iota in H1. apply Forall_inv_tail in HF.
destruct (Z_lt_dec a (F_STDERR + lo + Z.of_N n)) as [Hlt|Hge].
+ exists (Z_to_bv 8 (le_byte v (N.to_nat n) (Z.to_nat (a - (F_STDERR + lo))))).
replace a with (F_STDERR + lo + Z.of_nat (Z.to_nat (a - (F_STDERR + lo)))) at 1 by img_lia.
img_apply H1. pose proof (N_nat_Z n). img_lia.
+ img_apply (IH m (lo + Z.of_N n) hi HF Hc a). img_lia.
Qed.
Lemma fw_phaseA : forall (W : world tfxsegs) E ms md,
st_ok tfxsegs E ss_fwrite (restrict (w_H W) ms) ->
1 <= U E fw_len ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok_ecall tfxsegs E ss_fw_ecall (restrict (w_H W) ms1) /\
frame_of E (ss_mem ss_fwrite) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss_fwrite) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ms md HS Hl. pose proof Hwx_tfa as Hwx.
srr_run_with tfxmusl_tbl_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfxmusl_tbl_ok HS.
-   exfalso. rewrite branch_geu_U in Hc. apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
rewrite U_SLit, !U_add0 in Hc. img_change (zcanon 0) with 0 in Hc. unfold fw_len in Hl. img_lia.
- srr_run_with tfxmusl_tbl_ok HS.
img_apply SRr_ret. split; [img_refl|]. eexists _, _. split; [img_refl|]. split; [img_try (img_exact HS)|].
split.
+ eapply frame_of_trans; [| img_try (img_exact HF1) | img_try (img_exact HF)]. img_case; vm_compute. all: img_refl.
+ eapply frame_of_trans; [| img_try (img_exact HFr1) | img_try (img_exact HFr)]. img_case; vm_compute. all: img_refl.
Qed.
Lemma fw_phaseC : forall (W : world tfxsegs) Eb ms2 md2,
st_ok tfxsegs Eb ss_fw_after (restrict (w_H W) ms2) ->
SRr tfxsegs W (mkCfg ms2 md2)
(fun W' c' => W' = W /\ exists ms3 mat3,
c' = mkCfg (mkst (ms_regs ms3) (v_jalr (getr (ms_regs ms3) 1) 0) (ms_mem ms3) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md2) mat3 md2) /\
st_ok tfxsegs Eb ss_fw_ret (restrict (w_H W) ms3) /\
frame_of Eb (ss_mem ss_fw_after) (ms_mem ms2) (ms_mem ms3) /\
frame_of Eb (ss_mem ss_fw_after) (mrestrict (w_H W) (ms_mem ms2)) (mrestrict (w_H W) (ms_mem ms3))).
Proof.
intros W Eb ms2 md2 HS. pose proof Hwx_tfa as Hwx.
srr_run_with tfxmusl_tbl_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfxmusl_tbl_ok HS.
- srr_run_with tfxmusl_tbl_ok HS.
eapply (SRr_ret_at tfxsegs tfxmusl_tbl tfxmusl_tbl_ok Hwx W Eb); [img_try (img_exact HS) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. eexists _, _. split; [img_refl|]. split; [img_try (img_exact HS)|].
split.
+ eapply frame_of_trans; [| img_try (img_exact HF1) | img_try (img_exact HF)]. img_case; vm_compute. all: img_refl.
+ eapply frame_of_trans; [| img_try (img_exact HFr1) | img_try (img_exact HFr)]. img_case; vm_compute. all: img_refl.
-   exfalso.
rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. img_apply Hc. unfold fw_len. rewrite !U_add0. img_refl.
Qed.
Theorem tfx_fwrite_at : forall ly S (W : world tfxsegs) regs mem md ch p size nmemb cval (msg : list byte) T,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + FW_STK <= spZ regs ->
(forall a, spZ regs - FW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 p -> getr regs 11 = w64 size -> getr regs 12 = w64 nmemb -> getr regs 13 = w64 F_STDERR ->
1 <= size -> 1 <= nmemb -> size * nmemb <= 2 ^ 25 ->
0 <= p -> p + size * nmemb <= kHighMemEnd ->
(p + size * nmemb <= spZ regs - FW_STK \/ spZ regs <= p) ->
(p + size * nmemb <= F_STDERR \/ F_STDERR + FILE_SZ <= p) ->
rdn tfxsegs (mrestrict (w_H W) mem) (Z_to_bv 64 p) (Z.to_nat (size * nmemb)) = Some msg ->
stderr_pristine (mrestrict (w_H W) mem) ->
(forall a, F_STDERR <= a < F_STDERR + FILE_SZ -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 nmemb ->
stderr_written (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FW_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs A_fwrite regs mem md) (t_emit (map (WriteEv ch) msg) T).
Proof.
intros ly S W regs mem md ch p size nmemb cval msg T HPRE Hstk Hpres Ha0 Ha1 Ha2 Ha3 Hsz Hnm Hl Hp0 Hphi Hpstk HpF
Hmsg HFP HFpr Hgot Hcan Hcv Hch HAI HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hstop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx.
assert (HFW : FW_STK = 176) by img_refl. assert (HFS : FILE_SZ = 232) by img_refl. assert (HFF : F_STDERR = (681808 + D_10f0)) by img_refl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
set (l := size * nmemb) in *.
assert (Hl1 : 1 <= l) by (img_try ((subst l; cbv beta); img_apply (Z.le_trans 1 (size * 1)); [img_lia | img_try (img_apply Z.mul_le_mono_nonneg_l; img_lia)])).
assert (Hszb : size <= l) by (img_try ((subst l; cbv beta); rewrite <- (Z.mul_1_r size) at 1; img_apply Z.mul_le_mono_nonneg_l; img_lia)).
assert (Hnmb : nmemb <= l) by (img_try ((subst l; cbv beta); rewrite <- (Z.mul_1_l nmemb) at 1; img_apply Z.mul_le_mono_nonneg_r; img_lia)).
unfold cfg_at. img_change (w64 A_fwrite) with (Z_to_bv 64 A_fwrite).
pose proof (fwrite_entry W regs mem cval ltac:(img_lia) ltac:(img_lia) Hal16 Hpres Ha3 HFP Hgot Hcan Hcv) as HS.
remember (Ereg regs [Z_to_bv 64 cval]) as E eqn:HE.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (img_try (intros i r Hi; (subst E; cbv beta); img_exact (ew_Ereg_nat regs _ i r Hi))).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E1. pose proof (EE 2%nat (2%bv : bv 5) eq_refl) as E2.
pose proof (EE 3%nat (3%bv : bv 5) eq_refl) as E3. pose proof (EE 4%nat (4%bv : bv 5) eq_refl) as E4.
pose proof (EE 10%nat (10%bv : bv 5) eq_refl) as E10. pose proof (EE 11%nat (11%bv : bv 5) eq_refl) as E11.
pose proof (EE 12%nat (12%bv : bv 5) eq_refl) as E12.
assert (E32 : ew E 32 = Z_to_bv 64 cval) by (img_try ((subst E; cbv beta); img_exact (ew_Ereg_extra regs _ 0))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (img_try (rewrite E2; img_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 cval]) E) by (img_try (rewrite HE; split; [img_try (intros i Hi; img_refl) | img_refl])).
assert (Ul : U E (SMd M_MUL (SOff 12 0) (SOff 11 0)) = l).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 12 nmemb) by (img_try (first [rewrite E12; img_exact Ha2 | img_lia])).
rewrite (U_atom E 11 size) by (img_try (first [rewrite E11; img_exact Ha1 | img_lia])).
replace (nmemb * size) with l by (img_try ((subst l; cbv beta); img_apply Z.mul_comm)). img_apply zcanon_id. unfold M64. img_lia. }
eapply (SRr_srealizes tfxsegs W _ _ _ (fw_phaseA W E _ md HS ltac:(img_try (unfold fw_len; rewrite Ul; img_exact Hl1))) HAI).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1.
assert (WIN : forall a, in_wrange E (ss_mem ss_fwrite) a ->
(spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ)).
{ intros a Ha. destruct (in_wrange_windows E _ a Ha) as (bb & lo & hi & Hin & Hr).
cbn in Hin. destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; inversion Hq; (subst; cbv beta); cbn [base_val] in Hr; rewrite ?Usp in Hr;
unfold F_STDERR, FILE_SZ, FW_STK, A_GOT_canary, A_canary in *; img_lia. }
pose proof HS1 as HS1c. destruct HS1c as (_ & _ & _ & _ & _ & _ & Hregs1 & Hmem1 & HG1).
assert (Hmsg1 : rdn tfxsegs (mrestrict (w_H W) (ms_mem ms1)) (Z_to_bv 64 p) (Z.to_nat l) = Some msg).
{ img_apply (rdn_agree (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) mem) p (Z.to_nat l) msg); [img_lia | img_try (rewrite Z2Nat.id by img_lia; img_lia) | | img_try (img_exact Hmsg)].
intros x Hx. img_apply HFr1. intros Hin. destruct (WIN _ Hin) as [Hw | Hw]; rewrite Z2Nat.id in Hx by img_lia; img_lia. }
pose proof (lit_buf_sound tfxsegs E (mrestrict (w_H W) (ms_mem ms1)) (ss_mem ss_fw_ecall) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem1
ltac:(img_try ((img_case; vm_compute); img_refl))) as Hfdrd.
cbn [sv_denot] in Hfdrd.
eapply (srz_sym_stdio_writev1 W E ss_fw_ecall ms1 _ (Z_to_bv 64 2) ch 0 2 (- FW_STK) F_STDERR _ (SOff 10 0) fw_vl1 msg
(map (Z_to_bv 8) [2; 0; 0; 0]) 33 T HAI1 HS1 eq_refl eq_refl eq_refl).
- img_refl.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_apply with_vm_backing_same)].
- img_refl.
- img_case; vm_compute. all: img_refl.
- img_refl.
- img_refl.
- img_refl.
- img_refl.
- img_refl.
-   match goal with |- U E ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end.
unfold fw_vl1, fw_len. rewrite U_add0l. img_refl.
- match goal with |- U E ?x = _ => let x' := img_ev constr:(x) in img_change x with x' end. rewrite U_SLit. img_refl.
- img_refl.
- img_refl.
- cbn. img_lia. - cbn. img_lia. - cbn. img_lia. - cbn. img_lia.
- img_case; vm_compute. all: img_refl.
-   cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, Ha0.
rewrite word_to_nat_U. unfold fw_vl1, fw_len. rewrite !U_add0, Ul. img_exact Hmsg1.
- unfold fw_vl1, fw_len. rewrite !U_add0, Ul. img_lia.
- unfold fw_vl1, fw_len. rewrite !U_add0, Ul, (U_atom E 10 p) by (img_try (first [rewrite E10; img_exact Ha0 | img_lia])). img_lia.
- unfold fw_vl1, fw_len. rewrite !U_add0, Ul, (U_atom E 10 p) by (img_try (first [rewrite E10; img_exact Ha0 | img_lia])). rewrite Usp. unfold FW_STK in *. img_lia.
- img_exact Hfdrd.
- img_case; vm_compute. all: img_refl.
- unfold F_STDERR. img_lia. - unfold F_STDERR. img_lia.
- rewrite Usp. unfold F_STDERR, FW_STK in *. img_lia.
- rewrite Usp. unfold FW_STK in *. img_lia. - rewrite Usp. unfold FW_STK in *. img_lia.
- img_case; vm_compute. all: img_refl.
-
intros ms2 ws mat2 HS2 HF2 HFr2 HAI2. rewrite wvb_wvb in HAI2 |- *.
img_change (wl_after ss_fw_ecall 0 (- FW_STK) 33) with ss_fw_after in HS2.
eapply (SRr_srealizes tfxsegs W _ _ T (fw_phaseC W _ ms2 _ HS2) HAI2).
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. rewrite wvb_wvb in HAI3 |- *.
remember (havoc E 33 ws) as Eb eqn:HEb in *.
assert (OLD : forall i, (i < 33)%nat -> ew Eb i = ew E i) by (img_try (intros i Hi; rewrite HEb; img_apply ew_havoc_old; img_exact Hi)).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 cval]) Eb) by (img_try (rewrite HEb, HE; img_apply env_agree_havoc_ge; [img_try ((img_case; cbv); img_lia) | img_try (split; [intros i Hi; img_refl | img_refl])])).
assert (Usp' : bv_unsigned (ew Eb 2) = spZ regs) by (img_try (rewrite OLD by ((img_case; cbv); img_lia); img_exact Usp)).
set (mem3 := ms_mem ms3) in *. set (regs3 := ms_regs ms3) in *.
assert (WIN2 : forall Ex (rs : smem) a, (Ex = E \/ Ex = Eb) ->
(rs = ss_mem ss_fwrite \/ rs = ss_mem ss_fw_ecall \/ rs = ss_mem ss_fw_after) ->
in_wrange Ex rs a -> (spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ)).
{ intros Ex rs a HEx Hrs Ha. destruct (in_wrange_windows Ex _ a Ha) as (bb & lo & hi & Hin & Hr).
assert (Hu2 : bv_unsigned (ew Ex 2) = spZ regs) by (img_try (destruct HEx as [-> | ->]; [img_try (img_exact Usp) | img_try (img_exact Usp')])).
destruct Hrs as [-> | [-> | ->]]; cbn in Hin;
(destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; inversion Hq; (subst; cbv beta); cbn [base_val] in Hr; rewrite ?Hu2 in Hr;
unfold F_STDERR, FILE_SZ, FW_STK, A_GOT_canary, A_canary in *; img_lia). }
assert (OUTr : forall x : word, ~ (spZ regs - FW_STK <= bv_unsigned x < spZ regs) -> ~ (F_STDERR <= bv_unsigned x < F_STDERR + FILE_SZ) ->
mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem x).
{ intros x Hx1 Hx2.
rewrite (HFr3 x) by (img_try (intros Hin; destruct (WIN2 Eb _ _ (or_intror eq_refl) (or_intror (or_intror eq_refl)) Hin); img_lia)).
rewrite (HFr2 x) by (img_try (intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) Hin); img_lia)).
img_apply HFr1. intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_introl eq_refl) Hin); img_lia. }
assert (OUT : forall x : word, ~ (spZ regs - FW_STK <= bv_unsigned x < spZ regs) -> ~ (F_STDERR <= bv_unsigned x < F_STDERR + FILE_SZ) ->
mem3 x = mem x).
{ intros x Hx1 Hx2.
rewrite (HF3 x) by (img_try (intros Hin; destruct (WIN2 Eb _ _ (or_intror eq_refl) (or_intror (or_intror eq_refl)) Hin); img_lia)).
rewrite (HF2 x) by (img_try (intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) Hin); img_lia)).
img_apply HF1. intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_introl eq_refl) Hin); img_lia. }
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FW_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview tfxsegs (w_H W) mem3 a = aview tfxsegs (w_H W) mem a).
{ intros a Hr Hy1 Hy2. img_apply aview_eq_of. img_apply OUTr; rewrite unsigned_lit_small by img_lia; assumption. }
assert (PRES3s : forall a, spZ regs - FW_STK <= a < spZ regs -> apresent (w_H W) mem3 a).
{ intros a Ha.
img_apply (apresent_of_writable (w_H W) mem3 a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
pose proof (Forall_inv Hrs) as Hr0. destruct Hr0 as (_ & _ & Hw0 & _).
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val restrict ms_mem] in Hw0. rewrite Usp' in Hw0.
replace a with (spZ regs + (a - spZ regs)) by img_lia. img_apply Hw0. unfold FW_STK in *. img_lia. }
assert (HFILE3 : stderr_written (mrestrict (w_H W) mem3)).
{ destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _).
unfold stderr_written, file_is, stderr_fields_after.
repeat img_apply Forall_cons; try img_apply Forall_nil;
(eapply (val_mem_of_lit Eb (mrestrict (w_H W) mem3) (ss_mem ss_fw_ret) _ _ _ Hmem3); (img_case; vm_compute); img_refl). }
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (10%bv : bv 5) Q10.
fold regs3 in Q1, Q10. rewrite OLD in Q1 by (img_try ((img_case; cbv); img_lia)). rewrite E1 in Q1.
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat3)) as MF3.
replace (v_jalr (getr regs3 1) 0) with (w64 (raZ regs))
by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
img_apply (HK regs3 mem3 (with_vm_backing (m_vm_lazy md) mat3 md)).
+
img_apply (al_frame _ _ LAWS ly S W mem md mem3 _ HAR).
* intros a Hr Hown. img_apply AV3; [img_try (img_exact Hr) | |].
-- intros Hw'. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_lia) Hown).
-- intros Hw'. img_exact (HFpr a Hw' Hown).
* assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfxsegs (w_H W) mem a <> None -> aview tfxsegs (w_H W) mem3 a <> None).
{ intros a Hr Hv.
assert (CASE : (spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ) \/
(~ (spZ regs - FW_STK <= a < spZ regs) /\ ~ (F_STDERR <= a < F_STDERR + FILE_SZ))) by img_lia.
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* img_apply aview_some_of_apresent. img_apply PRES3s. img_exact Hin.
*
destruct (file_is_readable _ _ 0 FILE_SZ HFILE3 ltac:(img_try ((img_case; vm_compute); img_refl)) a ltac:(img_lia)) as [b Hb].
unfold aview. rewrite Hb. cbn. discriminate.
* rewrite AV3; assumption. }
intros a Hv. rewrite (aview_mod _ mem3 a). img_apply PV; [img_try (img_apply Z.mod_pos_bound; img_lia) | img_try (rewrite <- aview_mod; img_exact Hv)].
* img_apply MF3. * img_apply MF3. * img_apply MF3.
*
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.
assert (Hf' : ~ (F_STDERR <= a < F_STDERR + FILE_SZ)) by (img_try (unfold in_band_rw, F_STDERR, FILE_SZ, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; img_lia)).
assert (CASE : (spZ regs - FW_STK <= a < spZ regs) \/ ~ (spZ regs - FW_STK <= a < spZ regs)) by img_lia.
destruct CASE as [Hin|Hout]; [img_try (exfalso; destruct (Hpres a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh)|].
rewrite OUT; [img_refl | |]; rewrite unsigned_lit_small by (img_try (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)); assumption.
+
img_exact (aregs_preserved_of_st_ok _ Eb _ _ regs [Z_to_bv 64 cval] HS3 HAEb ltac:(img_try ((img_case; vm_compute); img_refl))).
+ apply same_but_materialized_trans with (with_vm_backing (m_vm_lazy md) mat1 md); [img_try (img_apply with_vm_backing_same)|].
rewrite <- (wvb_collapse (m_vm_lazy md) mat3 mat1 md). img_apply with_vm_backing_same.
+
rewrite Q10. rewrite (OLD 11%nat) by (img_try ((img_case; cbv); img_lia)). rewrite (OLD 12%nat) by (img_try ((img_case; cbv); img_lia)). rewrite E11, E12, Ha1, Ha2.
img_apply bv_eq. unfold alu64, alu, w64, bv_ltu. rewrite !unsigned_lit_small by img_lia.
replace (size <? 1) with false by (img_try (symmetry; img_apply Z.ltb_ge; img_lia)).
rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small nmemb) by img_lia.
img_change ((0 mod 2 ^ 64 + -1 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by img_lia. img_apply Z.mod_small. img_lia.
+ img_exact HFILE3.
+   intros a Hr Hx1 Hx2. img_apply AV3; assumption.
+
assert (PVp : forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a).
{ intros a Hr HnF Hp.
assert (CASE : (spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ) \/
(~ (spZ regs - FW_STK <= a < spZ regs) /\ ~ (F_STDERR <= a < F_STDERR + FILE_SZ))) by img_lia.
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
-- img_apply PRES3s. img_exact Hin.
-- exfalso. img_exact (HnF Hin).
-- destruct Hp as [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. exists b. rewrite OUT; [img_try (img_exact Hb)| |]; rewrite unsigned_lit_small by img_lia; assumption. }
img_exact PVp.
+ img_exact HAI3.
Qed.
End S.
End c.
