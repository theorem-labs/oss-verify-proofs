(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AE3e AE3f AE3g AE6g AF0x AE20 AE2y AE7f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition A_fwrite : Z := 0x93808.
Definition FW_STK : Z := 176.
Definition F_STDERR : Z := 0xa2578.
Definition STDERR_BUF : Z := 0x5f9698.
Definition A_GOT_canary : Z := 0x9ec38.
Definition A_canary : Z := 0x5f8fd0.
Definition FILE_SZ : Z := 232.
Definition stderr_fields : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x92ba0); (32, 8%N, 0); (40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0); (64, 8%N, 0);
(72, 8%N, 0x92cec); (80, 8%N, 0x92ce4); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 2);
(128, 8%N, 0); (136, 4%N, 0); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition stderr_fields_after : list (Z * N * Z) :=
[(0, 4%N, 5); (4, 4%N, 0); (8, 8%N, 0); (16, 8%N, 0); (24, 8%N, 0x92ba0); (32, 8%N, STDERR_BUF); (40, 8%N, STDERR_BUF); (48, 8%N, 0);
(56, 8%N, STDERR_BUF); (64, 8%N, 0); (72, 8%N, 0x92cec); (80, 8%N, 0x92ce4); (88, 8%N, STDERR_BUF); (96, 8%N, 0); (104, 8%N, 0);
(112, 8%N, 0); (120, 8%N, 2); (128, 8%N, 0); (136, 4%N, 0xffffffff); (140, 4%N, 0xffffffff); (144, 8%N, 0xffffffff);
(152, 8%N, 0); (160, 8%N, 0); (168, 8%N, 0); (176, 8%N, 0); (184, 8%N, 0); (192, 8%N, 0); (200, 8%N, 0); (208, 8%N, 0);
(216, 8%N, 0); (224, 8%N, 0)].
Definition file_is (flds : list (Z * N * Z)) (m : word -> option byte) : Prop :=
Forall (fun f => match f with (o, n, v) => val_mem tfibsegs m (F_STDERR + o) (N.to_nat n) v end) flds.
Definition stderr_pristine : (word -> option byte) -> Prop := file_is stderr_fields.
Definition stderr_written : (word -> option byte) -> Prop := file_is stderr_fields_after.
Definition fw_file_chunks : list YP09.chunk :=
map (fun f => match f with (o, n, v) => YP09.mkChunk (F_STDERR + o) (CVal n (SLit v)) end) stderr_fields.
Definition fw_regions : smem :=
[ YP09.mkRegion (Some 2%nat) (- FW_STK) 0 (- FW_STK) 0 [];
YP09.mkRegion None F_STDERR (F_STDERR + FILE_SZ) F_STDERR (F_STDERR + FILE_SZ) fw_file_chunks;
YP09.mkRegion None A_GOT_canary (A_GOT_canary + 8) 0 0 [YP09.mkChunk A_GOT_canary (CVal 8 (SLit A_canary))];
YP09.mkRegion None A_canary (A_canary + 8) 0 0 [YP09.mkChunk A_canary (CVal 8 (SOff 32 0))] ].
Definition fw_sr : list sv := sr_set sr_atoms (13%bv : bv 5) (SLit F_STDERR).
Definition fw_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
Definition ss_fwrite : sstate := mkSS A_fwrite fw_sr fw_regions None fw_facts.
Definition fw_len : sv := SMd M_MUL (SOff 12 0) (SOff 11 0).
Definition fw_vl1 : sv := SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD fw_len (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0).
Definition ss_fw_br : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ss_fwrite).
Definition fw_cond : acond := mkAC BC_LTU (SLit 0) (SAlu ALU_ADD (SAlu ALU_ADD fw_len (SLit 0)) (SLit 0)).
Definition ss_fw_ecall : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (add_cond ss_fw_br fw_cond)).
Definition ss_fw_after : sstate := Eval vm_compute in wl_after ss_fw_ecall 0 (- FW_STK) 33.
Definition ss_fw_br2 : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL ss_fw_after).
Definition fw_cond2 : acond :=
mkAC BC_EQ (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD fw_len (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0)) (SLit 0)) fw_len.
Definition ss_fw_ret : sstate := Eval vm_compute in fst (sym_runN tfibsegs tfibmusl_tbl FUEL (add_cond ss_fw_br2 fw_cond2)).
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma fwrite_entry : forall (W : world tfibsegs) regs mem cval,
2 ^ 44 <= spZ regs -> spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - FW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 13 = w64 F_STDERR ->
stderr_pristine (mrestrict (w_H W) mem) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
st_ok tfibsegs (Ereg regs [Z_to_bv 64 cval]) ss_fwrite
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_fwrite) mem (seg_rom tfibsegs))).
Proof.
intros W regs mem cval Hsp1 Hsp2 Hal Hpres H13 HF Hgot Hcan Hcv. rewrite restrict_mkst_fx. unfold ss_fwrite.
set (E := Ereg regs [Z_to_bv 64 cval]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 0)).
apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 cval]) with E.
-   unfold fw_sr. apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx; discriminate Hx | rewrite H13; reflexivity].
- vm_compute. reflexivity.
- unfold fw_regions. repeat apply Forall_cons; try apply Forall_nil.
+ apply (region_ok_stack tfibsegs E _ 2 (spZ regs) (- FW_STK)); [exact E2 | unfold FW_STK; lia | lia |].
intros a Ha. apply apresent_writable. apply Hpres. unfold FW_STK in *. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold F_STDERR, FILE_SZ. split; [lia|]. split; [lia|]. split.
* intros o Ho. rewrite Z.add_0_l. unfold writable_at.
apply (store_ok_all tfibsegs (mrestrict (w_H W) mem) 232 (Z_to_bv 64 F_STDERR));
[rewrite unsigned_lit_small by (unfold F_STDERR; lia); unfold F_STDERR; cbn; lia
| apply store_ok_wseg; vm_compute; reflexivity
| rewrite !unsigned_lit_small by (unfold F_STDERR in *; lia); unfold F_STDERR in *; cbn; lia].
* unfold fw_file_chunks, stderr_fields. cbn [map].
unfold stderr_pristine, file_is, stderr_fields in HF.
repeat match type of HF with Forall _ (_ :: _) =>
let h := fresh "HFf" in pose proof (Forall_inv HF) as h; cbn beta iota in h; apply Forall_inv_tail in HF end.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold STDERR_BUF; zside | zside | rewrite Z.add_0_l; unfold F_STDERR, STDERR_BUF in *; assumption]).
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_GOT_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0); [reflexivity | unfold A_canary; zside | zside |].
rewrite Z.add_0_l. exact Hgot.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold A_canary. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply (chunk_ok_val tfibsegs E _ 0 _ 8 _ cval); [| zside | zside | rewrite Z.add_0_l; exact Hcan].
cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- apply pairwise_disjoint_of_extents. unfold fw_regions, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold F_STDERR, FILE_SZ, A_GOT_canary, A_canary, FW_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
cbn [fw_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
change (2 ^ 4) with 16. repeat split; try lia.
Qed.
Lemma U_add0 : forall E v, U E (SAlu ALU_ADD v (SLit 0)) = U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r.
pose proof (U_range E v). apply zcanon_id. lia.
Qed.
Lemma U_add0l : forall E v, U E (SAlu ALU_ADD (SLit 0) v) = U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_l.
pose proof (U_range E v). apply zcanon_id. lia.
Qed.
Definition le_bytes (n : nat) (v : Z) : list Z := map (fun k => le_byte v n k) (seq 0 n).
Lemma val_mem_of_lit : forall E m rs a n v,
mem_ok tfibsegs E m rs -> lit_buf tfibsegs rs (SLit a) n = Some (le_bytes n v) -> val_mem tfibsegs m a n v.
Proof.
intros E m rs a n v HM Hl k Hk.
pose proof (lit_buf_sound tfibsegs E m rs (SLit a) n _ HM Hl) as Hr. cbn [sv_denot] in Hr.
apply (proj1 (rdn_mbytes tfibsegs m n a _)) in Hr as [_ Hr].
rewrite (Hr k Hk). unfold le_bytes. rewrite !nth_error_map.
rewrite (nth_error_nth' (seq 0 n) 0%nat) by (rewrite length_seq; exact Hk). rewrite seq_nth by exact Hk. reflexivity.
Qed.
Fixpoint cells_cover (flds : list (Z * N * Z)) (lo hi : Z) : bool :=
match flds with
| [] => lo =? hi
| (o, n, _) :: r => (o =? lo) && cells_cover r (o + Z.of_N n) hi
end.
Lemma file_is_readable : forall flds m lo hi,
file_is flds m -> cells_cover flds lo hi = true ->
forall a, F_STDERR + lo <= a < F_STDERR + hi -> exists b, mbyte tfibsegs m a = Some b.
Proof.
induction flds as [|[[o n] v] r IH]; intros m lo hi HF Hc a Ha; cbn [cells_cover] in Hc.
- apply Z.eqb_eq in Hc. lia.
- apply andb_prop in Hc as [Ho Hc]. apply Z.eqb_eq in Ho. subst o.
pose proof (Forall_inv HF) as H1. cbn beta iota in H1. apply Forall_inv_tail in HF.
destruct (Z_lt_dec a (F_STDERR + lo + Z.of_N n)) as [Hlt|Hge].
+ exists (Z_to_bv 8 (le_byte v (N.to_nat n) (Z.to_nat (a - (F_STDERR + lo))))).
replace a with (F_STDERR + lo + Z.of_nat (Z.to_nat (a - (F_STDERR + lo)))) at 1 by lia.
apply H1. pose proof (N_nat_Z n). lia.
+ apply (IH m (lo + Z.of_N n) hi HF Hc a). lia.
Qed.
Lemma fw_phaseA : forall (W : world tfibsegs) E ms md,
st_ok tfibsegs E ss_fwrite (restrict (w_H W) ms) ->
1 <= U E fw_len ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok_ecall tfibsegs E ss_fw_ecall (restrict (w_H W) ms1) /\
frame_of E (ss_mem ss_fwrite) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss_fwrite) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ms md HS Hl. pose proof Hwx_tfa as Hwx.
srr_run_with tfibmusl_tbl_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibmusl_tbl_ok HS.
-   exfalso. rewrite branch_geu_U in Hc. apply negb_true_iff in Hc. apply Z.ltb_ge in Hc.
rewrite U_SLit, !U_add0 in Hc. change (zcanon 0) with 0 in Hc. unfold fw_len in Hl. lia.
- srr_run_with tfibmusl_tbl_ok HS.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [exact HS|].
split.
+ eapply frame_of_trans; [| exact HF1 | exact HF]. vm_compute. reflexivity.
+ eapply frame_of_trans; [| exact HFr1 | exact HFr]. vm_compute. reflexivity.
Qed.
Lemma fw_phaseC : forall (W : world tfibsegs) Eb ms2 md2,
st_ok tfibsegs Eb ss_fw_after (restrict (w_H W) ms2) ->
SRr tfibsegs W (mkCfg ms2 md2)
(fun W' c' => W' = W /\ exists ms3 mat3,
c' = mkCfg (mkst (ms_regs ms3) (v_jalr (getr (ms_regs ms3) 1) 0) (ms_mem ms3) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md2) mat3 md2) /\
st_ok tfibsegs Eb ss_fw_ret (restrict (w_H W) ms3) /\
frame_of Eb (ss_mem ss_fw_after) (ms_mem ms2) (ms_mem ms3) /\
frame_of Eb (ss_mem ss_fw_after) (mrestrict (w_H W) (ms_mem ms2)) (mrestrict (w_H W) (ms_mem ms3))).
Proof.
intros W Eb ms2 md2 HS. pose proof Hwx_tfa as Hwx.
srr_run_with tfibmusl_tbl_ok HS. rename HF into HF1. rename HFr into HFr1.
srr_branch_with tfibmusl_tbl_ok HS.
- srr_run_with tfibmusl_tbl_ok HS.
eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W Eb); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [exact HS|].
split.
+ eapply frame_of_trans; [| exact HF1 | exact HF]. vm_compute. reflexivity.
+ eapply frame_of_trans; [| exact HFr1 | exact HFr]. vm_compute. reflexivity.
-   exfalso.
rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. unfold fw_len. rewrite !U_add0. reflexivity.
Qed.
Theorem tfib_fwrite_at : forall ly S (W : world tfibsegs) regs mem md ch p size nmemb cval (msg : list byte) T,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + FW_STK <= spZ regs ->
(forall a, spZ regs - FW_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 p -> getr regs 11 = w64 size -> getr regs 12 = w64 nmemb -> getr regs 13 = w64 F_STDERR ->
1 <= size -> 1 <= nmemb -> size * nmemb <= 2 ^ 25 ->
0 <= p -> p + size * nmemb <= kHighMemEnd ->
(p + size * nmemb <= spZ regs - FW_STK \/ spZ regs <= p) ->
(p + size * nmemb <= F_STDERR \/ F_STDERR + FILE_SZ <= p) ->
rdn tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 p) (Z.to_nat (size * nmemb)) = Some msg ->
stderr_pristine (mrestrict (w_H W) mem) ->
(forall a, F_STDERR <= a < F_STDERR + FILE_SZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 nmemb ->
stderr_written (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FW_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_fwrite regs mem md) (t_emit (map (WriteEv ch) msg) T).
Proof.
intros ly S W regs mem md ch p size nmemb cval msg T HPRE Hstk Hpres Ha0 Ha1 Ha2 Ha3 Hsz Hnm Hl Hp0 Hphi Hpstk HpF
Hmsg HFP HFpr Hgot Hcan Hcv Hch HAI HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Hstop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx.
assert (HFW : FW_STK = 176) by reflexivity. assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFF : F_STDERR = 664952) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (l := size * nmemb) in *.
assert (Hl1 : 1 <= l) by (subst l; apply (Z.le_trans 1 (size * 1)); [lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hszb : size <= l) by (subst l; rewrite <- (Z.mul_1_r size) at 1; apply Z.mul_le_mono_nonneg_l; lia).
assert (Hnmb : nmemb <= l) by (subst l; rewrite <- (Z.mul_1_l nmemb) at 1; apply Z.mul_le_mono_nonneg_r; lia).
unfold cfg_at. change (w64 A_fwrite) with (Z_to_bv 64 A_fwrite).
pose proof (fwrite_entry W regs mem cval ltac:(lia) ltac:(lia) Hal16 Hpres Ha3 HFP Hgot Hcan Hcv) as HS.
remember (Ereg regs [Z_to_bv 64 cval]) as E eqn:HE.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
by (intros i r Hi; subst E; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E1. pose proof (EE 2%nat (2%bv : bv 5) eq_refl) as E2.
pose proof (EE 3%nat (3%bv : bv 5) eq_refl) as E3. pose proof (EE 4%nat (4%bv : bv 5) eq_refl) as E4.
pose proof (EE 10%nat (10%bv : bv 5) eq_refl) as E10. pose proof (EE 11%nat (11%bv : bv 5) eq_refl) as E11.
pose proof (EE 12%nat (12%bv : bv 5) eq_refl) as E12.
assert (E32 : ew E 32 = Z_to_bv 64 cval) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 cval]) E) by (rewrite HE; split; [intros i Hi; reflexivity | reflexivity]).
assert (Ul : U E (SMd M_MUL (SOff 12 0) (SOff 11 0)) = l).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 12 nmemb) by (first [rewrite E12; exact Ha2 | lia]).
rewrite (U_atom E 11 size) by (first [rewrite E11; exact Ha1 | lia]).
replace (nmemb * size) with l by (subst l; apply Z.mul_comm). apply zcanon_id. unfold M64. lia. }
eapply (SRr_srealizes tfibsegs W _ _ _ (fw_phaseA W E _ md HS ltac:(unfold fw_len; rewrite Ul; exact Hl1)) HAI).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1.
assert (WIN : forall a, in_wrange E (ss_mem ss_fwrite) a ->
(spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ)).
{ intros a Ha. destruct (in_wrange_windows E _ a Ha) as (bb & lo & hi & Hin & Hr).
cbn in Hin. destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; inversion Hq; subst; cbn [base_val] in Hr; rewrite ?Usp in Hr;
unfold F_STDERR, FILE_SZ, FW_STK, A_GOT_canary, A_canary in *; lia. }
pose proof HS1 as HS1c. destruct HS1c as (_ & _ & _ & _ & _ & _ & Hregs1 & Hmem1 & HG1).
assert (Hmsg1 : rdn tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (Z_to_bv 64 p) (Z.to_nat l) = Some msg).
{ apply (rdn_agree (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W) mem) p (Z.to_nat l) msg); [lia | rewrite Z2Nat.id by lia; lia | | exact Hmsg].
intros x Hx. apply HFr1. intros Hin. destruct (WIN _ Hin) as [Hw | Hw]; rewrite Z2Nat.id in Hx by lia; lia. }
pose proof (lit_buf_sound tfibsegs E (mrestrict (w_H W) (ms_mem ms1)) (ss_mem ss_fw_ecall) (SLit (F_STDERR + 120)) 4 [2; 0; 0; 0] Hmem1
ltac:(vm_compute; reflexivity)) as Hfdrd.
cbn [sv_denot] in Hfdrd.
eapply (srz_sym_stdio_writev1 W E ss_fw_ecall ms1 _ (Z_to_bv 64 2) ch 0 2 (- FW_STK) F_STDERR _ (SOff 10 0) fw_vl1 msg
(map (Z_to_bv 8) [2; 0; 0; 0]) 33 T HAI1 HS1 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
-   match goal with |- U E ?x = _ => let x' := eval vm_compute in x in change x with x' end.
unfold fw_vl1, fw_len. rewrite U_add0l. reflexivity.
- match goal with |- U E ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-   cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, Ha0.
rewrite word_to_nat_U. unfold fw_vl1, fw_len. rewrite !U_add0, Ul. exact Hmsg1.
- unfold fw_vl1, fw_len. rewrite !U_add0, Ul. lia.
- unfold fw_vl1, fw_len. rewrite !U_add0, Ul, (U_atom E 10 p) by (first [rewrite E10; exact Ha0 | lia]). lia.
- unfold fw_vl1, fw_len. rewrite !U_add0, Ul, (U_atom E 10 p) by (first [rewrite E10; exact Ha0 | lia]). rewrite Usp. unfold FW_STK in *. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDERR. lia. - unfold F_STDERR. lia.
- rewrite Usp. unfold F_STDERR, FW_STK in *. lia.
- rewrite Usp. unfold FW_STK in *. lia. - rewrite Usp. unfold FW_STK in *. lia.
- vm_compute. reflexivity.
-
intros ms2 ws mat2 HS2 HF2 HFr2 HAI2. rewrite wvb_wvb in HAI2 |- *.
change (wl_after ss_fw_ecall 0 (- FW_STK) 33) with ss_fw_after in HS2.
eapply (SRr_srealizes tfibsegs W _ _ T (fw_phaseC W _ ms2 _ HS2) HAI2).
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3. rewrite wvb_wvb in HAI3 |- *.
remember (havoc E 33 ws) as Eb eqn:HEb in *.
assert (OLD : forall i, (i < 33)%nat -> ew Eb i = ew E i) by (intros i Hi; rewrite HEb; apply ew_havoc_old; exact Hi).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 cval]) Eb) by (rewrite HEb, HE; apply env_agree_havoc_ge; [cbv; lia | split; [intros i Hi; reflexivity | reflexivity]]).
assert (Usp' : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLD by (cbv; lia); exact Usp).
set (mem3 := ms_mem ms3) in *. set (regs3 := ms_regs ms3) in *.
assert (WIN2 : forall Ex (rs : smem) a, (Ex = E \/ Ex = Eb) ->
(rs = ss_mem ss_fwrite \/ rs = ss_mem ss_fw_ecall \/ rs = ss_mem ss_fw_after) ->
in_wrange Ex rs a -> (spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ)).
{ intros Ex rs a HEx Hrs Ha. destruct (in_wrange_windows Ex _ a Ha) as (bb & lo & hi & Hin & Hr).
assert (Hu2 : bv_unsigned (ew Ex 2) = spZ regs) by (destruct HEx as [-> | ->]; [exact Usp | exact Usp']).
destruct Hrs as [-> | [-> | ->]]; cbn in Hin;
(destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; inversion Hq; subst; cbn [base_val] in Hr; rewrite ?Hu2 in Hr;
unfold F_STDERR, FILE_SZ, FW_STK, A_GOT_canary, A_canary in *; lia). }
assert (OUTr : forall x : word, ~ (spZ regs - FW_STK <= bv_unsigned x < spZ regs) -> ~ (F_STDERR <= bv_unsigned x < F_STDERR + FILE_SZ) ->
mrestrict (w_H W) mem3 x = mrestrict (w_H W) mem x).
{ intros x Hx1 Hx2.
rewrite (HFr3 x) by (intros Hin; destruct (WIN2 Eb _ _ (or_intror eq_refl) (or_intror (or_intror eq_refl)) Hin); lia).
rewrite (HFr2 x) by (intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) Hin); lia).
apply HFr1. intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_introl eq_refl) Hin); lia. }
assert (OUT : forall x : word, ~ (spZ regs - FW_STK <= bv_unsigned x < spZ regs) -> ~ (F_STDERR <= bv_unsigned x < F_STDERR + FILE_SZ) ->
mem3 x = mem x).
{ intros x Hx1 Hx2.
rewrite (HF3 x) by (intros Hin; destruct (WIN2 Eb _ _ (or_intror eq_refl) (or_intror (or_intror eq_refl)) Hin); lia).
rewrite (HF2 x) by (intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) Hin); lia).
apply HF1. intros Hin; destruct (WIN2 E _ _ (or_introl eq_refl) (or_introl eq_refl) Hin); lia. }
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FW_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem a).
{ intros a Hr Hy1 Hy2. apply aview_eq_of. apply OUTr; rewrite unsigned_lit_small by lia; assumption. }
assert (PRES3s : forall a, spZ regs - FW_STK <= a < spZ regs -> apresent (w_H W) mem3 a).
{ intros a Ha.
apply (apresent_of_writable (w_H W) mem3 a ltac:(lia) (high_not_img a ltac:(lia))).
destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
pose proof (Forall_inv Hrs) as Hr0. destruct Hr0 as (_ & _ & Hw0 & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val restrict ms_mem] in Hw0. rewrite Usp' in Hw0.
replace a with (spZ regs + (a - spZ regs)) by lia. apply Hw0. unfold FW_STK in *. lia. }
assert (HFILE3 : stderr_written (mrestrict (w_H W) mem3)).
{ destruct HS3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _).
unfold stderr_written, file_is, stderr_fields_after.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit Eb (mrestrict (w_H W) mem3) (ss_mem ss_fw_ret) _ _ _ Hmem3); vm_compute; reflexivity). }
rreg HS3 (1%bv : bv 5) Q1. rreg HS3 (10%bv : bv 5) Q10.
fold regs3 in Q1, Q10. rewrite OLD in Q1 by (cbv; lia). rewrite E1 in Q1.
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat3)) as MF3.
replace (v_jalr (getr regs3 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
apply (HK regs3 mem3 (with_vm_backing (m_vm_lazy md) mat3 md)).
+
apply (al_frame _ _ LAWS ly S W mem md mem3 _ HAR).
* intros a Hr Hown. apply AV3; [exact Hr | |].
-- intros Hw'. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
-- intros Hw'. exact (HFpr a Hw' Hown).
* assert (PV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mem a <> None -> aview tfibsegs (w_H W) mem3 a <> None).
{ intros a Hr Hv.
assert (CASE : (spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ) \/
(~ (spZ regs - FW_STK <= a < spZ regs) /\ ~ (F_STDERR <= a < F_STDERR + FILE_SZ))) by lia.
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
* apply aview_some_of_apresent. apply PRES3s. exact Hin.
*
destruct (file_is_readable _ _ 0 FILE_SZ HFILE3 ltac:(vm_compute; reflexivity) a ltac:(lia)) as [b Hb].
unfold aview. rewrite Hb. cbn. discriminate.
* rewrite AV3; assumption. }
intros a Hv. rewrite (aview_mod _ mem3 a). apply PV; [apply Z.mod_pos_bound; lia | rewrite <- aview_mod; exact Hv].
* apply MF3. * apply MF3. * apply MF3.
*
intros a Ha Hh. unfold YG0d.w64 in Hh. unfold YG0d.w64.
assert (Hf' : ~ (F_STDERR <= a < F_STDERR + FILE_SZ)) by (unfold in_band_rw, F_STDERR, FILE_SZ, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia).
assert (CASE : (spZ regs - FW_STK <= a < spZ regs) \/ ~ (spZ regs - FW_STK <= a < spZ regs)) by lia.
destruct CASE as [Hin|Hout]; [exfalso; destruct (Hpres a Hin) as [Hf _]; rewrite Hf in Hh; discriminate Hh|].
rewrite OUT; [reflexivity | |]; rewrite unsigned_lit_small by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia); assumption.
+
exact (aregs_preserved_of_st_ok _ Eb _ _ regs [Z_to_bv 64 cval] HS3 HAEb ltac:(vm_compute; reflexivity)).
+ apply same_but_materialized_trans with (with_vm_backing (m_vm_lazy md) mat1 md); [apply with_vm_backing_same|].
rewrite <- (wvb_collapse (m_vm_lazy md) mat3 mat1 md). apply with_vm_backing_same.
+
rewrite Q10. rewrite (OLD 11%nat) by (cbv; lia). rewrite (OLD 12%nat) by (cbv; lia). rewrite E11, E12, Ha1, Ha2.
apply bv_eq. unfold alu64, alu, w64, bv_ltu. rewrite !unsigned_lit_small by lia.
replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite bv_and_unsigned, bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small nmemb) by lia.
change ((0 mod 2 ^ 64 + -1 mod 2 ^ 64) mod 2 ^ 64) with (Z.ones 64).
rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
+ exact HFILE3.
+   intros a Hr Hx1 Hx2. apply AV3; assumption.
+
assert (PVp : forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem3 a).
{ intros a Hr HnF Hp.
assert (CASE : (spZ regs - FW_STK <= a < spZ regs) \/ (F_STDERR <= a < F_STDERR + FILE_SZ) \/
(~ (spZ regs - FW_STK <= a < spZ regs) /\ ~ (F_STDERR <= a < F_STDERR + FILE_SZ))) by lia.
destruct CASE as [Hin | [Hin | [Ho1 Ho2]]].
-- apply PRES3s. exact Hin.
-- exfalso. exact (HnF Hin).
-- destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite OUT; [exact Hb| |]; rewrite unsigned_lit_small by lia; assumption. }
exact PVp.
+ exact HAI3.
Qed.
End S.
End c.
