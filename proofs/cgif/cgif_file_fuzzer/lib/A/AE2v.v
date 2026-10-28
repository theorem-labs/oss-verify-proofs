(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3f AE2p AE3i AE3h AE3l AE31.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FP_ENTRY : Z := 0x4192c.
Definition FP_REAL : Z := 0x93ad0.
Definition FP_RET : Z := 0x451d4.
Definition FP_ALIGN : Z := 0x63970.
Definition FP_WIN : Z := 2400.
Definition FPI_STK : Z := 9216.
Definition FMT : Z := 0x196bf.
Lemma fp_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_fp FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_fp tbl_fp_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma fp_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_fp FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fp tbl_fp_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition fpA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x9df88, 8, [(0, 8%N, 0x137b28)]); (0x137b7c, 1, [(0, 1%N, 1)]); (0x9fd10, 8, [(0, 8%N, 0x93ad0)])].
Lemma fpA_rodata_chk : forall ly, rodata_chk ly fpA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition SH_LO : Z := 0x7fffb2d0.  Definition SH_HI : Z := 0x7fffb2e0.
Definition shz : YP09.region := YP09.mkRegion None SH_LO SH_HI SH_LO SH_LO [YP09.mkChunk SH_LO (CZero (SH_HI - SH_LO))].
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FP_WIN) 0 (- FP_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 0 (2^32) 0)].
Definition regsA : list sv := Eval vm_compute in (firstn 11 sr_atoms ++ [SLit FMT] ++ skipn 12 sr_atoms).
Definition memA : smem := stkA :: shz :: img_ro_region :: map ro_region fpA_rodata.
Definition ssA : sstate := mkSS FP_ENTRY regsA memA None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_fp FUEL FP_REAL s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_fp FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Definition eA1 : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A1 : RUNTOR ssA = (eA1, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2328))) (SLit 15)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0))).
Lemma r_A2 : RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)) = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 56 (CVal 8 (SOff 32 0));
YP09.mkChunk 48 (CVal 8 (SOff 33 0));
YP09.mkChunk 40 (CVal 8 (SOff 34 0));
YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition ss_epi : sstate := mkSS FP_RET sr_atoms [YP09.mkRegion (Some 2%nat) 0 112 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition SAVEDA : list (Z * Z) := [(1, -56); (8, -64); (9, -72); (18, -80); (12, -48)].
Definition KEPTA : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FP_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - FP_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SLit FMT) && reg_is ss 12 (SOff 2 (-48)) &&
reg_is ss 1 (SLit FP_RET) && reg_is ss 2 (SOff 2 (-112)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma br_memset_align : forall E sp0, bv_unsigned (ew E 2) = sp0 -> sp0 mod 16 = 0 -> 2 ^ 44 <= sp0 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2328))) (SLit 15))) (sv_denot E (SLit 0)) = false.
Proof.
intros E sp0 H2 Hal Hsp. rewrite branch_eq_U, !U_SAlu, !U_SLit, U_SOff, H2. cbn [zalu_raw].
rewrite (zcanon_small 40), (zcanon_small 15), (zcanon_small 0), (zcanon_small (sp0 + -2328)) by lia.
assert (Hm : (sp0 + -2328) mod 16 = 8).
{ replace (sp0 + -2328) with (sp0 - 146 * 16 + 8) by lia. rewrite <- Z.add_mod_idemp_l by lia.
replace ((sp0 - 146 * 16) mod 16) with 0; [reflexivity|]. rewrite <- Zminus_mod_idemp_l. rewrite Hal. reflexivity. }
assert (Hand : Z.land (Z.lor 40 (sp0 + -2328)) 15 = 8).
{ rewrite Z.land_lor_distr_l. change 15 with (Z.ones 4). rewrite !Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Hm. reflexivity. }
assert (Hlt : Z.lor 40 (sp0 + -2328) < 2 ^ 64).
{ destruct (Z.eq_dec (Z.lor 40 (sp0 + -2328)) 0) as [E0|E0]; [rewrite E0; lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg 40 (sp0 + -2328)); lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; [cbv; reflexivity | apply Z.log2_lt_pow2; lia]. }
rewrite (zcanon_small (Z.lor 40 (sp0 + -2328))) by (pose proof (Z.lor_nonneg 40 (sp0 + -2328)); lia).
rewrite Hand. reflexivity.
Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis TL : TfibSyms B.
Lemma ocpy_of_icpt : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. rewrite (ts_code B TB). exact (memcpy_icpt_realizes B LAWS TB). Qed.
Theorem tfib_fprintf_icpt_refused : forall ly S (W : world tfibsegs) regs mem md ch cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + FPI_STK <= spZ regs ->
(forall a, spZ regs - FPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_refused -> getr regs 12 = w64 V_refused ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview tfibsegs (w_H W) mem) FMT_refused 33 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 38 ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FPI_STK <= a < spZ regs) -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs FP_ENTRY regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) msg_refused)) T).
Proof.
intros ly S W regs mem md ch cval T HPRE Hstk Hpres G10 G11 G12 HFP HFown Hgot Hcan Hcv Hro HZ Hch HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold FPI_STK in *.
assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFF : F_STDERR = 664952) by reflexivity.
assert (HGC : A_GOT_canary = 0x9ec38) by reflexivity. assert (HCA : A_canary = 0x5f8fd0) by reflexivity.
assert (HVFS : VF_STK = 9104) by reflexivity. assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
assert (HFMT : FMT_refused = FMT) by reflexivity. assert (HFMTV : FMT = 104127) by reflexivity. assert (HVR : V_refused = 67108864) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfibsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf. lia. }
assert (FT : forall flds (m m' : word -> option byte),
Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) flds ->
file_is flds (mrestrict H m) ->
(forall b, F_STDERR <= b < F_STDERR + FILE_SZ -> aview tfibsegs H m' b = aview tfibsegs H m b) -> file_is flds (mrestrict H m')).
{ intros flds m m' Hwf Hf Hb. unfold file_is in *. apply Forall_forall. intros [[o nn] v] Hin.
pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. pose proof (proj1 (Forall_forall _ _) Hwf _ Hin) as Ho. cbn beta iota in Hv, Ho |- *.
apply (VT m); [exact Hv|]. intros b Hbb. apply Hb. pose proof (N_nat_Z nn). lia. }
assert (WF1 : Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) stderr_fields) by (unfold stderr_fields, FILE_SZ; repeat constructor; cbn; lia).
unfold cfg_at. change (w64 FP_ENTRY) with (Z_to_bv 64 FP_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 F_STDERR) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE12 : ew EE 12 = Z_to_bv 64 V_refused) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (HZ' : forall s, SH_LO <= s < SH_HI -> aview tfibsegs H mem s = Some 0).
{ intros s Hs. apply HZ. unfold SH_LO, SH_HI in Hs.
match goal with |- ?a <= s < ?b => let a' := eval vm_compute in a in change a with a'; let b' := eval vm_compute in b in change b with b' end. lia. }
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 FP_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
apply (st_ok_regs tfibsegs EE (mkSS FP_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 11 11%bv eq_refl), G11; reflexivity) ] |]).
destruct Hr. }
unfold memA, EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [apply Hro | exact (rodata_ok B TB fpA_rodata ly S H mem EE (fpA_rodata_chk ly) (proj1 HAR))]]].
+ unfold stkA, FP_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2400)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia.
+ unfold shz, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold SH_LO, SH_HI. split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|]. apply HZ'. unfold SH_LO, SH_HI. cbn in Hi. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, shz, img_ro_region, fpA_rodata, icpt_rodata, ro_region, extent_of_region, FP_WIN, SH_LO, SH_HI, IMG_RO_LO, IMG_RO_HI.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | subst sp0; lia]. }
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HS0 r_A1) HAI0).
intros Wa ca _ HAIa (-> & msa & mata & -> & HSa & HFa & HFra). cbn [cfg_model] in HAIa. rewrite ?wvb_wvb in HAIa |- *.
assert (MEQa : forall z : word, ~ (sp0 - 2400 <= bv_unsigned z < sp0) -> ms_mem msa z = mem z).
{ intros z Hz. apply (HFa z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold FP_WIN in *. lia. }
clear HFa HFra.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG eA1 13) (SLit 0) HSa (br_memset_align EE sp0 EE2 Hal16 ltac:(lia))) as HSa'.
change (neg_bc BC_EQ) with BC_NE in HSa'. clear HSa.
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSa' r_A2) HAIa).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2400 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQa; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold FP_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 F_STDERR) by (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q11 : getr regs1 11 = w64 FMT_refused) by (rewrite (RD 11%bv (SLit FMT) R11); reflexivity).
assert (Q12 : getr regs1 12 = w64 (sp0 - 48)) by (rewrite (RD 12%bv (SOff 2 (-48)) R12); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q1 : getr regs1 1 = w64 FP_RET) by (rewrite (RD 1%bv (SLit FP_RET) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 112)) by (rewrite (RD 2%bv (SOff 2 (-112)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 112) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (R1ra : raZ regs1 = FP_RET) by (unfold raZ; rewrite Q1; unfold w64; apply unsigned_lit_small; unfold FP_RET; lia).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1).
{ subst md1. apply with_vm_backing_same. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2400 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2400 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold FP_WIN. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2400)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2400)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
assert (HPRE1 : ecall_pre tfibsegs B ly S W regs1 (ms_mem ms1) md1).
{ split; [exact HAR1|]. split; [rewrite Q1; apply (ret_ok_lit FP_RET); [unfold FP_RET; lia | reflexivity]|].
split; [rewrite R1sp; replace (sp0 - 112) with (sp0 + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite R1sp; unfold ESTACK; unfold sp0 in *; lia|]. split; [rewrite R1sp; unfold sp0 in *; lia|].
split; [intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; apply PM1; apply Hpres; unfold sp0 in *; lia|].
split; [rewrite Q3; exact Hgp | rewrite Q4; exact Htp]. }
change (mkCfg (mkst regs1 (Z_to_bv 64 FP_REAL) (ms_mem ms1) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs A_vfprintf regs1 (ms_mem ms1) md1).
apply (tfib_vfprintf_refused B TL LAWS ocpy_of_icpt ly S W regs1 (ms_mem ms1) md1 ch (sp0 - 48) cval T HPRE1).
- rewrite R1sp. lia.
- rewrite R1sp, HVFS. unfold sp0 in *. lia.
- intros a Ha. unfold vf_band in Ha. rewrite R1sp, HVFS in Ha. apply PM1. apply Hpres. unfold sp0 in *. lia.
- exact Q10.
- exact Q11.
- exact Q12.
- rewrite R1sp. lia.
- lia.
- pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hdm. rewrite Hal16, Z.add_0_r in Hdm.
replace (sp0 - 48) with ((2 * (sp0 / 16) - 6) * 8) by lia. apply Z_mod_mult.
- replace (sp0 - 48) with (sp0 + -48) by lia. replace V_refused with (bv_unsigned (getr regs 12)) by (rewrite G12; unfold w64; rewrite unsigned_lit_small by (rewrite HVR; lia); reflexivity).
exact (CK 4%nat 12%Z (-48)%Z eq_refl).
- apply (FT stderr_fields mem); [exact WF1 | exact HFP | intros b Hb; apply AV1; lia].
- exact HFown.
- apply (VT mem); [exact Hgot | intros b Hb; apply AV1; lia].
- apply (VT mem); [exact Hcan | intros b Hb; apply AV1; lia].
- exact Hcv.
- apply (ro_img_kept _ mem (ms_mem ms1)); [intros x Hx; apply MEQ1; unfold IMG_RO_LO, IMG_RO_HI in Hx; lia | exact Hro].
- intros a Ha. exists 0. split; [|left; reflexivity]. change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). rewrite AV1.
+ apply HZ. pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)).
assert (shadow_addr FMT_refused / 8 <= shadow_addr a / 8) by (apply Z.div_le_mono; [lia|]; unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (shadow_addr a / 8 <= shadow_addr (FMT_refused + 33 - 1) / 8) by (apply Z.div_le_mono; [lia|]; unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia.
+ pose proof (shadow_addr_bounds a ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. lia.
+ pose proof (shadow_addr_bounds a ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. unfold sp0 in *. lia.
- intros s Hs. rewrite AV1; [rewrite (HZ s); [discriminate|] | |].
+ pose proof (Z.div_le_mono (shadow_addr (FMT_refused + 32 - 1)) (shadow_addr (FMT_refused + 33 - 1)) 8 ltac:(lia) ltac:(unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia)). lia.
+ match type of Hs with ?a <= s < ?b => let a' := eval vm_compute in a in let b' := eval vm_compute in b in change (a <= s < b) with (a' <= s < b') in Hs end. lia.
+ match type of Hs with ?a <= s < ?b => let a' := eval vm_compute in a in let b' := eval vm_compute in b in change (a <= s < b) with (a' <= s < b') in Hs end. unfold sp0 in *. lia.
- eapply fdchan_sbm; [exact Hch | exact MF1].
- exact HAI1.
-
intros regs2 mem2 md2 HAR2 AP2 Hsbm2 A10_2 HFW2 Hfr2 Hpm2 HAI2.
rewrite R1ra. unfold vf_band in Hfr2. rewrite R1sp, HVFS in Hfr2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr) by (intros rr z -> Hcs; exact (AP2 z Hcs)).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - 9104 <= a < sp0 - 112) -> ~ vf_file a -> aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms1) a)
by (intros a Hr Ha Hf; exact (Hfr2 a Hr Ha Hf)).
unfold cfg_at. change (w64 FP_RET) with (Z_to_bv 64 FP_RET).
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
assert (R4sp : getr regs2 2 = w64 (sp0 - 112)) by (rewrite (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q2).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 112).
{ subst E4. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R4sp. unfold w64. apply unsigned_lit_small. lia. }
assert (WS : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> -80 <= off -> val_mem tfibsegs (mrestrict H mem2) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj Hoff80. assert (Hoff : off <= -48) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (VT (ms_mem ms1)); [exact (CK j rz off Hj) | intros b Hb; apply AV2; [unfold sp0 in *; lia | unfold sp0 in *; lia | unfold vf_file; lia]]. }
pose proof (WS 0%nat 1%Z (-56)%Z eq_refl ltac:(lia)) as W0. replace (sp0 + -56) with (sp0 - 56) in W0 by lia.
pose proof (WS 1%nat 8%Z (-64)%Z eq_refl ltac:(lia)) as W1. replace (sp0 + -64) with (sp0 - 64) in W1 by lia.
pose proof (WS 2%nat 9%Z (-72)%Z eq_refl ltac:(lia)) as W2. replace (sp0 + -72) with (sp0 - 72) in W2 by lia.
pose proof (WS 3%nat 18%Z (-80)%Z eq_refl ltac:(lia)) as W3. replace (sp0 + -80) with (sp0 - 80) in W3 by lia.
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 FP_RET) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 112) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18] (Z_to_bv 64 0) = getr regs r ->
off = 56 - 8 * Z.of_nat j -> Z.of_nat j < 4 ->
val_mem tfibsegs (mrestrict H mem2) (sp0 - 56 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem2) (sp0 - 112) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 112) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 112 + (56 - 8 * Z.of_nat j)) with (sp0 - 56 - 8 * Z.of_nat j) by lia. exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK4 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 0) with (sp0 - 56) by lia; exact W0].
+ apply (CK4 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 1) with (sp0 - 64) by lia; exact W1].
+ apply (CK4 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 2) with (sp0 - 72) by lia; exact W2].
+ apply (CK4 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 3) with (sp0 - 80) by lia; exact W3].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_srealizes tfibsegs W _ _ T (fp_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI2).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem2 z) by (intros z; apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md2) mat' md2)) T); [ | exact HAI5 | ].
{ eapply (SRr_ret_at tfibsegs tbl_fp tbl_fp_ok Hwx W E4); [exact HS5 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (10%bv : bv 5) P10. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19.
rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21. rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23.
rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25. rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs2 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs2 _ 0)). rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
assert (SBM56 : same_but_materialized (with_vm_backing (m_vm_lazy md2) mat5 md2) (with_vm_backing (m_vm_lazy md2) mat6 md2))
by (rewrite <- (wvb_collapse (m_vm_lazy md2) mat6 mat5 md2); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBM56) as MF.
assert (AV5 : forall a, aview tfibsegs H (ms_mem ms5) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply MEQ5).
assert (GG : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr).
{ intros z rr Hrr H1. subst rr. exact (K2 _ z eq_refl H1). }
apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat6 md2)).
+ apply (al_frame _ _ LAWS ly S W mem2 (with_vm_backing (m_vm_lazy md2) mat5 md2) (ms_mem ms5) _).
* apply (al_frame _ _ LAWS ly S W mem2 md2 mem2 _ HAR2); [intros; reflexivity | intros a Hv; exact Hv | | | | exact (AE2y.hs_kept_refl _ _)]; apply (same_but_materialized_frame md2 _ (with_vm_backing_same md2 mat5)).
* intros a Hr Hown. apply AV5.
* intros a Hv. rewrite AV5. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (AE2y.hs_kept_eq _ _ _ MEQ5).
+ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P3, (Y 3%nat 3%bv eq_refl), (GG 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P4, (Y 4%nat 4%bv eq_refl), (GG 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P9. exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P19, (Y 19%nat 19%bv eq_refl), (GG 19 19%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 19%bv 19%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P20, (Y 20%nat 20%bv eq_refl), (GG 20 20%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 20%bv 20%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P21, (Y 21%nat 21%bv eq_refl), (GG 21 21%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 21%bv 21%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P22, (Y 22%nat 22%bv eq_refl), (GG 22 22%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P23, (Y 23%nat 23%bv eq_refl), (GG 23 23%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P24, (Y 24%nat 24%bv eq_refl), (GG 24 24%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P25, (Y 25%nat 25%bv eq_refl), (GG 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P26, (Y 26%nat 26%bv eq_refl), (GG 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P27, (Y 27%nat 27%bv eq_refl), (GG 27 27%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)).
+ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm2|]. apply with_vm_backing_same.
+ rewrite P10, (Y 10%nat 10%bv eq_refl). exact A10_2.
+ apply Tfib_vfaux_stderr_after_xfer with (m := mem2) || idtac.
unfold stderr_after_vfprintf in *. revert HFW2. generalize stderr_fields_after_vf. intros flds Hf.
unfold file_is in *. apply Forall_forall. intros [[o nn] v] Hin. pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. cbn beta iota in Hv |- *.
apply (AF0x.val_mem_ext (mrestrict H mem2)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply AV5.
+ intros a Hr Hs Hf. rewrite AV5. rewrite AV2; [| exact Hr | unfold sp0 in *; lia | exact Hf]. apply AV1; [exact Hr | unfold sp0 in *; lia].
+ intros a Hr Hf Hp. apply (apresent_same H mem2 (ms_mem ms5) a (MEQ5 _)). apply Hpm2; [exact Hr | exact Hf|]. apply PM1. exact Hp.
+ exact HAI6.
Qed.
End g.
End d.
