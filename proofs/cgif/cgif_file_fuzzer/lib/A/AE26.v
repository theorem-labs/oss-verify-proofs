(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2l AE2h AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2d AE2c AE2b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FW_ENTRY : Z := 0x41914.
Definition FW_REAL : Z := 0x93808.
Definition FW_RET : Z := 0x438e8.
Definition FW_B : Z := 0x438f4.
Definition FW_END : Z := 0x4394c.
Definition FW_FRAME : Z := 2128.
Definition FW_WIN : Z := 2144.
Definition AFW_STK : Z := 6352.
Definition fwA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [(0x9fcf0, 8, [(0, 8%N, 0x93808)])].
Lemma fwA_rodata_chk : forall ly, rodata_chk ly fwA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FW_WIN) 0 (- FW_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 1 1 0); (12%nat, mkAF 1 (2^30) 0); (13%nat, mkAF 4096 (2^47) 4)].
Definition ssA : sstate := mkSS FW_ENTRY sr_atoms (stkA :: map ro_region fwA_rodata) None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_icpt FUEL FW_REAL s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A : RUNTOR ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition RUNI (s : sstate) := sym_runN tfibsegs tbl_icpt FUEL s.
Definition RGA (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2120 (CVal 8 (SOff 32 0)); YP09.mkChunk 2112 (CVal 8 (SOff 33 0)); YP09.mkChunk 2104 (CVal 8 (SOff 34 0));
YP09.mkChunk 2096 (CVal 8 (SOff 35 0)); YP09.mkChunk 2088 (CVal 8 (SOff 36 0)); YP09.mkChunk 2080 (CVal 8 (SOff 37 0));
YP09.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi : sstate := mkSS FW_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUNI ss_epi).
Lemma r_epi : RUNI ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition reg_isA (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RGA ss r) v.
Definition chunk_isA (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunkA (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_isA off v) (YP09.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Definition KEPTA : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FW_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - FW_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_isA ss 10 (SOff 10 0) && reg_isA ss 11 (SOff 11 0) && reg_isA ss 12 (SOff 12 0) && reg_isA ss 13 (SOff 13 0) &&
reg_isA ss 1 (SLit FW_RET) && reg_isA ss 2 (SOff 2 (-2128)) &&
reg_isA ss 9 (SOff 11 0) && reg_isA ss 18 (SOff 10 0) && reg_isA ss 19 (SOff 13 0) && reg_isA ss 20 (SOff 12 0) && reg_isA ss 21 (SLit 1) &&
forallb (fun r => reg_isA ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunkA ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_isA_sound : forall off v c, chunk_isA off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_isA in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma lk_ret0 : clookup tbl_icpt 0x438e8 = Some 0x060a8263. Proof. vm_compute. reflexivity. Qed.
Lemma lk_ret1 : clookup tbl_icpt 0x438ec = Some 0x06050063. Proof. vm_compute. reflexivity. Qed.
Lemma lk_ret2 : clookup tbl_icpt 0x438f0 = Some 0x029504b3. Proof. vm_compute. reflexivity. Qed.
Lemma fw_mid3n : forall (W : world tfibsegs) regs mem md n,
getr regs 21 = w64 1 -> getr regs 10 = w64 n -> getr regs 9 = w64 1 -> 1 <= n < 2 ^ 32 ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 FW_RET) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists md', c' = mkCfg (mkst (regupd regs 9%bv (getr regs 10%bv)) (Z_to_bv 64 FW_B) mem (seg_rom tfibsegs)) md' /\
same_but_materialized md md').
Proof.
intros W regs mem md n G21 G10 G9 Hn. pose proof AF0x.Hwx_tfa as Hwx.
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_beq_ft tfibsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret0) eq_refl ltac:(vm_compute; reflexivity)).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (21%bv : bv 5) by (apply bv_eq; reflexivity); replace r0 with (0%bv : bv 5) by (apply bv_eq; reflexivity) end.
rewrite G21. vm_compute. reflexivity. }
intros md1 Hs1. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 FW_RET) 4) with (Z_to_bv 64 0x438ec : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_beq_ft tfibsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret1) eq_refl ltac:(vm_compute; reflexivity)).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (10%bv : bv 5) by (apply bv_eq; reflexivity); replace r0 with (0%bv : bv 5) by (apply bv_eq; reflexivity) end.
rewrite G10, getr_zero. unfold c_eq. apply Bool.not_true_is_false. intros E. apply bv_eqb_eq in E.
apply (f_equal bv_unsigned) in E. unfold w64 in E. rewrite !unsigned_lit_small in E by lia. lia. }
intros md2 Hs2. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 0x438ec) 4) with (Z_to_bv 64 0x438f0 : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_mul tfibsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret2) eq_refl ltac:(vm_compute; reflexivity)). }
intros md3 Hs3. rewrite unrestrict_mkst_mrestrict.
match goal with |- SRr _ _ (mkCfg (mkst (if bv_eqb ?rd _ then _ else regupd _ _ (v_mul (getr _ ?a) (getr _ ?b))) _ _ _) _) _ =>
replace rd with (9%bv : bv 5) by (apply bv_eq; reflexivity); replace a with (10%bv : bv 5) by (apply bv_eq; reflexivity);
replace b with (9%bv : bv 5) by (apply bv_eq; reflexivity) end.
replace (bv_eqb (9%bv : bv 5) 0) with false by reflexivity. cbn iota.
replace (v_addi (Z_to_bv 64 0x438f0) 4) with (Z_to_bv 64 FW_B : word) by (apply bv_eq; vm_compute; reflexivity).
assert (EM : v_mul (getr regs 10) (getr regs 9) = getr regs 10).
{ unfold v_mul. rewrite G9, G10. unfold w64. rewrite !unsigned_lit_small by lia. rewrite Z.mul_1_r. reflexivity. }
rewrite EM.
apply SRr_ret. split; [reflexivity|]. exists md3. split; [reflexivity|].
eapply same_but_materialized_trans; [exact Hs1|]. eapply same_but_materialized_trans; [exact Hs2 | exact Hs3].
Qed.
Ltac INL := cbn; repeat (first [left; reflexivity | right]).
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (f fd n p cval : Z) (P bs Wb : list Z).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let m0 := mrestrict H mem.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hal16 : sp0 mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + AFW_STK <= sp0.
Hypothesis Hshi : sp0 <= ly_stk_hi ly.
Hypothesis Hpres : forall a, sp0 - AFW_STK <= a < sp0 -> apresent H mem a.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis G10 : getr regs 10 = w64 p.
Hypothesis G11 : getr regs 11 = w64 1.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis G13 : getr regs 13 = w64 f.
Hypothesis HFILE : file_at tfibsegs tfib_K m0 f fd P.
Hypothesis Hf0 : 4096 <= f.
Hypothesis Hfhi : f + FILE_BLOCK <= 2 ^ 47.
Hypothesis Hfal : f mod 16 = 0.
Hypothesis Hfd : 0 <= fd < 2 ^ 31.
Hypothesis HBLK : forall a, f <= a < f + FILE_BLOCK -> apresent H mem a /\ ~ aowned B ly S a.
Hypothesis HBstk : f + FILE_BLOCK <= sp0 - AFW_STK \/ sp0 <= f.
Hypothesis HBimg : f + FILE_BLOCK <= TFIB_IMG_LO \/ TFIB_IMG_END <= f.
Hypothesis HBam : amem_range f FILE_BLOCK.
Hypothesis HBra : range_addressable (aview tfibsegs H mem) SHADOW_OFF (f + 240) 1024.
Hypothesis HBhull : shadow_hull_vis (aview tfibsegs H mem) (f + 240) 1024.
Hypothesis HSRC : garr8 tfibsegs m0 p bs.
Hypothesis Hn : n = Z.of_nat (length bs).
Hypothesis Hn1 : 1 <= n <= 2 ^ 30.
Hypothesis Hp0 : 0 <= p.
Hypothesis Hphi : p + n <= 2 ^ 47.
Hypothesis HSf : p + n <= f \/ f + FILE_BLOCK <= p.
Hypothesis HSstk : p + n <= sp0 - AFW_STK \/ sp0 <= p.
Hypothesis HSam : amem_range p n.
Hypothesis HSra : range_addressable (aview tfibsegs H mem) SHADOW_OFF p n.
Hypothesis HShull : shadow_hull_vis (aview tfibsegs H mem) p n.
Hypothesis Hcan1 : val_mem tfibsegs m0 A_GOT_canary 8 A_canary.
Hypothesis Hcan2 : val_mem tfibsegs m0 A_canary 8 cval.
Hypothesis Hcv : 0 <= cval < 2 ^ 64.
Hypothesis HfdL : fd_lookup (m_fds md) (Z_to_bv 64 fd) = Some (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb)))).
Hypothesis HfsL : Fs.fs_lookup (m_fs md) sink_path = Some (YE00.bytes Wb).
Hypothesis HSmax : Z.of_nat (length Wb) + Z.of_nat (length P) + n <= SINK_MAX.
Definition APOST : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' (Wb' P' : list Z),
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\ AR tfibsegs B ly S W mem' md' /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 n /\
m_vmmaps md' = m_vmmaps md /\ m_vm_lazy md' = m_vm_lazy md /\ os_kept md md' /\
Wb' ++ P' = Wb ++ P ++ bs /\ Z.of_nat (length P') <= 1024 /\
hdr_is (mrestrict H mem') f (f + 240 + Z.of_nat (length P')) fd /\
garr8 tfibsegs (mrestrict H mem') (f + 240) P' /\
Fs.fs_lookup (m_fs md') sink_path = Some (YE00.bytes Wb') /\
(Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted (m_fs md') = true) /\
m_fds md' = (if (length Wb' =? length Wb)%nat then m_fds md else fd_insert (m_fds md) (Z_to_bv 64 fd) (FdFileW sink_path (Z_to_bv 64 (Z.of_nat (length Wb'))))) /\
(forall q, q <> sink_path -> Fs.fs_lookup (m_fs md') q = Fs.fs_lookup (m_fs md) q) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + FILE_BLOCK) -> ~ (sp0 - AFW_STK <= a < sp0) -> aview tfibsegs H mem' a = aview tfibsegs H mem a) /\
(forall a, apresent H mem a -> apresent H mem' a).
Theorem tfib_afwrite : SRr tfibsegs W (cfg_at tfibsegs FW_ENTRY regs mem md) APOST.
Proof.
assert (FB : FILE_BLOCK = 1264) by reflexivity. assert (FS : AFW_STK = 6352) by reflexivity. assert (FRS : FWR_STK = 4224) by reflexivity.
rewrite FB in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; rewrite FS in Hslo; lia).
assert (Lhs : 17594333495296 + 6352 <= sp0) by (subst sp0; rewrite FS in Hslo; lia).
pose proof AF0x.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfibsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf'. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf'. lia. }
unfold cfg_at. change (w64 FW_ENTRY) with (Z_to_bv 64 FW_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 p) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 1) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (EE12 : ew EE 12 = Z_to_bv 64 n) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (EE13 : ew EE 13 = Z_to_bv 64 f) by (rewrite (EEreg 13%nat 13%bv eq_refl); exact G13).
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 FW_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB fwA_rodata ly S H mem EE (fwA_rodata_chk ly) (proj1 HAR))].
unfold stkA, FW_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2144)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply Hpres. rewrite FS. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, fwA_rodata, icpt_rodata, ro_region, extent_of_region, FW_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, EE12, EE13, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; try lia. }
eapply SRr_bind; [exact (AE2y.icpt_phase_to W EE FW_REAL _ _ _ _ _ HS0 r_A)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
assert (MEQ1 : forall z : word, ~ (sp0 - 2144 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FW_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold FW_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R21]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R13]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_isA eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_isA, RGA in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunkA in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_isA_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 p) by (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q11 : getr regs1 11 = w64 1) by (rewrite (RD 11%bv (SOff 11 0) R11); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; reflexivity).
assert (Q12 : getr regs1 12 = w64 n) by (rewrite (RD 12%bv (SOff 12 0) R12); cbn [sv_denot]; rewrite EE12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q13 : getr regs1 13 = w64 f) by (rewrite (RD 13%bv (SOff 13 0) R13); cbn [sv_denot]; rewrite EE13, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q1 : getr regs1 1 = w64 FW_RET) by (rewrite (RD 1%bv (SLit FW_RET) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2128)) by (rewrite (RD 2%bv (SOff 2 (-2128)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q9 : getr regs1 9 = w64 1) by (rewrite (RD 9%bv (SOff 11 0) R9); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; reflexivity).
assert (Q18 : getr regs1 18 = w64 p) by (rewrite (RD 18%bv (SOff 10 0) R18); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q21 : getr regs1 21 = w64 1) by (rewrite (RD 21%bv (SLit 1) R21); reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 2128) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (R1ra : raZ regs1 = FW_RET) by (unfold raZ; rewrite Q1; unfold w64; apply unsigned_lit_small; unfold FW_RET; lia).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2144 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2144 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent_off H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| right; unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold FW_WIN. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hpa. pose proof Hpa as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hpa.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hpa]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hpa]. }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 Hpres ltac:(rewrite FS; lia) ltac:(lia)). }
assert (AVband1 : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs H (ms_mem ms1) s = aview tfibsegs H mem s).
{ intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. apply AV1; lia. }
assert (RAX : forall (ma mb : word -> option byte) a len, (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs H mb s = aview tfibsegs H ma s) ->
0 <= a -> a + len <= kHighMemEnd -> range_addressable (aview tfibsegs H ma) SHADOW_OFF a len -> range_addressable (aview tfibsegs H mb) SHADOW_OFF a len).
{ intros ma mb a len AVB Ha Hl HR. eapply range_addressable_agree; [|exact HR]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
apply AVB. apply AE2y.shadow_addr_bounds. lia. }
assert (HVX : forall (ma mb : word -> option byte) a len, (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs H mb s = aview tfibsegs H ma s) ->
0 <= a -> 1 <= len -> a + len <= kHighMemEnd -> shadow_hull_vis (aview tfibsegs H ma) a len -> shadow_hull_vis (aview tfibsegs H mb) a len).
{ intros ma mb a len AVB Ha Hl1 Hl HVS s Hs. rewrite AVB; [exact (HVS s Hs)|].
pose proof (AE2y.shadow_addr_bounds a ltac:(lia)) as [B1 B2]. pose proof (AE2y.shadow_addr_bounds (a + len - 1) ltac:(lia)) as [T1 T2].
pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (a + len - 1)) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr (a + len - 1)) 8 ltac:(lia)).
unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (HamF : f + 1264 <= kHighMemEnd) by (clear - HBam Hfhi; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (HamS : p + n <= kHighMemEnd) by (clear - HSam Hphi Hn1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
change (mkCfg (mkst regs1 (Z_to_bv 64 FW_REAL) (ms_mem ms1) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs FWR_ENTRY regs1 (ms_mem ms1) md1).
eapply SRr_bind.
{ apply (fwrite_entry B LAWS TB ly S W regs1 (ms_mem ms1) md1 f fd n p cval P bs Wb HAR1).
- rewrite Q1. apply (ret_ok_lit FW_RET); [unfold FW_RET; lia | reflexivity].
- rewrite R1sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite R1sp, FRS. clear - Hslo FS. unfold sp0 in *. lia.
- rewrite R1sp. clear - Hshi Hsp. unfold sp0 in *. lia.
- intros a Ha. rewrite R1sp, FRS in Ha. apply PM1. apply Hpres. rewrite FS. lia.
- rewrite Q3. exact Hgp.
- rewrite Q4. exact Htp.
- exact Q10. - exact Q11. - exact Q12. - exact Q13.
- subst m0. apply (file_at_frame tfibsegs tfib_K (mrestrict H mem)); [|exact HFILE]. intros x Hx. rewrite FB in Hx. apply mbyte_of_aview. apply AV1; [lia|]. rewrite FS in HBstk. lia.
- exact Hf0. - rewrite FB; exact Hfhi. - exact Hfal. - exact Hfd.
- intros a Ha. rewrite FB in Ha. split; [apply PM1; apply (proj1 (HBLK a Ha)) | apply (proj2 (HBLK a Ha))].
- rewrite FB, R1sp, FRS. rewrite FS in HBstk. clear - HBstk. lia.
- exact HBimg. - rewrite FB; exact HBam.
- apply (RAX mem); [exact AVband1 | lia | lia | exact HBra].
- apply (HVX mem); [exact AVband1 | lia | lia | lia | exact HBhull].
- subst m0. eapply garr8_frame; [exact HSRC|]. intros a Ha. apply mbyte_of_aview. apply AV1; [lia|]. rewrite FS in HSstk. lia.
- exact Hn. - exact Hn1. - exact Hp0. - exact Hphi. - rewrite FB; exact HSf.
- rewrite R1sp, FRS. rewrite FS in HSstk. clear - HSstk. lia.
- exact HSam.
- apply (RAX mem); [exact AVband1 | lia | lia | exact HSra].
- apply (HVX mem); [exact AVband1 | lia | lia | lia | exact HShull].
- apply (VT mem); [exact Hcan1 | intros b Hb; apply AV1; [unfold A_GOT_canary in Hb; lia | unfold A_GOT_canary in Hb; lia]].
- apply (VT mem); [exact Hcan2 | intros b Hb; apply AV1; [unfold A_canary in Hb; lia | unfold A_canary in Hb; lia]].
- exact Hcv.
- pose proof (same_but_materialized_frame md md1 MF1) as (_ & _ & _ & _ & _ & _ & _ & _ & Ffds & _). rewrite Ffds. exact HfdL.
- pose proof (same_but_materialized_frame md md1 MF1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ffs & _). rewrite Ffs. exact HfsL.
- exact HSmax. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Wb' & P' & -> & HAR2 & AP2 & A10_2 & Evm2 & Elz2 & HOK2 & HCAT & HPL' & HHDR2 & HP2 & HFS2 & HSO2 & HFDS2 & HFSo2 & HFR2 & HPM2).
rewrite R1ra. rewrite R1sp, FRS in HFR2. fold H in HFR2, HPM2, HHDR2, HP2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr) by (intros rr z -> Hcs; exact (AP2 z Hcs)).
assert (G21_2 : getr regs2 21 = w64 1) by (rewrite (K2 21%bv 21 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q21).
assert (G9_2 : getr regs2 9 = w64 1) by (rewrite (K2 9%bv 9 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q9).
unfold cfg_at. change (w64 FW_RET) with (Z_to_bv 64 FW_RET).
eapply SRr_bind; [exact (fw_mid3n W regs2 mem2 md2 n G21_2 A10_2 G9_2 ltac:(lia))|].
intros W3 c3 _ (-> & md3 & -> & Hsbm3).
set (regs3 := regupd regs2 9%bv (getr regs2 10%bv)).
assert (R3 : forall rr : bv 5, rr <> 9%bv -> getr regs3 rr = getr regs2 rr).
{ intros rr Hne. subst regs3. apply getr_other. exact Hne. }
assert (R3_9 : getr regs3 9 = w64 n) by (subst regs3; rewrite getr_same by (intros X0; discriminate X0); exact A10_2).
assert (R3sp : spZ regs3 = sp0 - 2128).
{ unfold spZ. rewrite R3 by (intros X0; discriminate X0). rewrite (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact R1sp. }
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (f <= a < f + 1264) -> ~ (sp0 - 2128 - 4224 <= a < sp0 - 2128) -> aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms1) a)
by (intros a Hr Hb Hs'; exact (HFR2 a Hr Hb Hs')).
pose proof (os_kept_sbm _ _ Hsbm3) as HOK3.
pose proof (same_but_materialized_frame md2 md3 Hsbm3) as (_ & F3maps & F3lazy & _ & _ & _ & _ & _ & F3fds & _ & _ & F3fs & _).
assert (HAR3 : AR tfibsegs B ly S W mem2 md3).
{ apply (al_frame _ _ LAWS ly S W mem2 md2 mem2 _ HAR2); [intros; reflexivity | intros a Hv; exact Hv | exact F3maps | exact F3lazy | | exact (AE2y.hs_kept_refl _ _)].
apply (same_but_materialized_frame md2 _ Hsbm3). }
assert (AVband2 : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs H mem2 s = aview tfibsegs H mem s).
{ intros s Hs. rewrite AV2; [apply AVband1; exact Hs | unfold kLowMemEnd, kHighShadowEnd in Hs; lia | | unfold kLowMemEnd, kHighShadowEnd in Hs; lia].
clear - Hs HBam Hfhi. unfold amem_range, kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *. lia. }
eapply SRr_bind.
{ apply (fwr_check_srr B LAWS TB ly S W regs3 mem2 md3 p n HAR3).
- rewrite R3sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite R3sp. unfold AE2b.RC_SCR. clear - Hslo FS. unfold sp0 in *. lia.
- rewrite R3sp. clear - Hshi Hsp. unfold sp0 in *. lia.
- intros a Ha. rewrite R3sp in Ha. unfold AE2b.RC_SCR in Ha. apply HPM2. apply PM1. apply Hpres. rewrite FS. lia.
- exact R3_9.
- rewrite R3 by (intros X0; discriminate X0). rewrite (K2 18%bv 18 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q18.
- clear - Hn1. lia.
- exact Hp0.
- clear - Hphi. lia.
- exact HSam.
- apply (RAX mem); [exact AVband2 | lia | lia | exact HSra].
- apply (HVX mem); [exact AVband2 | lia | lia | lia | exact HShull]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & K4 & Hsbm4 & A10_4 & Hfr4 & Hpm4).
rewrite R3sp in Hfr4. unfold AE2b.RC_SCR in Hfr4. fold H in Hfr4, Hpm4.
assert (KK4 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 -> getr regs4 rr = getr regs3 rr).
{ intros z rr -> H1 H2 H3 H5. exact (K4 z H1 H2 H3 H5). }
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2128 - 72 <= a < sp0 - 2128) -> aview tfibsegs H mem4 a = aview tfibsegs H mem2 a) by (intros a Hr Ha; exact (Hfr4 a Hr Ha)).
pose proof (os_kept_sbm _ _ Hsbm4) as HOK4.
pose proof (same_but_materialized_frame md3 md4 Hsbm4) as (_ & F4maps & F4lazy & _ & _ & _ & _ & _ & F4fds & _ & _ & F4fs & _).
set (E4 := Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (R4sp : getr regs4 2 = w64 (sp0 - 2128)).
{ rewrite (KK4 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite R3 by (intros X0; discriminate X0). rewrite (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2128).
{ subst E4. rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl), R4sp. unfold w64. apply unsigned_lit_small. lia. }
assert (WS : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H mem4) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. assert (Hoff : -56 <= off <= -8) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (VT mem2); [apply (VT (ms_mem ms1)); [exact (CK j rz off Hj) | intros b Hb; apply AV2; [lia | rewrite FS in HBstk; clear - Hb Hoff HBstk Hsp; lia | lia]] | intros b Hb; apply AV4; lia]. }
pose proof (WS 0%nat 1%Z (-8)%Z eq_refl) as W0. replace (sp0 + -8) with (sp0 - 8) in W0 by lia.
pose proof (WS 1%nat 8%Z (-16)%Z eq_refl) as W1'. replace (sp0 + -16) with (sp0 - 16) in W1' by lia.
pose proof (WS 2%nat 9%Z (-24)%Z eq_refl) as W2'. replace (sp0 + -24) with (sp0 - 24) in W2' by lia.
pose proof (WS 3%nat 18%Z (-32)%Z eq_refl) as W3'. replace (sp0 + -32) with (sp0 - 32) in W3' by lia.
pose proof (WS 4%nat 19%Z (-40)%Z eq_refl) as W4'. replace (sp0 + -40) with (sp0 - 40) in W4' by lia.
pose proof (WS 5%nat 20%Z (-48)%Z eq_refl) as W5'. replace (sp0 + -48) with (sp0 - 48) in W5' by lia.
pose proof (WS 6%nat 21%Z (-56)%Z eq_refl) as W6'. replace (sp0 + -56) with (sp0 - 56) in W6' by lia.
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs4 (w64 AE2b.RC_END) mem4 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2128) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat j -> Z.of_nat j < 7 ->
val_mem tfibsegs (mrestrict H mem4) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem4) (sp0 - 2128) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs4 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 2128 + (2120 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia. exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK4 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 0) with (sp0 - 8) by lia; exact W0].
+ apply (CK4 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact W1'].
+ apply (CK4 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact W2'].
+ apply (CK4 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact W3'].
+ apply (CK4 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact W4'].
+ apply (CK4 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact W5'].
+ apply (CK4 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact W6'].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply SRr_bind; [exact (AE2y.icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi)|].
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem4 z) by (intros z; apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
eapply SRr_bind.
{ eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E4); [exact HS5 | reflexivity | vm_compute; reflexivity |].
intros mat'. instantiate (1 := fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md4) mat' md4)).
cbv beta. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
cbv beta. intros W6 c6 _ (-> & mat6 & ->).
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (10%bv : bv 5) P10. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19.
rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21. rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23.
rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25. rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs4 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs4 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs4 _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs4 _ 0)). rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
set (md6 := with_vm_backing (m_vm_lazy md4) mat6 md4).
assert (MF46 : same_but_materialized md4 md6) by (subst md6; apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ MF46) as (_ & F6maps & F6lazy & _ & _ & _ & _ & _ & F6fds & _ & _ & F6fs & _).
assert (AV5 : forall a, aview tfibsegs H (ms_mem ms5) a = aview tfibsegs H mem4 a) by (intros a; apply aview_same; apply MEQ5).
assert (GG : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 -> getr regs4 rr = getr regs1 rr).
{ intros z rr Hrr H1 H2 H3 H5. rewrite (KK4 z rr Hrr H1 H2 H3 H5). rewrite R3.
2:{ subst rr. intros X0. apply H2. apply (f_equal bv_unsigned) in X0. rewrite Z_to_bv_unsigned in X0. unfold acallee_saved in H1. unfold bv_wrap in X0. change (bv_modulus 5) with 32 in X0. rewrite Z.mod_small in X0 by lia. replace (bv_unsigned (9%bv : bv 5)) with 9 in X0 by reflexivity. lia. }
subst rr. exact (K2 _ z eq_refl H1). }
assert (AV25 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2128 - 72 <= a < sp0 - 2128) -> aview tfibsegs H (ms_mem ms5) a = aview tfibsegs H mem2 a).
{ intros a Hr Ha. rewrite AV5. apply AV4; [exact Hr | exact Ha]. }
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms5), (ms_mem ms5), md6, Wb', P'.
split; [reflexivity|].
split.
{ apply (al_frame _ _ LAWS ly S W mem4 md4 (ms_mem ms5) _ HAR4); [intros a Hr Hown; apply AV5 | intros a Hv; rewrite AV5; exact Hv | exact F6maps | exact F6lazy | | exact (AE2y.hs_kept_eq _ _ _ MEQ5)].
apply (same_but_materialized_frame md4 _ MF46). }
split.
{ intros rr Hr. unfold acallee_saved in Hr.
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
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P19. exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P20. exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P21. exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P22, (Y 22%nat 22%bv eq_refl), (GG 22 22%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P23, (Y 23%nat 23%bv eq_refl), (GG 23 23%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P24, (Y 24%nat 24%bv eq_refl), (GG 24 24%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P25, (Y 25%nat 25%bv eq_refl), (GG 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P26, (Y 26%nat 26%bv eq_refl), (GG 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P27, (Y 27%nat 27%bv eq_refl), (GG 27 27%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)). }
split; [rewrite P10, (Y 10%nat 10%bv eq_refl), A10_4, R3 by (intros X0; discriminate X0); exact A10_2|].
split; [rewrite F6maps, F4maps, F3maps, Evm2; apply (same_but_materialized_frame md _ MF1)|].
split; [rewrite F6lazy, F4lazy, F3lazy, Elz2; apply (same_but_materialized_frame md _ MF1)|].
split; [eapply os_kept_trans; [exact (os_kept_sbm _ _ MF1) | eapply os_kept_trans; [exact HOK2 | eapply os_kept_trans; [exact HOK3 | eapply os_kept_trans; [exact HOK4 | exact (os_kept_sbm _ _ MF46)]]]]|].
split; [exact HCAT|]. split; [exact HPL'|].
split.
{ unfold hdr_is in *. apply Forall_forall. intros [[o nn] v] Hin. pose proof (proj1 (Forall_forall _ _) HHDR2 _ Hin) as Hv. cbn beta iota in Hv |- *.
assert (Ho : 0 <= o /\ o + Z.of_N nn <= 232) by (unfold hdr_cells in Hin; cbn [In] in Hin; repeat (destruct Hin as [Ei | Hin]; [injection Ei as <- <- <-; cbn; lia|]); destruct Hin).
apply (VT mem2); [exact Hv|]. intros b Hb. apply AV25; [lia|]. pose proof (N_nat_Z nn). rewrite FS in HBstk. clear - Hb Ho HBstk Hsp Hf0 H0. lia. }
split.
{ eapply garr8_frame; [exact HP2|]. intros a Ha. apply mbyte_of_aview. apply AV25; [lia|]. rewrite FS in HBstk. clear - Ha HBstk Hsp Hf0 HPL'. lia. }
split; [rewrite F6fs, F4fs, F3fs; exact HFS2|].
split; [intros Hso; rewrite F6fs, F4fs, F3fs; apply HSO2; pose proof (same_but_materialized_frame md md1 MF1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ffs1 & _); rewrite Ffs1; exact Hso|].
split; [rewrite F6fds, F4fds, F3fds, HFDS2; pose proof (same_but_materialized_frame md md1 MF1) as (_ & _ & _ & _ & _ & _ & _ & _ & Ffds1 & _); rewrite Ffds1; reflexivity|].
split; [intros q Hq; rewrite F6fs, F4fs, F3fs, (HFSo2 q Hq); pose proof (same_but_materialized_frame md md1 MF1) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ffs1 & _); rewrite Ffs1; reflexivity|].
split.
{ intros a Hr Hb Hs. rewrite AV25; [| exact Hr | rewrite FS in Hs; clear - Hs; lia]. rewrite AV2; [| exact Hr | exact Hb | rewrite FS in Hs; clear - Hs; lia].
apply AV1; [exact Hr | rewrite FS in Hs; clear - Hs; lia]. }
intros a Hpa. apply (apresent_same H mem4 (ms_mem ms5) a (MEQ5 _)). apply Hpm4. apply HPM2. apply PM1. exact Hpa.
Qed.
End g.
End d.
