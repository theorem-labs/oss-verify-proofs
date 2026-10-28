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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3f AE2p AE6w.
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
Definition FWI_STK : Z := 6224.
Definition fwA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) := icpt_rodata ++ [(0x9fcf0, 8, [(0, 8%N, 0x93808)])].
Lemma fwA_rodata_chk : forall ly, rodata_chk ly fwA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FW_WIN) 0 (- FW_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 1 (2^25) 0); (12%nat, mkAF 1 1 0)].
Definition ssA : sstate := mkSS FW_ENTRY sr_atoms (stkA :: map ro_region fwA_rodata) None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_icpt FUEL FW_REAL s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A : RUNTOR ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_icpt FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2120 (CVal 8 (SOff 32 0));
YP09.mkChunk 2112 (CVal 8 (SOff 33 0));
YP09.mkChunk 2104 (CVal 8 (SOff 34 0));
YP09.mkChunk 2096 (CVal 8 (SOff 35 0));
YP09.mkChunk 2088 (CVal 8 (SOff 36 0));
YP09.mkChunk 2080 (CVal 8 (SOff 37 0));
YP09.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi : sstate := mkSS FW_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Definition KEPTA : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FW_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - FW_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 11 0) && reg_is ss 12 (SOff 12 0) && reg_is ss 13 (SOff 13 0) &&
reg_is ss 1 (SLit FW_RET) && reg_is ss 2 (SOff 2 (-2128)) &&
reg_is ss 9 (SOff 11 0) && reg_is ss 18 (SOff 10 0) && reg_is ss 19 (SOff 13 0) && reg_is ss 20 (SOff 12 0) && reg_is ss 21 (SLit 1) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma lk_ret0 : clookup tbl_icpt 0x438e8 = Some 0x060a8263. Proof. vm_compute. reflexivity. Qed.
Lemma lk_ret1 : clookup tbl_icpt 0x438ec = Some 0x06050063. Proof. vm_compute. reflexivity. Qed.
Lemma lk_ret2 : clookup tbl_icpt 0x438f0 = Some 0x029504b3. Proof. vm_compute. reflexivity. Qed.
Lemma fw_mid3 : forall (W : world tfibsegs) regs mem md,
getr regs 21 = w64 1 -> getr regs 10 = w64 1 ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 FW_RET) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists md', c' = mkCfg (mkst (regupd regs 9%bv (getr regs 9%bv)) (Z_to_bv 64 FW_B) mem (seg_rom tfibsegs)) md' /\
same_but_materialized md md').
Proof.
intros W regs mem md G21 G10. pose proof AF0x.Hwx_tfa as Hwx.
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
rewrite G10. vm_compute. reflexivity. }
intros md2 Hs2. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 0x438ec) 4) with (Z_to_bv 64 0x438f0 : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_mul tfibsegs _ _ _ _ _ _ _ _ (tbl_icpt_ok _ _ lk_ret2) eq_refl ltac:(vm_compute; reflexivity)). }
intros md3 Hs3. rewrite unrestrict_mkst_mrestrict.
match goal with |- SRr _ _ (mkCfg (mkst (if bv_eqb ?rd _ then _ else regupd _ _ (v_mul (getr _ ?a) (getr _ ?b))) _ _ _) _) _ =>
replace rd with (9%bv : bv 5) by (apply bv_eq; reflexivity); replace a with (10%bv : bv 5) by (apply bv_eq; reflexivity) end.
replace (bv_eqb (9%bv : bv 5) 0) with false by reflexivity. cbn iota.
replace (v_addi (Z_to_bv 64 0x438f0) 4) with (Z_to_bv 64 FW_B : word) by (apply bv_eq; vm_compute; reflexivity).
replace (v_mul (getr regs 10) (getr regs 9)) with (getr regs 9).
2:{ unfold v_mul. rewrite G10. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.mul_1_l, Z_to_bv_bv_unsigned. reflexivity. }
apply SRr_ret. split; [reflexivity|]. exists md3. split; [reflexivity|].
eapply same_but_materialized_trans; [exact Hs1|]. eapply same_but_materialized_trans; [exact Hs2 | exact Hs3].
Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem tfib_fwrite_icpt : forall ly S (W : world tfibsegs) regs mem md ch p size cval (msg : list byte) T,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + FWI_STK <= spZ regs ->
(forall a, spZ regs - FWI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 p -> getr regs 11 = w64 size -> getr regs 12 = w64 1 -> getr regs 13 = w64 F_STDERR ->
1 <= size -> size <= 2 ^ 25 ->
0 <= p -> p + size <= kHighMemEnd ->
(p + size <= spZ regs - FWI_STK \/ spZ regs <= p) ->
(p + size <= F_STDERR \/ F_STDERR + FILE_SZ <= p) ->
rdn tfibsegs (mrestrict (w_H W) mem) (Z_to_bv 64 p) (Z.to_nat size) = Some msg ->
stderr_pristine (mrestrict (w_H W) mem) ->
(forall a, F_STDERR <= a < F_STDERR + FILE_SZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
amem_range p size ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p size ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) p size ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 1 ->
stderr_written (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FWI_STK <= a < spZ regs) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs FW_ENTRY regs mem md) (t_emit (map (WriteEv ch) msg) T).
Proof.
intros ly S W regs mem md ch p size cval msg T HPRE Hstk Hpres G10 G11 G12 G13 Hsz Hszhi Hp0 Hphi Hpband HpF Hmsg HFP HFown Hgot Hcan Hcv
Ham Hra Hhull Hch HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold FWI_STK in *.
assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFF : F_STDERR = 664952) by reflexivity.
assert (HGC : A_GOT_canary = 0x9ec38) by reflexivity. assert (HCA : A_canary = 0x5f8fd0) by reflexivity.
assert (HFWS : FW_STK = 176) by reflexivity. assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
assert (Hamr : p + size <= 2 ^ 47 - 1) by (pose proof Ham as X1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X1; lia).
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
assert (WF2 : Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) stderr_fields_after) by (unfold stderr_fields_after, FILE_SZ; repeat constructor; cbn; lia).
unfold cfg_at. change (w64 FW_ENTRY) with (Z_to_bv 64 FW_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 p) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 size) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (EE12 : ew EE 12 = Z_to_bv 64 1) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 FW_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (rodata_ok B TB fwA_rodata ly S H mem EE (fwA_rodata_chk ly) (proj1 HAR))].
unfold stkA, FW_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2144)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, fwA_rodata, icpt_rodata, ro_region, extent_of_region, FW_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, EE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | subst sp0; lia]. }
eapply (SRr_srealizes tfibsegs W _ _ _ (icpt_phase_to W EE FW_REAL _ _ _ _ _ HS0 r_A) HAI0).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
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
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
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
assert (Q10 : getr regs1 10 = w64 p) by (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q11 : getr regs1 11 = w64 size) by (rewrite (RD 11%bv (SOff 11 0) R11); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q12 : getr regs1 12 = w64 1) by (rewrite (RD 12%bv (SOff 12 0) R12); cbn [sv_denot]; rewrite EE12, unsigned_lit_small by lia; reflexivity).
assert (Q13 : getr regs1 13 = w64 F_STDERR) by (rewrite (RD 13%bv (SOff 13 0) R13); cbn [sv_denot]; rewrite (EEreg 13%nat 13%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact G13).
assert (Q1 : getr regs1 1 = w64 FW_RET) by (rewrite (RD 1%bv (SLit FW_RET) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2128)) by (rewrite (RD 2%bv (SOff 2 (-2128)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q9 : getr regs1 9 = w64 size) by (rewrite (RD 9%bv (SOff 11 0) R9); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
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
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold FW_WIN. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2144)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
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
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
assert (HPRE1 : ecall_pre tfibsegs B ly S W regs1 (ms_mem ms1) md1).
{ split; [exact HAR1|]. split; [rewrite Q1; apply (ret_ok_lit FW_RET); [unfold FW_RET; lia | reflexivity]|].
split; [rewrite R1sp; replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite R1sp; unfold ESTACK; unfold sp0 in *; lia|]. split; [rewrite R1sp; unfold sp0 in *; lia|].
split; [intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; apply PM1; apply Hpres; unfold sp0 in *; lia|].
split; [rewrite Q3; exact Hgp | rewrite Q4; exact Htp]. }
change (mkCfg (mkst regs1 (Z_to_bv 64 FW_REAL) (ms_mem ms1) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs A_fwrite regs1 (ms_mem ms1) md1).
apply (tfib_fwrite_at B LAWS ly S W regs1 (ms_mem ms1) md1 ch p size 1 cval msg T HPRE1).
- rewrite R1sp, HFWS. unfold sp0 in *. lia.
- intros a Ha. rewrite R1sp, HFWS in Ha. apply PM1. apply Hpres. unfold sp0 in *. lia.
- exact Q10.
- exact Q11.
- exact Q12.
- exact Q13.
- exact Hsz.
- lia.
- rewrite Z.mul_1_r. exact Hszhi.
- exact Hp0.
- rewrite Z.mul_1_r. exact Hphi.
- rewrite Z.mul_1_r, R1sp, HFWS. unfold sp0 in *. lia.
- rewrite Z.mul_1_r. exact HpF.
- rewrite Z.mul_1_r. pose proof (proj1 (rdn_mbytes tfibsegs _ _ _ _) Hmsg) as [Hlen Hby].
apply (proj2 (rdn_mbytes tfibsegs _ _ _ _)). split; [exact Hlen|]. intros i Hi. rewrite <- (Hby i Hi).
apply mbyte_of_aview. apply AV1; [lia | unfold sp0 in *; lia].
- apply (FT stderr_fields mem); [exact WF1 | exact HFP | intros b Hb; apply AV1; lia].
- exact HFown.
- apply (VT mem); [exact Hgot | intros b Hb; apply AV1; lia].
- apply (VT mem); [exact Hcan | intros b Hb; apply AV1; lia].
- exact Hcv.
- eapply fdchan_sbm; [exact Hch | exact MF1].
- exact HAI1.
-
intros regs2 mem2 md2 HAR2 AP2 Hsbm2 A10_2 HFW2 Hfr2 Hpm2 HAI2.
rewrite R1ra. rewrite R1sp, HFWS in Hfr2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr) by (intros rr z -> Hcs; exact (AP2 z Hcs)).
assert (G21_2 : getr regs2 21 = w64 1) by (rewrite (K2 21%bv 21 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q21).
unfold cfg_at. change (w64 FW_RET) with (Z_to_bv 64 FW_RET).
eapply (SRr_srealizes tfibsegs W _ _ T (fw_mid3 W regs2 mem2 md2 G21_2 A10_2) HAI2).
intros W3' c3 _ HAI3 (-> & md3 & -> & Hsbm3). cbn [cfg_model] in HAI3.
set (regs3 := regupd regs2 9%bv (getr regs2 9%bv)).
assert (R3 : forall rr : bv 5, getr regs3 rr = getr regs2 rr).
{ intros rr. subst regs3. destruct (bv_eq_dec _ rr 9%bv) as [->|Hne]; [apply getr_same; intros X0; discriminate X0 | apply getr_other; exact Hne]. }
assert (R3sp : spZ regs3 = sp0 - 2128) by (unfold spZ; rewrite R3, (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact R1sp).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2128 - 176 <= a < sp0 - 2128) -> ~ (F_STDERR <= a < F_STDERR + FILE_SZ) -> aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms1) a)
by (intros a Hr Ha Hf; exact (Hfr2 a Hr Ha Hf)).
assert (HAR3 : AR tfibsegs B ly S W mem2 md3).
{ apply (al_frame _ _ LAWS ly S W mem2 md2 mem2 _ HAR2); [intros; reflexivity | intros a Hv; exact Hv | | | | exact (AE2y.hs_kept_refl _ _)]; apply (same_but_materialized_frame md2 _ Hsbm3). }
eapply (SRr_srealizes tfibsegs W _ _ T); [| exact HAI3 |].
{ apply (fwr_check_srr B LAWS TB ly S W regs3 mem2 md3 p size HAR3).
- rewrite R3sp. replace (sp0 - 2128) with (sp0 + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite R3sp. unfold AE6w.RC_SCR. unfold sp0 in *. lia.
- rewrite R3sp. unfold sp0 in *. lia.
- intros a Ha. rewrite R3sp in Ha. unfold AE6w.RC_SCR in Ha. apply Hpm2; [lia | lia |]. apply PM1. apply Hpres. unfold sp0 in *. lia.
- rewrite R3, (K2 9%bv 9 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q9.
- rewrite R3, (K2 18%bv 18 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q18.
- rewrite R3. exact A10_2.
- lia.
- exact Hp0.
- lia.
- exact Ham.
- eapply range_addressable_agree; [|exact Hra]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2.
rewrite AV2 by (unfold sp0 in *; lia). apply AV1; unfold sp0 in *; lia.
- intros s' Hs. rewrite AV2, AV1; [exact (Hhull s' Hs) | | | | | ];
pose proof (shadow_addr_bounds p ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (p + size - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr p) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr p) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (p + size - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (p + size - 1)) 8 ltac:(lia)); unfold sp0 in *; lia. }
intros W4' c4 _ HAI4 (-> & regs4 & mem4 & md4 & -> & HAR4 & K4 & Hsbm4 & A10_4 & Hfr4 & Hpm4). cbn [cfg_model] in HAI4.
rewrite R3sp in Hfr4. unfold AE6w.RC_SCR in Hfr4.
assert (KK4 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 -> getr regs4 rr = getr regs3 rr).
{ intros z rr -> H1 H2 H3 H5. exact (K4 z H1 H2 H3 H5). }
assert (AV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2128 - 72 <= a < sp0 - 2128) -> aview tfibsegs H mem4 a = aview tfibsegs H mem2 a) by (intros a Hr Ha; exact (Hfr4 a Hr Ha)).
set (E4 := Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (R4sp : getr regs4 2 = w64 (sp0 - 2128)).
{ rewrite (KK4 2 2%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). rewrite R3, (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q2. }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2128).
{ subst E4. rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl), R4sp. unfold w64. apply unsigned_lit_small. lia. }
assert (WS : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H mem4) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. assert (Hoff : -56 <= off <= -8) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (VT mem2); [apply (VT (ms_mem ms1)); [exact (CK j rz off Hj) | intros b Hb; apply AV2; unfold sp0 in *; lia] | intros b Hb; apply AV4; unfold sp0 in *; lia]. }
pose proof (WS 0%nat 1%Z (-8)%Z eq_refl) as W0. replace (sp0 + -8) with (sp0 - 8) in W0 by lia.
pose proof (WS 1%nat 8%Z (-16)%Z eq_refl) as W1. replace (sp0 + -16) with (sp0 - 16) in W1 by lia.
pose proof (WS 2%nat 9%Z (-24)%Z eq_refl) as W2. replace (sp0 + -24) with (sp0 - 24) in W2 by lia.
pose proof (WS 3%nat 18%Z (-32)%Z eq_refl) as W3. replace (sp0 + -32) with (sp0 - 32) in W3 by lia.
pose proof (WS 4%nat 19%Z (-40)%Z eq_refl) as W4. replace (sp0 + -40) with (sp0 - 40) in W4 by lia.
pose proof (WS 5%nat 20%Z (-48)%Z eq_refl) as W5. replace (sp0 + -48) with (sp0 - 48) in W5 by lia.
pose proof (WS 6%nat 21%Z (-56)%Z eq_refl) as W6. replace (sp0 + -56) with (sp0 - 56) in W6 by lia.
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs4 (w64 AE6w.RC_END) mem4 (seg_rom tfibsegs)))).
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
+ apply (CK4 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 1) with (sp0 - 16) by lia; exact W1].
+ apply (CK4 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 2) with (sp0 - 24) by lia; exact W2].
+ apply (CK4 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 3) with (sp0 - 32) by lia; exact W3].
+ apply (CK4 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 4) with (sp0 - 40) by lia; exact W4].
+ apply (CK4 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 5) with (sp0 - 48) by lia; exact W5].
+ apply (CK4 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 8 - 8 * Z.of_nat 6) with (sp0 - 56) by lia; exact W6].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_srealizes tfibsegs W _ _ T (icpt_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI4).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem4 z) by (intros z; apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md4) mat' md4)) T); [ | exact HAI5 | ].
{ eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok Hwx W E4); [exact HS5 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (10%bv : bv 5) P10. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19.
rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21. rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23.
rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25. rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs4 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs4 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs4 _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs4 _ 0)). rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
assert (SBM56 : same_but_materialized (with_vm_backing (m_vm_lazy md4) mat5 md4) (with_vm_backing (m_vm_lazy md4) mat6 md4))
by (rewrite <- (wvb_collapse (m_vm_lazy md4) mat6 mat5 md4); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBM56) as MF.
assert (AV5 : forall a, aview tfibsegs H (ms_mem ms5) a = aview tfibsegs H mem4 a) by (intros a; apply aview_same; apply MEQ5).
assert (GG : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 -> getr regs4 rr = getr regs1 rr).
{ intros z rr Hrr H1 H2 H3 H5. rewrite (KK4 z rr Hrr H1 H2 H3 H5), R3. subst rr. exact (K2 _ z eq_refl H1). }
apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md4) mat6 md4)).
+ apply (al_frame _ _ LAWS ly S W mem4 (with_vm_backing (m_vm_lazy md4) mat5 md4) (ms_mem ms5) _).
* apply (al_frame _ _ LAWS ly S W mem4 md4 mem4 _ HAR4); [intros; reflexivity | intros a Hv; exact Hv | | | | exact (AE2y.hs_kept_refl _ _)]; apply (same_but_materialized_frame md4 _ (with_vm_backing_same md4 mat5)).
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
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P19. exact (X 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P20. exact (X 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P21. exact (X 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P22, (Y 22%nat 22%bv eq_refl), (GG 22 22%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P23, (Y 23%nat 23%bv eq_refl), (GG 23 23%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P24, (Y 24%nat 24%bv eq_refl), (GG 24 24%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P25, (Y 25%nat 25%bv eq_refl), (GG 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P26, (Y 26%nat 26%bv eq_refl), (GG 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P27, (Y 27%nat 27%bv eq_refl), (GG 27 27%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)).
+ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm2|]. eapply same_but_materialized_trans; [exact Hsbm3|].
eapply same_but_materialized_trans; [exact Hsbm4|]. apply with_vm_backing_same.
+ rewrite P10, (Y 10%nat 10%bv eq_refl). exact A10_4.
+ apply (FT stderr_fields_after mem2); [exact WF2 | exact HFW2 | intros b Hb; rewrite AV5; apply AV4; lia].
+ intros a Hr Hs Hf. rewrite AV5. rewrite AV4 by (unfold sp0 in *; lia). rewrite AV2; [| exact Hr | unfold sp0 in *; lia | exact Hf]. apply AV1; [exact Hr | unfold sp0 in *; lia].
+ intros a Hr Hf Hp. apply (apresent_same H mem4 (ms_mem ms5) a (MEQ5 _)). apply Hpm4. apply Hpm2; [exact Hr | exact Hf|]. apply PM1. exact Hp.
+ exact HAI6.
Qed.
End g.
End d.
