(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGwrcT.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 17 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfGwrcT.table); zify flag override made Local; YImgTop zify_pre_hook added after the last Require. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copy of A/AE2b.v (fwr_check_srr) re-instanced at the vsnprintf interceptor's WRITE_RANGE check (RC_ENTRY 0x44ea0 -> RC_END 0x44ef8; the shadow loads at 0x44ee8/0x44eec), over code table tbl_vsn (tbl_icpt plus 0x44dfc..0x45114), with x19 = size >= n (slow path `bnez s3`) and x10 = res kept, stated over Poison's ARU (any U); theorem vsn_wr_check_srrU. *)
(* Modified by Theorem Labs, 2026-10: relocated to fm.asan (module paths, addresses, code table over 0x458a0); entered at 0x45a18 (the size >= res + 1 path); icpt_rodata_okU copied from FMpfsU.v. *)
(* Modified by Theorem Labs, 2026-10: copy of FMsnprintfGwrc.v (its Section f: the WRITE_RANGE check walk and theorem
   vsn_wr_check_srrU) entered at 0x45944, the size < res + 1 path of fm.asan's __interceptor_vsnprintf (s1 = size, the
   check WRITE_RANGE (str, size)): 0x45944..0x45950 are the instructions of 0x45a18..0x45a24 with the overflow branch
   inverted (bltu a1, s1 to the slow path, falling into 0x45954 where 0x45a24's bgeu goes), so each path's first run
   (MEASURED: stops at the bltu, BC_LTU (~s2) s1) and its second run (MEASURED: from the not-taken side it reaches
   FMsnprintfGwrc's state r1_*_e1 / r2*_e1) are new and every later run is FMsnprintfGwrc's; theorem vsn_wr_check_srrUT. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfGwrc.
#[local] Ltac Zify.zify_pre_hook ::= try unfold PcapImgEnd.pcap_img_end, YImgTop.IMG_TOP, YImgTop.IMG_LO in *.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RT_ENTRY : Z := 0x46bd4.
(* FMsnprintfGwrc's entry states at 0x46bd4 *)
Definition ssR1T (t : Z) : sstate :=
  mkSS RT_ENTRY regsF (stkR :: shreg1 t :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 t)).
Definition ssR2LT : sstate :=
  mkSS RT_ENTRY regsF (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2L [] aliases2).
Definition ssR2HT : sstate :=
  mkSS RT_ENTRY regsF (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2H [] aliases2).
Definition t1_0_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 0)).
Lemma r_t1_0_0 : RUN (ssR1T 0) = (t1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_0_1 : RUN (AC t1_0_e0 BC_GEU (RG t1_0_e0 11) (RG t1_0_e0 9)) = (r1_0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_1_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 1)).
Lemma r_t1_1_0 : RUN (ssR1T 1) = (t1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_1_1 : RUN (AC t1_1_e0 BC_GEU (RG t1_1_e0 11) (RG t1_1_e0 9)) = (r1_1_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_2_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 2)).
Lemma r_t1_2_0 : RUN (ssR1T 2) = (t1_2_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_2_1 : RUN (AC t1_2_e0 BC_GEU (RG t1_2_e0 11) (RG t1_2_e0 9)) = (r1_2_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_3_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 3)).
Lemma r_t1_3_0 : RUN (ssR1T 3) = (t1_3_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_3_1 : RUN (AC t1_3_e0 BC_GEU (RG t1_3_e0 11) (RG t1_3_e0 9)) = (r1_3_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_4_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 4)).
Lemma r_t1_4_0 : RUN (ssR1T 4) = (t1_4_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_4_1 : RUN (AC t1_4_e0 BC_GEU (RG t1_4_e0 11) (RG t1_4_e0 9)) = (r1_4_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_5_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 5)).
Lemma r_t1_5_0 : RUN (ssR1T 5) = (t1_5_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_5_1 : RUN (AC t1_5_e0 BC_GEU (RG t1_5_e0 11) (RG t1_5_e0 9)) = (r1_5_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_6_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 6)).
Lemma r_t1_6_0 : RUN (ssR1T 6) = (t1_6_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_6_1 : RUN (AC t1_6_e0 BC_GEU (RG t1_6_e0 11) (RG t1_6_e0 9)) = (r1_6_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_7_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 7)).
Lemma r_t1_7_0 : RUN (ssR1T 7) = (t1_7_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_7_1 : RUN (AC t1_7_e0 BC_GEU (RG t1_7_e0 11) (RG t1_7_e0 9)) = (r1_7_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_8_e0 : sstate := Eval vm_compute in fst (RUN (ssR1T 8)).
Lemma r_t1_8_0 : RUN (ssR1T 8) = (t1_8_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t1_8_1 : RUN (AC t1_8_e0 BC_GEU (RG t1_8_e0 11) (RG t1_8_e0 9)) = (r1_8_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 41 (-65)))). Proof. vm_compute. reflexivity. Qed.
Definition t2L_e0 : sstate := Eval vm_compute in fst (RUN ssR2LT).
Lemma r_t2L_0 : RUN ssR2LT = (t2L_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t2L_1 : RUN (AC t2L_e0 BC_GEU (RG t2L_e0 11) (RG t2L_e0 9)) = (r2L_e1, RS_stopped (SR_branch BC_GEU (SLit 2147450879) (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t2H_e0 : sstate := Eval vm_compute in fst (RUN ssR2HT).
Lemma r_t2H_0 : RUN ssR2HT = (t2H_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Lemma r_t2H_1 : RUN (AC t2H_e0 BC_GEU (RG t2H_e0 11) (RG t2H_e0 9)) = (r2H_e1, RS_stopped (SR_branch BC_LTU (SLit 140737488355327) (SAlu ALU_ADD (SOff 18 0) (SOff 41 0)))). Proof. vm_compute. reflexivity. Qed.
(* the overflow branch at 0x46be0 is not taken: ~p >= n *)
Lemma br_novf_ltu : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d <= 2 ^ 47 ->
  0 <= n < 2 ^ 63 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 0)) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn. pose proof (br_novf_geu E pa pn d n Hd Hn Rd Rn) as G.
rewrite branch_geu_U in G. rewrite branch_ltu_U. apply negb_true_iff in G. exact G.
Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z).
Variable U : list (Z * Z).
Variables (res sz : Z).
Hypothesis HAR : ARU tfibsegs B ly S U W mem md.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + RC_SCR <= spZ regs.
Hypothesis Hshi : spZ regs <= ly_stk_hi ly.
Hypothesis HpresS : forall a, spZ regs - RC_SCR <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis GN : getr regs 9 = w64 n.
Hypothesis GP : getr regs 18 = w64 p.
Hypothesis G10 : getr regs 10 = w64 res.
Hypothesis GS : getr regs 19 = w64 sz.
Hypothesis Hsz : n <= sz < 2 ^ 64.
Hypothesis Hn : 1 <= n < 2 ^ 32.
Hypothesis Hp : 0 <= p.
Hypothesis Hpn : p + n <= 2 ^ 63.
Hypothesis HAM : amem_range p n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n.
Hypothesis HHULL : shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Definition POSTr : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs RC_END regs' mem' md' /\
ARU tfibsegs B ly S U W mem' md' /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 21 -> r <> 22 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = w64 res /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(forall z : word, ~ (spZ regs - RC_SCR <= bv_unsigned z < spZ regs) -> mem' z = mem z).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := p / 8.
Let g1 : Z := (p + n - 1) / 8.
Let du : Z := (p + 7) / 8 * 8.
Let de : Z := (p + n) / 8 * 8.
Let gu : Z := (p + 7) / 8.
Let ge : Z := (p + n) / 8.
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 72 <= sp0 /\ sp0 mod 16 = 0 /\ p + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 72 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfibsegs H (unpoison U mem)).
Proof.
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hshi'. pose proof HAM as HAM'.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, RC_SCR in *. subst sp0 H.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact HpresS | exact (ARU_ARm tfibsegs B ly S U W mem md HAR)].
Qed.
Lemma finishR : forall E ss ms mat,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeR ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - RC_SCR <= a < sp0 - RC_STK -> apresent H (ms_mem ms) a) ->
POSTr W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros E ss ms mat HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hstop. unfold RC_SCR, RC_STK in *.
unfold shapeR in Hsh. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (RD : forall (r : bv 5) v, reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E ss ms r HS). }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 72 <= a < sp0) -> aview tfibsegs H (ms_mem ms) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PW : forall a, sp0 - 64 <= a < sp0 -> apresent H (ms_mem ms) a).
{ intros a Ha. apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold RC_STK. lia. }
assert (PM : forall a, apresent H mem a -> apresent H (ms_mem ms) a).
{ intros a Hpa. pose proof Hpa as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms) a). rewrite (AE2y.apresent_mod _ mem a) in Hpa.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 72)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms) a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hpa]|].
destruct (Z_lt_le_dec a' (sp0 - 64)) as [L2|L2]; [apply PRS; lia|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PW; lia|].
apply (apresent_same H mem (ms_mem ms) a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hpa]. }
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
split; [rewrite Hshape; reflexivity|].
split; [|split; [|split; [|split; [|split; [|split]]]]].
-
apply (ARU_frame tfibsegs B LAWS ly S U W mem md (ms_mem ms) _ HAR).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hs. exact (ARU_stack tfibsegs B LAWS ly S U W mem md a HAR ltac:(lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 72)) as [L1|L1]; [rewrite AV by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV by lia; exact Hv].
apply aview_some_of_apresent. destruct (Z_lt_le_dec a' (sp0 - 64)); [apply PRS; lia | apply PW; lia].
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md mat)).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ Bpres ltac:(lia) ltac:(lia)).
-
intros r Hr H9 H18 H21 H22. unfold acallee_saved in Hr. rewrite forallb_forall in HK.
assert (Hin : In r KEPT) by (unfold KEPT; cbn; lia).
specialize (HK r Hin). cbn beta in HK.
assert (Hr32 : 0 <= r < 32) by lia.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK. }
cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- apply with_vm_backing_same.
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. exact G10.
- intros a Hr Hs. apply AV; [exact Hr | exact Hs].
- exact PM.
- intros z Hz. apply MEQ. exact Hz.
Qed.
Local Notation Env := (AE2y.Env regs).
Lemma Env_reg : forall extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env extra) i = getr regs r.
Proof. intros. apply AE2y.Env_reg. assumption. Qed.
Lemma Env_x : forall extra j z, nth_error extra j = Some z -> ew (Env extra) (32 + j) = Z_to_bv 64 z.
Proof. intros. apply AE2y.Env_x. assumption. Qed.
Lemma Env2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. intros extra. rewrite (Env_reg extra 2 2%bv eq_refl). reflexivity. Qed.
Lemma EnvP : forall extra, ew (Env extra) 18 = Z_to_bv 64 p.
Proof. intros extra. rewrite (Env_reg extra 18 18%bv eq_refl). exact GP. Qed.
Lemma EnvN : forall extra, nth_error extra 9 = Some n -> ew (Env extra) 41 = Z_to_bv 64 n.
Proof. intros extra He. exact (Env_x extra 9 n He). Qed.
Lemma ent_stk : forall extra, region_ok tfibsegs (Env extra) (mrestrict H mem) stkR.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold stkR, RC_STK.
apply (region_ok_stack tfibsegs (Env extra) _ 2 sp0 (- 64)); [exact (Env2 extra) | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Bpres. lia.
Qed.
Lemma ent_ro : forall extra, Forall (region_ok tfibsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros extra. exact (icpt_rodata_okU B TB ly S U W mem md (Env extra) HAR). Qed.
Lemma ent1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 0 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 0) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 0 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 0))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 0 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 1) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 1 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 1))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 1 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 2 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 2) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 2 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 2))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 2 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 3 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 3) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 3 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 3))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 3 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 4 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 4) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 4 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 4))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 4 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 5 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 5) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 5 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 5))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 5 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 6 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 6) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 6 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 6))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 6 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 7 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 7) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 7 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 7))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 7 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 8 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1T 8) (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Hn64 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1T.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shreg1 8 :: map ro_region icpt_rodata) None (mkFacts factsR1 [] (aliases1 8))) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply ent_ro]].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) Hp); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 8 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent2L : forall b1, 64 < n -> p + n <= kLowMemEnd - 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]) ssR2LT (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (apply (Env_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (apply (Env_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E9. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (p + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (p + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR2LT.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2L [] aliases2)) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply Forall_cons; [| apply ent_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n g0 HRA ltac:(lia) Hp). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkR, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR2L]. unfold afact_ok. cbn [af_lo af_hi af_al2].
assert (E19 : ew EE 19 = Z_to_bv 64 sz) by exact (eq_trans (Env_reg [g0; g1; b1; 0; 0; du; de; gu; ge; n] 19 19%bv eq_refl) GS).
rewrite E2, E9, E10, E32, E33, E34, E37, E38, E39, E40, E19, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom EE 33 g1 E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 18 p 7 E9), (U_atom EE 37 du E37) by lia. pose proof (Z.div_mod (p + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 18 41 p n E9 E10), (U_atom EE 38 de E38) by lia. pose proof (Z.div_mod (p + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma ent2H : forall b1, 64 < n -> kHighMemBeg <= p /\ p + n <= kHighMemEnd - 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]) ssR2HT (restrict H (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 Hn64 Hrg Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg.
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E37 : ew EE 37 = Z_to_bv 64 du) by (apply (Env_x _ 5); reflexivity).
assert (E38 : ew EE 38 = Z_to_bv 64 de) by (apply (Env_x _ 6); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as E9. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (p + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (p + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR2HT.
apply (st_ok_regs tfibsegs EE (mkSS RT_ENTRY sr_atoms (stkR :: shregs2 ++ map ro_region icpt_rodata) None (mkFacts factsR2H [] aliases2)) _ regsF).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, E10; unfold EE; rewrite (AE2y.Env_reg regs _ 9 9%bv eq_refl), GN; reflexivity) | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10'; apply bv_eq; vm_compute; reflexivity) ] |]).
destruct Hr. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; 0; 0; du; de; gu; ge; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [apply ent_stk | apply Forall_cons; [| apply Forall_cons; [| apply ent_ro]]].
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|].
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n g0 HRA ltac:(lia) Hp). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkR, shregs2, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold RC_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR2H]. unfold afact_ok. cbn [af_lo af_hi af_al2].
assert (E19 : ew EE 19 = Z_to_bv 64 sz) by exact (eq_trans (Env_reg [g0; g1; b1; 0; 0; du; de; gu; ge; n] 19 19%bv eq_refl) GS).
rewrite E2, E9, E10, E32, E33, E34, E37, E38, E39, E40, E19, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8. repeat split; try lia; try apply Z.mod_1_r.
all: first [rewrite (proj2 Hgu) | rewrite (proj2 Hge)]; rewrite Z.mul_comm; apply Z_mod_mult.
+ cbn [f_alias aliases2 alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom EE 33 g1 E33) by lia. reflexivity.
* apply U_inj. rewrite U_and_m8, (U_atom_off EE 18 p 7 E9), (U_atom EE 37 du E37) by lia. pose proof (Z.div_mod (p + 7) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_and_m8, (U_add2 EE 18 41 p n E9 E10), (U_atom EE 38 de E38) by lia. pose proof (Z.div_mod (p + n) 8 ltac:(lia)). lia.
* apply U_inj. rewrite U_srl3, (U_atom EE 37 du E37), (U_atom EE 39 gu E39) by lia. rewrite (proj2 Hgu), Z.mul_comm, Z.div_mul by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_atom EE 38 de E38), (U_atom EE 40 ge E40) by lia. rewrite (proj2 Hge), Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Lemma path1_0 : n <= 64 -> g1 - g0 = 0 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_0_e0 11) (RG t1_0_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_0_e1 12) (RG r1_0_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_0_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450880 E32) by lia. f_equal. subst h2. replace (g0 + 2147450880) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_0_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_0_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_0_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_0_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_0n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 0%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_1 : n <= 64 -> g1 - g0 = 1 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_1_e0 11) (RG t1_1_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_1_e1 12) (RG r1_1_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_1_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450881 E32) by lia. f_equal. subst h2. replace (g0 + 2147450881) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_1_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_1_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_1_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_1_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_1n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 1%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_2 : n <= 64 -> g1 - g0 = 2 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_2_e0 11) (RG t1_2_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_2_e1 12) (RG r1_2_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_2_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450882 E32) by lia. f_equal. subst h2. replace (g0 + 2147450882) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_2_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_2_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_2_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_2_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_2n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 2%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_3 : n <= 64 -> g1 - g0 = 3 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_3_e0 11) (RG t1_3_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_3_e1 12) (RG r1_3_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_3_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450883 E32) by lia. f_equal. subst h2. replace (g0 + 2147450883) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_3_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_3_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_3_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_3_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_3n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 3%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_4 : n <= 64 -> g1 - g0 = 4 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_4_e0 11) (RG t1_4_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_4_e1 12) (RG r1_4_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_4_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450884 E32) by lia. f_equal. subst h2. replace (g0 + 2147450884) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_4_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_4_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_4_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_4_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_4n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 4%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_5 : n <= 64 -> g1 - g0 = 5 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_5_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_5_e0 11) (RG t1_5_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_5_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_5_e1 12) (RG r1_5_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_5_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_5_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450885 E32) by lia. f_equal. subst h2. replace (g0 + 2147450885) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_5_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_5_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_5_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_5_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_5z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_5z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_5_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_5n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_5n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 5%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_5n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_5n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_6 : n <= 64 -> g1 - g0 = 6 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_6_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_6_e0 11) (RG t1_6_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_6_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_6_e1 12) (RG r1_6_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_6_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_6_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450886 E32) by lia. f_equal. subst h2. replace (g0 + 2147450886) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_6_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_6_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_6_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_6_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_6z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_6z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_6_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_6n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_6n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 6%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_6n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_6n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_7 : n <= 64 -> g1 - g0 = 7 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_7_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_7_e0 11) (RG t1_7_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_7_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_7_e1 12) (RG r1_7_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_7_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_7_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450887 E32) by lia. f_equal. subst h2. replace (g0 + 2147450887) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_7_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_7_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_7_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_7_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_7z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_7z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_7_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_7n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_7n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 7%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_7n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_7n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path1_8 : n <= 64 -> g1 - g0 = 8 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64' Ht. assert (Hn64 : 1 <= n <= 64) by lia.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
pose proof HHULL as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem p n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem p n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EE2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t1_8_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_8_e0 11) (RG t1_8_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t1_8_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r1_8_e1 12) (RG r1_8_e1 11) HS2 (br_cls65_small EE 41 n EEN Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r1_8_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (r1_8_e2) ms3 _ 14%bv 14%bv 472835 h1 35 56 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None) by (intros z Hz; rewrite HM4; apply PSL3; exact Hz).
clear HW4 HM4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450888 E32) by lia. f_equal. subst h2. replace (g0 + 2147450888) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold RC_STK, RC_SCR, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc r1_8_e2 [((14%bv : bv 5), SOff 35 0)] (ss_pc r1_8_e2 + 4)) ms4 _ 15%bv 15%bv 505731 h2 36 56 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None) by (intros z Hz; rewrite HM5; apply PSL4; exact Hz).
clear HW5 HM5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_r1_8_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_8_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS6' r_r1_8z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
apply SRr_ret. apply (finishR EE r1_8z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms7 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL7 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_8_e3 14) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r1_8n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_8n_e0 11) (SLit 0) HS7 (qc_flag_zero EE 8%nat 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE RC_END _ _ _ _ _ HS7' r_r1_8n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE r1_8n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path2L : 64 < n -> p + n <= kLowMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (p + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (p + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)); lia).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EE2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EEP. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (ent2L b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t2L_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t2L_e0 11) (RG t2L_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t2L_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG r2L_e1 18) HS2 (br_end_low EE 18 41 p n EEP EEN Hp ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r2L_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r2L_e2 8) (RG r2L_e2 18) HS3 (br_beg_lt_end EE 18 41 p n EEP EEN Hp ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_r2L_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r2L_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Lz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r2Lz_e0 19) (RG r2Lz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Lz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) p n (a - SB) HRA); [unfold SB in *; lia | exact Hp]. }
assert (R10 : sv_denot EE (RG r2Lz_e1 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG r2Lz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG r2Lz_e1 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG r2Lz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG r2Lz_e1 2) = Z_to_bv 64 (sp0 - 64)).
{ change (sv_denot EE (RG r2Lz_e1 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG r2Lz_e1 1) = Z_to_bv 64 351396).
{ change (sv_denot EE (RG r2Lz_e1 1)) with (sv_denot EE (SLit 351396)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem r2Lz_e1)).
{ cbn [ss_mem r2Lz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE r2Lz_e1 ms6 _ 56 (ss_mem r2Lz_e1) (gu + SB) (ge - gu) (sp0 - 64) 351396 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 351396 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (subst EE'; rewrite ew_havoc_old by lia; exact EEN).
assert (MEQ7 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold RC_SCR in *; lia). apply MEQ6. unfold RC_SCR, RC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold RC_SCR, RC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS7 r_r2Lz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE' r2Lz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (p + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG r2L_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Ln_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG r2Ln_e0 12) (RG r2Ln_e0 11) HS5 (rp_blt_last EE 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Ln_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r2Ln_e1 19) (RG r2Ln_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r2Ln_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) p n (a - SB) HRA); [unfold SB in *; lia | exact Hp]. }
assert (R10 : sv_denot EE (RG r2Ln_e2 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG r2Ln_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG r2Ln_e2 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG r2Ln_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG r2Ln_e2 2) = Z_to_bv 64 (sp0 - 64)).
{ change (sv_denot EE (RG r2Ln_e2 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG r2Ln_e2 1) = Z_to_bv 64 351396).
{ change (sv_denot EE (RG r2Ln_e2 1)) with (sv_denot EE (SLit 351396)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem r2Ln_e2)).
{ cbn [ss_mem r2Ln_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE r2Ln_e2 ms7 _ 56 (ss_mem r2Ln_e2) (gu + SB) (ge - gu) (sp0 - 64) 351396 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 351396 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (subst EE'; rewrite ew_havoc_old by lia; exact EEN).
assert (MEQ8 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold RC_SCR in *; lia). apply MEQ7. unfold RC_SCR, RC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold RC_SCR, RC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS8 r_r2Ln_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. apply (finishR EE' r2Ln_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma path2H : 64 < n -> kHighMemBeg <= p /\ p + n <= kHighMemEnd - 1 -> SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Hrg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 RT_ENTRY) with (Z_to_bv 64 RT_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (PSL0 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem (mkst regs (Z_to_bv 64 RT_ENTRY) mem (seg_rom tfibsegs)) z <> None).
{ intros z Hz. cbn [ms_mem mkst]. unfold RC_SCR, RC_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
pose proof Hrg as Hrg'. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hrg'.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hgu : 8 * gu <= p + 7 < 8 * gu + 8 /\ du = 8 * gu) by (subst gu du; pose proof (Z.div_mod (p + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)); lia).
assert (Hge : 8 * ge <= p + n < 8 * ge + 8 /\ de = 8 * ge) by (subst ge de; pose proof (Z.div_mod (p + n) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)); lia).
set (EE := Env [g0; g1; b1; 0; 0; du; de; gu; ge; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EE2. pose proof (EnvP [g0; g1; b1; 0; 0; du; de; gu; ge; n]) as EEP. pose proof (EnvN [g0; g1; b1; 0; 0; du; de; gu; ge; n] eq_refl) as EEN. fold EE in EE2, EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E33 : ew EE 33 = Z_to_bv 64 g1) by (apply (Env_x _ 1); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E39 : ew EE 39 = Z_to_bv 64 gu) by (apply (Env_x _ 7); reflexivity).
assert (E40 : ew EE 40 = Z_to_bv 64 ge) by (apply (Env_x _ 8); reflexivity).
assert (E32u : bv_unsigned (ew EE 32) = g0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E33u : bv_unsigned (ew EE 33) = g1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (ent2H b1 Hn64 Hrg Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_t2H_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL1 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms1 z <> None).
{ intros z Hz. rewrite (HF1 z); [apply PSL0; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t2H_e0 11) (RG t2H_e0 9) HS1 (br_novf_ltu EE 18 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'. clear HS1.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_t2H_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL2 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms2 z <> None).
{ intros z Hz. rewrite (HF2 z); [apply PSL1; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG r2H_e1 18) HS2 (br_end_high EE 18 41 p n EEP EEN Hp ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_r2H_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL3 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms3 z <> None).
{ intros z Hz. rewrite (HF3 z); [apply PSL2; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF3 HFr3.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r2H_e2 8) (RG r2H_e2 18) HS3 (br_beg_lt_end EE 18 41 p n EEP EEN Hp ltac:(lia) ltac:(lia))) as HS3'.
change (neg_bc BC_GEU) with BC_LTU in HS3'. clear HS3.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS3' r_r2H_3)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z).
{ intros z Hz. rewrite (HF4 z); [apply MEQ3; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL4 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms4 z <> None).
{ intros z Hz. rewrite (HF4 z); [apply PSL3; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF4 HFr4.
destruct (Z.eq_dec b1 0) as [Hbz|Hbz].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r2H_e3 11) (SLit 0) HS4 (rp_b1_zero EE 34 ltac:(rewrite E34, Hbz; reflexivity))) as HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Hz_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r2Hz_e0 19) (RG r2Hz_e0 10) HS5 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS5'.
change (neg_bc BC_GEU) with BC_LTU in HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Hz_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfibsegs (mrestrict H (ms_mem ms6)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms6 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL6 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms6) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms6) a) by (apply MEQ6; rewrite unsigned_lit_small by lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) p n (a - SB) HRA); [unfold SB in *; lia | exact Hp]. }
assert (R10 : sv_denot EE (RG r2Hz_e1 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG r2Hz_e1 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG r2Hz_e1 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG r2Hz_e1 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG r2Hz_e1 2) = Z_to_bv 64 (sp0 - 64)).
{ change (sv_denot EE (RG r2Hz_e1 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG r2Hz_e1 1) = Z_to_bv 64 351396).
{ change (sv_denot EE (RG r2Hz_e1 1)) with (sv_denot EE (SLit 351396)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem r2Hz_e1)).
{ cbn [ss_mem r2Hz_e1]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE r2Hz_e1 ms6 _ 56 (ss_mem r2Hz_e1) (gu + SB) (ge - gu) (sp0 - 64) 351396 HS6 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 351396 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HM7 & HP7). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms7)) MZ_CLOB)) in HS7.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (subst EE'; rewrite ew_havoc_old by lia; exact EEN).
assert (MEQ7 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HM7 z) by (unfold RC_SCR in *; lia). apply MEQ6. unfold RC_SCR, RC_STK in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. apply HP7. unfold RC_SCR, RC_STK in *. lia. }
clear HM7 HP7 SLW SZERO R10 R11 R2 R1 HOFF HS6.
eapply SRr_bind; [apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS7 r_r2Hz_2)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. rewrite (HF8 z); [apply PSL7; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF8 HFr8.
apply SRr_ret. apply (finishR EE' r2Hz_e2 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ8. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms8 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL8 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
+
assert (Hlt : (p + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hbz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG r2H_e3 11) (SLit 0) HS4 (rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS4'.
change (neg_bc BC_EQ) with BC_NE in HS4'. clear HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS4' r_r2Hn_0)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z).
{ intros z Hz. rewrite (HF5 z); [apply MEQ4; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL5 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms5 z <> None).
{ intros z Hz. rewrite (HF5 z); [apply PSL4; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG r2Hn_e0 12) (RG r2Hn_e0 11) HS5 (rp_blt_last EE 18 41 34 p n b1 EEP EEN E34 Hp ltac:(lia) Hpn Hlt)) as HS5'. clear HS5.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5' r_r2Hn_1)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL6 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms6 z <> None).
{ intros z Hz. rewrite (HF6 z); [apply PSL5; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF6 HFr6.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG r2Hn_e1 19) (RG r2Hn_e1 10) HS6 (br_sbeg_lt_send EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(unfold SB; lia))) as HS6'.
change (neg_bc BC_GEU) with BC_LTU in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_r2Hn_2)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - RC_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL7 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms7 z <> None).
{ intros z Hz. rewrite (HF7 z); [apply PSL6; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF7 HFr7.
assert (SLW : forall z, sp0 - 64 - 8 <= z < sp0 - 64 -> writable_at tfibsegs (mrestrict H (ms_mem ms7)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. unfold RC_SCR, RC_STK in *.
destruct (ms_mem ms7 (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL7 (Z_to_bv 64 z) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs H (ms_mem ms7) a = Some 0).
{ intros a Ha. unfold SB in Ha. rewrite (aview_same H mem (ms_mem ms7) a) by (apply MEQ7; rewrite unsigned_lit_small by lia; unfold RC_STK, RC_SCR, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (ra_granule_zero (aview tfibsegs H mem) p n (a - SB) HRA); [unfold SB in *; lia | exact Hp]. }
assert (R10 : sv_denot EE (RG r2Hn_e2 10) = Z_to_bv 64 (gu + SB)).
{ change (sv_denot EE (RG r2Hn_e2 10)) with (sv_denot EE (SOff 39 SB)). cbn [sv_denot]. rewrite E39, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot EE (RG r2Hn_e2 11) = Z_to_bv 64 (ge - gu)).
{ change (sv_denot EE (RG r2Hn_e2 11)) with (sv_denot EE (SAlu ALU_ADD (SMd M_MUL (SOff 39 0) (SLit (-1))) (SOff 40 0))). exact (U_mz_len EE 39 40 gu ge E39 E40 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot EE (RG r2Hn_e2 2) = Z_to_bv 64 (sp0 - 64)).
{ change (sv_denot EE (RG r2Hn_e2 2)) with (sv_denot EE (SOff 2 (-64))). cbn [sv_denot]. rewrite EE2. f_equal; lia. }
assert (R1 : sv_denot EE (RG r2Hn_e2 1) = Z_to_bv 64 351396).
{ change (sv_denot EE (RG r2Hn_e2 1)) with (sv_denot EE (SLit 351396)). apply bv_eq. vm_compute. reflexivity. }
assert (HOFF : Forall (fun r => 0 <= base_val EE (YP09.r_base r) + YP09.r_lo r /\ base_val EE (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val EE (YP09.r_base r) + YP09.r_hi r <= sp0 - 64 - 8 \/ sp0 - 64 <= base_val EE (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem r2Hn_e2)).
{ cbn [ss_mem r2Hn_e2]. repeat (apply Forall_cons); try apply Forall_nil.
all: cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?EE2, ?E32u, ?E33u; unfold RC_STK, SB, kHighMemBeg in *; repeat split; lia. }
eapply SRr_bind; [exact (icpt_memisz W EE r2Hn_e2 ms7 _ 56 (ss_mem r2Hn_e2) (gu + SB) (ge - gu) (sp0 - 64) 351396 HS7 eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB, kHighMemBeg in *; lia) ltac:(unfold TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(lia)
(ret_ok_lit 351396 ltac:(lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HM8 & HP8). rewrite ?wvb_wvb in *.
set (EE' := havoc EE 56 (map (getr (ms_regs ms8)) MZ_CLOB)) in HS8.
assert (EE'reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE' i = getr regs r).
{ intros i r Hi. subst EE'. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (EE'2 : bv_unsigned (ew EE' 2) = sp0) by (subst EE'; rewrite ew_havoc_old by lia; exact EE2).
assert (EE'N : ew EE' 41 = Z_to_bv 64 n) by (subst EE'; rewrite ew_havoc_old by lia; exact EEN).
assert (MEQ8 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HM8 z) by (unfold RC_SCR in *; lia). apply MEQ7. unfold RC_SCR, RC_STK in *. lia. }
assert (PSL8 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms8 z <> None).
{ intros z Hz. apply HP8. unfold RC_SCR, RC_STK in *. lia. }
clear HM8 HP8 SLW SZERO R10 R11 R2 R1 HOFF HS7.
eapply SRr_bind; [apply (icpt_phase_to W EE' RC_END _ _ _ _ _ HS8 r_r2Hn_3)|].
cbv beta. intros W9 c9 _ (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). rewrite ?wvb_wvb in *.
assert (MEQ9 : forall z : word, ~ (sp0 - RC_SCR <= bv_unsigned z < sp0) -> ms_mem ms9 z = mem z).
{ intros z Hz. rewrite (HF9 z); [apply MEQ8; unfold RC_STK, RC_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
assert (PSL9 : forall z : word, sp0 - RC_SCR <= bv_unsigned z < sp0 - RC_STK -> ms_mem ms9 z <> None).
{ intros z Hz. rewrite (HF9 z); [apply PSL8; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE' _ (bv_unsigned z) 2 (- RC_STK) 0 sp0 _ EE'2 Hin) as X; [vm_compute; reflexivity|]. unfold RC_STK, RC_SCR in *. lia. }
clear HF9 HFr9.
apply SRr_ret. apply (finishR EE' r2Hn_e3 ms9 mat9 HS9 eq_refl ltac:(vm_compute; reflexivity) EE'reg).
- intros z Hz. apply MEQ9. unfold RC_SCR, RC_STK in *. lia.
- intros a Ha. unfold RC_SCR, RC_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms9 (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL9 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. lia. Qed.
Theorem vsn_wr_check_srrUT : SRr tfibsegs W (cfg_at tfibsegs RT_ENTRY regs mem md) POSTr.
Proof.
destruct (Z_le_gt_dec n 64) as [Hle|Hgt].
- assert (Hg0 : 8 * g0 <= p < 8 * g0 + 8) by (subst g0; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
destruct (t_cases (g1 - g0) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply path1_0 | apply path1_1 | apply path1_2 | apply path1_3 | apply path1_4 | apply path1_5 | apply path1_6 | apply path1_7 | apply path1_8]; assumption.
- destruct HAM as [HL|HH]; [apply path2L; [lia | exact HL] | apply path2H; [lia | exact HH]].
Qed.
End f.
End e.
