(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6y.v's walk of the wrapper's shadow check (with AE7e.v's entry registers), restated for the strlen wrapper of libreac/fuzz_disco: a0 = n - 1 and s1 = 1 at RC_ENTRY, the size test is decided by the engine, the code table adds the wrapper body, and the common-flags pointer and the strlen flag are read-only cells; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Rt/StrlenChk.v, with its module paths, addresses and numbers changed; 193 of its 495 lines of code are new or changed and 2194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen_chk1.v and proofs/libreac/fuzz_identity/lib/A/FMstrlen_chk2.v at 6ebe35ba632; the range check of the set in the strcspn wrapper of reac-pw/fuzz_pin.asan (0x42d38 .. 0x42d88) for n <= 2: the symbolic runs are recomputed over tbl_cs (p in s3, a0 = n - 1, no init test and no flags-byte load at this entry), only t = 0 and t = 1 are kept, and the result is FMcs0's CS_CHK1. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE34
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0l
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0m
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0x
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1w
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE20
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import FMcs0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* The range check of the set [p, p + n) in the strcspn wrapper of fuzz_pin.asan, from 0x42d38 (CS1_ENTRY, the return
   address of the call of the runtime's internal_strlen) to 0x42d88 (CS1_END), with s3 = p and a0 = n - 1:
     42d38 s2 = a0 + 1 ; 42d3c a1 = ~s3 ; 42d40 bltu a1, s2 (wrap of p + n: not taken)
     42d44 a1 = 64 ; 42d48 bgeu a0, a1 (n - 1 >= 64: not taken)
     42d4c-42d70 the addresses of the two aligned words that hold the shadow bytes of p and of p + n - 1
     42d74 / 42d78 the two 8-byte loads (cs_ld8, atoms 35 and 36) ; 42d7c or ; 42d80 a0 = s5 ; 42d84 bnez -> 42f18
     42f18-42f48 the byte-exact test of the shadow bytes (its flag is 0 for an addressable range: back to 42d88)
   For n <= 2 only t = g1 - g0 = 0 or 1 happens. These paths call nothing and store nothing. *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the stack window the symbolic states carry below sp (nothing is written in it) *)
Definition CS1_STK : Z := 64.
Definition shreg1 (t : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YP09.mkChunk SB (CZero t)] else []) ++ [YP09.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).
Definition aliases1 (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 19 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 19 (-1)) (SOff 41 0)) (SLit 3), SOff 32 t) ].
Definition stkR : YP09.region := YP09.mkRegion (Some 2%nat) (- CS1_STK) 0 (- CS1_STK) 0 [].
Definition factsR1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (19%nat, mkAF 0 (2^47) 0); (41%nat, mkAF 1 2 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition regsS : list sv := Eval vm_compute in (firstn 10 sr_atoms ++ [SOff 41 (-1)] ++ skipn 11 sr_atoms).
Definition ssR1 (t : Z) : sstate := mkSS CS1_ENTRY regsS (stkR :: shreg1 t :: map ro_region cs_rodata) None (mkFacts factsR1 [] (aliases1 t)).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_cs FUEL s.
Definition RUNTO (s : sstate) := sym_run_toN tfibsegs tbl_cs FUEL CS1_END s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* the wrap test stops the run; the length test is decided from the fact 1 <= n <= 2; the run stops at the load
   0x42d74 of the aligned word holding the first shadow byte; the two loads are done by cs_ld8 (atoms 35, 36); the or
   of the two words decides the byte-exact path 0x42f18, whose flag (a1) is the qc_flag of AE2y. *)
Definition r1_0_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 0)).
Lemma r_r1_0_0 : RUN (ssR1 0) = (r1_0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 19 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 11) (RG r1_0_e0 18))).
Lemma r_r1_0_1 : RUN (AC r1_0_e0 BC_GEU (RG r1_0_e0 11) (RG r1_0_e0 18)) = (r1_0_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_0_e1 [((10%bv : bv 5), SOff 35 0)] 0x42d78) [((14%bv : bv 5), SOff 36 0)] 0x42d7c)).
Lemma r_r1_0_2 : RUN (set_regs_pc (set_regs_pc r1_0_e1 [((10%bv : bv 5), SOff 35 0)] 0x42d78) [((14%bv : bv 5), SOff 36 0)] 0x42d7c) = (r1_0_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_0_e2 BC_EQ (RG r1_0_e2 14) (SLit 0))).
Lemma r_r1_0z_0 : RUNTO (AC r1_0_e2 BC_EQ (RG r1_0_e2 14) (SLit 0)) = (r1_0z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_0n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_0_e2 BC_NE (RG r1_0_e2 14) (SLit 0))).
Lemma r_r1_0n_0 : RUN (AC r1_0_e2 BC_NE (RG r1_0_e2 14) (SLit 0)) = (r1_0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 19 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_0n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 11) (SLit 0))).
Lemma r_r1_0n_1 : RUNTO (AC r1_0n_e0 BC_EQ (RG r1_0n_e0 11) (SLit 0)) = (r1_0n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e0 : sstate := Eval vm_compute in fst (RUN (ssR1 1)).
Lemma r_r1_1_0 : RUN (ssR1 1) = (r1_1_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 19 0) (SLit (-1))) (SOff 41 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e1 : sstate := Eval vm_compute in fst (RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 11) (RG r1_1_e0 18))).
Lemma r_r1_1_1 : RUN (AC r1_1_e0 BC_GEU (RG r1_1_e0 11) (RG r1_1_e0 18)) = (r1_1_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc r1_1_e1 [((10%bv : bv 5), SOff 35 0)] 0x42d78) [((14%bv : bv 5), SOff 36 0)] 0x42d7c)).
Lemma r_r1_1_2 : RUN (set_regs_pc (set_regs_pc r1_1_e1 [((10%bv : bv 5), SOff 35 0)] 0x42d78) [((14%bv : bv 5), SOff 36 0)] 0x42d7c) = (r1_1_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC r1_1_e2 BC_EQ (RG r1_1_e2 14) (SLit 0))).
Lemma r_r1_1z_0 : RUNTO (AC r1_1_e2 BC_EQ (RG r1_1_e2 14) (SLit 0)) = (r1_1z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition r1_1n_e0 : sstate := Eval vm_compute in fst (RUN (AC r1_1_e2 BC_NE (RG r1_1_e2 14) (SLit 0))).
Lemma r_r1_1n_0 : RUN (AC r1_1_e2 BC_NE (RG r1_1_e2 14) (SLit 0)) = (r1_1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 19 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition r1_1n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 11) (SLit 0))).
Lemma r_r1_1n_1 : RUNTO (AC r1_1n_e0 BC_EQ (RG r1_1n_e0 11) (SLit 0)) = (r1_1n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
(* the region writes s2 (n) and sets a0 = s5; every other callee-saved register keeps its entry value *)
Definition KEPT : list Z := [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeR (ss : sstate) : bool :=
(ss_pc ss =? CS1_END) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - CS1_STK) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 21 0) && forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT.
Definition win_chk (rs : smem) : bool := forallb (fun t => win_eqb t (Some 2%nat, - CS1_STK, 0) || (snd t <=? snd (fst t))) (windows rs).
Lemma md_wvb_gen : forall m : Model, m = with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z).
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + CHK_SCR <= spZ regs.
Hypothesis Hshi : spZ regs <= ly_stk_hi ly.
Hypothesis HpresS : forall a, spZ regs - CHK_SCR <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis GN : getr regs 10 = w64 (n - 1).
Hypothesis GP : getr regs 19 = w64 p.
Hypothesis Hp1 : 0 < p.
Hypothesis Hn : 1 <= n <= 2.
Hypothesis Hpn : p + n <= 2 ^ 63.
Hypothesis HAM : amem_range p n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n.
Hypothesis HHULL : shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Definition POSTr : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs CS1_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 18 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = getr regs 21 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHK_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := p / 8.
Let g1 : Z := (p + n - 1) / 8.
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + 72 <= sp0 /\ sp0 mod 16 = 0 /\ p + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - 72 <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfibsegs H mem).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hshi'. pose proof HAM as HAM'.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, CHK_SCR in *. subst sp0 H.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact HpresS | exact (proj1 HAR)].
Qed.
Lemma finishR : forall E ss ms mat,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeR ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
(forall z : word, ~ (sp0 - CHK_SCR <= bv_unsigned z < sp0) -> ms_mem ms z = mem z) ->
(forall a, sp0 - CHK_SCR <= a < sp0 - CS1_STK -> apresent H (ms_mem ms) a) ->
POSTr W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros E ss ms mat HS Hrv Hsh HE MEQ PRS.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hstop. unfold CHK_SCR, CS1_STK in *.
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
{ intros a Ha. apply (st_ok_window_apresent H E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.TFIB_IMG_END, YImgTop.IMG_TOP, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold CS1_STK. lia. }
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
split; [|split; [|split; [|split; [|split]]]].
-
apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms) _ HAR).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
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
intros r Hr H18. unfold acallee_saved in Hr. rewrite forallb_forall in HK.
assert (Hin : In r KEPT) by (unfold KEPT; cbn; lia).
specialize (HK r Hin). cbn beta in HK.
assert (Hr32 : 0 <= r < 32) by lia.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK. }
cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- apply with_vm_backing_same.
- rewrite (RD 10%bv (SOff 21 0) R10). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (HE 21%nat 21%bv eq_refl).
- intros a Hr Hs. apply AV; [exact Hr | exact Hs].
- exact PM.
Qed.
Local Notation Env := (AE2y.Env regs).
Lemma Env_reg : forall extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env extra) i = getr regs r.
Proof. intros. apply AE2y.Env_reg. assumption. Qed.
Lemma Env_x : forall extra j z, nth_error extra j = Some z -> ew (Env extra) (32 + j) = Z_to_bv 64 z.
Proof. intros. apply AE2y.Env_x. assumption. Qed.
Lemma Env2 : forall extra, bv_unsigned (ew (Env extra) 2) = sp0.
Proof. intros extra. rewrite (Env_reg extra 2 2%bv eq_refl). reflexivity. Qed.
Lemma EnvP : forall extra, ew (Env extra) 19 = Z_to_bv 64 p.
Proof. intros extra. rewrite (Env_reg extra 19 19%bv eq_refl). exact GP. Qed.
Lemma EnvN : forall extra, nth_error extra 9 = Some n -> ew (Env extra) 41 = Z_to_bv 64 n.
Proof. intros extra He. exact (Env_x extra 9 n He). Qed.
Lemma ent_stk : forall extra, region_ok tfibsegs (Env extra) (mrestrict H mem) stkR.
Proof.
intros extra. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). unfold stkR, CS1_STK.
apply (region_ok_stack tfibsegs (Env extra) _ 2 sp0 (- 64)); [exact (Env2 extra) | lia | lia |].
intros a Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, YImgTop.IMG_TOP, kHighMemBeg in *; lia|]. apply Bpres. lia.
Qed.
Lemma ent_ro : forall extra, Forall (region_ok tfibsegs (Env extra) (mrestrict H mem)) (map ro_region cs_rodata).
Proof. intros extra. pose proof basics as (_ & _ & _ & _ & _ & BM). exact (rodata_ok B TB cs_rodata ly S H mem (Env extra) (cs_rodata_chk ly) BM). Qed.
(* the memory frame the phases keep: outside [sp0 - k, sp0) the memory is the entry memory, and the 8 bytes below
   the region's stack window stay present *)
Definition MP (k : Z) (m' : word -> option byte) : Prop :=
(forall z : word, ~ (sp0 - k <= bv_unsigned z < sp0) -> m' z = mem z) /\
(forall z : word, sp0 - CHK_SCR <= bv_unsigned z < sp0 - CS1_STK -> m' z <> None).
Lemma MP0 : MP CS1_STK (ms_mem (mkst regs (Z_to_bv 64 CS1_ENTRY) mem (seg_rom tfibsegs))).
Proof.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM). split; [intros; reflexivity|].
intros z Hz. cbn [ms_mem mkst]. unfold CHK_SCR, CS1_STK in Hz. destruct (Bpres (bv_unsigned z) ltac:(lia)) as [_ [b Hb]]. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate.
Qed.
Lemma frame_upd : forall E rs (m m1 : word -> option byte) k, CS1_STK <= k -> bv_unsigned (ew E 2) = sp0 -> win_chk rs = true ->
frame_of E rs m m1 -> MP k m -> MP k m1.
Proof.
intros E rs m m1 k Hk E2 Hw HF [M P]. split.
- intros z Hz. rewrite (HF z); [apply M; exact Hz|]. intros Hin.
pose proof (in_wrange_single_b E rs (bv_unsigned z) 2 (- CS1_STK) 0 sp0 Hw E2 Hin) as X. unfold CS1_STK, CHK_SCR in *. lia.
- intros z Hz. rewrite (HF z); [apply P; exact Hz|]. intros Hin.
pose proof (in_wrange_single_b E rs (bv_unsigned z) 2 (- CS1_STK) 0 sp0 Hw E2 Hin) as X. unfold CS1_STK, CHK_SCR in *. lia.
Qed.
Lemma phaseR : forall E ss ss' r ms mat0 k (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict H ms) -> RUN ss = (ss', RS_stopped r) ->
CS1_STK <= k -> bv_unsigned (ew E 2) = sp0 -> MP k (ms_mem ms) -> win_chk (ss_mem ss) = true ->
(forall ms1 mat1, st_ok tfibsegs E ss' (restrict H ms1) -> MP k (ms_mem ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md)) Q) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat0 md)) Q.
Proof.
intros E ss ss' r ms mat0 k Q HS Hrun Hk E2 M Hw K.
eapply SRr_bind; [exact (cs_phase W E ss ss' (RS_stopped r) ms _ HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _). rewrite wvb_collapse.
exact (K ms1 mat1 HS1 (frame_upd E (ss_mem ss) (ms_mem ms) (ms_mem ms1) k Hk E2 Hw HF1 M)).
Qed.
Lemma phaseT : forall E ss ss' ms mat0 k (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict H ms) -> RUNTO ss = (ss', RS_running) ->
CS1_STK <= k -> bv_unsigned (ew E 2) = sp0 -> MP k (ms_mem ms) -> win_chk (ss_mem ss) = true ->
(forall ms1 mat1, st_ok tfibsegs E ss' (restrict H ms1) -> MP k (ms_mem ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md)) Q) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat0 md)) Q.
Proof.
intros E ss ss' ms mat0 k Q HS Hrun Hk E2 M Hw K.
eapply SRr_bind; [exact (cs_phase_to W E CS1_END ss ss' RS_running ms _ HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & _). rewrite wvb_collapse.
exact (K ms1 mat1 HS1 (frame_upd E (ss_mem ss) (ms_mem ms) (ms_mem ms1) k Hk E2 Hw HF1 M)).
Qed.
Lemma ldR : forall E ss ms mat0 (rd rs : bv 5) (w h : Z) (kx K : nat) k (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_cs (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs H (ms_mem ms)) h = Some (bv_unsigned (ew E kx)) -> MP k (ms_mem ms) ->
(forall ms1 mat1, st_ok tfibsegs E (set_regs_pc ss [(rd, SOff kx 0)] (ss_pc ss + 4)) (restrict H ms1) -> MP k (ms_mem ms1) ->
SRr tfibsegs W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md)) Q) ->
SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat0 md)) Q.
Proof.
intros E ss ms mat0 rd rs w h kx K k Q HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw M Kc.
eapply SRr_bind; [exact (cs_ld8 W E ss ms _ rd rs w h kx K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HM1). rewrite wvb_collapse.
apply (Kc ms1 mat1 HS1). rewrite HM1. exact M.
Qed.
Lemma finishR' : forall E ss ms mat k, k <= CHK_SCR ->
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeR ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
MP k (ms_mem ms) ->
POSTr W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)).
Proof.
intros E ss ms mat k Hk HS Hrv Hsh HE [M P]. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
apply (finishR E ss ms mat HS Hrv Hsh HE).
- intros z Hz. apply M. unfold CHK_SCR, CS1_STK in *. lia.
- intros a Ha. unfold CHK_SCR, CS1_STK in *. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (P (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by lia; lia) Eb)].
Qed.
Lemma ent1_0 : forall b1 q1 q2, g1 - g0 = 0 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 0) (restrict H (mkst regs (Z_to_bv 64 CS1_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfibsegs EE (mkSS CS1_ENTRY sr_atoms (stkR :: shreg1 0 :: map ro_region cs_rodata) None (mkFacts factsR1 [] (aliases1 0))) _ regsS).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by lia; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [reflexivity | f_equal; lia]) ] |]).
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
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, cs_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold CS1_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 19 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 19 41 p n E9 E10), (U_atom_off EE 32 g0 0 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_1 : forall b1 q1 q2, g1 - g0 = 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssR1 1) (restrict H (mkst regs (Z_to_bv 64 CS1_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros b1 q1 q2 Ht Hb1 Hok. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
pose proof (Env2 [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
rewrite restrict_mkst_fx. unfold ssR1.
apply (st_ok_regs tfibsegs EE (mkSS CS1_ENTRY sr_atoms (stkR :: shreg1 1 :: map ro_region cs_rodata) None (mkFacts factsR1 [] (aliases1 1))) _ regsS).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E10, unsigned_lit_small by lia; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), GN; unfold w64; first [reflexivity | f_equal; lia]) ] |]).
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
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold stkR, shreg1, cs_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, unsigned_lit_small by lia. unfold CS1_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsR1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliases1 alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 19 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 19 41 p n E9 E10), (U_atom_off EE 32 g0 1 E32) by lia. subst g0 g1. lia.
Qed.
Lemma path1_0 : g1 - g0 = 0 -> SRr tfibsegs W (cfg_at tfibsegs CS1_ENTRY regs mem md) POSTr.
Proof.
intros Ht.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 CS1_ENTRY) with (Z_to_bv 64 CS1_ENTRY). rewrite (md_wvb_gen md) at 1. pose proof MP0 as M0.
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
pose proof (ent1_0 b1 q1 q2 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS0 r_r1_0_0 ltac:(unfold CS1_STK; lia) EE2 M0 ltac:(vm_compute; reflexivity) _).
intros ms1 mat1 HS1 M1. clear HS0 M0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG r1_0_e0 11) (RG r1_0_e0 18) HS1 (br_ovf_false EE 19 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS1' r_r1_0_1 ltac:(unfold CS1_STK; lia) EE2 M1 ltac:(vm_compute; reflexivity) _).
intros ms2 mat2 HS2 M2. clear HS1' M1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply (proj1 M2). rewrite unsigned_lit_small by lia. unfold CS1_STK, CHK_SCR, kHighMemBeg in *. lia. }
refine (ldR EE r1_0_e1 ms2 mat2 10%bv 10%bv 341251 h1 35 56 CS1_STK _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 _).
intros ms3 mat3 HS3 M3. clear HW3 HS2 M2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450880 E32) by lia. f_equal. subst h2. replace (g0 + 2147450880) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply (proj1 M3). rewrite unsigned_lit_small by lia. unfold CS1_STK, CHK_SCR, kHighMemBeg in *. lia. }
refine (ldR EE (set_regs_pc r1_0_e1 [((10%bv : bv 5), SOff 35 0)] (ss_pc r1_0_e1 + 4)) ms3 mat3 14%bv 14%bv 472835 h2 36 56 CS1_STK _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 _).
intros ms4 mat4 HS4 M4. clear HW4 HS3 M3.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS4 r_r1_0_2 ltac:(unfold CS1_STK; lia) EE2 M4 ltac:(vm_compute; reflexivity) _).
intros ms5 mat5 HS5 M5. clear HS4 M4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_0_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phaseT EE _ _ _ _ CS1_STK _ HS5' r_r1_0z_0 ltac:(unfold CS1_STK; lia) EE2 M5 ltac:(vm_compute; reflexivity) _).
intros ms6 mat6 HS6 M6. clear HS5' M5.
apply SRr_ret. exact (finishR' EE r1_0z_e0 ms6 mat6 CS1_STK ltac:(unfold CS1_STK, CHK_SCR; lia) HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg M6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_0_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS5' r_r1_0n_0 ltac:(unfold CS1_STK; lia) EE2 M5 ltac:(vm_compute; reflexivity) _).
intros ms6 mat6 HS6 M6. clear HS5' M5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_0n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 0%nat 19 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phaseT EE _ _ _ _ CS1_STK _ HS6' r_r1_0n_1 ltac:(unfold CS1_STK; lia) EE2 M6 ltac:(vm_compute; reflexivity) _).
intros ms7 mat7 HS7 M7. clear HS6' M6.
apply SRr_ret. exact (finishR' EE r1_0n_e1 ms7 mat7 CS1_STK ltac:(unfold CS1_STK, CHK_SCR; lia) HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg M7).
Qed.
Lemma path1_1 : g1 - g0 = 1 -> SRr tfibsegs W (cfg_at tfibsegs CS1_ENTRY regs mem md) POSTr.
Proof.
intros Ht.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 CS1_ENTRY) with (Z_to_bv 64 CS1_ENTRY). rewrite (md_wvb_gen md) at 1. pose proof MP0 as M0.
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
pose proof (ent1_1 b1 q1 q2 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS0 r_r1_1_0 ltac:(unfold CS1_STK; lia) EE2 M0 ltac:(vm_compute; reflexivity) _).
intros ms1 mat1 HS1 M1. clear HS0 M0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG r1_1_e0 11) (RG r1_1_e0 18) HS1 (br_ovf_false EE 19 41 p n EEP EEN ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS1' r_r1_1_1 ltac:(unfold CS1_STK; lia) EE2 M1 ltac:(vm_compute; reflexivity) _).
intros ms2 mat2 HS2 M2. clear HS1' M1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply (proj1 M2). rewrite unsigned_lit_small by lia. unfold CS1_STK, CHK_SCR, kHighMemBeg in *. lia. }
refine (ldR EE r1_1_e1 ms2 mat2 10%bv 10%bv 341251 h1 35 56 CS1_STK _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 _).
intros ms3 mat3 HS3 M3. clear HW3 HS2 M2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450881 E32) by lia. f_equal. subst h2. replace (g0 + 2147450881) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply (proj1 M3). rewrite unsigned_lit_small by lia. unfold CS1_STK, CHK_SCR, kHighMemBeg in *. lia. }
refine (ldR EE (set_regs_pc r1_1_e1 [((10%bv : bv 5), SOff 35 0)] (ss_pc r1_1_e1 + 4)) ms3 mat3 14%bv 14%bv 472835 h2 36 56 CS1_STK _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 _).
intros ms4 mat4 HS4 M4. clear HW4 HS3 M3.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS4 r_r1_1_2 ltac:(unfold CS1_STK; lia) EE2 M4 ltac:(vm_compute; reflexivity) _).
intros ms5 mat5 HS5 M5. clear HS4 M4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG r1_1_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phaseT EE _ _ _ _ CS1_STK _ HS5' r_r1_1z_0 ltac:(unfold CS1_STK; lia) EE2 M5 ltac:(vm_compute; reflexivity) _).
intros ms6 mat6 HS6 M6. clear HS5' M5.
apply SRr_ret. exact (finishR' EE r1_1z_e0 ms6 mat6 CS1_STK ltac:(unfold CS1_STK, CHK_SCR; lia) HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg M6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG r1_1_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phaseR EE _ _ _ _ _ CS1_STK _ HS5' r_r1_1n_0 ltac:(unfold CS1_STK; lia) EE2 M5 ltac:(vm_compute; reflexivity) _).
intros ms6 mat6 HS6 M6. clear HS5' M5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG r1_1n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 1%nat 19 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phaseT EE _ _ _ _ CS1_STK _ HS6' r_r1_1n_1 ltac:(unfold CS1_STK; lia) EE2 M6 ltac:(vm_compute; reflexivity) _).
intros ms7 mat7 HS7 M7. clear HS6' M6.
apply SRr_ret. exact (finishR' EE r1_1n_e1 ms7 mat7 CS1_STK ltac:(unfold CS1_STK, CHK_SCR; lia) HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg M7).
Qed.
Theorem cs1_srr : SRr tfibsegs W (cfg_at tfibsegs CS1_ENTRY regs mem md) POSTr.
Proof.
assert (Hg0 : 8 * g0 <= p < 8 * g0 + 8) by (subst g0; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
destruct (Z.eq_dec (g1 - g0) 0) as [Ht|Ht]; [exact (path1_0 Ht)|].
apply path1_1. lia.
Qed.
End f.
Theorem cs_chk1 : forall B, AR_laws tfibsegs B -> TfibSyms B -> CS_CHK1 B.
Proof.
intros B LAWS TB. unfold CS_CHK1.
intros ly S W regs mem md p n HAR Hal Hslo Hshi HpresS GN GP Hp1 Hn Hpn HAM HRA HHULL.
eapply cs1_srr; eassumption.
Qed.
End e.
