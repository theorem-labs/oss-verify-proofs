(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE6y.v through lib/A/Rt/RtFSpChk.v, with the phase / load / finish shape of lib/A/Rt/RtSStrlenChk1.v + RtSStrlenChk2.v: the write-range check site 0x49c10 .. 0x49c58 of plugin-hostd/fuzz_command's vsprintf interceptor proved for every size 1 <= n < 2 ^ 31, with the range check over 64 bytes discharged by lib/A/Rt/RtSRegion.v cmd_region_band (so no rt_rom_view and no Section hypothesis is left), and with the model carried as one variable per phase. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtSRegionDef RtAPI RtSRegion RtFSprintfChk1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z).
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + SPC_SCR <= spZ regs.
Hypothesis Hshi : spZ regs <= ly_stk_hi ly.
Hypothesis HpresS : forall a, spZ regs - SPC_SCR <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis GR : getr regs 10 = w64 (n - 1).
Hypothesis GP : getr regs 18 = w64 p.
Hypothesis GN : getr regs 9 = w64 n.
Hypothesis Hp1 : 0 < p.
Hypothesis Hn : 1 <= n < 2 ^ 31.
Hypothesis Hpn : p + n <= 2 ^ 63.
Hypothesis HAM : amem_range p n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n.
Hypothesis HHULL : shadow_hull_vis (aview tfibsegs (w_H W) mem) p n.
Hypothesis HSRC : forall a, p <= a < p + n -> aview tfibsegs (w_H W) mem a <> None /\ ~ (spZ regs - SPC_SCR <= a < spZ regs).
Definition POSTr : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs SPC_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 18 -> r <> 21 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = getr regs 10 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SPC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := p / 8.
Let g1 : Z := (p + n - 1) / 8.
Lemma basics : 2 ^ 44 <= sp0 <= 2 ^ 47 /\ kHighMemBeg + SPC_SCR <= sp0 /\ sp0 mod 16 = 0 /\ p + n <= 2 ^ 47 - 1 /\
(forall a, sp0 - SPC_SCR <= a < sp0 -> apresent H mem a) /\ ARm B ly S (aview tfibsegs H mem).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hslo as Hslo'. pose proof Hshi as Hshi'. pose proof HAM as HAM'.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SPC_SCR in *. subst sp0 H.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact HpresS | exact (proj1 HAR)].
Qed.
Lemma bv9 : (Z_to_bv 5 9 : bv 5) = 9%bv. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
(* The end of the walk: the shape check of RtFSprintfChk1 gives every register the post names. *)
Lemma finishR : forall E ss ms mf,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeR ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
ew E 41 = Z_to_bv 64 n ->
AR tfibsegs B ly S W (ms_mem ms) mf -> same_but_materialized md mf ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SPC_SCR <= a < sp0) -> aview tfibsegs H (ms_mem ms) a = aview tfibsegs H mem a) ->
(forall a, apresent H mem a -> apresent H (ms_mem ms) a) ->
POSTr W (mkCfg ms mf).
Proof.
intros E ss ms mf HS Hrv Hsh HE HEN HARf Hsbm AV PM.
unfold shapeR in Hsh. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R9].
apply andb_prop in Hsh as [Hpc R10]. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is ss (bv_unsigned r) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E ss ms r HS). }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mf.
split; [rewrite Hshape; reflexivity|].
split; [exact HARf|]. split; [|split; [exact Hsbm|split; [|split; [exact AV | exact PM]]]].
-
intros r Hr H18 H21. unfold acallee_saved in Hr. assert (Hr32 : 0 <= r < 32) by lia.
destruct (Z.eq_dec r 9) as [Hr9|Hr9].
+ subst r. rewrite (RD (Z_to_bv 5 9) (SOff 41 0)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact R9. }
cbn [sv_denot]. rewrite HEN, Z.add_0_r, Z_to_bv_bv_unsigned, bv9. unfold w64 in GN. rewrite GN. reflexivity.
+ rewrite forallb_forall in HK. assert (Hin : In r KEPT) by (unfold KEPT; cbn; lia).
specialize (HK r Hin). cbn beta in HK.
rewrite (RD (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK. }
cbn [sv_denot]. rewrite (HE (Z.to_nat r) (Z_to_bv 5 r)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- rewrite (RD 10%bv (SOff 10 0) R10). cbn [sv_denot]. rewrite (HE 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ar_keep : forall mem' md', (forall z, mem' z = mem z) -> same_but_materialized md md' -> AR tfibsegs B ly S W mem' md'.
Proof.
intros mem' md' MEQ Hsbm.
assert (AV : forall a, aview tfibsegs H mem' a = aview tfibsegs H mem a) by (intros a; apply aview_same; apply MEQ).
apply (al_frame _ _ LAWS ly S W mem md mem' md' HAR).
- intros a _ _. apply AV.
- intros a Hv. rewrite AV. exact Hv.
- apply (same_but_materialized_frame md md' Hsbm).
- apply (same_but_materialized_frame md md' Hsbm).
- apply (same_but_materialized_frame md md' Hsbm).
- exact (AE2y.hs_kept_eq _ _ _ MEQ).
Qed.
Lemma finish_keep : forall E ss ms md0,
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> shapeR ss = true ->
(forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) ->
ew E 41 = Z_to_bv 64 n ->
(forall z, ms_mem ms z = mem z) -> same_but_materialized md md0 ->
POSTr W (mkCfg ms md0).
Proof.
intros E ss ms md0 HS Hrv Hsh HE HEN MEQ Hsbm.
apply (finishR E ss ms md0 HS Hrv Hsh HE HEN).
- apply ar_keep; [exact MEQ | exact Hsbm].
- exact Hsbm.
- intros a _ _. apply aview_same. apply MEQ.
- intros a Hp. apply (apresent_same H mem (ms_mem ms) a (MEQ _)). exact Hp.
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
Lemma EnvS : forall extra, nth_error extra 9 = Some n -> sv_denot (Env extra) (SOff 41 0) = sv_denot (Env extra) (SOff 9 0).
Proof.
intros extra He. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
rewrite (EnvN extra He), (Env_reg extra 9 9%bv eq_refl), GN. reflexivity.
Qed.
Lemma ent_ro : forall extra, Forall (region_ok tfibsegs (Env extra) (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros extra. pose proof basics as (_ & _ & _ & _ & _ & BM). exact (rodata_ok B TB icpt_rodata ly S H mem (Env extra) (icpt_rodata_chk ly) BM). Qed.
Ltac regs_tac EE :=
apply reg_cases_lit; intros r Hr; cbv [all_regs In] in Hr;
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity | (unfold EE; apply EnvS; reflexivity) ] |]);
destruct Hr.
(* One symbolic run.  The model stays one variable: each phase hands back a fresh one with
   same_but_materialized from the base model the caller names (md before the range check, the model the range
   check returns after it), so no with_vm_backing term is ever nested. *)
Lemma phR : forall (mdb : Model) E ss ss' r ms md0 (m0 : word -> option byte) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict H ms) -> RUN ss = (ss', RS_stopped r) -> nowin (ss_mem ss) = true ->
(forall z, ms_mem ms z = m0 z) -> same_but_materialized mdb md0 ->
(forall ms1 md1, st_ok tfibsegs E ss' (restrict H ms1) -> (forall z, ms_mem ms1 z = m0 z) ->
same_but_materialized mdb md1 -> SRr tfibsegs W (mkCfg ms1 md1) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros mdb E ss ss' r ms md0 m0 Q HS Hrun Hw MEQ SBM K.
eapply SRr_bind; [exact (spc_phase W E ss ss' (RS_stopped r) ms md0 HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
apply (K ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0) HS1).
- intros z. rewrite (frame_none E (ss_mem ss) (ms_mem ms) (ms_mem ms1) Hw HF1 z). apply MEQ.
- exact (same_but_materialized_trans mdb md0 _ SBM (with_vm_backing_same md0 mat1)).
Qed.
Lemma phT : forall (mdb : Model) E ss ss' ms md0 (m0 : word -> option byte) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict H ms) -> RUNTO ss = (ss', RS_running) -> nowin (ss_mem ss) = true ->
(forall z, ms_mem ms z = m0 z) -> same_but_materialized mdb md0 ->
(forall ms1 md1, st_ok tfibsegs E ss' (restrict H ms1) -> (forall z, ms_mem ms1 z = m0 z) ->
same_but_materialized mdb md1 -> SRr tfibsegs W (mkCfg ms1 md1) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros mdb E ss ss' ms md0 m0 Q HS Hrun Hw MEQ SBM K.
eapply SRr_bind; [exact (spc_phase_to W E SPC_END ss ss' RS_running ms md0 HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
apply (K ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0) HS1).
- intros z. rewrite (frame_none E (ss_mem ss) (ms_mem ms) (ms_mem ms1) Hw HF1 z). apply MEQ.
- exact (same_but_materialized_trans mdb md0 _ SBM (with_vm_backing_same md0 mat1)).
Qed.
Lemma ldR : forall (mdb : Model) E ss ms md0 (m0 : word -> option byte) (rd rs : bv 5) (w h : Z) (kx K : nat) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_spc (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs H (ms_mem ms)) h = Some (bv_unsigned (ew E kx)) ->
(forall z, ms_mem ms z = m0 z) -> same_but_materialized mdb md0 ->
(forall ms1 md1, st_ok tfibsegs E (set_regs_pc ss [(rd, SOff kx 0)] (ss_pc ss + 4)) (restrict H ms1) ->
(forall z, ms_mem ms1 z = m0 z) -> same_but_materialized mdb md1 -> SRr tfibsegs W (mkCfg ms1 md1) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros mdb E ss ms md0 m0 rd rs w h kx K Q HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw MEQ SBM Kc.
eapply SRr_bind; [exact (spc_ld8 W E ss ms md0 rd rs w h kx K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HM1).
apply (Kc ms1 (with_vm_backing (m_vm_lazy md0) mat1 md0) HS1).
- intros z. rewrite HM1. apply MEQ.
- exact (same_but_materialized_trans mdb md0 _ SBM (with_vm_backing_same md0 mat1)).
Qed.
Lemma ent1_0 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 0 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 0) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 0 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 0))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 0 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_1 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 1 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 1) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 1 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 1))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 1 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_2 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 2 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 2) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 2 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 2))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 2 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_3 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 3 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 3) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 3 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 3))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 3 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_4 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 4 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 4) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 4 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 4))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 4 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_5 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 5 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 5) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 5 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 5))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 5 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_6 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 6 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 6) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 6 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 6))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 6 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_7 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 7 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 7) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 7 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 7))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 7 E32) by lia. subst g0 g1. lia.
Qed.
Lemma ent1_8 : forall b1 q1 q2, 1 <= n <= 64 -> g1 - g0 = 8 -> aview tfibsegs H mem (SB + g1) = Some b1 -> saddr_ok (p + n - 1) b1 ->
st_ok tfibsegs (Env [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) (ssS1 8) (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
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
rewrite restrict_mkst_fx. unfold ssS1.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms (shreg1 8 :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS 8))) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply ent_ro].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs H mem) p n (g0 + i) HRA ltac:(lia) ltac:(lia)); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
- apply pairwise_disjoint_of_extents. unfold shreg1, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms atoms_ok factsS1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, E32, E34, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
+ cbn [f_alias aliasesS alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_srl3, (U_atom EE 18 p E9), (U_atom EE 32 g0 E32) by lia. reflexivity.
* apply U_inj. rewrite U_srl3, (U_dn1 EE 18 41 p n E9 E10), (U_atom_off EE 32 g0 8 E32) by lia. subst g0 g1. lia.
Qed.
Lemma path1_0 : 1 <= n <= 64 -> g1 - g0 = 0 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t0_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t0_e0 11) (RG t0_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t0_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t0_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450880 E32) by lia. f_equal. subst h2. replace (g0 + 2147450880) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t0_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t0_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t0_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t0_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t0z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t0z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t0_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t0n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t0n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 0%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t0n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t0n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_1 : 1 <= n <= 64 -> g1 - g0 = 1 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t1_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t1_e0 11) (RG t1_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t1_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t1_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450881 E32) by lia. f_equal. subst h2. replace (g0 + 2147450881) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t1_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t1_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t1_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t1_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t1z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t1z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t1_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t1n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t1n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 1%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t1n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t1n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_2 : 1 <= n <= 64 -> g1 - g0 = 2 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t2_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t2_e0 11) (RG t2_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t2_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t2_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450882 E32) by lia. f_equal. subst h2. replace (g0 + 2147450882) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t2_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t2_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t2_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t2_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t2z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t2z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t2_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t2n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t2n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 2%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t2n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t2n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_3 : 1 <= n <= 64 -> g1 - g0 = 3 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t3_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t3_e0 11) (RG t3_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t3_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t3_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450883 E32) by lia. f_equal. subst h2. replace (g0 + 2147450883) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t3_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t3_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t3_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t3_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t3z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t3z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t3_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t3n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t3n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 3%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t3n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t3n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_4 : 1 <= n <= 64 -> g1 - g0 = 4 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t4_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t4_e0 11) (RG t4_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t4_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t4_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450884 E32) by lia. f_equal. subst h2. replace (g0 + 2147450884) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t4_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t4_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t4_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t4_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t4z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t4z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t4_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t4n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t4n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 4%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t4n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t4n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_5 : 1 <= n <= 64 -> g1 - g0 = 5 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_5 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t5_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t5_e0 11) (RG t5_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t5_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t5_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450885) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450885 E32) by lia. f_equal. subst h2. replace (g0 + 2147450885) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t5_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t5_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t5_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t5_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t5z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t5z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t5_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t5n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t5n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 5%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t5n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t5n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_6 : 1 <= n <= 64 -> g1 - g0 = 6 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_6 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t6_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t6_e0 11) (RG t6_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t6_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t6_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450886) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450886 E32) by lia. f_equal. subst h2. replace (g0 + 2147450886) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t6_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t6_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t6_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t6_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t6z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t6z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t6_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t6n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t6n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 6%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t6n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t6n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_7 : 1 <= n <= 64 -> g1 - g0 = 7 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_7 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t7_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t7_e0 11) (RG t7_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t7_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t7_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450887) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450887 E32) by lia. f_equal. subst h2. replace (g0 + 2147450887) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t7_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t7_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t7_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t7_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t7z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t7z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t7_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t7n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t7n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 7%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t7n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t7n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma path1_8 : 1 <= n <= 64 -> g1 - g0 = 8 -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64 Ht. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
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
pose proof (EnvP [g0; g1; b1; q1; q2; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [g0; g1; b1; q1; q2; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_8 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_t8_0 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG t8_e0 11) (RG t8_e0 12) HS1 (br_cls64_small EE 41 n EEN Hn64)) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
refine (phR md EE _ _ _ _ _ mem _ HS1' r_t8_1 ltac:(vm_compute; reflexivity) M1 S1 _).
intros ms2 md2 HS2 M2 S2. clear HS1' M1 S1.
assert (HW3 : rdword (aview tfibsegs H (ms_mem ms2)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply M2. }
refine (ldR md EE t8_e1 ms2 md2 mem 14%bv 14%bv 472835 h1 35 56 _ HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl
(U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW3 M2 S2 _).
intros ms3 md3 HS3 M3 S3. clear HW3 HS2 M2 S2.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450888) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450888 E32) by lia. f_equal. subst h2. replace (g0 + 2147450888) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply M3. }
refine (ldR md EE (set_regs_pc t8_e1 [((14%bv : bv 5), SOff 35 0)] (ss_pc t8_e1 + 4)) ms3 md3 mem 15%bv 15%bv 505731 h2 36 56 _ HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl Hrs2 ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4 M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HW4 HS3 M3 S3.
refine (phR md EE _ _ _ _ _ mem _ HS4 r_t8_2 ltac:(vm_compute; reflexivity) M4 S4 _).
intros ms5 md5 HS5 M5 S5. clear HS4 M4 S4.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+ pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG t8_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS5'.
change (neg_bc BC_NE) with BC_EQ in HS5'. clear HS5.
refine (phT md EE _ _ _ _ mem _ HS5' r_t8z_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
apply SRr_ret. exact (finish_keep EE t8z_e0 ms6 md6 HS6 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M6 S6).
+ pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG t8_e2 14) (SLit 0) HS5 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS5'. clear HS5.
refine (phR md EE _ _ _ _ _ mem _ HS5' r_t8n_0 ltac:(vm_compute; reflexivity) M5 S5 _).
intros ms6 md6 HS6 M6 S6. clear HS5' M5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG t8n_e0 11) (SLit 0) HS6 (qc_flag_zero EE 8%nat 18 41 34 p n b1 EEP EEN E34 ltac:(lia) ltac:(lia) Hpn ltac:(lia) Hok)) as HS6'. clear HS6.
refine (phT md EE _ _ _ _ mem _ HS6' r_t8n_1 ltac:(vm_compute; reflexivity) M6 S6 _).
intros ms7 md7 HS7 M7 S7. clear HS6' M6 S6.
apply SRr_ret. exact (finish_keep EE t8n_e1 ms7 md7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg EEN M7 S7).
Qed.
Lemma ent2 : 64 < n -> st_ok tfibsegs (Env [0; 0; 0; 0; 0; 0; 0; 0; 0; n]) ssS2 (restrict H (mkst regs (Z_to_bv 64 SPC_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros Hn64. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
set (EE := Env [0; 0; 0; 0; 0; 0; 0; 0; 0; n]).
pose proof (Env2 [0; 0; 0; 0; 0; 0; 0; 0; 0; n]) as E2. pose proof (EnvP [0; 0; 0; 0; 0; 0; 0; 0; 0; n]) as E9. pose proof (EnvN [0; 0; 0; 0; 0; 0; 0; 0; 0; n] eq_refl) as E10.
fold EE in E2, E9, E10.
rewrite restrict_mkst_fx. unfold ssS2.
apply (st_ok_regs tfibsegs EE (mkSS SPC_ENTRY sr_atoms [] None (mkFacts factsS2 [] [])) _ regsS).
2:{ regs_tac EE. }
unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [0; 0; 0; 0; 0; 0; 0; 0; 0; n])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok factsS2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E9, E10, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
Qed.
(* A size over 64: the run leaves the table at 0x5a1ac with a0 = p, a1 = n, ra = 0x49d44 and the site's own sp;
   RtSRegion.cmd_region_band (which needs no rt_rom_view) returns a0 = 0, writes only [sp - 72, sp) and keeps
   every callee-saved register, so `beqz s2` at 0x49d4c goes to 0x49c58. *)
Lemma path2 : 64 < n -> SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
intros Hn64. pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
unfold cfg_at. change (w64 SPC_ENTRY) with (Z_to_bv 64 SPC_ENTRY).
set (EE := Env [0; 0; 0; 0; 0; 0; 0; 0; 0; n]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (EnvP [0; 0; 0; 0; 0; 0; 0; 0; 0; n]) as EEP. pose proof (EnvN [0; 0; 0; 0; 0; 0; 0; 0; 0; n] eq_refl) as EEN. fold EE in EEP, EEN.
pose proof (ent2 Hn64) as HS0. fold EE in HS0.
refine (phR md EE _ _ _ _ _ mem _ HS0 r_s2 ltac:(vm_compute; reflexivity) ltac:(intros z; reflexivity) (same_but_materialized_refl md) _).
intros ms1 md1 HS1 M1 S1. clear HS0.
pose proof s2_e_shape as (Spc & Srv & Smem & Sat & SR1 & SR2 & SR10 & SR11).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 Srv) as Hshape. rewrite Spc in Hshape.
assert (RD : forall (r : bv 5) v, RG s2_e (bv_unsigned r) = v -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold RG in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE s2_e ms1 r HS1). }
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 SPC_CALL_RET) by (rewrite (RD 1%bv _ SR1); reflexivity).
assert (R2 : getr (ms_regs ms1) 2 = getr regs 2).
{ rewrite (RD 2%bv _ SR2). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply EEreg. reflexivity. }
assert (R10 : getr (ms_regs ms1) 10 = w64 p).
{ rewrite (RD 10%bv _ SR10). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact EEP. }
assert (R11 : getr (ms_regs ms1) 11 = w64 n).
{ rewrite (RD 11%bv _ SR11). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact EEN. }
assert (Hsp1 : spZ (ms_regs ms1) = sp0) by (unfold spZ; rewrite R2; reflexivity).
assert (AV1 : forall a, aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a) by (intros a; apply aview_same; apply M1).
rewrite Hshape.
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 SPC_RGN) (ms_mem ms1) (seg_rom tfibsegs)) md1)
with (cfg_at tfibsegs SPC_RGN (ms_regs ms1) (ms_mem ms1) md1).
eapply SRr_bind.
{ exact (cmd_region_band B LAWS TB SPC_SCR ltac:(unfold SPC_SCR, RGN_SCR; lia) ly S W (ms_regs ms1) (ms_mem ms1) md1 p n
(ar_keep (ms_mem ms1) md1 M1 S1)
ltac:(rewrite R1; apply AE2y.ret_ok_lit; [unfold SPC_CALL_RET; lia | reflexivity])
ltac:(rewrite Hsp1; exact Hal)
ltac:(rewrite Hsp1; exact Hslo)
ltac:(rewrite Hsp1; exact Hshi)
ltac:(intros a Ha; rewrite Hsp1 in Ha; apply (apresent_same H mem (ms_mem ms1) a (M1 _)); apply Bpres; exact Ha)
R10 R11 ltac:(lia) Hp1
ltac:(unfold aread_ok, ascratch_stk; rewrite Hsp1; split; [lia|]; split; [lia|]; split; [lia|];
split; [intros a Ha; destruct (HSRC a Ha) as [Hv Hns]; split; [rewrite AV1; exact Hv | exact Hns]|];
split; [exact HAM|];
split; [eapply range_addressable_agree; [intros y Hy; apply AV1 | exact HRA]|];
intros Hn0 s Hs; rewrite AV1; exact (HHULL s Hs))
ltac:(pose proof HAM as HAM'; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & Ha0 & Hfr2 & Hpres2 & Hscr2).
assert (Hra1 : w64 (raZ (ms_regs ms1)) = Z_to_bv 64 SPC_CALL_RET)
by (unfold raZ, w64; rewrite R1, unsigned_lit_small by (unfold SPC_CALL_RET; lia); reflexivity).
unfold cfg_at. rewrite Hra1.
pose proof (st_ok_after_call tfibsegs 42 EE s2_e (restrict H (mkst (ms_regs ms1) (Z_to_bv 64 SPC_RGN) (ms_mem ms1) (seg_rom tfibsegs))) regs2 (mrestrict H mem2) [] SPC_CALL_RET
ltac:(rewrite <- Hshape; exact HS1) Srv Sat eq_refl eq_refl eq_refl (submem_nil _) SR1
ltac:(intros r Hr; apply HP2; unfold acallee_saved; exact Hr) (Forall_nil _)) as HS2.
change (ss_after_call s2_e [] 42 SPC_CALL_RET) with s2_a in HS2. rewrite <- restrict_mkst_fx in HS2.
assert (E2reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (havoc EE 42 (map (getr regs2) CLOB)) i = getr regs r).
{ intros i r Hi. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (E2N : ew (havoc EE 42 (map (getr regs2) CLOB)) 41 = Z_to_bv 64 n) by (rewrite ew_havoc_old by lia; exact EEN).
assert (F46 : ew (havoc EE 42 (map (getr regs2) CLOB)) 46 = w64 0).
{ change 46%nat with (42 + 4)%nat. rewrite (ew_havoc_new EE 42 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia). cbn. exact Ha0. }
refine (phR md2 (havoc EE 42 (map (getr regs2) CLOB)) _ _ _ _ _ mem2 _ HS2 r_s2_b ltac:(vm_compute; reflexivity)
ltac:(intros z; reflexivity) (same_but_materialized_refl md2) _).
intros ms3 md3 HS3 M3 S3. clear HS2.
pose proof (st_ok_add_cond tfibsegs (havoc EE 42 (map (getr regs2) CLOB)) _ _ BC_EQ (RG s2_b 18) (SLit 0) HS3) as HS3'.
specialize (HS3' ltac:(change (RG s2_b 18) with (SOff 46 0);
rewrite branch_eq_U, U_SLit, (U_atom (havoc EE 42 (map (getr regs2) CLOB)) 46 0 F46) by lia; reflexivity)).
clear HS3.
refine (phT md2 (havoc EE 42 (map (getr regs2) CLOB)) _ _ _ _ mem2 _ HS3' r_s2_c ltac:(vm_compute; reflexivity) M3 S3 _).
intros ms4 md4 HS4 M4 S4. clear HS3' M3 S3.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply M4).
apply SRr_ret. apply (finishR (havoc EE 42 (map (getr regs2) CLOB)) s2_c ms4 md4 HS4 eq_refl ltac:(vm_compute; reflexivity) E2reg E2N).
- apply (al_frame _ _ LAWS ly S W mem2 md2 (ms_mem ms4) md4 HAR2).
+ intros a _ _. apply AV4.
+ intros a Hv. rewrite AV4. exact Hv.
+ apply (same_but_materialized_frame md2 md4 S4).
+ apply (same_but_materialized_frame md2 md4 S4).
+ apply (same_but_materialized_frame md2 md4 S4).
+ intros a _ _. apply M4.
- exact (same_but_materialized_trans md md2 md4 (same_but_materialized_trans md md1 md2 S1 Hsbm2) S4).
- intros a Hr Ha. exact (eq_trans (AV4 a) (eq_trans (Hfr2 a Hr ltac:(unfold ascratch_stk; rewrite Hsp1; exact Ha) (fun HF : False => HF)) (AV1 a))).
- intros a Hp. apply (apresent_same H mem2 (ms_mem ms4) a (M4 _)). apply Hpres2.
apply (apresent_same H mem (ms_mem ms1) a (M1 _)). exact Hp.
Qed.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. lia. Qed.
Theorem spc_site_srr : SRr tfibsegs W (cfg_at tfibsegs SPC_ENTRY regs mem md) POSTr.
Proof.
destruct (Z_le_gt_dec n 64) as [Hle|Hgt]; [|apply path2; lia].
assert (Hg0 : 8 * g0 <= p < 8 * g0 + 8) by (subst g0; pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
assert (Hn1 : 1 <= n <= 64) by lia.
destruct (t_cases (g1 - g0) ltac:(lia)) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]];
[apply path1_0 | apply path1_1 | apply path1_2 | apply path1_3 | apply path1_4 | apply path1_5 | apply path1_6 | apply path1_7 | apply path1_8]; assumption.
Qed.
End f.

(* The interface the sprintf walk calls. *)
Theorem spf_check_srr : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B ->
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z),
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + SPC_SCR <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - SPC_SCR <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 (n - 1) -> getr regs 18 = w64 p -> getr regs 9 = w64 n ->
0 < p -> 1 <= n < 2 ^ 31 -> p + n <= 2 ^ 63 -> amem_range p n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
(forall a, p <= a < p + n -> aview tfibsegs (w_H W) mem a <> None /\ ~ (spZ regs - SPC_SCR <= a < spZ regs)) ->
SRr tfibsegs W (cfg_at tfibsegs 0x49c10 regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs 0x49c58 regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 18 -> r <> 21 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = getr regs 10 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SPC_SCR <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md p n HAR Hal Hslo Hshi HpresS Hgp Htp GR GP GN Hp1 Hn Hpn HAM HRA HHULL HSRC.
(* Hgp, Htp and GR are not used: the range check is reached through cmd_region_band, which asks for no
   ecall_pre (so no gp/tp), and the post names a0 only as the entry's own value. *)
exact (spc_site_srr B LAWS TB ly S W regs mem md p n HAR Hal Hslo Hshi HpresS GP GN Hp1 Hn Hpn HAM HRA HHULL HSRC).
Qed.
End e.
