(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE6y.v through lib/A/Rt/RtFSpChk.v, with the phase / load / finish shape of lib/A/Rt/RtSStrlenChk1.v + RtSStrlenChk2.v: the write-range check site 0x49c10 .. 0x49c58 of plugin-hostd/fuzz_command's vsprintf interceptor proved for every size 1 <= n < 2 ^ 31, with the range check over 64 bytes discharged by lib/A/Rt/RtSRegion.v cmd_region_band (so no rt_rom_view and no Section hypothesis is left), and with the model carried as one variable per phase. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtFSprintfChk2.v, with its module names and numbers changed; 844 of its 977 lines of code are new or changed and 1099 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI RtSRegionDef RtSStrcspnIT.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtSRegion.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The check of the set argument in ___interceptor_strcspn (flavor B), measured on the pinned fuzz_command.asan,
   from the return of internal_strlen to the start of the check of the string argument. It is the set site of
   ___interceptor_strspn (lib/A/Rt/RtSStrspnSiteY.v) at +0x488:
     0x46d18 addi s2,a0,1  (size = len + 1)        0x46d20 bltu ~s3,s2 -> overflow report (cut: s3 + size <= 2^63)
     0x46d28 bgeu a0,64 -> 0x46eec (size > 64)    0x46d2c..0x46d5c the two shadow words, 0x46d64 bnez -> 0x46ef8
     0x46ef8..0x46f28 the shadow byte loop, beqz -> 0x46d68
     0x46eec mv a0,s5; bnez s2 -> 0x46f2c: mv a0,s3; mv a1,s2; jal 0x5a1ac; 0x46f38 mv s3,a0; mv a0,s5; beqz s3 -> 0x46d68
     0x46d68 lbu a1,245(s7) (strict_string_checks, 0 in the record); mv s3,a0; bnez a1 -> 0x46df4 (not taken)
   On entry a0 = len, s3 = set, s5 = the result of musl's strcspn, s7 = common_flags. *)
Definition RCY_ENTRY : Z := 0x46d18.
Definition RCY_END : Z := 0x46d74.
Definition RCY_RET : Z := 0x46f38.
Definition RC_SCR : Z := 72.
Definition siteY_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x142cd8, 8, [(0, 8%N, 0x101000100000000)])].
Lemma siteY_rodata_chk : forall ly, rodata_chk ly siteY_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition regsY : list sv := Eval vm_compute in (firstn 23 sr_atoms ++ [SLit 0x142be8] ++ skipn 24 sr_atoms).
Definition aliasesY (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 19 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) (SLit 3), SOff 32 t) ].
Definition factsY1 : list (nat * afact) :=
[(19%nat, mkAF 1 (2^47) 0); (10%nat, mkAF 0 63 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition ssY1 (t : Z) : sstate :=
mkSS RCY_ENTRY regsY (shreg1 t :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY t)).
Definition factsY2 : list (nat * afact) := [(19%nat, mkAF 1 (2^47) 0); (10%nat, mkAF 64 (2^32 - 2) 0)].
Definition ssY2 : sstate := mkSS RCY_ENTRY regsY (map ro_region siteY_rodata) None (mkFacts factsY2 [] []).
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition KEPTY : list Z := [2; 3; 4; 8; 9; 20; 21; 22; 24; 25; 26; 27].
Definition shapeY (ss : sstate) : bool :=
(ss_pc ss =? RCY_END) && reg_is ss 10 (SOff 21 0) && reg_is ss 19 (SOff 21 0) && reg_is ss 23 (SLit 0x142be8) &&
forallb (fun q => reg_is ss q (SOff (Z.to_nat q) 0)) KEPTY.
Lemma t_cases : forall t, 0 <= t <= 8 -> t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ t = 4 \/ t = 5 \/ t = 6 \/ t = 7 \/ t = 8.
Proof. intros t Ht. lia. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n r : Z).
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + RC_SCR <= spZ regs.
Hypothesis Hshi : spZ regs <= ly_stk_hi ly.
Hypothesis HpresS : forall a, spZ regs - RC_SCR <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis GN : getr regs 10 = w64 (n - 1).
Hypothesis GP : getr regs 19 = w64 p.
Hypothesis GR : getr regs 21 = w64 r.
Hypothesis G23 : getr regs 23 = w64 0x142be8.
Hypothesis Hn1 : 1 <= n.
Hypothesis Hp1 : 0 < p.
Hypothesis HRD : aread_ok tfibsegs RC_SCR W regs mem p n.
Hypothesis HROM : rt_rom_view tfibsegs B W mem.

Definition POSTr : world tfibsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs RCY_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall q, acallee_saved q -> q <> 18 -> q <> 19 -> getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) /\
same_but_materialized md md' /\
getr regs' 10 = w64 r /\ getr regs' 19 = w64 r /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).

Lemma basics : 2 ^ 44 <= spZ regs <= 2 ^ 47 /\ kHighMemBeg + 72 <= spZ regs /\ p + n <= 2 ^ 47 - 1 /\
ARm B ly S (aview tfibsegs (w_H W) mem).
Proof.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof HRD as (_ & _ & _ & _ & HAM & _ & _).
pose proof Hslo as Hslo'. pose proof Hshi as Hshi'.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, RC_SCR in *.
split; [lia|]. split; [lia|]. split; [lia|]. exact (proj1 HAR).
Qed.

Lemma finishY : forall E ss ms md',
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> shapeY ss = true ->
(forall i (q : bv 5), Z.of_nat i = bv_unsigned q -> (i < 32)%nat -> ew E i = getr regs q) ->
AR tfibsegs B ly S W (ms_mem ms) md' -> same_but_materialized md md' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RC_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
POSTr W (mkCfg ms md').
Proof.
intros E ss ms md' HS Hrv Hsh HE HAR' Hsbm AV PM.
unfold shapeY in Hsh. apply andb_prop in Hsh as [Hsh HK]. apply andb_prop in Hsh as [Hsh R23].
apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hpc R10]. apply Z.eqb_eq in Hpc.
assert (RD : forall (q : bv 5) v, reg_is ss (bv_unsigned q) v = true -> getr (ms_regs ms) q = sv_denot E v).
{ intros q v Hq. unfold reg_is, RG in Hq. apply sv_eqb_eq in Hq. rewrite Z_to_bv_bv_unsigned in Hq. rewrite <- Hq.
apply (st_ok_restrict_reg tfibsegs (w_H W) E ss ms q HS). }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
assert (E21 : ew E 21 = w64 r) by (rewrite (HE 21%nat 21%bv eq_refl ltac:(lia)); exact GR).
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md'.
split; [rewrite Hshape; reflexivity|].
split; [exact HAR'|].
split.
- intros q Hq H18 H19. unfold acallee_saved in Hq.
assert (Hq32 : 0 <= q < 32) by lia.
destruct (Z.eq_dec q 23) as [->|Hn23].
+ rewrite (RD (Z_to_bv 5 23) (SLit 0x142be8)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact R23. }
replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G23. reflexivity.
+ rewrite forallb_forall in HK.
assert (Hin : In q KEPTY) by (unfold KEPTY; cbn; lia).
specialize (HK q Hin). cbn beta in HK.
rewrite (RD (Z_to_bv 5 q) (SOff (Z.to_nat q) 0)).
2:{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact HK. }
cbn [sv_denot]. rewrite (HE (Z.to_nat q) (Z_to_bv 5 q)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity| |lia].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- split; [exact Hsbm|].
split; [rewrite (RD 10%bv (SOff 21 0) R10); cbn [sv_denot]; rewrite E21, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite (RD 19%bv (SOff 21 0) R19); cbn [sv_denot]; rewrite E21, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact AV | exact PM].
Qed.

Lemma EnvY_reg : forall extra i (q : bv 5), Z.of_nat i = bv_unsigned q -> (i < 32)%nat -> ew (AE2y.Env regs extra) i = getr regs q.
Proof. intros extra i q Hi _. apply AE2y.Env_reg. exact Hi. Qed.

(* Sizes 1..64: the two shadow words, then (when they are not both zero) the shadow byte loop, over the
   t = (p + n - 1) / 8 - p / 8 granules between the first and the last byte. *)
Lemma path1 : n <= 64 -> SRr tfibsegs W (cfg_at tfibsegs RCY_ENTRY regs mem md) POSTr.
Proof.
intros Hn64.
pose proof basics as (Bsp & Bhi & Bpn & BM).
pose proof HRD as (Hp0 & Hpn & Hn32 & Hvis & HAM & HRA & HHULL).
pose proof AF0x.Hwx_tfa as Hwx.
destruct (ra_last (aview tfibsegs (w_H W) mem) p n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
set (g0 := p / 8) in *. set (g1 := (p + n - 1) / 8) in *.
assert (Hg0d : g0 = p / 8) by reflexivity. assert (Hg1d : g1 = (p + n - 1) / 8) by reflexivity.
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= p < 8 * g0 + 8) by (rewrite Hg0d; split; [apply Z.div_pos; lia | pose proof (Z.div_mod p 8 ltac:(lia)); pose proof (Z.mod_pos_bound p 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= p + n - 1 < 8 * g1 + 8) by (rewrite Hg1d; pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)); lia).
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1d : h1 = (g0 + 2147450880) / 8 * 8) by reflexivity.
assert (Hh2d : h2 = (g1 + 2147450880) / 8 * 8) by reflexivity.
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (rewrite Hh1d; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (rewrite Hh2d; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (rewrite Hh1d, Hh2d; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr p / 8 * 8 = h1) by (rewrite Hh1d; unfold shadow_addr, SHADOW_OFF; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (p + n - 1) / 8 * 8 = h2) by (rewrite Hh2d; unfold shadow_addr, SHADOW_OFF; f_equal; f_equal; lia).
destruct (hull_rdword (w_H W) mem p n h1 (HHULL ltac:(lia)) ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword (w_H W) mem p n h2 (HHULL ltac:(lia)) ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := AE2y.Env regs [g0; g1; b1; q1; q2]).
assert (EEreg : forall i (q : bv 5), Z.of_nat i = bv_unsigned q -> (i < 32)%nat -> ew EE i = getr regs q) by (intros; apply EnvY_reg; assumption).
assert (E10 : ew EE 10 = Z_to_bv 64 (n - 1)) by (rewrite (EEreg 10%nat 10%bv eq_refl ltac:(lia)); exact GN).
assert (E19 : ew EE 19 = Z_to_bv 64 p) by (rewrite (EEreg 19%nat 19%bv eq_refl ltac:(lia)); exact GP).
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (AE2y.Env_x _ _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (AE2y.Env_x _ _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (AE2y.Env_x _ _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (AE2y.Env_x _ _ 4); reflexivity).
assert (Ht8 : 0 <= g1 - g0 <= 8) by lia.
unfold cfg_at. change (w64 RCY_ENTRY) with (Z_to_bv 64 RCY_ENTRY).
pose proof (same_but_materialized_refl md) as HMD.
destruct (t_cases (g1 - g0) Ht8) as [Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|[Ht|Ht]]]]]]]].
- (* t = 0 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 0) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 0 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 0))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 0 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 0)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 0) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 0%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 0%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 1 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 1) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 1 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 1))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 1 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 1)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 1) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 1%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 1%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 2 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 2) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 2 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 2))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 2 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 2)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 2) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 2%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 2%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 3 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 3) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 3 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 3))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 3 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 3)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 3) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 3%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 3%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 4 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 4) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 4 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 4))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 4 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 4)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 4) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 4%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 4%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 5 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 5) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 5 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 5))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 5 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 5)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 5) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 5%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 5%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 6 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 6) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 6 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 6))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 6 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 6)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 6) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 6%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 6%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 7 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 7) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 7 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 7))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 7 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 7)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 7) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 7%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 7%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
- (* t = 8 *)
assert (HS0 : st_ok tfibsegs EE (ssY1 8) (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY1.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (shreg1 8 :: map ro_region siteY_rodata) None (mkFacts factsY1 [] (aliasesY 8))) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; q1; q2])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ apply Forall_cons; [| exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM)].
unfold shreg1, region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks Z.ltb Z.compare Pos.compare Pos.compare_cont app].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
repeat apply Forall_cons; try apply Forall_nil.
all: first
[ apply chunk_ok_zero; intros i Hi; rewrite (AF0x.aview_byte (w_H W) mem _ 0); [reflexivity|];
rewrite <- (ra_granule_zero (aview tfibsegs (w_H W) mem) p n (g0 + i) HRA ltac:(lia) Hp0); unfold SB; f_equal; lia
| eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |];
apply val_mem1_of_aview; rewrite <- Hb1; unfold SB; f_equal; lia ].
+ apply pairwise_disjoint_of_extents. unfold shreg1, siteY_rodata, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E32, unsigned_lit_small by lia.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; [exact I|]].
* cbn [f_atoms atoms_ok factsY1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, E32, E34, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
* cbn [f_alias aliasesY alias_ok]. split; [|split; [|exact I]].
-- apply U_inj. rewrite U_srl3, (U_atom EE 19 p E19), (U_atom EE 32 g0 E32) by lia. reflexivity.
-- apply U_inj. rewrite U_srl3, (U_add2 EE 10 19 (n - 1) p E10 E19), (U_atom_off EE 32 g0 8 E32) by lia.
replace (n - 1 + p) with (p + n - 1) by lia. fold g1. lia.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. cbv in Hc. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 10%bv 10%bv 0x00053503 h1 35 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + 2147450880) / 8 * 8)); [apply (U_hull_addr EE 32 g0 2147450880 E32); lia | rewrite Hh1d; reflexivity].
- lia.
- lia.
- rewrite MEQ, E35, unsigned_lit_small by lia; exact Hq1. }
clear HS0. cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS0 & HM5). rewrite MEQ in HM5. clear MEQ. rename HM5 into MEQ. newmd HMD.
eapply SRr_bind.
{ apply (ci_ld8 W EE _ _ _ 14%bv 14%bv 0x00073703 h2 36 40 HS0 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl).
- transitivity (Z_to_bv 64 ((g0 + (2147450880 + 8)) / 8 * 8)); [apply (U_hull_addr EE 32 g0 (2147450880 + 8) E32); lia | rewrite Hh2d; f_equal; f_equal; f_equal; lia].
- lia.
- lia.
- rewrite MEQ, E36, unsigned_lit_small by lia; exact Hq2. }
clear HS0. cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS0 & HM6). rewrite MEQ in HM6. clear MEQ. rename HM6 into MEQ. newmd HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- exact HMD.
- intros a _ _. rewrite MEQ. reflexivity.
- intros a Ha. rewrite MEQ. exact Ha. }
exfalso.
change (branch_taken BC_EQ (sv_denot EE (qcB_flag 8%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34)) (sv_denot EE (SLit 0)) = false) in Hc.
rewrite (qcB_flag_zero EE 8%nat (SAlu ALU_ADD (SOff 10 0) (SOff 19 0)) 34 (n - 1 + p) b1) in Hc.
- cbv in Hc. discriminate.
- apply (U_add2 EE 10 19 (n - 1) p E10 E19); lia.
- exact E34.
- lia.
- replace (n - 1 + p) with (p + n - 1) by lia. exact Hok. }
clear Hc.
srr_run_to_with tbl_ci_ok HS0 RCY_END. ro_mem MEQ. newmd HMD.
apply SRr_ret. apply (finishY EE _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity) EEreg).
+ apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
+ exact HMD.
+ intros a _ _. rewrite MEQ. reflexivity.
+ intros a Ha. rewrite MEQ. exact Ha.
Qed.

(* Sizes over 64: the range check 0x5a1ac, under RtSRegion's proved contract with the scratch window 72, from
   inside this frame; then back into the run at its return address 0x46f38. *)
Lemma path2 : 64 < n -> SRr tfibsegs W (cfg_at tfibsegs RCY_ENTRY regs mem md) POSTr.
Proof.
intros Hn64.
pose proof basics as (Bsp & Bhi & Bpn & BM).
pose proof HRD as (Hp0 & Hpn & Hn32 & Hvis & HAM & HRA & HHULL).
pose proof AF0x.Hwx_tfa as Hwx.
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (q : bv 5), Z.of_nat i = bv_unsigned q -> (i < 32)%nat -> ew EE i = getr regs q) by (intros; apply EnvY_reg; assumption).
assert (E10 : ew EE 10 = Z_to_bv 64 (n - 1)) by (rewrite (EEreg 10%nat 10%bv eq_refl ltac:(lia)); exact GN).
assert (E19 : ew EE 19 = Z_to_bv 64 p) by (rewrite (EEreg 19%nat 19%bv eq_refl ltac:(lia)); exact GP).
assert (HS0 : st_ok tfibsegs EE ssY2 (restrict (w_H W) (mkst regs (Z_to_bv 64 RCY_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssY2.
apply (st_ok_regs tfibsegs EE (mkSS RCY_ENTRY sr_atoms (map ro_region siteY_rodata) None (mkFacts factsY2 [] [])) _ regsY).
- unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
+ apply regs_ok_Ereg.
+ vm_compute. reflexivity.
+ exact (rodata_ok B TB siteY_rodata ly S (w_H W) mem EE (siteY_rodata_chk ly) BM).
+ apply pairwise_disjoint_of_extents. unfold siteY_rodata, icpt_rodata, ro_region, extent_of_region.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N zpairwise_disjoint zall_disjoint].
unfold zdisj. cbn [fst snd]. repeat split; lia.
+ split; [|split; exact I]. cbn [f_atoms atoms_ok factsY2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E10, E19, !unsigned_lit_small by lia. change (2 ^ 0) with 1. repeat split; try lia; apply Z.mod_1_r.
- apply reg_cases_lit. intros q Hq. cbv [all_regs In] in Hq.
repeat (destruct Hq as [<-|Hq]; [
match goal with |- sv_denot _ (sr_get ?a ?r1) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r1) in change (sr_get a r1) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 23 23%bv eq_refl), G23; reflexivity) ] |]).
destruct Hq. }
unfold cfg_at. change (w64 RCY_ENTRY) with (Z_to_bv 64 RCY_ENTRY).
pose proof (same_but_materialized_refl md) as HMD.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
srr_branch_with tbl_ci_ok HS0.
{ exfalso. rewrite (br_ovf1_false EE 19 10 p (n - 1) E19 E10) in Hc by lia. discriminate. }
clear Hc.
srr_run_with tbl_ci_ok HS0. ro_mem MEQ. newmd HMD.
lazymatch type of HS0 with st_ok _ _ _ (restrict _ ?m) => rename m into msR end.
rreg HS0 (1%bv : bv 5) R1. rreg HS0 (2%bv : bv 5) R2. rreg HS0 (10%bv : bv 5) R10. rreg HS0 (11%bv : bv 5) R11.
assert (Rsp : spZ (ms_regs msR) = spZ regs) by (unfold spZ; rewrite R2, (EEreg 2%nat 2%bv eq_refl ltac:(lia)); reflexivity).
assert (Hra : raZ (ms_regs msR) = RCY_RET) by (unfold raZ; rewrite R1; reflexivity).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EE _ _ HS0 eq_refl) as Hshape. cbn [ss_pc] in Hshape.
rewrite Hshape.
eapply SRr_bind.
{ apply (RtSRegion.cmd_region_zero_stk B LAWS TB RGN_SCR (Z.le_refl _) ly S W _ _ _ p n).
- apply (ar_same B LAWS ly S W mem md); [exact HAR | intros z; rewrite MEQ; reflexivity | exact HMD].
- rewrite R1. apply ret_ok_lit; [lia | reflexivity].
- rewrite Rsp. exact Hal.
- rewrite Rsp. unfold RGN_SCR. unfold RC_SCR in Hslo. lia.
- rewrite Rsp. exact Hshi.
- intros a Ha. rewrite Rsp in Ha. rewrite MEQ. apply HpresS. unfold RC_SCR, RGN_SCR in *. lia.
- rewrite R10, E19. reflexivity.
- rewrite R11, E10, unsigned_lit_small by lia. unfold w64. f_equal. lia.
- lia.
- exact Hp1.
- rewrite MEQ. exact (aread_ok_sp RGN_SCR W regs (ms_regs msR) mem p n HRD Rsp).
- rewrite MEQ. exact HROM. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP2 & Hsbm2 & A10 & Hfr2 & Hpres2 & Hscr2).
pose proof (same_but_materialized_trans _ _ _ HMD Hsbm2) as HMD2. clear HMD Hsbm2. rename HMD2 into HMD.
jafter_call HS0 32%nat regs2 (mrestrict (w_H W) mem2) HP2 HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ repeat apply Forall_cons; try apply Forall_nil.
all: split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; [| lia].
all: cbn [ms_mem restrict]; apply mbyte_of_aview; apply Hfr2; [lia | unfold ascratch_stk; rewrite Rsp; unfold RGN_SCR; lia | tauto]. }
rewrite <- restrict_mkst_fx in HS2. clear HS0.
set (E2 := havoc EE 32 (map (getr regs2) CLOB)) in HS2.
assert (E2reg : forall i (q : bv 5), Z.of_nat i = bv_unsigned q -> (i < 32)%nat -> ew E2 i = getr regs q).
{ intros i q Hi Hl. unfold E2. rewrite ew_havoc_old by exact Hl. apply EEreg; assumption. }
assert (E36 : ew E2 36 = Z_to_bv 64 0).
{ unfold E2. change 36%nat with (32 + 4)%nat. rewrite (ew_havoc_new EE 32 _ 4 (Z_to_bv 64 0)) by (cbn; lia). cbn. exact A10. }
rewrite Hra. unfold cfg_at. change (w64 RCY_RET) with (Z_to_bv 64 RCY_RET).
pose proof (same_but_materialized_refl md2) as HMDb.
srr_run_with tbl_ci_ok HS2. ro_mem MEQ2. newmd2 HMD HMDb.
srr_branch_with tbl_ci_ok HS2.
- clear Hc. srr_run_to_with tbl_ci_ok HS2 RCY_END. ro_mem MEQ2. newmd2 HMD HMDb.
apply SRr_ret. apply (finishY E2 _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity) E2reg).
+ apply (ar_same B LAWS ly S W mem2 md2); [exact HAR2 | intros z; rewrite MEQ2; reflexivity | exact HMDb].
+ exact HMD.
+ intros a Hr Hs. rewrite MEQ2. rewrite Hfr2; [rewrite MEQ; reflexivity | exact Hr | | tauto].
unfold ascratch_stk. rewrite Rsp. unfold RGN_SCR. unfold RC_SCR in Hs. exact Hs.
+ intros a Ha. rewrite MEQ2. apply Hpres2. rewrite MEQ. exact Ha.
- exfalso. rewrite (br_atom_eq0 E2 36 0 E36) in Hc by lia. cbv in Hc. discriminate.
Qed.

Theorem siteY_srr : SRr tfibsegs W (cfg_at tfibsegs RCY_ENTRY regs mem md) POSTr.
Proof using All. destruct (Z_le_gt_dec n 64) as [Hle|Hgt]; [apply path1 | apply path2]; lia. Qed.

End f.
