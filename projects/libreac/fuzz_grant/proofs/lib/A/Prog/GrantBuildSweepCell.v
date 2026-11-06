(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the cut lemma pb_bs_cell of reac_grant_build_sweep's cell loop, adapting the call-and-reseat walk pattern of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v and lib/A/AChf.v and the caller-journal call block of lib/YC20.v; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC4b YC81 YC88 YCbw YCkd YC1g YC1h YC45 YC85 GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1i ACj1 ACbf GrantACjr GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective CtrlBuildGrantSweepSpec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require CtrlFinish.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantBuildSweepLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis TEFF : theadamp_tx_effective_spec B.
Hypothesis TBGS : tctrl_build_grant_sweep_spec B (BASE + AF_reac_ctrl_build_grant_sweep) pa_relro_lo pa_relro_hi.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* Narrow the row region's writable window to the cells not yet written
   (offsets p..2, p read from s11), so that a run keeps the written ones. *)
Ltac bsc_narrow HS :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let pv := eval vm_compute in (sr_get (ss_regs ssx) 27%bv) in
lazymatch pv with SLit ?p =>
let rs := eval vm_compute in (match ss_mem ssx with r :: rs => set_window r p 3 :: rs | [] => [] end) in
let HS3 := fresh "HS3" in
pose proof (st_ok_pi_submem Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS end end; norm_ss HS.
(* A register's symbolic value as it stands (prreg without the normalisation). *)
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* The frame regions a call of reac_headamp_tx_effective keeps: the row (601),
   F's header and tail (516) and F's shadow (529, read-only over the call) in
   the own frame (2, fpos); al's two bytes (12) and al's shadow cell (35) in
   al's frame (cid, pos). *)
Ltac bsc_kept_frames HK AG Hfin2 HfinS2 HFp F Hf64 Hfb64 Hflo Hfhi :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in
lazymatch goal with
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 601%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin2 | left; fsb_lits; fold F; lia
| intros a Ha Hn; exact Hn | intros a Ha; apply (proj1 (HFp a ltac:(lia))) ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 516%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin2 | left; fsb_lits; fold F; lia
| intros a Ha Hn; exact Hn | intros a Ha; apply (proj1 (HFp a ltac:(lia))) ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 529%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact Hfin2
| right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; fsb_lits; fold F; unfold SB; lia
| intros a Ha Hn; exact Hn | intros a Ha; lia ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _) =>
eapply (region_kept_frame_aj _ _ _ _ _ _ _ _ _ _ _ _ 12%nat); [exact HK | evalE AG | exact HfinS2 | lia | lia | lia | intros a Ha Hn; exact Hn ]
| |- region_kept _ _ _ _ (YP09.mkRegion (Some 35%nat) _ _ _ _ _) =>
eapply (region_kept_ownframe_aj _ _); [exact HK | evalE AG | exact HfinS2
| right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; unfold SB;
lazymatch type of Hflo with frame_addr ?l ?ci ?po <= ?x =>
let Hsf := fresh "Hsf" in
pose proof (shadow_in_frame (frame_addr l ci po) (fs_frame_bytes ci) x Hf64 Hfb64 ltac:(lia) ltac:(lia) ltac:(lia)) as Hsf end; lia
| intros a Ha Hn; exact Hn | intros a Ha; lia ]
end.
(* reac_headamp_tx_effective's second argument: (base + c) & 255 = base + c. *)
Lemma bsc_ch_denot : forall E base c, ew E 33 = Z_to_bv 64 base -> ew E 600 = Z_to_bv 64 c ->
0 <= base -> 0 <= c -> base + c < 256 ->
sv_denot E (SAlu ALU_ADD bs_ch (SLit 0)) = Z_to_bv 64 (base + c).
Proof.
intros E b c Hb Hc Hb0 Hc0 Hbc. rewrite denot_lit_U. f_equal. unfold bs_ch.
rewrite !U_SAlu, !U_SLit, (U_atom E 33 b Hb), (U_atom E 600 c Hc) by lia. cbn [zalu_raw].
rewrite (zcanon_id (b + c)) by (unfold M64; lia). change (zcanon 255) with 255. change (zcanon 0) with 0.
rewrite land255_small by lia. rewrite Z.add_0_r, !(zcanon_id (b + c)) by (unfold M64; lia). reflexivity.
Qed.
(* The values buffer after the cell's store: the first 3c + p values kept, and
   the stored byte the next one (BuildSweepModel's nth_sweep_vals). *)
Lemma bsc_vals : forall (H : word -> bool) (m m' : word -> option byte) F T tx base w c p,
0 <= c < w -> 0 <= p < 3 ->
garr8 SEGS (mrestrict H m) (F + 32) (map bv_unsigned (firstn (Z.to_nat (3 * c + p)) (sweep_vals T tx base (Z.to_nat w)))) ->
(forall a, F + 32 <= a < F + 32 + (3 * c + p) -> aview SEGS H m' a = aview SEGS H m a) ->
val_mem SEGS (mrestrict H m') (F + 32 + 3 * c + p) 1 (eff T tx (base + c) p) ->
garr8 SEGS (mrestrict H m') (F + 32) (map bv_unsigned (firstn (Z.to_nat (3 * c + p + 1)) (sweep_vals T tx base (Z.to_nat w)))).
Proof.
intros H m m' F T tx base w c p Hc Hp HG HK HV.
pose proof (OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.GroupaModel.eff_range T tx (base + c) p) as Hr.
assert (Hn : nth (Z.to_nat (3 * c + p)) (sweep_vals T tx base (Z.to_nat w)) (Z_to_bv 8 0) = Z_to_bv 8 (eff T tx (base + c) p)).
{ replace (Z.to_nat (3 * c + p)) with (3 * Z.to_nat c + Z.to_nat p)%nat by lia.
rewrite nth_sweep_vals by lia. rewrite !Z2Nat.id by lia. reflexivity. }
replace (Z.to_nat (3 * c + p + 1)) with (S (Z.to_nat (3 * c + p))) by lia.
rewrite (firstn_S_nth _ _ (Z_to_bv 8 0)) by (rewrite length_sweep_vals; lia).
rewrite map_app, Hn. cbn [map].
replace (bv_unsigned (Z_to_bv 8 (eff T tx (base + c) p))) with (eff T tx (base + c) p)
by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; symmetry; apply Z.mod_small; exact Hr).
apply (garr8_app1 SEGS (mrestrict H m) (mrestrict H m') (F + 32) _ _ HG).
- rewrite length_map, length_firstn, length_sweep_vals.
replace (F + 32 + Z.of_nat (Nat.min (Z.to_nat (3 * c + p)) (3 * Z.to_nat w))) with (F + 32 + 3 * c + p) by lia. exact HV.
- exact Hr.
- intros a Ha. apply (mbyte_of_aview SEGS). apply HK. rewrite length_map, length_firstn, length_sweep_vals in Ha. lia.
Qed.
(* The byte the cell's store left: the chunk at offset p of the row region
   (region 0), the value of the atom Eeff names. *)
Ltac bsc_vbyte HS AG Eeff F c T tx base Vbyte :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msX) =>
let HRrow := fresh "HRrow" in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wx) msX) 0 _ HS eq_refl) as HRrow; cbn [ms_mem restrict] in HRrow;
lazymatch type of HRrow with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk ?od (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 601 (F + 32 + 3 * c) cs lo hi wlo whi od 1%N e (eff T tx (base + c) od) HRrow
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite Eeff, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 1)) with 256; exact (OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.GroupaModel.eff_range T tx (base + c) od))
ltac:(cbn; lia)) as Vbyte end end; clear HRrow end.
(* The column step's branch `bne s8, s4` at 0x84b2c compares c + 1 with the width. *)
Lemma bsc_br : forall E c w, ew E 600 = Z_to_bv 64 c -> ew E 34 = Z_to_bv 64 w -> 0 <= c < 2 ^ 62 -> 0 <= w < 2 ^ 62 ->
(U E (SOff 600 1) =? U E (SOff 34 0)) = (c + 1 =? w).
Proof. intros E c w Hc Hw Rc Rw. rewrite (U_atom_off E 600 c 1 Hc), (U_atom E 34 w Hw) by lia. reflexivity. Qed.
Lemma bsc_br' : forall E c w, ew E 600 = Z_to_bv 64 c -> ew E 34 = Z_to_bv 64 w -> 0 <= c < 2 ^ 62 -> 0 <= w < 2 ^ 62 ->
(U E (SOff 34 0) =? U E (SOff 600 1)) = (w =? c + 1).
Proof. intros E c w Hc Hw Rc Rw. rewrite (U_atom_off E 600 c 1 Hc), (U_atom E 34 w Hw) by lia. reflexivity. Qed.
Lemma pb_bs_cell : bs_cell_spec B.
Proof.
unfold bs_cell_spec.
intros z ly S W regs mem md ch s mx al tx base w T shv fpos S2 sp1 cid pos c p Ec ms3 md3 Q HCTX Hc Hp HENV HS HMEM K1 K2 K3.
bs_cut_intro HCTX HENV HMEM ly S W mem md fpos S2 cid pos Ec.
assert (Hsp1al16 : sp1 mod 16 = 0)
by (pose proof (Z.div_mod sp1 32 ltac:(lia)) as D; rewrite Hsp1al, Z.add_0_r in D; rewrite D;
replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia; apply Z_mod_mult).
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Hsp8 : spZ regs mod 8 = 0) by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hal16; [|lia]; destruct Hal16 as [q Hq]; exists (2 * q); lia).
assert (HKV : forall a, F + 32 <= a < F + 32 + (3 * c + p) -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (HKT : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros; reflexivity).
assert (Hp3 : p = 0 \/ p = 1 \/ p = 2) by lia.
destruct Hp3 as [Ep | [Ep | Ep]]; destruct z.
all: rewrite Ep in HS; norm_ss HS; bsc_narrow HS.
(* ---- to the call of reac_headamp_tx_effective (0x84b10) ---- *)
all: paj_run_shc RUNP RUNC HS HJ2; [awrFL_with ltac:(idtac; awr_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 Hp HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E601 Ep Hc Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG;
first [ (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)
| (intros Hrg_rng; match goal with |- ?g => idtac "HKVFAIL" g end; match type of Hrg_rng with ?t => idtac t end; match type of Ha_rng with ?t => idtac t end; fail 1) ]).
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E601 Ep Hc Hw1 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG;
first [ (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)
| (intros Hrg_rng; match goal with |- ?g => idtac "HKTFAIL" g end; match type of Hrg_rng with ?t => idtac t end; match type of Ha_rng with ?t => idtac t end; fail 1) ]).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: prreg HS (10%bv : bv 5) Rb0; prreg_raw HS (11%bv : bv 5) Rb1; prreg HS (12%bv : bv 5) Rb2; prreg HS (1%bv : bv 5) Rbra;
prreg HS (2%bv : bv 5) Rbsp; prreg HS (3%bv : bv 5) Rbgp; prreg HS (4%bv : bv 5) Rbtp; prreg HS (8%bv : bv 5) Rbs0.
(* the call chain: the saved ra and s0 at sp - 8 and sp - 16 *)
all: lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msY) =>
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W) msY) 7 _ HS eq_refl) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; try rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra2;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(evalE AG) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; try rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs02
end; clear HRstk;
assert (Hch2 : achain ly (aview SEGS (w_H W) (ms_mem msY)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch))
by (replace (spZ regs + -8) with (spZ regs - 8) in Vra2 by lia; replace (spZ regs + -16) with (spZ regs - 16) in Vs02 by lia;
exact (achain_push ly _ _ (spZ regs) (s0Z regs) (raZ regs) _ sp1 Hch ltac:(lia) HUP
(rdword_of_val_mem SEGS _ _ _ _ Vra2 Qra) (rdword_of_val_mem SEGS _ _ _ _ Vs02 Qs0) Hra4 ltac:(lia) Hsp8 ltac:(lia) ltac:(lia)));
clear Vra2 Vs02 end.
all: lazymatch goal with |- SRr _ _ {| cfg_ms := ?msX; cfg_model := _ |} _ =>
assert (HTobj6 : obj_at SEGS (mrestrict (w_H W) (ms_mem msX)) tx LAY_TX (tx_vals T))
by (apply (obj_at_transport_range SEGS _ _ tx LAY_TX (tx_vals T) 460 HOBJ); [vm_compute; reflexivity|];
intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia) end.
all: pmkst HS.
all: rewrite pa_sigma_reac_headamp_tx_effective.
all: fs_roF HS.
all: eapply SRr_bind; [ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) ?mdX) _ =>
eapply (cl_callS B LAWS W (ms_regs msX) (ms_mem msX) _ TBSW_STK (spZ regs) (bsw_FP s al mx base w) ly S W mem md [(2, fpos)] ly S2 mdX 0
TEFF_STK [] 0 (sp1 - spZ regs) (getr (ms_regs msX) 1) ((spZ regs, raZ regs, s0Z regs) :: ch)
(fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S2 /\ W' = W /\ getr regs' 10 = w64 (eff T tx (base + c) p) /\
obj_at SEGS (mrestrict (w_H W) mem') tx LAY_TX (tx_vals T)) HJ2) end;
[ unfold spZ at 1; rewrite Rbsp; evalE AG
| rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity
| lia
| unfold TEFF_STK; rewrite Hes; lia
| rewrite FFS; unfold TEFF_STK; rewrite Hes; lia
| rewrite Rbgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rbtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; try rewrite (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| reflexivity
| rewrite Rbra; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite Rbra; pose proof pa_B_ok as HB; rewrite unsigned_lit_small by lia; lia
| replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia;
replace (s0Z _) with (spZ regs) by (unfold s0Z; rewrite Rbs0; evalE AG); exact Hch2
| intros HPRE7;
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg ?pcx ?mm ?rom) ?mdd) _ =>
change (mkCfg (mkst rg pcx mm rom) mdd) with (cfg_at SEGS A_tx_effectiveP rg mm mdd) end;
apply (TEFF ly S2 W _ _ _ _ tx (base + c) p T HPRE7);
[ rewrite Rb0; try rewrite (AG 13%nat) by lia; exact E13
| rewrite Rb1; exact (bsc_ch_denot _ base c E33 E600 ltac:(lia) ltac:(lia) ltac:(lia))
| rewrite Rb2, Ep; reflexivity
| lia | lia | exact HtxS2 | exact HTlen | exact HTobj6 ]
| let a := fresh "a" in let rg := fresh "rg" in intros a (rg & [] & _) ]
| ].
all: cbv beta; intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HJ7 & HJ7c & HP7 & (-> & -> & -> & Ha07 & HTobj7)).
all: rewrite Rbra.
(* ---- after the call: what it kept ---- *)
all: lazymatch type of HJ7c with ajournal _ _ _ _ _ _ _ _ ?memc _ _ _ _ _ _ _ _ =>
assert (HK7 : acall_kept SEGS B ly S2 W memc W mem7 (spZ regs + (sp1 - spZ regs) - TEFF_STK) (spZ regs + (sp1 - spZ regs)) (fun _ => False))
by (eapply (acall_kept_of_journal SEGS B Hsegs); [exact HJ7c | exact (proj1 HJ2) | intros a (rg & [] & _) | intros b m i Hb _ _; exact Hb | exact sink_closed_nil]);
assert (KF7 : forall a, F <= a < F + 256 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) memc a)
by (pose proof HK7 as (_ & _ & _ & K74 & _); intros a Ha; apply (K74 2 fpos a Hfin2);
[left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; change (fs_frame_bytes 2) with 256; lia | intros []]) end.
all: pose proof HK7 as (K71 & _).
all: assert (HUP7 : forall a, spZ regs <= a < 2 ^ 64 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite <- (HUP a Ha); apply K71; lia).
all: clear HUP K71; rename HUP7 into HUP.
all: assert (HKV7 : forall a, F + 32 <= a < F + 32 + (3 * c + p) -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) (ms_mem ms3) a)
by (intros a Ha; rewrite KF7 by lia; apply HKV; exact Ha).
all: clear HKV KF7 HKT; rename HKV7 into HKV.
all: assert (HKT : forall a, tx <= a < tx + 460 -> aview SEGS (w_H W) mem7 a = aview SEGS (w_H W) mem7 a) by (intros; reflexivity).
all: aconstsF HJ2 Qgot7p Qcell7p Qguar7p Quar7p; aconstsF HJ7 Qgot7 Qcell7 Qguar7 Quar7.
all: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFp7 & HFSp7).
all: fold F in HFp7, HFSp7; change (fs_frame_bytes 2 / 8) with 32 in HFSp7; change (fs_frame_bytes 2) with 256 in HFp7.
all: reseat HS HJ7 HP7 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG
ltac:(idtac; first [ bsc_kept_frames HK7 AG Hfin2 HfinS2 HFp7 F Hf64 Hfb64 Hflo Hfhi
| keptFL HK7 HJ7 AG Qgot7p Qgot7 Qcell7p Qcell7 Qguar7p Qguar7 Quar7p Quar7 ltac:(idtac; fail)
ltac:(idtac; match goal with |- apresent _ _ ?x => apply (proj1 (HFp7 x ltac:(lia))) end)
| match goal with |- ?g => idtac "KEEPFAIL" g end; fail ]).
all: fs_rwF HS E529 HFSp7.
(* ---- from the return (0x84b14): the store of the byte at F + 32 + 3c + p ---- *)
all: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let a0v := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in
lazymatch a0v with SOff ?k 0 =>
prreg HS (10%bv : bv 5) Ra0;
assert (Eeff : ew Ev k = Z_to_bv 64 (eff T tx (base + c) p)) by (rewrite <- Ra0; exact Ha07) end end.
1-4: paj_run_to_sh RUNTOP HS HJ7 17492; [awrFL_with ltac:(idtac; awr_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
5,6: paj_run_sh RUNP HS HJ7; [awrFL_with ltac:(idtac; awr_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |].
(* ---- after the store: the written bytes, the table and the caller's stack kept ---- *)
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 Hp HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E601 Ep Hc Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E601 Ep Hc Hw1 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: subst p.
(* ---- p < 2: the next cell, ss_I (p + 1) ---- *)
1-4: bsc_vbyte HS AG Eeff F c T tx base Vbyte.
1-4: destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFp8 & _).
1-4: (fold F in HFp8; change (fs_frame_bytes 2) with 256 in HFp8).
1-4: lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx 0 r (set_window r 0 3) HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 3 (st_ok_pi_region_nth Ex ssx msx 0 r HS eq_refl)
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; rewrite E601, unsigned_lit_small by lia;
let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp8 (F + 32 + 3 * c + o) ltac:(lia)))))) as HS3;
clear HS; rename HS3 into HS end; norm_ss HS.
1-4: clear Eeff Ra0.
1-4: first [ bs_rejoin HS AG (bs_row :: bs_RL0 true) (bs_FL true) bs_deads_I 602%nat
| bs_rejoin HS AG (bs_row :: bs_RL0 false) (bs_FL false) bs_deads_I 602%nat ].
1-4: (ACj1.rebaseE HS AG HEv; clear HEv).
1-4: lazymatch type of K1 with _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with ssK in HS | idtac "SEATFAIL" ssx; fail] end end.
1-4: eapply (K1 ltac:(lia)); [ | exact HS | ]; [ (unfold bs_env;
split; [match goal with H : img_env _ _ ?Ev |- img_env _ _ ?Ev => exact H end|];
split; [let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in let Hr := fresh "Hr" in
intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
try rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]) | (split; [exact HJ7|]; split; [exact HUP|]; split;
[ eapply (bsc_vals (w_H W) _ _ F T tx base w c); [exact Hc | lia | exact HVALS | exact HKV | exact Vbyte]
| apply (obj_at_transport_range SEGS _ _ tx LAY_TX (tx_vals T) 460 HTobj7); [vm_compute; reflexivity|];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ]) ].
(* ---- p = 2: the column step and its branch `bne s8, s4` (0x84b2c) ---- *)
all: psrr_branch_pi RUNP BR HS.
(* The branch's direction, read off the run itself: taken (c + 1 < w) reaches
   the loop head 0x84aec (17468, ss_L); not taken (c + 1 = w) falls through
   `j` to the instruction after the loop 0x84b44 (17556, ss_X). *)
all: first [ paj_run_to_sh RUNTOP HS HJ7 17468; [awrFL_with ltac:(idtac; awr_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |]
| paj_run_to_sh RUNTOP HS HJ7 17556; [awrFL_with ltac:(idtac; awr_row_rule AG fpos F EFA0 Hc Hw1) AG fpos F EFA0 |] ].
all: upd_rngW HKV HFr ltac:(clear - Ha_rng Hc Hw1 Hp HF4096 HFceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E601 Hc Hw1 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: upd_rngW HKT HFr ltac:(clear - Ha_rng Htx4096 Htxceil C1; lia)
ltac:(idtac; exfalso; clear - Ha_rng Hrg_rng AG Usp E60 RF E529 E601 Hc Hw1 Htx4096 Htxceil Htxia HtxF HF4096 HFceil HF8lo HF8hi HF8c Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3; revert Hrg_rng; evalE AG; try (intros Hrg_rng; zones; unfold SB, SHADOW_OFF in *; lia)).
all: upd_aboveW HUP HFr AG; clear HF HFr HG.
all: prreg HS (18%bv : bv 5) R18; prreg HS (24%bv : bv 5) R24.
all: rewrite E601, unsigned_lit_small in R18 by lia; rewrite E600, unsigned_lit_small in R24 by lia.
all: bsc_vbyte HS AG Eeff F c T tx base Vbyte.
all: lazymatch type of HS with
| st_ok_pi _ _ _ (mkSS 17468 _ _ _ _) _ => assert (Hcw : c + 1 < w) by (match goal with H : branch_taken _ _ _ = _ |- _ => revert H end;
first [rewrite branch_ne_U | rewrite branch_eq_U];
rewrite ?(bsc_br _ c w E600 E34 ltac:(lia) ltac:(lia)), ?(bsc_br' _ c w E600 E34 ltac:(lia) ltac:(lia));
let Hb := fresh "Hb" in intros Hb; destruct (Z.eqb_spec (c + 1) w); destruct (Z.eqb_spec w (c + 1)); cbn in Hb; first [discriminate Hb | lia])
| st_ok_pi _ _ _ (mkSS 17556 _ _ _ _) _ => assert (Hcw : c + 1 = w) by (match goal with H : branch_taken _ _ _ = _ |- _ => revert H end;
first [rewrite branch_ne_U | rewrite branch_eq_U];
rewrite ?(bsc_br _ c w E600 E34 ltac:(lia) ltac:(lia)), ?(bsc_br' _ c w E600 E34 ltac:(lia) ltac:(lia));
let Hb := fresh "Hb" in intros Hb; destruct (Z.eqb_spec (c + 1) w); destruct (Z.eqb_spec w (c + 1)); cbn in Hb; first [discriminate Hb | lia])
end.
all: clear E600 E601 Eeff Ra0.
all: first [ bs_rejoin HS AG (bs_RL0 true) (bs_FL true) bs_deads 600%nat | bs_rejoin HS AG (bs_RL0 false) (bs_FL false) bs_deads 600%nat ].
all: (lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo 600%nat ?ws) _ _ =>
assert (E600 : ew (havoc Eo 600 ws) 600 = Z_to_bv 64 (c + 1))
by (refine (eq_trans (ew_havoc_new Eo 600 ws 0 (Z_to_bv 64 0) ltac:(cbn [length]; lia)) _); cbn [nth ms_regs restrict mkst];
first [exact R24 | rewrite R24; reflexivity]);
assert (E601 : ew (havoc Eo 600 ws) 601 = Z_to_bv 64 (F + 32 + 3 * (c + 1)))
by (refine (eq_trans (ew_havoc_new Eo 600 ws 1 (Z_to_bv 64 0) ltac:(cbn [length]; lia)) _); cbn [nth ms_regs restrict mkst];
first [exact R18 | rewrite R18; f_equal; lia]) end).
all: (ACj1.rebaseE HS AG HEv; clear HEv).
(* taken: the next row, and the loop head ss_L (c + 1) *)
all: lazymatch type of HS with
| st_ok_pi _ _ _ (mkSS 17468 _ _ _ _) _ => (lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => assert (E12'' : ew Ev 12 = Z_to_bv 64 al) by (rewrite (AG 12%nat) by lia; exact E12) end);
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos (proj1 HJ7) Hfin2) as (_ & _ & HFp8 & HFSp8);
fold F in HFp8; change (fs_frame_bytes 2) with 256 in HFp8;
(lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ bs_row HS eq_refl
ltac:(unfold region_ok, bs_row; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E601, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ let o := fresh "o" in let Ho := fresh "Ho" in intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFp8 (F + 32 + 3 * (c + 1) + o) ltac:(lia))) | apply Forall_nil ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, bs_row; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?E601, ?E35, ?E12'', ?E529, ?RF, ?E60; evalE AG; ulits; unfold SB;
clear - Hc Hcw Hw1 Hsp1 Hceil Hslo Hstk0 Hshi H47 FFS C1 C3 HF4096 HFceil HFhigh HFhigh_img HF8lo HF8hi HF8c Hf4096 Hfceil Hfhigh Hfhigh_img HdFC Hflo Hfhi Hal512 Hal8d HF8 HFq Hob241 Hob242 Hob273 Hob274 Huar;
repeat split; first [zone_lia | match goal with |- ?g => idtac "ZFAILROW" g; fail end])) as HS3;
clear HS; rename HS3 into HS end);
norm_ss HS;
(lazymatch type of K2 with _ -> _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with ssK in HS | idtac "SEATFAIL" ssx; fail] end end);
eapply (K2 eq_refl Hcw); [ | exact HS | ]; [ (unfold bs_env;
split; [match goal with H : img_env _ _ ?Ev |- img_env _ _ ?Ev => exact H end|];
split; [let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in let Hr := fresh "Hr" in
intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
try rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]) | replace (3 * (c + 1)) with (3 * c + 2 + 1) by lia; (split; [exact HJ7|]; split; [exact HUP|]; split;
[ eapply (bsc_vals (w_H W) _ _ F T tx base w c); [exact Hc | lia | exact HVALS | exact HKV | exact Vbyte]
| apply (obj_at_transport_range SEGS _ _ tx LAY_TX (tx_vals T) 460 HTobj7); [vm_compute; reflexivity|];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ]) ]
| _ => idtac end.
(* not taken: the instruction after the loop, ss_X *)
all: rewrite Hcw in E600, E601;
norm_ss HS;
(lazymatch type of K3 with _ -> _ -> forall _ _ _, _ -> st_ok_pi _ _ _ ?ssK _ -> _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx => first [change ssx with ssK in HS | idtac "SEATFAIL" ssx; fail] end end);
eapply (K3 eq_refl Hcw); [ | exact HS | ]; [ (unfold bs_env;
split; [match goal with H : img_env _ _ ?Ev |- img_env _ _ ?Ev => exact H end|];
split; [let n := fresh "n" in let r := fresh "r" in let Hn := fresh "Hn" in let Hr := fresh "Hr" in
intros n r Hn; destruct (bv_unsigned_in_range _ r) as [_ Hr]; change (bv_modulus 5) with 32 in Hr;
try rewrite (AG n) by lia; apply EE; exact Hn|];
repeat (split; [first [assumption | (rewrite (AG 32%nat) by lia; exact E32)] |]);
first [assumption | (rewrite (AG 32%nat) by lia; exact E32)]) | replace (3 * w) with (3 * c + 2 + 1) by lia; (split; [exact HJ7|]; split; [exact HUP|]; split;
[ eapply (bsc_vals (w_H W) _ _ F T tx base w c); [exact Hc | lia | exact HVALS | exact HKV | exact Vbyte]
| apply (obj_at_transport_range SEGS _ _ tx LAY_TX (tx_vals T) 460 HTobj7); [vm_compute; reflexivity|];
let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply (mbyte_of_aview SEGS); apply HKT; lia ]) ].
Qed.
End e.
End d.
End b.
