(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YL0l.v. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/libreac/fuzz_scene/lib/Reusable/YL0l_cfw.v, with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YK0p YP0n YM06 YM02.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04 YN3v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0x YO0d YO0e YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO06.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YH00 YH01 YH03 YH02 YN3e YN35 YN3f YN3g YN34.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN03 YL07 YL01 YL08 YL0d YL0e YL0f YL02 YL0a YL0b YL00 YL0c YL09 YL0k YL0o YL0m.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YM0b YO03 YO04 YL0l DriverSlots.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0d_cf YO04_cfw YK15_cfw YP03_cfw YP0n2_cfw YN34b_cfw.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YL0k_cfw YL0b_cfw YL0o_cfw YL0d2_cfw SymTac_cfw.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma capflag_nonneg cap : 0 <= capflag cap.
Proof using. unfold capflag. destruct (cap <=? MMAP_THRESHOLD); unfold MMAX; lia. Qed.
Lemma rp_init : RPinv 0 1 CAP0 (rb_malloc (RB 0 0 0 0) CAP0) /\ 0 + capflag CAP0 <= 2 ^ 24.
Proof using.
split.
- unfold RPinv, rb_malloc. cbn -[mdelta]. unfold PGSZ. repeat split; lia.
- unfold capflag, CAP0, MMAP_THRESHOLD, MMAX. cbn. lia.
Qed.
Lemma rp_exit : forall b Kb c cap fuel, RPinv Kb c cap b -> Kb + capflag cap <= 2 ^ 24 -> 0 <= c -> c + Z.of_nat fuel <= 12 ->
RPinv (2 ^ 24) 12 cap b.
Proof using.
intros b Kb c cap fuel (V1 & V2 & V3 & V4 & V5) HK Hc Hcf. pose proof (capflag_nonneg cap).
unfold RPinv, PGSZ in *. repeat split; lia.
Qed.
Lemma rp_grow : forall A b Kb c cap f,
WF A -> res_ok A b -> RPinv Kb c cap b -> Kb + capflag cap <= 2 ^ 24 -> 0 <= c -> c + Z.of_nat (S f) <= 12 ->
cap = 2 ^ (27 - Z.of_nat (S f)) -> (1 <= f)%nat -> (S f <= 11)%nat ->
room b (2 * cap) /\ roomcf SRC_LIM_MIN (malloc (2 * cap) A) /\
rb_live (rb_malloc b (2 * cap)) <= SRC_LIM_MIN /\
RPinv (Kb + capflag cap) (c + 1) (2 * cap) (rb_free (rb_malloc b (2 * cap)) cap) /\
Kb + capflag cap + capflag (2 * cap) <= 2 ^ 24.
Proof using.
intros A b Kb c cap f HW HR (V1 & V2 & V3 & V4 & V5) HK Hc Hcf Hcap Hf1 Hf11.
set (k := 27 - Z.of_nat (S f)) in Hcap.
assert (Hk16 : 16 <= k) by (unfold k; lia). assert (Hk25 : k <= 25) by (unfold k; lia).
clearbody k.
assert (Hcap16 : 65536 <= cap).
{ subst cap. change 65536 with (2 ^ 16). apply Z.pow_le_mono_r; lia. }
assert (Hcap25 : cap <= 2 ^ 25) by (subst cap; apply Z.pow_le_mono_r; lia).
assert (Hfl : 0 <= capflag cap) by apply capflag_nonneg.
pose proof (mdelta_le cap ltac:(lia)) as Hmd.
assert (Hmd2 : mdelta (2 * cap) = 2 * cap + PGSZ).
{ rewrite mdelta_big by (unfold MMAP_THRESHOLD; lia). apply page_round_exact; [|lia].
subst cap. replace (2 * 2 ^ k) with ((2 * 2 ^ (k - 12)) * PGSZ); [apply Z_mod_mult|].
unfold PGSZ. change 4096 with (2 ^ 12). rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. f_equal. f_equal. lia. }
assert (Hpr2 : page_round (2 * cap + IB + UNIT) = 2 * cap + PGSZ) by (rewrite <- mdelta_big by (unfold MMAP_THRESHOLD; lia); exact Hmd2).
pose proof (shcap_845 (rb_hand b) ltac:(lia)) as SC.
pose proof (shcap_845 (rb_hand b + 65) ltac:(lia)) as SC2.
assert (Hroom : room b (2 * cap)).
{ unfold room. rewrite Hpr2.
unfold MG_LIVE, MG_SLOTS, MG_REQ, MAX_INPUT, MMAX, IB, UNIT, PGSZ in *.
assert (rb_brk b / 4096 <= 2 * c) by (apply Z.div_le_upper_bound; lia).
repeat split; try lia. }
assert (Hfl2 : capflag (2 * cap) = 0).
{ unfold capflag. replace (2 * cap <=? MMAP_THRESHOLD) with false by (symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD; lia). reflexivity. }
split; [exact Hroom|]. split.
{ apply (roomcf_malloc_res A b (2 * cap) SRC_LIM_MIN HW HR Hroom). rewrite Hpr2.
unfold rb_live, SRC_LIM_MIN, MMAX, IB, UNIT, PGSZ in *. lia. }
split.
{ unfold rb_live, rb_malloc. cbn [rb_bytes rb_cnt rb_hand rb_brk]. rewrite Hmd2.
unfold SRC_LIM_MIN, MMAX, IB, UNIT, PGSZ in *. lia. }
split; [| rewrite Hfl2; lia].
unfold RPinv, rb_free, rb_malloc. rewrite Hmd2.
destruct (MMAP_THRESHOLD <? cap) eqn:Et; cbn.
- apply Z.ltb_lt in Et. rewrite <- (mdelta_big cap) by lia. unfold PGSZ in *. repeat split; lia.
- apply Z.ltb_ge in Et. unfold capflag. replace (cap <=? MMAP_THRESHOLD) with true by (symmetry; apply Z.leb_le; exact Et).
unfold PGSZ, MMAX, MMAP_THRESHOLD, IB, UNIT in *. repeat split; lia.
Qed.
Section j.
Variable API : AllocAPI src0_msyms.
Hypothesis AX : AllocExtra src0_msyms (aa_MR API).
Hypothesis MRC : forall fx' : FPState, @malloc_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis FRC : forall fx' : FPState, @free_realizes_cf fx' rc src0_msyms (aa_MR API).
Hypothesis LIMLAW : forall L A mem md, aa_MR API L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Variables (sp tid : word) (a0 path : list byte) (inp : ProcInput) (data : list byte) (rnd : EntryDraw).
Hypothesis Hlk : fs_lookup (in_fs inp) path = Some data.
Local Abbreviation L := (Z.of_nat (length data)).
Hypothesis HSA0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored (E_main sp [a0; path] (in_envp inp) tid rnd) G.
Variable PRES : dleaf * astate -> Prop.
Local Abbreviation E_lp := (YL0l.E_lp sp tid a0 path inp data rnd).
Local Abbreviation ew_lp := (YL0l.ew_lp sp tid a0 path inp data rnd).
Local Abbreviation md_loop := (YL0l.md_loop path inp).
Local Abbreviation md_post := (YL0l.md_post inp).
Local Abbreviation md_loop_vm := (YL0l.md_loop_vm path inp).
Local Abbreviation md_loop_read := (YL0l.md_loop_read path inp).
Local Abbreviation md_loop_close := (YL0l.md_loop_close path inp).
Local Abbreviation MR_win := (YL0l.MR_win API AX data).
Local Abbreviation blk_data_win := (YL0l.blk_data_win API AX data).
Local Abbreviation anch_lp := (YL0l.anch_lp sp tid a0 path inp data rnd HSA0).
Local Abbreviation Ec14 := (YL0l.Ec14 sp tid a0 path inp data rnd).
Local Abbreviation Ec28 := (YL0l.Ec28 sp tid a0 path inp data rnd).
Local Abbreviation U_want := (YL0l.U_want sp tid a0 path inp data rnd).
Local Abbreviation U_dst := (YL0l.U_dst sp tid a0 path inp data rnd).
Local Abbreviation U_len1 := (YL0l.U_len1 sp tid a0 path inp data rnd).
Local Abbreviation U_big := (YL0l.U_big sp tid a0 path inp data rnd).
Local Abbreviation U_dbl := (YL0l.U_dbl sp tid a0 path inp data rnd).
Local Abbreviation agree_to_lp := (YL0l.agree_to_lp sp tid a0 path inp data rnd).
Local Abbreviation lp_junk := (YL0l.lp_junk sp tid a0 path inp data rnd).
Local Abbreviation TREE := (YL0l.TREE data).
Local Abbreviation ext29_ewset := (YL0l.ext29_ewset data).
Local Abbreviation ext29_havoc := (YL0l.ext29_havoc data).
Local Abbreviation ext29_post := (YL0l.ext29_post data).
Local Abbreviation cap_range := (YL0l.cap_range data).
Local Abbreviation bv_off_add := (YL0l.bv_off_add data).
#[local] Ltac drv_anch ::= first [ assumption | eapply anch_lp; [ eassumption | vm_compute; reflexivity ] ].
Definition POST_cf (K : dleaf * astate -> TSet) : Prop :=
forall cap' bufp' A' Lc' J' g' len0 w ms' md',
L < cap' -> 65536 <= cap' <= MAX_INPUT -> 0 <= len0 <= L ->
user_blocks A' = [(bufp', cap')] -> WF A' -> bounded A' -> st_init_done A' = true ->
DI A' -> (exists b, res_ok A' b /\ RPinv (2 ^ 24) 12 cap' b) ->
st_ok src0segs (ewset (E_lp J' (ptr_addr Lc' bufp') g' len0 cap') 46 (Z_to_bv 64 w)) S_HDR ms' -> 1 <= w <= 65536 ->
len0 = L ->
aa_MR API Lc' A' (ms_mem ms') md' -> md_post md' ->
blk_data src0_msyms (ms_mem ms') (ptr_addr Lc' bufp') data ->
jinv K (driver_tail data (RdLoaded bufp' cap') A') -> gtree mgrant (driver_tail data (RdLoaded bufp' cap') A') ->
leaves PRES (driver_tail data (RdLoaded bufp' cap') A') ->
crealizes src0_msyms (mkCfg ms' md') (tset (driver_tail data (RdLoaded bufp' cap') A') K).
Ltac ccarry E S HS HF HMR HD Hin len Hfl :=
lazymatch type of HD with blk_data _ _ ?a ?bs0 =>
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
let HD' := fresh "HD'" in
let HG0 := fresh "HG0" in let HSA1 := fresh "HSA1" in
assert (HG0 : facts_ok E (ss_facts S)) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & X); exact X);
assert (HSA1 : stack_anchored E (ss_facts S)) by drv_anch;
pose proof (fun h1 h2 => blk_data_after_frame src0_msyms (aa_MR API) (aa_laws API) AX _ _ m0 m1 _ E (ss_facts S) src0_keep rs0 _ _ a bs0
HMR HG0 HSA1 ltac:(vm_compute; reflexivity) HF Hin h1 h2 HD) as HD';
specialize (HD' ltac:(lia) ltac:(rewrite (Hfl len); lia)); clear HD HG0 HSA1; rename HD' into HD
end end;
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E HS HF HMR.
Theorem loop_rd_cf : forall N fuel cap bufp len A Lc J g ms md (K : dleaf * astate -> TSet),
(Z.to_nat (2 ^ 28 - len - cap) < N)%nat ->
cap = 2 ^ (27 - Z.of_nat fuel) -> (1 <= fuel <= 11)%nat ->
0 <= len < cap -> len <= L ->
user_blocks A = [(bufp, cap)] -> WF A -> bounded A -> st_init_done A = true ->
DI A -> (exists b Kb c, res_ok A b /\ RPinv Kb c cap b /\ Kb + capflag cap <= 2 ^ 24 /\ 0 <= c /\ c + Z.of_nat fuel <= 12) ->
st_ok src0segs (E_lp J (ptr_addr Lc bufp) g len cap) S_RD ms ->
aa_MR API Lc A (ms_mem ms) md -> md_loop md len ->
blk_data src0_msyms (ms_mem ms) (ptr_addr Lc bufp) (firstn (Z.to_nat len) data) ->
jinv K (TREE fuel cap bufp A) -> gtree mgrant (TREE fuel cap bufp A) -> leaves PRES (TREE fuel cap bufp A) ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
POST_cf K ->
crealizes src0_msyms (mkCfg ms md) (tset (TREE fuel cap bufp A) K).
Proof using AX MRC FRC LIMLAW Hlk HSA0.
induction N as [|N IHN]; [lia|].
intros fuel cap bufp len A Lc J g ms md K HN Hcap Hfuel Hlen HlenL Hub HW HB Hid HDI HRES HS HMR Hmd HD HJt HGt HLt HK HPOST.
destruct (cap_range fuel cap Hcap Hfuel) as [Hcr Hcm].
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp, cap) (user_blocks A)) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc A (ms_mem ms) md bufp cap 0 HMR Hin ltac:(lia)) as (_ & Hq1 & Hq2 & _).
assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
assert (Hb' : exists b, b = ptr_addr Lc bufp) by (eexists; reflexivity). destruct Hb' as [buf Hbuf]. rewrite <- Hbuf in *.
set (E := E_lp J buf g len cap) in HS.
assert (HX : ext29 (E_lp J buf g len cap) E) by apply ext29_refl.
assert (Hfl : forall k, 0 <= k <= L -> Z.of_nat (length (firstn (Z.to_nat k) data)) = k).
{ intros k Hk. rewrite firstn_length_le; lia. }
assert (Hbufr : 0 <= buf < 2 ^ 62) by lia. assert (Hlenr : 0 <= len <= cap) by lia. assert (Hcapr : 0 < cap <= 2 ^ 26) by lia.
pose proof (U_want J buf g len cap E HX Hbufr Hlenr Hcapr) as HUw.
assert (Hch2 : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md) by exact (proj1 (proj2 (proj2 Hmd))).
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E S_W msx) in HS end.
ccarry E S_W HS HF HMR HD Hin len Hfl.
assert (REABS : forall w ms1 (S : sstate),
st_ok src0segs E S ms1 -> reabs_check P_W S RW_regs RW_facts = true -> ss_mem S = LH_mem -> ss_pc S = RWPC ->
sv_denot E (sr_get (ss_regs S) (R 12)) = Z_to_bv 64 w -> 1 <= w <= 65536 ->
st_ok src0segs (ewset E 46 (Z_to_bv 64 w)) S_RW ms1).
{ intros w ms1 S HS1 Hck HmS HpcS H12 Hw.
unfold S_RW. rewrite <- HpcS.
apply (st_ok_reabs src0segs P_W E (ewset E 46 (Z_to_bv 64 w)) S ms1 RW_regs LH_mem RW_facts HS1).
- split; [| intros; reflexivity]. intros k Hk. unfold P_W in Hk. apply ew_ewset_other. intros ->. rewrite Nat.eqb_refl in Hk. discriminate.
- exact Hck.
- apply obl_W. rewrite ew_ewset_same. rewrite (st_ok_reg src0segs _ _ _ (R 12) HS1), H12. reflexivity.
- rewrite fobl_W. constructor; [| constructor]. unfold afact_ok, fact_want. cbn [fst snd af_lo af_hi af_al2].
rewrite ew_ewset_same, u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
- destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & HM & _). rewrite HmS in HM.
eapply (mem_ok_agree_pd src0segs P_W PT E); [| | exact HM].
+ split; [| intros; reflexivity]. intros k Hk. unfold P_W in Hk. apply ew_ewset_other. intros ->. rewrite Nat.eqb_refl in Hk. discriminate.
+ vm_compute. reflexivity. }
assert (CONT : forall w ms1, 1 <= w <= 65536 -> w <= cap - len ->
st_ok src0segs (ewset E 46 (Z_to_bv 64 w)) S_RW ms1 ->
aa_MR API Lc A (ms_mem ms1) md ->
blk_data src0_msyms (ms_mem ms1) buf (firstn (Z.to_nat len) data) ->
crealizes src0_msyms (mkCfg ms1 md) (tset (TREE fuel cap bufp A) K)).
2:{ destruct S_W_facts as (HpcW & H12a & H12b & HpcA & HpcB & HmA & HmB).
destruct (Z_lt_dec (cap - len) 65536) as [Hsmall | Hbig].
- sym_assume_with src0tbl_ok HS true.
{ rewrite branch_ltu_U, U_SLit.
match goal with |- (U E ?a <? _) = true => change (U E a) with (U E sv_want) end. rewrite HUw. apply Z.ltb_lt. change (zcanon 65536) with 65536. lia. }
cdrv_run_to_with src0tbl_ok HS RWPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E S_Wa msx) in HS end.
ccarry E S_Wa HS HF HMR HD Hin len Hfl.
lazymatch type of HS with st_ok _ _ _ ?msx =>
apply (CONT (cap - len) msx ltac:(lia) ltac:(lia)); [| exact HMR | exact HD] end.
apply (REABS (cap - len) _ S_Wa HS reabs_Wa HmA HpcA); [| lia].
change (sr_get (ss_regs S_Wa) (R 12)) with sv_want. rewrite (denot_lit_U E sv_want), HUw. reflexivity.
- sym_assume_with src0tbl_ok HS false.
{ rewrite branch_ltu_U, U_SLit.
match goal with |- (U E ?a <? _) = false => change (U E a) with (U E sv_want) end. rewrite HUw. apply Z.ltb_ge. change (zcanon 65536) with 65536. lia. }
cdrv_run_to_with src0tbl_ok HS RWPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E S_Wb msx) in HS end.
ccarry E S_Wb HS HF HMR HD Hin len Hfl.
lazymatch type of HS with st_ok _ _ _ ?msx =>
apply (CONT 65536 msx ltac:(lia) ltac:(lia)); [| exact HMR | exact HD] end.
apply (REABS 65536 _ S_Wb HS reabs_Wb HmB HpcB); [| lia].
change (sr_get (ss_regs S_Wb) (R 12)) with (SLit 65536). reflexivity. }
clear HS HMR HD ms.
intros w ms Hw Hwc HS HMR HD.
set (E1 := ewset E 46 (Z_to_bv 64 w)) in HS.
assert (HX1 : ext29 (E_lp J buf g len cap) E1) by (unfold E1; apply ext29_ewset; [lia | exact HX]).
assert (E46 : bv_unsigned (ew E1 46) = w) by (unfold E1; rewrite ew_ewset_same; apply u64_of_Z; lia).
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall src0segs E1 S_RE msx) in HS end.
ccarry E1 S_RE HS HF HMR HD Hin len Hfl.
destruct S_RE_facts as (Hpc1 & H17 & H10 & H11 & H12 & Hrv1).
eapply (crz_read_win src0_msyms E1 S_RE _ md (Z_to_bv 64 3) path (Z_to_bv 64 len) data _ RS_LO w _ Hh Hlz HS Hrv1).
- rewrite H17. reflexivity.
- rewrite H10. reflexivity.
- reflexivity.
- exact (proj1 Hmd).
- rewrite (proj1 (proj2 (proj2 (proj2 Hmd)))). exact Hlk.
- rewrite H11. vm_compute. reflexivity.
- rewrite H12. change (bv_unsigned (sv_denot E1 (SOff A_WANT 0))) with (U E1 (SOff 46 0)). rewrite U_SOff, E46, Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
- reflexivity.
- exact S_RE_dest.
- exact read_stage_seg.
- unfold RS_LO, src0_D_read_stage. lia.
- unfold RS_LO, src0_D_read_stage. lia.
- cbn [ms_mem pend_at] in HMR, HD |- *.
intros regs Hregs HG Hmem Hbytes Hfr Hnle.
lazymatch type of Hfr with context [wbytes ?m0 _ _] => remember m0 as mem eqn:Hmem_def in *; clear Hmem_def end.
set (bs := file_read data (Z_to_bv 64 len) (sv_denot E1 (sr_get (ss_regs S_RE) 12%bv))) in *.
assert (Hnlen : Z.of_nat (length bs) = Z.min w (L - len)).
{ subst bs. rewrite file_read_length. rewrite (denot_lit_U E1 (sr_get (ss_regs S_RE) 12%bv)), H12.
change (U E1 (SOff A_WANT 0)) with (U E1 (SOff 46 0)). rewrite U_SOff, E46, Z.add_0_r, zcanon_id by (unfold M64; lia).
rewrite !u64_of_Z by lia. lia. }
assert (Hbs : bs = firstn (Z.to_nat w) (skipn (Z.to_nat len) data)).
{ subst bs. rewrite file_read_unguarded. unfold word_to_nat. rewrite (denot_lit_U E1 (sr_get (ss_regs S_RE) 12%bv)), H12.
change (U E1 (SOff A_WANT 0)) with (U E1 (SOff 46 0)). rewrite U_SOff, E46, Z.add_0_r, zcanon_id by (unfold M64; lia).
rewrite !u64_of_Z by lia. reflexivity. }
pose proof (MR_win Lc A mem _ md RS_LO bs HMR ltac:(lia) ltac:(lia) Hfr eq_refl) as HMR1.
pose proof (blk_data_win Lc A mem _ md bufp cap RS_LO bs buf (firstn (Z.to_nat len) data) HMR Hin ltac:(lia) ltac:(rewrite (Hfl len); lia)
ltac:(lia) ltac:(lia) Hfr HD) as HD1.
clear HMR HD.
remember (Z.of_nat (length bs)) as n eqn:Hndef.
destruct (Z.eq_dec n 0) as [Hn0 | Hnpos].
+
assert (HLlen : len = L) by lia.
assert (Ebs : bs = []) by (destruct bs; [reflexivity | cbn in Hndef; lia]). rewrite Ebs in *. cbn [wbytes] in *.
assert (HS1 : st_ok src0segs E1 (resume S_RE (SLit 0) (ss_mem S_RE) (ss_facts S_RE))
(mkst (regupd regs 10%bv (len_word (@nil byte))) (v_addi (Z_to_bv 64 (ss_pc S_RE)) 4) mem (seg_rom src0segs))).
{ apply (st_ok_resume_sv src0segs E1 S_RE regs mem (SLit 0)); [exact Hregs | exact Hmem | exact HG | reflexivity]. }
clear Hregs HG Hmem HS. rename HS1 into HS.
match goal with |- crealizes _ (mkCfg _ ?M) _ =>
assert (Hmd1 : md_loop M len) by (apply (md_loop_read md len len); [exact Hmd | f_equal; rewrite bv_off_add by (cbn; lia); cbn; rewrite Z.add_0_r; reflexivity]);
assert (Hh1 : m_halted M = None) by (autorewrite with model; exact Hh);
assert (Hlz1 : m_vm_lazy M = []) by (autorewrite with model; exact Hlz) end.
apply (MR_with_fds src0_msyms (aa_MR API) (aa_laws API)) with (f := fd_insert (m_fds md) (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 len + len_word (@nil byte))%bv)) in HMR1.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok_ecall _ _ _ ?msx => change (st_ok_ecall src0segs E1 S_CL msx) in HS end.
ccarry E1 S_CL HS HF HMR1 HD1 Hin len Hfl.
destruct S_CL_facts as (Hpc3 & H17c & H10c & Hrv3).
sym_ecall_open HS. cbn [ms_mem pend_at] in HMR1, HD1.
eapply (crz_close src0_msyms regs0 _ mem0 (seg_rom src0segs) _ (Z_to_bv 64 3));
[exact Hh1 | exact Hlz1
| rewrite (Hregs 17%bv), H17c; reflexivity | rewrite (Hregs 10%bv), H10c; reflexivity | reflexivity
| exact (proj1 Hmd1) |].
cresume_sv src0segs (SLit 0). { reflexivity. }
change (resume _ _ _ _) with S_HDR in HS.
destruct fuel as [|f]; [lia|].
unfold YL0l.TREE in HJt, HGt, HLt |- *. rewrite (bind_ext1 _ (ret (RdLoaded bufp cap)) (driver_tail data) A) in HJt, HGt, HLt |- * by (apply read_phase_loaded_eq; apply Z.ltb_lt; lia).
rewrite bind_ret_l in HJt, HGt, HLt |- *.
unfold E1 in HS. subst buf.
pose proof HRES as (b & Kb & c & HR & HRP & HK1 & Hc0 & Hcf).
eapply (HPOST cap bufp A Lc J g len w _ _ ltac:(lia) ltac:(unfold MAX_INPUT; lia) ltac:(lia) Hub HW HB Hid
HDI (ex_intro _ b (conj HR (rp_exit b Kb c cap (S f) HRP HK1 Hc0 Hcf))) HS Hw HLlen).
* exact (MR_with_fds src0_msyms (aa_MR API) (aa_laws API) _ _ _ _ _ HMR1).
* apply (md_loop_close _ len). exact Hmd1.
* rewrite HLlen in HD1. rewrite firstn_all2 in HD1 by lia. exact HD1.
* exact HJt.
* exact HGt.
* exact HLt.
+
assert (Hnp : 1 <= n <= w) by lia.
assert (HnL : len + n <= L /\ len + n <= cap) by lia.
assert (HS1 : st_ok src0segs (ewset E1 47 (len_word bs))
(resume S_RE (SOff 47 0) (ss_mem S_RE) (mkFacts ((47%nat, fact_n) :: f_atoms (ss_facts S_RE)) (f_conds (ss_facts S_RE)) (f_alias (ss_facts S_RE))))
(mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc S_RE)) 4) (wbytes mem (Z_to_bv 64 RS_LO) bs) (seg_rom src0segs))).
{ apply (st_ok_resume_atom src0segs 47 fact_n E1 S_RE regs _ (len_word bs) Hregs).
- exact Hmem.
- exact HG.
- exact (proj1 (proj2 (proj2 S_RDc_pd))).
- unfold fact_n, len_word; cbn [af_lo af_hi]. rewrite u64_of_Z by lia. lia.
- cbn. lia.
- unfold len_word. cbn [af_al2 fact_n]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
clear Hregs HG Hmem HS. rename HS1 into HS.
set (E2 := ewset E1 47 (len_word bs)) in HS.
assert (HX2 : ext29 (E_lp J buf g len cap) E2) by (unfold E2; apply ext29_ewset; [lia | exact HX1]).
assert (HmemW : mem_ok src0segs E2 (wbytes mem (Z_to_bv 64 RS_LO) bs) (ss_mem S_RE)) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _); exact HM).
assert (E47 : bv_unsigned (ew E2 47) = n) by (unfold E2; rewrite ew_ewset_same; unfold len_word; rewrite u64_of_Z by lia; lia).
match goal with |- crealizes _ (mkCfg _ ?M) _ =>
assert (Hmd1 : md_loop M (len + n)) by (apply (md_loop_read md len (len + n)); [exact Hmd | f_equal; rewrite Hndef; apply bv_off_add; lia]);
assert (Hh1 : m_halted M = None) by (autorewrite with model; exact Hh);
assert (Hlz1 : m_vm_lazy M = []) by (autorewrite with model; exact Hlz);
apply (MR_with_fds src0_msyms (aa_MR API) (aa_laws API)) with (f := m_fds M) in HMR1; cbn [m_fds with_fds] in HMR1 || idtac end.
match goal with |- crealizes _ (mkCfg _ ?M) _ => change (aa_MR API Lc A (wbytes mem (Z_to_bv 64 RS_LO) bs) M) in HMR1 || idtac end.
cdrv_run_to_with src0tbl_ok HS src0_A_memcpy HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E2 S_CP msx) in HS end.
lazymatch type of HF with frame_of _ ?rs0 ?m0 ?m1 =>
assert (Hwin : forall i, 0 <= i < n -> mbyte src0segs m1 (RS_LO + i) = nth_error bs (Z.to_nat i));
[ intros i Hi; rewrite <- (Hbytes i ltac:(lia));
apply (mbyte_win_after_frame src0segs E2 m0 m1 rs0 RS_LO 65536 HmemW S_RE_dest HF); unfold RS_LO, src0_D_read_stage in *; lia | ] end.
ccarry E2 S_CP HS HF HMR1 HD1 Hin len Hfl.
destruct S_CP_facts as (HpcC & HraC & H10C & H11C & H12C & HrvC & HmC).
lazymatch type of HS with st_ok _ _ _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS) as Hr11; pose proof (st_ok_reg src0segs _ _ _ 12%bv HS) as Hr12;
rewrite H10C in Hr10; rewrite H11C in Hr11; rewrite H12C in Hr12;
eapply (src0_memcpy_from_abs_cf API AX E2 S_CP msx _ Lc A bufp cap (buf + len) RS_LO n bs A_BUF K_CP RA_CP _ HS ltac:(drv_anch) ltac:(vm_compute; reflexivity) HMR1 Hin);
[ change A_BUF with 14%nat; rewrite (Ec14 J buf g len cap E2 HX2 Hbufr); exact Hbuf
| rewrite Hr10, (denot_lit_U E2), (U_dst J buf g len cap E2 HX2 Hbufr Hlenr Hcapr); reflexivity
| lia | lia
| rewrite Hr11; reflexivity
| unfold RS_LO, src0_D_read_stage; lia
| unfold RS_LO, src0_D_read_stage; lia
| intros i Hi; apply read_stage_img; lia
| exact Hwin
| lia
| rewrite Hr12, (denot_lit_U E2); change (U E2 (SOff A_N 0)) with (U E2 (SOff 47 0)); rewrite U_SOff, E47, Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity
| lia
| clear Hr10 Hr11 Hr12 ] end.
intros mq3 HS3 HMR3 Hout3 Hbd3.
assert (HD3 : blk_data src0_msyms (ms_mem mq3) buf (firstn (Z.to_nat (len + n)) data)).
{ intros i Hi. change (ms_segs src0_msyms) with src0segs. rewrite firstn_length_le in Hi by lia.
destruct (Z_lt_dec i len) as [Hlt | Hge].
- rewrite (nth_error_firstn (Z.to_nat (len + n)) data). destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) (Z.to_nat (len + n))); [|lia].
transitivity (nth_error (firstn (Z.to_nat len) data) (Z.to_nat i)).
+ rewrite <- (HD1 i) by (rewrite firstn_length_le; lia). unfold mbyte. rewrite Hout3 by lia. reflexivity.
+ rewrite (nth_error_firstn (Z.to_nat len) data). destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) (Z.to_nat len)); [reflexivity | lia].
- replace (buf + i) with (buf + len + (i - len)) by lia. rewrite (Hbd3 (i - len)) by lia.
rewrite Hbs. rewrite (nth_error_firstn (Z.to_nat w)), nth_error_skipn, (nth_error_firstn _ data).
replace (Z.to_nat len + Z.to_nat (i - len))%nat with (Z.to_nat i) by lia.
destruct (PeanoNat.Nat.ltb_spec (Z.to_nat (i - len)) (Z.to_nat w)); destruct (PeanoNat.Nat.ltb_spec (Z.to_nat i) (Z.to_nat (len + n))); try reflexivity; try lia. }
clear HS HMR1 Hout3 Hbd3 HD1 Hwin.
lazymatch type of HS3 with st_ok _ ?Ec _ ?msx => set (E3 := Ec) in HS3; change (st_ok src0segs E3 S_CPp msx) in HS3 end.
assert (HX3 : ext29 (E_lp J buf g len cap) E3) by (unfold E3; apply ext29_havoc; [unfold K_CP; lia | exact HX2]).
assert (E47' : bv_unsigned (ew E3 47) = n) by (unfold E3; rewrite ew_havoc_old by (unfold K_CP; lia); exact E47).
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR3) as (Hh3 & Hlz3 & _).
rename mq3 into ms3. rename HS3 into HS. rename HMR3 into HMR. rename HD3 into HD.
match type of HMR with aa_MR _ _ _ _ ?M => rename Hmd1 into Hmd'; assert (Hmd1 : md_loop M (len + n)) by exact Hmd'; clear Hmd' end.
assert (Hch2' : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) _) by exact (proj1 (proj2 (proj2 Hmd1))).
pose proof (U_len1 J buf g len cap E3 HX3 Hbufr Hlenr Hcapr n ltac:(lia) E47') as HUl1.
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_T msx) in HS end.
ccarry E3 S_T HS HF HMR HD Hin (len + n) Hfl.
destruct (Z.eq_dec (len + n) cap) as [Heq | Hne].
*
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_eq_U. match goal with |- (U E3 ?a =? U E3 ?b) = true => change (U E3 a) with (U E3 sv_len1); change (U E3 b) with (U E3 (SOff 28 0)) end.
rewrite HUl1, U_SOff, (Ec28 J buf g len cap E3 HX3 Hbufr Hcapr), Z.add_0_r, zcanon_id by (unfold M64; lia). rewrite Heq. apply Z.eqb_refl. }
cdrv_run_with src0tbl_ok HS HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_G msx) in HS end.
ccarry E3 S_G HS HF HMR HD Hin (len + n) Hfl.
pose proof (U_big J buf g len cap E3 HX3 Hbufr Hlenr Hcapr n ltac:(lia) E47') as HUbig.
destruct fuel as [|f]; [lia|].
destruct (Z.eq_dec cap (2 ^ 26)) as [Hmax | Hnmax].
--
sym_assume_with src0tbl_ok HS true.
{ rewrite branch_ne_U, U_SLit. match goal with |- negb (U E3 ?a =? _) = true => change (U E3 a) with (U E3 sv_big) end.
rewrite HUbig, Heq, Hmax. reflexivity. }
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_RF msx) in HS end.
unfold YL0l.TREE. rewrite (bind_ext1 _ (ret RdRefused) (driver_tail data) A) by (apply read_phase_refused_eq; [apply Z.ltb_ge; lia | apply Z.leb_le; unfold MAX_INPUT; lia]).
rewrite bind_ret_l. change (tset (driver_tail data RdRefused A) K) with (K (DL_refused, A)).
apply (crz_conseq _ _ (diag msg_refused (in_fs inp)) _); [| apply t_eq_sym; apply HK].
unfold diag, wr, ex. rewrite <- (proj1 (proj2 (proj2 (proj2 Hmd1)))).
lazymatch type of HS with st_ok _ _ _ ?msx =>
exact (crealizes_diag_exit_by_run E3 S_RF msx _ (Z_to_bv 64 2) K_MG msg_refused 2 2 HS Hh3 Hlz3 ltac:(lia) refused_check Hch2') end.
--
assert (Hf1 : (1 <= f)%nat).
{ destruct f; [| lia]. exfalso. apply Hnmax. rewrite Hcap. reflexivity. }
assert (Hcap2 : 2 * cap = 2 ^ (27 - Z.of_nat f)).
{ rewrite Hcap. replace (27 - Z.of_nat f) with (Z.succ (27 - Z.of_nat (S f))) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
assert (H2cap : 2 * cap <= 2 ^ 26) by (rewrite Hcap2; apply Z.pow_le_mono_r; lia).
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_ne_U, U_SLit. match goal with |- negb (U E3 ?a =? _) = false => change (U E3 a) with (U E3 sv_big) end.
rewrite HUbig, Heq, Z.shiftr_div_pow2, Z.div_small by lia. reflexivity. }
cdrv_run_to_with src0tbl_ok HS src0_A_malloc HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_MG msx) in HS end.
ccarry E3 S_MG HS HF HMR HD Hin (len + n) Hfl.
unfold YL0l.TREE in HJt, HGt, HLt |- *.
rewrite (bind_ext1 _ _ (driver_tail data) A (read_phase_grow_eq f L cap bufp ltac:(apply Z.ltb_ge; lia) ltac:(apply Z.leb_gt; unfold MAX_INPUT; lia))) in HJt, HGt, HLt |- *.
apply jinv_bind_assoc in HJt. apply gtree_bind_assoc in HGt. apply leaves_bind_assoc in HLt.
apply (crz_conseq _ _ (tset (bind (malloc (2 * cap)) (fun p => bind (grow_k f L cap bufp p) (driver_tail data)) A) K)); [| apply t_eq_sym; apply tset_bind_assoc].
rewrite tset_mbind'.
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS) as Hr10.
rewrite (proj1 S_MG_facts) in Hr10.
rewrite (denot_lit_U E3), (U_dbl J buf g len cap E3 HX3 Hbufr Hlenr Hcapr n ltac:(lia) E47') in Hr10.
pose proof HRES as (b & Kb & c & HR & HRP & HK1 & Hc0 & Hcf).
destruct (rp_grow A b Kb c cap f HW HR HRP HK1 Hc0 Hcf Hcap Hf1 ltac:(lia)) as (Hroomb & Hroom & Hlive1 & HRP' & HK1').
lazymatch type of HS with st_ok _ _ _ ?msx =>
eapply (malloc_site_cf src0_msyms API AX (MRC _) LIMLAW E3 S_MG msx _ Lc A (2 * cap) MAIN_SP src0_keep [] K_MG L_MG RS_MG RA_MG _ HS ltac:(drv_anch) site_MG statics_MG HMR HW HB);
[ intros Hf'; rewrite Hid in Hf'; discriminate
| rewrite Hr10, Heq; reflexivity
| lia
| intros kb sz [ ]
| exact (jinv_mbind_head _ _ _ _ HJt)
| exact (gtree_mbind_head _ _ _ _ HGt)
| exact Hroom
| ] end.
intros res A2 L2 mq2 md2 g2 tr HS2 HSA2 HMR2 HW2 HB2 [vm2 Hmd2] Hpath Hstab Hhi Hbk Hres.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR2) as (Hh2 & Hlz2 & _).
assert (Hid2 : st_init_done A2 = true) by (exact (malloc_keeps_init_done _ _ _ _ _ Hid (cpath_yields _ _ _ Hpath))).
pose proof (leaves_cpath _ _ _ _ (malloc_leaves_res A b (2 * cap) HW HR Hroomb) Hpath) as [_ HR2]. cbn [snd] in HR2.
pose proof (DI_malloc A (2 * cap) tr res A2 HDI ltac:(lia) (cpath_yields _ _ _ Hpath)) as HDI2.
assert (Hmdl2 : md_loop md2 (len + n)) by (subst md2; apply md_loop_vm; exact Hmd1).
assert (Hch2'' : fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) md2) by exact (proj1 (proj2 (proj2 Hmdl2))).
destruct (Hstab _ _ Hin) as [Hin2 Hpb2]. rewrite <- Hbuf in Hpb2.
assert (HD2 : blk_data src0_msyms (ms_mem mq2) buf (firstn (Z.to_nat (len + n)) data)).
{ eapply (blk_data_kept src0_msyms); [| exact HD]. intros i Hi. rewrite Hbuf. apply (Hbk bufp cap i Hin). rewrite (Hfl (len + n)) in Hi by lia. lia. }
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs (post_env E3 K_MG (ms_regs mq2) g2) S_MGp msx) in HS2 end.
set (E4 := post_env E3 K_MG (ms_regs mq2) g2) in HS2, HSA2.
assert (HX4 : ext29 (E_lp J buf g len cap) E4) by (unfold E4; apply ext29_post; [unfold K_MG; lia | exact HX3]).
assert (E47'' : bv_unsigned (ew E4 47) = n) by (unfold E4; rewrite (proj1 (post_env_agree E3 K_MG _ _)) by (unfold K_MG; lia); exact E47').
pose proof (jinv_mbind_after K _ _ A tr res A2 HJt Hpath) as HJ2. pose proof (gtree_mbind_after mgrant _ _ A tr res A2 HGt Hpath) as HG2. pose proof (leaves_mbind_after PRES _ _ A tr res A2 HLt Hpath) as HL2.
clear HS HMR Hhi Hr10 HJt HGt HLt. cbn beta iota. cbn beta in HJ2, HG2, HL2.
destruct res as [nb|].
++
destruct Hres as (Hq0 & Hqnz & b1 & b2 & HubA2 & HubA).
assert (Hinb : In (nb, 2 * cap) (user_blocks A2)) by (rewrite HubA2; apply in_app_iff; right; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) L2 A2 (ms_mem mq2) md2 nb (2 * cap) 0 HMR2 Hinb ltac:(lia)) as (_ & Hn1 & Hn2 & _).
pose proof (mr_blocks_aligned _ _ (aa_laws API) L2 A2 (ms_mem mq2) md2 nb _ HMR2 Hinb) as Hnal.
assert (Hnbp : nb <> bufp).
{ intros ->. pose proof (blocks_same_ptr _ _ (aa_laws API) _ _ _ _ _ _ _ _ HMR2 Hinb Hin2 ltac:(lia) ltac:(lia) eq_refl). lia. }
unfold grow_k in HJ2, HG2, HL2 |- *.
apply jinv_bind_assoc in HJ2. apply gtree_bind_assoc in HG2. apply leaves_bind_assoc in HL2.
apply (crz_conseq _ _ (tset (bind (free (Some bufp)) (fun u => bind ((fun _ : unit => read_phase f L (2 * cap) nb) u) (driver_tail data)) A2) K)); [| apply t_eq_sym; apply tset_bind_assoc].
rewrite tset_mbind'.
assert (H63 : bv_unsigned (ew E4 63) = ptr_addr L2 nb).
{ unfold E4. change 63%nat with (K_MG + 4)%nat. rewrite post_env_a0, Hq0. apply u64_of_Z. lia. }
apply (st_ok_add_fact src0segs _ S_MGp mq2 A_NB blkq_fact) in HS2.
2:{ unfold afact_ok, blkq_fact. cbn [af_lo af_hi af_al2]. change A_NB with 63%nat. rewrite H63. change (2 ^ 4) with 16.
pose proof YM05.alloc_ceiling_val. lia. }
cdrv_run_to_with src0tbl_ok HS2 src0_A_memcpy HF.
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs E4 S_MC msx) in HS2 end.
ccarry E4 S_MC HS2 HF HMR2 HD2 Hin2 (len + n) Hfl.
lazymatch type of HS2 with st_ok _ _ _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS2) as Hr10; pose proof (st_ok_reg src0segs _ _ _ 11%bv HS2) as Hr11; pose proof (st_ok_reg src0segs _ _ _ 12%bv HS2) as Hr12;
rewrite (proj1 S_MC_facts) in Hr10; rewrite (proj1 (proj2 S_MC_facts)) in Hr11; rewrite (proj2 (proj2 S_MC_facts)) in Hr12;
eapply (src0_memcpy_site_cf API AX E4 S_MC msx md2 L2 A2 nb (2 * cap) (len + n) bufp cap buf A_NB K_MC RA_MC1 _ HS2 ltac:(drv_anch) ck_MC HMR2 Hinb Hin2 Hnbp);
[ rewrite Hr10; cbn [sv_denot]; rewrite Z.add_0_r; change A_NB with 63%nat; rewrite <- H63, Z_to_bv_bv_unsigned; reflexivity
| rewrite Hr11, (denot_lit_U E4), U_SOff; change A_BUF with 14%nat; rewrite (Ec14 J buf g len cap E4 HX4 Hbufr), Z.add_0_r, zcanon_id by (unfold M64; lia); reflexivity
| rewrite Hpb2; lia
| rewrite Hpb2; lia
| rewrite Hr12, (denot_lit_U E4), (U_len1 J buf g len cap E4 HX4 Hbufr Hlenr Hcapr n ltac:(lia) E47''); reflexivity
| lia | lia
| clear Hr10 Hr11 Hr12 ] end.
intros mq5 HS5 HMR5 Hout5 Hbd5.
assert (HD5 : blk_data src0_msyms (ms_mem mq5) (ptr_addr L2 nb) (firstn (Z.to_nat (len + n)) data)) by (apply Hbd5; [exact HD2 | rewrite (Hfl (len + n)); lia]).
clear HS2 HMR2 Hout5 Hbd5 HD2.
lazymatch type of HS5 with st_ok _ ?Ec _ ?msx => set (E5 := Ec) in HS5; change (st_ok src0segs E5 S_MCp msx) in HS5 end.
assert (HX5 : ext29 (E_lp J buf g len cap) E5) by (unfold E5; apply ext29_havoc; [unfold K_MC; lia | exact HX4]).
assert (H63' : bv_unsigned (ew E5 63) = ptr_addr L2 nb) by (unfold E5; rewrite ew_havoc_old by (unfold K_MC; lia); exact H63).
assert (E47_5 : bv_unsigned (ew E5 47) = n) by (unfold E5; rewrite ew_havoc_old by (unfold K_MC; lia); exact E47'').
cdrv_run_to_with src0tbl_ok HS5 src0_A_free HF.
lazymatch type of HS5 with st_ok _ _ _ ?msx => change (st_ok src0segs E5 S_FR msx) in HS5 end.
ccarry E5 S_FR HS5 HF HMR5 HD5 Hinb (len + n) Hfl.
pose proof (roomcf_free_res A2 (rb_malloc b (2 * cap)) bufp cap SRC_LIM_MIN HW2 Hin2 HR2 Hlive1) as Hroomf.
lazymatch type of HS5 with st_ok _ _ _ ?msx =>
pose proof (st_ok_reg src0segs _ _ _ 10%bv HS5) as Hr10; rewrite S_FR_facts in Hr10;
eapply (free_site_tset_cf src0_msyms API AX (FRC _) LIMLAW E5 S_FR msx md2 L2 A2 bufp cap MAIN_SP src0_keep [] K_FR L_FR RS_FR RA_FR _
HS5 ltac:(drv_anch) site_FR statics_FR HMR5 HW2 HB2 Hid2 Hin2);
[ rewrite Hr10, (denot_lit_U E5), U_SOff; change A_BUF with 14%nat; rewrite (Ec14 J buf g len cap E5 HX5 Hbufr), Z.add_0_r, zcanon_id by (unfold M64; lia); rewrite Hpb2; reflexivity
| intros kb sz [ ]
| exact (jinv_mbind_head _ _ _ _ HJ2)
| exact (gtree_mbind_head _ _ _ _ HG2)
| exact Hroomf
| clear Hr10 ] end.
intros A3 L3 mq6 md6 g6 tr6 HS6 HSA6 HMR6 HW6 HB6 [vm6 Hmd6] Hpath6 (l1 & l2 & HubA2' & HubA3) Hstab6 Hhi6 Hbk6.
cbn beta iota. change (bind (read_phase f L (2 * cap) nb) (driver_tail data) A3) with (TREE f (2 * cap) nb A3).
pose proof (jinv_mbind_after K _ _ A2 tr6 tt A3 HJ2 Hpath6) as HJ3. pose proof (gtree_mbind_after mgrant _ _ A2 tr6 tt A3 HG2 Hpath6) as HG3. pose proof (leaves_mbind_after PRES _ _ A2 tr6 tt A3 HL2 Hpath6) as HL3.
cbn beta in HJ3, HG3, HL3. change (bind (read_phase f L (2 * cap) nb) (driver_tail data) A3) with (TREE f (2 * cap) nb A3) in HJ3, HG3, HL3.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR6) as (Hh6 & Hlz6 & _).
assert (Hub3 : user_blocks A3 = [(nb, 2 * cap)]).
{ apply (blocks_after_grow b1 b2 l1 l2 bufp nb cap (user_blocks A2)); [exact HubA2 | rewrite <- Hub; exact HubA | exact HubA2' | exact HubA3 | lia]. }
destruct (Hstab6 nb (2 * cap) Hinb Hnbp) as [Hinb3 Hpnb3].
assert (Hid3 : st_init_done A3 = true) by (exact (free_keeps_init_done _ _ _ _ _ Hid2 (cpath_yields _ _ _ Hpath6))).
pose proof (leaves_cpath _ _ _ _ (free_leaves_res A2 _ bufp cap HW2 Hin2 HR2) Hpath6) as [_ HR3]. cbn [snd] in HR3.
pose proof (DI_free A2 bufp cap tr6 A3 HDI2 Hin2 (cpath_yields _ _ _ Hpath6)) as HDI3.
assert (Hmdl6 : md_loop md6 (len + n)) by (subst md6; apply md_loop_vm; exact Hmdl2).
assert (HD6 : blk_data src0_msyms (ms_mem mq6) (ptr_addr L2 nb) (firstn (Z.to_nat (len + n)) data)).
{ eapply (blk_data_kept src0_msyms); [| exact HD5]. intros i Hi. apply (Hbk6 nb (2 * cap) i Hinb Hnbp). rewrite (Hfl (len + n)) in Hi by lia. lia. }
clear HS5 HMR5 Hhi6 Hbk6 HD5.
lazymatch type of HS6 with st_ok _ ?Ec _ ?msx => set (E6 := Ec) in HS6, HSA6; change (st_ok src0segs E6 S_RD' msx) in HS6 end.
assert (HX6 : ext29 (E_lp J buf g len cap) E6) by (unfold E6; apply ext29_post; [unfold K_FR; lia | exact HX5]).
assert (H63'' : bv_unsigned (ew E6 63) = ptr_addr L2 nb) by (unfold E6; rewrite (proj1 (post_env_agree E5 K_FR _ _)) by (unfold K_FR; lia); exact H63').
assert (E47_6 : bv_unsigned (ew E6 47) = n) by (unfold E6; rewrite (proj1 (post_env_agree E5 K_FR _ _)) by (unfold K_FR; lia); exact E47_5).
lazymatch type of HS6 with st_ok _ _ _ ?msx =>
set (J' := map (getr (ms_regs msx)) Jregs);
assert (HSc : st_ok src0segs (E_lp J' (ptr_addr L3 nb) g (len + n) (2 * cap)) S_RDc msx);
[ unfold S_RDc; rewrite <- (proj1 S_RD'_facts);
apply (st_ok_reabs src0segs P_GR E6 (E_lp J' (ptr_addr L3 nb) g (len + n) (2 * cap)) S_RD' msx RD_regs (map snd LH_cut) RD_facts HS6) | ] end.
** apply (agree_to_lp P_GR J buf g len cap E6); [exact HX6|].
intros k Hk. unfold P_GR, P_junk in Hk. repeat (apply andb_prop in Hk as [Hk ?X]). apply Nat.ltb_lt in Hk.
destruct (Nat.eqb_spec k 14); [discriminate|]. destruct (Nat.eqb_spec k 26); [discriminate|]. destruct (Nat.eqb_spec k 27); [discriminate|]. destruct (Nat.eqb_spec k 28); [discriminate|].
repeat split; intros; lia || congruence.
** exact reabs_RD'.
** apply obl_RD.
+++ intros k r Hr Hk. apply (lp_junk Jregs); [reflexivity | exact Hr | exact Hk].
+++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 9) HS6). change (sr_get (ss_regs S_RD') (R 9)) with (SOff 63 0).
cbn [sv_denot]. rewrite Z.add_0_r. rewrite Hpnb3, <- H63'', Z_to_bv_bv_unsigned. reflexivity.
+++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 19) HS6). change (sr_get (ss_regs S_RD') (R 19)) with sv_len1.
rewrite (denot_lit_U E6), (U_len1 J buf g len cap E6 HX6 Hbufr Hlenr Hcapr n ltac:(lia) E47_6). reflexivity.
+++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 21) HS6).
change (sr_get (ss_regs S_RD') (R 21)) with (SAlu ALU_ADD (SAlu ALU_SLL (SOff A_LEN 0) (SLit 1)) (SAlu ALU_SLL (SOff A_N 0) (SLit 1))).
rewrite (denot_lit_U E6), (U_dbl J buf g len cap E6 HX6 Hbufr Hlenr Hcapr n ltac:(lia) E47_6), Heq. reflexivity.
** rewrite fobl_RD. constructor; [| constructor; [| constructor; [| constructor]]]; unfold afact_ok, fact_len, fact_cap; cbn [fst snd af_lo af_hi af_al2]; rewrite ew_lp; cbn [Nat.eqb Nat.ltb Nat.leb].
+++ rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
+++ rewrite u64_of_Z by lia. change (2 ^ 16) with 65536. split; [lia|]. split; [| lia].
replace (2 * cap) with (cap + cap) by lia. rewrite Z.add_mod, Hcm by lia. reflexivity.
+++ rewrite u64_of_Z by lia. rewrite Hpnb3. change (2 ^ 4) with 16. pose proof YM05.alloc_ceiling_val. repeat split; lia.
** destruct HS6 as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (mem_ok_relayout src0segs) with (l := back (map snd LH_cut)) in HM; [| exact relayout_RD']. rewrite back_cut in HM.
eapply (mem_ok_agree_pd src0segs P_GR PT E6); [| exact (proj1 LH_mem_atoms) | exact HM].
apply (agree_to_lp P_GR J buf g len cap E6); [exact HX6|].
intros k Hk. unfold P_GR, P_junk in Hk. repeat (apply andb_prop in Hk as [Hk ?X]). apply Nat.ltb_lt in Hk.
destruct (Nat.eqb_spec k 14); [discriminate|]. destruct (Nat.eqb_spec k 26); [discriminate|]. destruct (Nat.eqb_spec k 27); [discriminate|]. destruct (Nat.eqb_spec k 28); [discriminate|].
repeat split; intros; lia || congruence.
**
pose proof LH_statics as Hadd. unfold drv_add_statics in Hadd.
destruct (abs_region_index (map snd LH_cut) (ms_got_guard src0_msyms) 0) as [i1|]; [|discriminate].
destruct (abs_region_index (map snd LH_cut) (ms_libc src0_msyms + 3) 0) as [i2|]; [|discriminate].
destruct (abs_region_index (map snd LH_cut) (ms_guard src0_msyms) 0) as [i3|]; [|discriminate].
lazymatch type of HSc with st_ok _ _ _ ?msx =>
destruct (st_ok_statics_pd src0_msyms (aa_MR API) AX _ S_RDc msx L3 A3 md6 G_M1 i1 i2 i3 LH_mem HSc HMR6 (proj1 S_RDc_pd) Hadd) as (g' & Hg' & HS7);
change (st_ok src0segs (ewset (E_lp J' (ptr_addr L3 nb) g (len + n) (2 * cap)) 26 (Z_to_bv 64 g')) S_RD msx) in HS7;
assert (HS8 : st_ok src0segs (E_lp J' (ptr_addr L3 nb) g' (len + n) (2 * cap)) S_RD msx);
[ apply (st_ok_agree_pd src0segs PT PT _ _ S_RD msx HS7); [| exact (proj1 (proj2 S_RDc_pd))];
split; [| intros; reflexivity]; intros k _;
destruct (Nat.eqb_spec k 26) as [->|Hk26]; [rewrite ew_lp, ew_ewset_same; reflexivity|];
rewrite (ew_ewset_other _ _ _ _ Hk26), !ew_lp, (proj2 (Nat.eqb_neq _ _) Hk26); reflexivity | ] end.
clear HSc HS7 HS6.
assert (HRES3 : exists b Kb c, res_ok A3 b /\ RPinv Kb c (2 * cap) b /\ Kb + capflag (2 * cap) <= 2 ^ 24 /\ 0 <= c /\ c + Z.of_nat f <= 12).
{ exists (rb_free (rb_malloc b (2 * cap)) cap), (Kb + capflag cap), (c + 1).
refine (conj HR3 (conj HRP' (conj HK1' (conj _ _)))); lia. }
lazymatch type of HS8 with st_ok _ _ _ ?msx =>
refine (IHN f (2 * cap) nb (len + n) A3 L3 J' g' msx md6 K ltac:(lia) Hcap2 ltac:(lia) ltac:(lia) ltac:(lia) Hub3 HW6 HB6 Hid3
HDI3 HRES3 HS8 HMR6 Hmdl6 _ HJ3 HG3 HL3 HK HPOST);
rewrite Hpnb3; exact HD6 end.
++
destruct Hres as [Hq0 HubA2].
unfold grow_k. rewrite bind_ret_l. change (tset (driver_tail data RdOOM A2) K) with (K (DL_oom, A2)).
apply (crz_conseq _ _ (diag msg_oom (in_fs inp)) _); [| apply t_eq_sym; apply HK].
apply (st_ok_regs src0segs _ _ mq2 (sr_set (ss_regs S_MGp) 10%bv (SLit 0))) in HS2.
2:{ intros r. destruct (decide (r = 10%bv)) as [->|Hne'].
- rewrite sr_get_set_same by reflexivity. rewrite (proj2 S_MG_facts).
cbn [sv_denot]. rewrite Z.add_0_r. unfold E4. change A_NB with (K_MG + 4)%nat. rewrite post_env_a0, Hq0. reflexivity.
- rewrite sr_get_set_other by exact Hne'. reflexivity. }
lazymatch type of HS2 with st_ok _ _ _ ?msx => change (st_ok src0segs E4 S_MGn msx) in HS2 end.
unfold diag, wr, ex. rewrite <- (proj1 (proj2 (proj2 (proj2 Hmdl2)))).
lazymatch type of HS2 with st_ok _ _ _ ?msx =>
exact (crealizes_diag_exit_by_run E4 S_MGn msx md2 (Z_to_bv 64 2) K_MC msg_oom 2 2 HS2 Hh2 Hlz2 ltac:(lia) oom_check Hch2'') end.
*
sym_assume_with src0tbl_ok HS false.
{ rewrite branch_eq_U. match goal with |- (U E3 ?a =? U E3 ?b) = false => change (U E3 a) with (U E3 sv_len1); change (U E3 b) with (U E3 (SOff 28 0)) end.
rewrite HUl1, U_SOff, (Ec28 J buf g len cap E3 HX3 Hbufr Hcapr), Z.add_0_r, zcanon_id by (unfold M64; lia). apply Z.eqb_neq. exact Hne. }
cdrv_run_to_with src0tbl_ok HS RDPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E3 S_RDn msx) in HS end.
ccarry E3 S_RDn HS HF HMR HD Hin (len + n) Hfl.
lazymatch type of HS with st_ok _ _ _ ?msx =>
set (J' := map (getr (ms_regs msx)) Jregs);
assert (HS' : st_ok src0segs (E_lp J' buf g (len + n) cap) S_RD msx);
[ unfold S_RD; rewrite <- (proj1 S_RDn_facts);
apply (st_ok_reabs src0segs P_RDLH E3 (E_lp J' buf g (len + n) cap) S_RDn msx RD_regs LH_mem RD_facts HS) | ] end.
-- apply (agree_to_lp P_RDLH J buf g len cap E3); [exact HX3|].
intros k Hk. unfold P_RDLH, P_junk in Hk. apply andb_prop in Hk as [Hk1 Hk2]. apply Nat.ltb_lt in Hk1.
destruct (Nat.eqb_spec k 27); [discriminate|]. repeat split; intros; lia || congruence.
-- exact reabs_RDn.
-- apply obl_RDn.
++ intros k r Hr Hk. apply (lp_junk Jregs); [reflexivity | exact Hr | exact Hk].
++ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 19) HS). change (sr_get (ss_regs S_RDn) (R 19)) with sv_len1.
rewrite (denot_lit_U E3), HUl1. reflexivity.
-- rewrite fobl_RDn. constructor; [| constructor]. unfold afact_ok, fact_len. cbn [fst snd af_lo af_hi af_al2].
rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
-- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (mem_ok_relayout src0segs) with (l := back LH_mem) in HM; [| exact relayout_RDn]. rewrite back_LH_mem in HM.
eapply (mem_ok_agree_pd src0segs P_RDLH PT E3); [| exact (proj1 (proj2 (proj2 (proj2 LH_mem_atoms)))) | exact HM].
apply (agree_to_lp P_RDLH J buf g len cap E3); [exact HX3|].
intros k Hk. unfold P_RDLH, P_junk in Hk. apply andb_prop in Hk as [Hk1 Hk2]. apply Nat.ltb_lt in Hk1.
destruct (Nat.eqb_spec k 27); [discriminate|]. repeat split; intros; lia || congruence.
-- clear HS. subst E. subst buf.
lazymatch type of HS' with st_ok _ _ _ ?msx =>
apply (IHN fuel cap bufp (len + n) A Lc J' g msx _ K ltac:(lia) Hcap Hfuel ltac:(lia) ltac:(lia) Hub HW HB Hid HDI HRES HS' HMR Hmd1 HD HJt HGt HLt HK HPOST) end.
Qed.
Theorem src0_read_loop_cf : forall (brk mbase : word) (lim : Z) regs' g ms md Lc A bufp vm (K : dleaf * astate -> TSet),
st_ok src0segs (E_m1 sp tid [a0; path] (in_envp inp) rnd regs' g) ss_m1_post ms ->
getr regs' 10%bv = Z_to_bv 64 (ptr_addr Lc bufp) ->
aa_MR API Lc A (ms_mem ms) md -> WF A -> bounded A -> st_init_done A = true ->
DI A -> res_ok A (rb_malloc (RB 0 0 0 0) CAP0) ->
user_blocks A = [(bufp, CAP0)] ->
md = with_vmmaps vm (MD_file path tid brk mbase sp lim inp) ->
jinv K (TREE READ_FUEL CAP0 bufp A) -> gtree mgrant (TREE READ_FUEL CAP0 bufp A) -> leaves PRES (TREE READ_FUEL CAP0 bufp A) ->
(forall r, t_eq (K r) (leaf_shapeX data (in_fs inp) r)) ->
POST_cf K ->
crealizes src0_msyms (mkCfg ms md) (tset (TREE READ_FUEL CAP0 bufp A) K).
Proof using AX MRC FRC LIMLAW Hlk HSA0.
intros brk mbase lim regs' g ms md Lc A bufp vm K HS Ha0 HMR HW HB Hid HDI HR0 Hub Hmd HJ HG HL HK HPOST.
destruct (mr_model _ _ (aa_laws API) _ _ _ _ HMR) as (Hh & Hlz & _).
assert (Hin : In (bufp, CAP0) (user_blocks A)) by (rewrite Hub; left; reflexivity).
pose proof (mr_blocks _ _ (aa_laws API) Lc A (ms_mem ms) md bufp CAP0 0 HMR Hin ltac:(unfold CAP0; lia)) as (_ & Hq1 & Hq2 & _).
pose proof (mr_blocks_aligned _ _ (aa_laws API) Lc A (ms_mem ms) md bufp CAP0 HMR Hin) as Hqal.
unfold CAP0 in Hq2. assert (Hac : alloc_ceiling < 2 ^ 47) by (pose proof YM05.alloc_ceiling_val; lia).
set (E0 := E_m1 sp tid [a0; path] (in_envp inp) rnd regs' g) in HS.
assert (E14 : ew E0 14 = Z_to_bv 64 (ptr_addr Lc bufp)).
{ unfold E0, E_m1. change 14%nat with (K_M1 + 4)%nat. rewrite post_env_a0. exact Ha0. }
assert (HSAE0 : forall G, anchored_atoms G = anchored_atoms RD_facts -> stack_anchored E0 G).
{ intros G HGa. apply (stack_anchored_ext (E_main sp [a0; path] (in_envp inp) tid rnd) E0 RD_facts G (HSA0 RD_facts eq_refl) HGa).
intros [n K0] Hn. cbn [fst].
match type of Hn with In _ ?l => let v := eval vm_compute in l in change l with v in Hn end.
assert (Hn10 : (n < 10)%nat).
{ cbn in Hn. repeat (destruct Hn as [Hn|Hn]; [injection Hn as <- <-; lia |]). destruct Hn. }
unfold E0, E_m1. apply (proj1 (post_env_agree _ K_M1 _ _)). unfold K_M1. lia. }
apply (st_ok_add_fact src0segs E0 ss_m1_post ms A_BUF blk_fact) in HS.
2:{ unfold afact_ok, blk_fact. cbn [af_lo af_hi af_al2]. change A_BUF with 14%nat. rewrite E14, u64_of_Z by lia. change (2 ^ 4) with 16.
pose proof YM05.alloc_ceiling_val. lia. }
change (add_atom ss_m1_post A_BUF blk_fact) with ss_m1_ok in HS.
cdrv_run_to_with src0tbl_ok HS RDPC HF.
lazymatch type of HS with st_ok _ _ _ ?msx => change (st_ok src0segs E0 X0 msx) in HS end.
assert (HSAX : stack_anchored E0 (ss_facts X0)) by (apply HSAE0; vm_compute; reflexivity).
drv_mr (MR_after_frame src0_msyms (aa_MR API) (aa_laws API) AX) src0_keep E0 HS HF HMR.
apply (st_ok_edset src0segs E0 2 data) in HS; [| vm_compute; reflexivity].
lazymatch type of HS with st_ok _ _ _ ?msx =>
set (J := map (getr (ms_regs msx)) Jregs);
assert (HS' : st_ok src0segs (E_lp J (ptr_addr Lc bufp) g 0 65536) S_RD msx);
[ unfold S_RD; change RDPC with (ss_pc X0);
apply (st_ok_reabs src0segs P_X0 (edset E0 2 data) (E_lp J (ptr_addr Lc bufp) g 0 65536) X0 msx RD_regs LH_mem RD_facts HS) | ] end.
- split; [| intros d _; reflexivity].
intros n Hn. unfold P_X0 in Hn. rewrite ew_lp.
apply orb_prop in Hn as [Hn|Hn]; [apply orb_prop in Hn as [Hn|Hn]|].
+ apply Nat.ltb_lt in Hn. destruct (Nat.eqb_spec n 28); [lia|]. destruct (Nat.eqb_spec n 27); [lia|]. destruct (Nat.eqb_spec n 26); [lia|].
destruct (Nat.eqb_spec n 14); [lia|]. destruct (Nat.ltb_spec n 29); [|lia].
unfold E0, E_m1, post_env, edset. cbn [ew]. rewrite ew_ewset_other by (unfold K_M1; lia). rewrite !ew_havoc_old by (unfold K_M1; lia). reflexivity.
+ apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset. cbn [ew]. rewrite E14. reflexivity.
+ apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset, E0, E_m1, post_env. cbn [ew]. change 26%nat with (K_M1 + 16)%nat. rewrite ew_ewset_same. reflexivity.
- exact reabs_X0.
- apply obl_X0.
+ intros k r Hr Hk. apply (lp_junk Jregs); [reflexivity | exact Hr | exact Hk].
+ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 19) HS). reflexivity.
+ rewrite ew_lp. cbn [Nat.eqb Nat.ltb Nat.leb]. rewrite (st_ok_reg src0segs _ _ _ (R 21) HS). reflexivity.
- rewrite fobl_X0. constructor; [| constructor; [| constructor]]; unfold afact_ok, fact_len, fact_cap; cbn [fst snd af_lo af_hi af_al2]; rewrite ew_lp; cbn [Nat.eqb Nat.ltb Nat.leb].
+ rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
+ rewrite u64_of_Z by lia. repeat split; try lia; try reflexivity.
- destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (mem_ok_relayout src0segs) with (l := back LH_mem) in HM; [| exact relayout_X0]. rewrite back_LH_mem in HM.
eapply (mem_ok_agree_pd src0segs P_X0 PT (edset E0 2 data)); [| | exact HM].
+ split; [| intros d _; reflexivity].
intros n Hn. unfold P_X0 in Hn. rewrite ew_lp.
apply orb_prop in Hn as [Hn|Hn]; [apply orb_prop in Hn as [Hn|Hn]|].
* apply Nat.ltb_lt in Hn. destruct (Nat.eqb_spec n 28); [lia|]. destruct (Nat.eqb_spec n 27); [lia|]. destruct (Nat.eqb_spec n 26); [lia|].
destruct (Nat.eqb_spec n 14); [lia|]. destruct (Nat.ltb_spec n 29); [|lia].
unfold E0, E_m1, post_env, edset. cbn [ew]. rewrite ew_ewset_other by (unfold K_M1; lia). rewrite !ew_havoc_old by (unfold K_M1; lia). reflexivity.
* apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset. cbn [ew]. rewrite E14. reflexivity.
* apply Nat.eqb_eq in Hn. subst n. cbn [Nat.eqb Nat.ltb Nat.leb]. unfold edset, E0, E_m1, post_env. cbn [ew]. change 26%nat with (K_M1 + 16)%nat. rewrite ew_ewset_same. reflexivity.
+ vm_compute. reflexivity.
- clear HS.
assert (HRES0 : exists b Kb c, res_ok A b /\ RPinv Kb c CAP0 b /\ Kb + capflag CAP0 <= 2 ^ 24 /\ 0 <= c /\ c + Z.of_nat READ_FUEL <= 12).
{ exists (rb_malloc (RB 0 0 0 0) CAP0), 0, 1.
refine (conj HR0 (conj (proj1 rp_init) (conj (proj2 rp_init) (conj _ _)))); [lia | unfold READ_FUEL; cbn; lia]. }
lazymatch type of HS' with st_ok _ _ _ ?msx =>
apply (loop_rd_cf (S (Z.to_nat (2 ^ 28))) READ_FUEL CAP0 bufp 0 A Lc J g msx md K ltac:(unfold CAP0; lia) eq_refl ltac:(unfold READ_FUEL; lia)
ltac:(unfold CAP0; lia) ltac:(lia) Hub HW HB Hid HDI HRES0 HS' HMR) end.
+ subst md. unfold YL0l.md_loop, MD_file, fdchan. autorewrite with model. rewrite MD0_fds, MD0_fs.
rewrite fd_lookup_insert_eq, !fd_lookup_insert_neq by (intros H'; apply (f_equal bv_unsigned) in H'; discriminate).
repeat split; first [apply fd_insert_std3 | reflexivity].
+ cbn. apply (blk_data_nil src0_msyms).
+ exact HJ.
+ exact HG.
+ exact HL.
+ exact HK.
+ exact HPOST.
Qed.
End j.
End h.
