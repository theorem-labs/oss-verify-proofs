(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCgl YCg2 YCgi YCg4 YCg0 YCfy YCg8 YCg1 YCfz YCga YCgk.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition PC_MISS : Z := 0x8aadc.
Definition shp (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 23 0).
Inductive mcase := MC_full | MC_map | MC_sw | MC_first.
Definition mc_of (dp vLM vLI : Z) : mcase :=
if dp =? 4096 then MC_full else if negb (vLM =? 0) then MC_map else if vLI =? 0 then MC_first else MC_sw.
Definition is_full (mc : mcase) : bool := match mc with MC_full => true | _ => false end.
Definition is_map (mc : mcase) : bool := match mc with MC_map => true | _ => false end.
Definition is_sw (mc : mcase) : bool := match mc with MC_sw => true | _ => false end.
Definition is_first (mc : mcase) : bool := match mc with MC_first => true | _ => false end.
Definition tms_X : sv := SAluw ALU_ADD (SMd M_MUL (SOff 62%nat (-1)) (SOff 25%nat 0)) (SLit 0).
Definition tms_Y : sv := SAluw ALU_ADD (SAlu ALU_ADD tms_X (SOff 61%nat 0)) (SLit 0).
Definition tms_ROW : sv := SMdw M_MUL (SOff 43%nat (-1)) (SOff 25%nat 0).
Definition tms_Y2 : sv := SAluw ALU_ADD (SAlu ALU_ADD tms_ROW (SOff 61%nat 0)) (SLit 0).
Definition tmiss_J (mc : mcase) (vLM mp idl c : Z) : Z :=
match mc with MC_map => (vLM - 1) * idl + c | MC_sw => (mp - 1) * idl | _ => 0 end.
Definition tmiss_facts (mc : mcase) : list (nat * afact) :=
[ (14%nat, mkAF 0 4095 0); (27%nat, mkAF 0 8190 1); (24%nat, mkAF 1 99999999 0); (16%nat, APTR 0); (11%nat, APTR 1); (12%nat, APTR 1);
(60%nat, APTR 1); (61%nat, mkAF 0 255 0); (62%nat, mkAF 0 2046 0); (63%nat, mkAF 0 4095 0); (64%nat, APTR 0) ]
++ (if is_map mc then [ (65%nat, APTR 1) ] else [])
++ (if is_sw mc then [ (66%nat, APTR 1); (67%nat, APTR 1) ] else []).
Definition tmiss_conds (mc : mcase) : list acond :=
[ mkAC BC_GEU (SOff 60 0) (SOff 37 0); mkAC (if is_full mc then BC_NE else BC_EQ) (SAlu ALU_SRL (SOff 42 0) (SLit 12)) (SLit 0) ]
++ (if is_full mc then [] else [ mkAC BC_LTU (SOff 24 0) (SOff 39 0); mkAC (if is_map mc then BC_NE else BC_EQ) (SOff 62 0) (SLit 0) ])
++ (if is_map mc then
[ mkAC BC_EQ (SMdw M_MUL (SOff 62 (-1)) (SOff 25 0)) (SMd M_MUL (SOff 62 (-1)) (SOff 25 0));
mkAC BC_EQ (SAluw ALU_ADD tms_X (SOff 61 0)) (SAlu ALU_ADD tms_X (SOff 61 0));
mkAC BC_GEU (SOff 65 0) (SOff 36 0);
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 65 0) (SOff 36 0)) (SAlu ALU_SLT tms_Y (SLit 0))) (SLit 1)) (SLit 0) ]
else if is_sw mc then
[ mkAC BC_NE (SOff 63 0) (SLit 0);
mkAC BC_EQ tms_ROW (SMd M_MUL (SOff 43 (-1)) (SOff 25 0));
mkAC BC_GEU (SOff 66 0) (SOff 36 0);
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 66 0) (SOff 36 0)) (SAlu ALU_SLT tms_ROW (SLit 0))) (SLit 1)) (SLit 0);
mkAC BC_EQ (SAluw ALU_ADD tms_ROW (SOff 61 0)) (SAlu ALU_ADD tms_ROW (SOff 61 0));
mkAC BC_GEU (SOff 67 0) (SOff 36 0);
mkAC BC_NE (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 67 0) (SOff 36 0)) (SAlu ALU_SLT tms_Y2 (SLit 0))) (SLit 1)) (SLit 0);
mkAC BC_GEU (SOff 12 0) (SOff 33 0) ]
else if is_first mc then
[ mkAC BC_EQ (SOff 63 0) (SLit 0); mkAC BC_GEU (SOff 64 0) (SOff 34 0); mkAC BC_GEU (SOff 11 0) (SOff 35 0) ]
else []).
Definition tmiss_alias (mc : mcase) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 37 0) (SAlu ALU_SLL (SOff 41 0) (SLit 1)), SOff 60 0); (SAlu ALU_ADD (SOff 34 0) (SOff 14 0), SOff 64 0);
(SAlu ALU_ADD (SOff 35 0) (SOff 27 0), SOff 11 0); (SAlu ALU_ADD (SOff 33 0) (SOff 27 0), SOff 12 0) ]
++ (if is_map mc then [ (SAlu ALU_ADD (SOff 36 0) (SAlu ALU_SLL tms_Y (SLit 1)), SOff 65 0) ] else [])
++ (if is_sw mc then [ (SAlu ALU_ADD (SAlu ALU_SLL tms_ROW (SLit 1)) (SOff 36 0), SOff 66 0);
(SAlu ALU_ADD (SOff 36 0) (SAlu ALU_SLL tms_Y2 (SLit 1)), SOff 67 0) ] else []).
Definition tms_img1 : YQ0b.region := YQ0b.mkRegion (Some 16%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 61 0))].
Definition tmiss_regions (mc : mcase) : smem :=
[ regw 60 2 ]
++ (if is_full mc then [] else [ tms_img1; reg16 12 62 (is_sw mc) ])
++ (if is_map mc then [ regw 65 2 ] else if is_sw mc then [ reg16 11 63 false ] else if is_first mc then [ reg16 11 63 true; regw 64 1 ] else []).
Definition sr_tmiss : list sv := sr_set (sr_set (sr_set (sr_set (sr_set asr_fix 17%bv (SOff 14 0)) 5%bv (shp 16)) 6%bv (shp 11)) 29%bv (shp 12)) 10%bv (SOff 16 0).
Definition ss_tmiss0 (mc : mcase) : sstate :=
alzw_ss PC_MISS asr_fix true (is_sw mc) (tmiss_regions mc) (tmiss_facts mc) (tmiss_conds mc) (tmiss_alias mc).
Definition ss_tmiss (mc : mcase) : sstate :=
alzw_ss PC_MISS sr_tmiss true (is_sw mc) (tmiss_regions mc) (tmiss_facts mc) (tmiss_conds mc) (tmiss_alias mc).
Definition tmiss_env (E : env) (cx : lzw_acx) (lp dp mp s1 q c vLI vLM J : Z) : Prop :=
ew E 2 = Z_to_bv 64 (z_sp cx - 304) /\ ew E 8 = Z_to_bv 64 (z_ctx cx) /\ ew E 23 = Z_to_bv 64 SB /\ ew E 25 = Z_to_bv 64 (z_idl cx) /\
ew E 3 = Z_to_bv 64 (z_gp cx) /\ ew E 4 = Z_to_bv 64 (z_tp cx) /\
ew E 32 = Z_to_bv 64 (z_ti cx) /\ ew E 33 = Z_to_bv 64 (z_lm cx) /\ ew E 34 = Z_to_bv 64 (z_lc cx) /\ ew E 35 = Z_to_bv 64 (z_li cx) /\
ew E 36 = Z_to_bv 64 (z_tm cx) /\ ew E 37 = Z_to_bv 64 (z_ld cx) /\ ew E 38 = Z_to_bv 64 (z_img cx) /\ ew E 39 = Z_to_bv 64 (z_nP cx) /\
ew E 41 = Z_to_bv 64 lp /\ ew E 42 = Z_to_bv 64 dp /\ ew E 43 = Z_to_bv 64 mp /\ ew E 45 = Z_to_bv 64 (2 * z_idl cx) /\
ew E 14 = Z_to_bv 64 q /\ ew E 27 = Z_to_bv 64 (2 * q) /\ ew E 24 = Z_to_bv 64 s1 /\
ew E 16 = Z_to_bv 64 (z_img cx + s1) /\ ew E 11 = Z_to_bv 64 (z_li cx + 2 * q) /\ ew E 12 = Z_to_bv 64 (z_lm cx + 2 * q) /\
ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp) /\ ew E 61 = Z_to_bv 64 c /\ ew E 62 = Z_to_bv 64 vLM /\ ew E 63 = Z_to_bv 64 vLI /\
ew E 64 = Z_to_bv 64 (z_lc cx + q) /\ ew E 65 = Z_to_bv 64 (z_tm cx + 2 * J) /\ ew E 66 = Z_to_bv 64 (z_tm cx + 2 * J) /\
ew E 67 = Z_to_bv 64 (z_tm cx + 2 * (J + c)).
Lemma alias_sll1_base : forall E nb nk e base v,
ew E nb = Z_to_bv 64 base -> U E e = v -> ew E nk = Z_to_bv 64 (base + 2 * v) ->
0 <= base -> 0 <= v -> base + 2 * v < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL e (SLit 1)) (SOff nb 0)) = sv_denot E (SOff nk 0).
Proof.
intros E nb nk e base v Hb He Hk R1 R2 R3. apply U_inj.
rewrite (U_add_small E (SAlu ALU_SLL e (SLit 1)) (SOff nb 0) (2 * v) base); try lia.
- rewrite (U_atom E nk _ Hk) by lia. lia.
- apply U_sll1_small; [exact He | lia | lia].
- apply (U_atom E nb base Hb). lia.
Qed.
Section S.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL.
Lemma tmiss_seed : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) TI LM LI TM s lp dp mp Cn R s1 q c,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal trbsegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_fix regs cx -> agen_at (mrestrict (w_H W7) memT) cx lp dp mp ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx (mkLA TI LM LI TM s lp dp mp Cn R) -> lzw_inv (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ->
tmiss_pre cx (mkLA TI LM LI TM s lp dp mp Cn R) regs s1 q c -> s < s1 <= z_nP cx - 1 -> 0 <= q < 4096 -> 0 <= c < z_idl cx ->
val_mem trbsegs (mrestrict (w_H W7) memT) (z_img cx + s1) 1 c ->
let vLI := nth (Z.to_nat q) LI 0 in let vLM := nth (Z.to_nat q) LM 0 in
let mc := mc_of dp vLM vLI in let J := tmiss_J mc vLM mp (z_idl cx) c in
exists E more,
E = Ereg regs (acx_extra cx lp dp mp regs0 ++ more) /\
st_ok trbsegs E (ss_tmiss mc) (restrict (w_H W7) (mkst regs (Z_to_bv 64 PC_MISS) memT (seg_rom trbsegs))) /\
tmiss_env E cx lp dp mp s1 q c vLI vLM J /\
(is_map mc = true -> 0 <= J /\ (Z.to_nat J < length TM)%nat /\ 2 * J + 2 <= 4098 * z_idl cx /\ 1 <= vLM < mp /\ dp < 4096) /\
(is_sw mc = true -> 0 <= J /\ J = (mp - 1) * z_idl cx /\ J + z_idl cx <= 2048 * z_idl cx /\ vLM = 0 /\ vLI <> 0 /\ dp < 4096) /\
(is_first mc = true -> vLM = 0 /\ vLI = 0 /\ dp < 4096) /\
(is_full mc = true -> dp = 4096).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 TI LM LI TM s lp dp mp Cn R s1 q c HCX HRG HSEP (HBg & HBi & HBt) HJ HFX HG HSL HSS HFR HT HI
(H26 & H14 & H17 & H24 & H16 & H10 & H5 & H11 & H6 & H12 & H29) Hs1 Hq Hc HC.
pose proof HJ as (HAR & _). pose proof (alzw_regs_core_of_fix _ _ HFX) as HFC.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBld : In (z_ld cx, 2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; left; reflexivity).
assert (HBlm : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity).
assert (HBlc : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity).
assert (HBli : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ctx cx) 72 HAR HBg) as (_ & _ & _ & _ & Hcpres & _). change (req_size 72) with 72 in Hcpres.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_ld cx) _ HAR HBld) as (_ & _ & _ & _ & Hldpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_li cx) _ HAR HBli) as (_ & _ & _ & _ & Hlipres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_lm cx) _ HAR HBlm) as (_ & _ & _ & _ & Hlmpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_lc cx) _ HAR HBlc) as (_ & _ & _ & _ & Hlcpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_tm cx) _ HAR HBtm) as (_ & _ & _ & _ & Htmpres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_bi cx) _ HAR HBi) as (_ & _ & _ & _ & Hbipres & _).
pose proof (req_size_pos (2 * (lzw_MR (z_nP cx) (z_idl cx) + z_nP cx + 2)) ltac:(pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)); unfold lzw_MR; lia)) as Hrqld.
pose proof (req_size_pos 8192 ltac:(lia)) as Hrq8. pose proof (req_size_pos 4096 ltac:(lia)) as Hrq4. pose proof (req_size_pos (4098 * z_idl cx) ltac:(lia)) as Hrqtm.
assert (Hsws : forall a, z_sp cx - 336 <= a < z_sp cx -> apresent (w_H W7) memT a).
{ intros a Ha. apply (proj1 (awr_byte_present trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ ltac:(left; rewrite HTS, Has; lia))). }
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
pose proof (maxres_bounds (z_idl cx) (z_nP cx) Hidl ltac:(lia)) as [HMR1 HMR2].
assert (EMR' : lzw_MR (z_nP cx) (z_idl cx) = z_MR cx) by (symmetry; exact EMR). unfold lzw_MR in EMR'. unfold lzw_MR in Rld1, Rld2, Rld4, Hrqld, HBld, Hldpres. rewrite EMR' in *.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
pose proof (mp_bound (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(lia) HI) as Hmpb. cbn [la_mp] in Hmpb.
set (m := mrestrict (w_H W7) memT) in *.
destruct (LI_read (z_idl cx) (z_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ trbsegs m (z_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ trbsegs m (z_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM. clearbody vLI vLM.
remember (mc_of dp vLM vLI) as mc eqn:Hmc. set (J := tmiss_J mc vLM mp (z_idl cx) c).
assert (Hrow : forall mm, 1 <= mm <= 2048 -> 0 <= (mm - 1) * z_idl cx /\ (mm - 1) * z_idl cx + z_idl cx <= 2048 * z_idl cx).
{ intros mm Hmm. split; [apply Z.mul_nonneg_nonneg; lia |].
replace ((mm - 1) * z_idl cx + z_idl cx) with (mm * z_idl cx) by lia. apply Z.mul_le_mono_nonneg_r; lia. }
assert (H2049 : 2049 * z_idl cx <= 2049 * 256) by (apply Z.mul_le_mono_nonneg_l; lia).
assert (Hmap : is_map mc = true -> 0 <= J /\ (Z.to_nat J < length TM)%nat /\ 2 * J + 2 <= 4098 * z_idl cx /\ 1 <= vLM < mp /\ dp < 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [discriminate Hmc|]. destruct (Z.eqb_spec vLM 0); cbn in Hmc; [destruct (vLI =? 0); discriminate Hmc|].
cbn [J tmiss_J].
destruct (TM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) vLM c ltac:(lia) HI ltac:(cbn; lia) ltac:(lia)) as (T1 & T2 & T3).
cbn [la_TM] in T1, T2. destruct (Hrow vLM ltac:(lia)) as [Hr1 Hr2]. repeat split; try lia; exact T1. }
assert (Hsw : is_sw mc = true -> 0 <= J /\ J = (mp - 1) * z_idl cx /\ J + z_idl cx <= 2048 * z_idl cx /\ vLM = 0 /\ vLI <> 0 /\ dp < 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [discriminate Hmc|]. destruct (Z.eqb_spec vLM 0); cbn in Hmc; [|discriminate Hmc].
destruct (Z.eqb_spec vLI 0); cbn in Hmc; [discriminate Hmc|]. cbn [J tmiss_J].
destruct (Hrow mp ltac:(lia)) as [Hr1 Hr2]. repeat split; lia. }
assert (Hfirst : is_first mc = true -> vLM = 0 /\ vLI = 0 /\ dp < 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [discriminate Hmc|]. destruct (Z.eqb_spec vLM 0); cbn in Hmc; [|discriminate Hmc].
destruct (Z.eqb_spec vLI 0); cbn in Hmc; [|discriminate Hmc]. lia. }
assert (Hfull : is_full mc = true -> dp = 4096).
{ intros Hm. destruct mc; try discriminate Hm. unfold mc_of in Hmc.
destruct (Z.eqb_spec dp 4096); cbn in Hmc; [lia|]. destruct (negb (vLM =? 0)); cbn in Hmc; [discriminate Hmc|]. destruct (vLI =? 0); discriminate Hmc. }
assert (Hnfull : is_full mc = false -> dp < 4096).
{ intros Hm. destruct mc; [discriminate Hm | exact (proj2 (proj2 (proj2 (proj2 (Hmap eq_refl))))) | exact (proj2 (proj2 (proj2 (proj2 (proj2 (Hsw eq_refl)))))) | exact (proj2 (proj2 (Hfirst eq_refl)))]. }
assert (HJr : 0 <= J /\ 2 * J + 2 <= 4098 * z_idl cx).
{ destruct mc.
- cbn [J tmiss_J]; lia.
- destruct (Hmap eq_refl) as (T0 & _ & T2 & _). exact (conj T0 T2).
- destruct (Hsw eq_refl) as (T0 & T1 & T2 & _). split; [exact T0 | lia].
- cbn [J tmiss_J]; lia. }
assert (Pld : forall i, 0 <= i < 2 * (z_nP cx + 2 + z_MR cx) -> YP0c.present m (z_ld cx + i)).
{ intros i Hi. destruct (Hldpres (z_ld cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
set (more := [Z_to_bv 64 (z_ld cx + 2 * lp); Z_to_bv 64 c; Z_to_bv 64 vLM; Z_to_bv 64 vLI; Z_to_bv 64 (z_lc cx + q); Z_to_bv 64 (z_tm cx + 2 * J); Z_to_bv 64 (z_tm cx + 2 * J);
Z_to_bv 64 (z_tm cx + 2 * (J + c))]).
remember (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) as E eqn:HE0.
assert (HE60 : ew E 60 = Z_to_bv 64 (z_ld cx + 2 * lp)) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0); reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 c) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1); reflexivity).
assert (HE62 : ew E 62 = Z_to_bv 64 vLM) by (rewrite HE0; change 62%nat with (60 + 2)%nat; rewrite (AE_more regs _ _ _ _ _ more 2); reflexivity).
assert (HE63 : ew E 63 = Z_to_bv 64 vLI) by (rewrite HE0; change 63%nat with (60 + 3)%nat; rewrite (AE_more regs _ _ _ _ _ more 3); reflexivity).
assert (HE64 : ew E 64 = Z_to_bv 64 (z_lc cx + q)) by (rewrite HE0; change 64%nat with (60 + 4)%nat; rewrite (AE_more regs _ _ _ _ _ more 4); reflexivity).
assert (HE65 : ew E 65 = Z_to_bv 64 (z_tm cx + 2 * J)) by (rewrite HE0; change 65%nat with (60 + 5)%nat; rewrite (AE_more regs _ _ _ _ _ more 5); reflexivity).
assert (HE66 : ew E 66 = Z_to_bv 64 (z_tm cx + 2 * J)) by (rewrite HE0; change 66%nat with (60 + 6)%nat; rewrite (AE_more regs _ _ _ _ _ more 6); reflexivity).
assert (HE67 : ew E 67 = Z_to_bv 64 (z_tm cx + 2 * (J + c))) by (rewrite HE0; change 67%nat with (60 + 7)%nat; rewrite (AE_more regs _ _ _ _ _ more 7); reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE21. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_gp regs cx lp dp mp regs0 more HFC) as HE3. pose proof (AE_tp regs cx lp dp mp regs0 more HFC) as HE4.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE32. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE33.
pose proof (AE_lc regs cx lp dp mp regs0 more) as HE34. pose proof (AE_li regs cx lp dp mp regs0 more) as HE35.
pose proof (AE_tm regs cx lp dp mp regs0 more) as HE36. pose proof (AE_ld regs cx lp dp mp regs0 more) as HE37.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE38. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE39.
pose proof (AE_lp regs cx lp dp mp regs0 more) as HE41. pose proof (AE_dp regs cx lp dp mp regs0 more) as HE42.
pose proof (AE_mp regs cx lp dp mp regs0 more) as HE43. pose proof (AE_idl2 regs cx lp dp mp regs0 more) as HE45.
rewrite <- HE0 in HE2, HE8, HE21, HE25, HE3, HE4, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE43, HE45.
assert (HE26 : ew E 24 = Z_to_bv 64 s1) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 24%bv 24) by reflexivity; exact H26).
assert (HE14 : ew E 14 = Z_to_bv 64 q) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 14%bv 14) by reflexivity; exact H14).
assert (HE24 : ew E 27 = Z_to_bv 64 (2 * q)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 27%bv 27) by reflexivity; exact H24).
assert (HE16 : ew E 16 = Z_to_bv 64 (z_img cx + s1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 16%bv 16) by reflexivity; exact H16).
assert (HE11 : ew E 11 = Z_to_bv 64 (z_li cx + 2 * q)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 11%bv 11) by reflexivity; exact H11).
assert (HE12 : ew E 12 = Z_to_bv 64 (z_lm cx + 2 * q)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 12%bv 12) by reflexivity; exact H12).
pose proof (proj1 Hbi0) as Hb4096.
exists E, more. split; [exact HE0|].
split.
2:{ split; [unfold tmiss_env; repeat (split; [assumption|]); assumption|].
split; [exact Hmap|]. split; [exact Hsw|]. split; [exact Hfirst | exact Hfull]. }
assert (HUX : is_map mc = true -> U E tms_X = (vLM - 1) * z_idl cx).
{ intros Hm. destruct (Hmap Hm) as (T0 & T1 & T2 & T3 & T4). destruct (Hrow vLM ltac:(lia)) as [Hr1 Hr2].
unfold tms_X. apply U_sextw_small; [apply (U_mul_row64 E 62 25 vLM (z_idl cx) HE62 HE25); lia | lia]. }
assert (HUY : is_map mc = true -> U E tms_Y = J).
{ intros Hm. destruct (Hmap Hm) as (T0 & T1 & T2 & T3 & T4). destruct (Hrow vLM ltac:(lia)) as [Hr1 Hr2].
assert (EJ : J = (vLM - 1) * z_idl cx + c) by (subst J; destruct mc; try discriminate Hm; reflexivity).
unfold tms_Y. apply U_sextw_small; [|lia].
rewrite (U_add_small E tms_X (SOff 61%nat 0) ((vLM - 1) * z_idl cx) c (HUX Hm) (U_atom E 61 c HE61 ltac:(lia))) by lia. lia. }
assert (HUROW : is_sw mc = true -> U E tms_ROW = J).
{ intros Hm. destruct (Hsw Hm) as (T0 & T1 & _). rewrite T1. unfold tms_ROW. apply (U_mulw_row E 43 25 mp (z_idl cx) HE43 HE25); lia. }
assert (HUY2 : is_sw mc = true -> U E tms_Y2 = J + c).
{ intros Hm. destruct (Hsw Hm) as (T0 & T1 & T2 & _).
unfold tms_Y2. apply U_sextw_small; [|lia].
rewrite (U_add_small E tms_ROW (SOff 61%nat 0) J c (HUROW Hm) (U_atom E 61 c HE61 ltac:(lia))) by lia. lia. }
assert (HS1 : st_ok trbsegs E (ss_tmiss0 mc) (mkst regs (Z_to_bv 64 PC_MISS) m (seg_rom trbsegs))).
{ unfold ss_tmiss0. rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_MISS asr_fix true (is_sw mc)); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros _ a Ha. apply (apresent_writable trbsegs). apply (proj1 (Hcpres a ltac:(lia))).
- intros _ a Ha. apply (apresent_writable trbsegs). apply Hsws. lia.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_fix regs cx); [exact HFX | lia | lia].
- destruct mc; vm_compute; reflexivity.
-
unfold tmiss_regions. apply Forall_app. split.
{ apply Forall_cons; [|apply Forall_nil].
apply (region_ok_regw _ E m 60 2 (z_ld cx + 2 * lp) HE60); [lia | lia | lia |].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hldpres (z_ld cx + 2 * lp + o) ltac:(lia))). }
apply Forall_app. split.
{ destruct (is_full mc); [apply Forall_nil|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- unfold region_ok, tms_img1. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE16, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [| change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE61, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
- apply (region_ok_reg16 _ E m 12 62 (is_sw mc) (z_lm cx + 2 * q) vLM HE12 HE62); [lia | lia | lia | exact VLM |].
intros _ o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hlmpres (z_lm cx + 2 * q + o) ltac:(lia))). }
destruct mc; cbn [is_map is_sw is_first].
+ apply Forall_nil.
+ destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4). apply Forall_cons; [|apply Forall_nil].
apply (region_ok_regw _ E m 65 2 (z_tm cx + 2 * J) HE65); [lia | lia | lia |].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Htmpres (z_tm cx + 2 * J + o) ltac:(lia))).
+ apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E m 11 63 false (z_li cx + 2 * q) vLI HE11 HE63); [lia | lia | lia | exact VLI | intros X0; discriminate X0].
+ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
* apply (region_ok_reg16 _ E m 11 63 true (z_li cx + 2 * q) vLI HE11 HE63); [lia | lia | lia | exact VLI |].
intros _ o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hlipres (z_li cx + 2 * q + o) ltac:(lia))).
* apply (region_ok_regw _ E m 64 1 (z_lc cx + q) HE64); [lia | lia | lia |].
intros o Ho. apply (apresent_writable trbsegs). apply (proj1 (Hlcpres (z_lc cx + q + o) ltac:(lia))).
-
unfold tmiss_regions. destruct mc; cbn [is_full is_map is_sw is_first app all_disjoint];
unfold extent_disjoint, regw, reg16, tms_img1, actx_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite HE8, HE60, ?HE16, ?HE12, ?HE11, ?HE64, ?HE65, !unsigned_lit_small by lia.
+ split; [septac HSEP 0%nat 6%nat; lia | exact I].
+ split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 2%nat 6%nat; lia|].
split; [septac HSEP 5%nat 6%nat; lia | exact I].
+ split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 2%nat 6%nat; lia|].
split; [septac HSEP 4%nat 6%nat; lia | exact I].
+ split; [septac HSEP 0%nat 6%nat; lia|]. split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 2%nat 6%nat; lia|].
split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 3%nat 6%nat; lia | exact I].
-
unfold tmiss_regions. destruct mc; cbn [is_full is_map is_sw is_first app all_disjoint];
unfold extent_disjoint, regw, reg16, tms_img1, astk_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite HE2, HE60, ?HE16, ?HE12, ?HE11, ?HE64, ?HE65, !unsigned_lit_small by lia; repeat split; lia.
- unfold tmiss_regions. destruct mc; cbn [is_full is_map is_sw is_first app pairwise_disjoint all_disjoint];
unfold extent_disjoint, regw, reg16, tms_img1; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite ?HE60, ?HE16, ?HE12, ?HE11, ?HE64, ?HE65, ?unsigned_lit_small by lia.
+ split; exact I.
+ split; [split; [septac HSEP 0%nat 7%nat; lia | split; [septac HSEP 0%nat 2%nat; lia | split; [septac HSEP 0%nat 5%nat; lia | exact I]]]|].
split; [split; [septac HSEP 2%nat 7%nat; lia | split; [septac HSEP 5%nat 7%nat; lia | exact I]]|].
split; [split; [septac HSEP 2%nat 5%nat; lia | exact I]|]. split; exact I.
+ split; [split; [septac HSEP 0%nat 7%nat; lia | split; [septac HSEP 0%nat 2%nat; lia | split; [septac HSEP 0%nat 4%nat; lia | exact I]]]|].
split; [split; [septac HSEP 2%nat 7%nat; lia | split; [septac HSEP 4%nat 7%nat; lia | exact I]]|].
split; [split; [septac HSEP 2%nat 4%nat; lia | exact I]|]. split; exact I.
+ split; [split; [septac HSEP 0%nat 7%nat; lia | split; [septac HSEP 0%nat 2%nat; lia | split; [septac HSEP 0%nat 4%nat; lia | split; [septac HSEP 0%nat 3%nat; lia | exact I]]]]|].
split; [split; [septac HSEP 2%nat 7%nat; lia | split; [septac HSEP 4%nat 7%nat; lia | split; [septac HSEP 3%nat 7%nat; lia | exact I]]]|].
split; [split; [septac HSEP 2%nat 4%nat; lia | split; [septac HSEP 2%nat 3%nat; lia | exact I]]|].
split; [split; [septac HSEP 3%nat 4%nat; lia | exact I]|]. split; exact I.
-
unfold tmiss_facts. apply atoms_ok_app; [|apply atoms_ok_app].
+ cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE14, HE24, HE26, HE16, HE11, HE12, HE60, HE61, HE62, HE63, HE64, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
* apply Z.mod_divide; [lia|]. exists q; lia.
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists lp; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rld3].
+ destruct (is_map mc) eqn:Hm; [|exact I]. destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4). cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE65, !unsigned_lit_small by lia. change (2 ^ 1) with 2. repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists J; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
+ destruct (is_sw mc) eqn:Hm; [|exact I]. destruct (Hsw eq_refl) as (T0 & T1 & T2 & T3 & T4 & T5). cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE66, HE67, !unsigned_lit_small by lia. change (2 ^ 1) with 2. repeat split; try lia.
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists J; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists (J + c); lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
-
unfold tmiss_conds. apply aconds_ok_app; [|apply aconds_ok_app].
+ cbn [conds_ok]. split; [apply (cond_geu E 60 0 37 0 (z_ld cx + 2 * lp) (z_ld cx) HE60 HE37); lia|]. split; [|exact I].
destruct (is_full mc) eqn:Hm.
* apply (cond_ne_U E). rewrite (U_dpfull12 E 42 dp HE42), (Hfull eq_refl), U_SLit by lia. discriminate.
* apply (cond_eq_U E). rewrite (U_dpfull12 E 42 dp HE42), U_SLit by lia. pose proof (Hnfull eq_refl).
destruct (Z.eqb_spec dp 4096); [lia | reflexivity].
+ destruct (is_full mc) eqn:Hf; [exact I|]. cbn [conds_ok]. split; [apply (cond_ltu E 24 0 39 0 s1 (z_nP cx) HE26 HE39); lia|]. split; [|exact I].
destruct (is_map mc) eqn:Hm.
* apply (cond_ne_U E). rewrite (U_atom E 62 vLM HE62), U_SLit by lia. change (zcanon 0) with 0. destruct (Hmap eq_refl) as (_ & _ & _ & T3 & _). lia.
* apply (cond_eq_U E). rewrite (U_atom E 62 vLM HE62), U_SLit by lia. change (zcanon 0) with 0.
destruct mc; try discriminate Hf; try discriminate Hm; [exact (proj1 (proj2 (proj2 (proj2 (Hsw eq_refl))))) | exact (proj1 (Hfirst eq_refl))].
+ destruct mc; cbn [is_map is_sw is_first]; [exact I | | |]; cbn [conds_ok].
*
destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4). destruct (Hrow vLM ltac:(lia)) as [Hr1 Hr2].
split; [|split; [|split; [|split; [|exact I]]]].
-- apply cond_eq_U. rewrite (U_mulw_row E 62 25 vLM (z_idl cx) HE62 HE25), (U_mul_row64 E 62 25 vLM (z_idl cx) HE62 HE25) by lia. reflexivity.
-- apply cond_eq_U.
rewrite (U_addw_small E tms_X (SOff 61%nat 0) ((vLM - 1) * z_idl cx) c (HUX eq_refl) (U_atom E 61 c HE61 ltac:(lia))) by lia.
rewrite (U_add_small E tms_X (SOff 61%nat 0) ((vLM - 1) * z_idl cx) c (HUX eq_refl) (U_atom E 61 c HE61 ltac:(lia))) by lia. reflexivity.
-- apply (cond_geu E 65 0 36 0 (z_tm cx + 2 * J) (z_tm cx) HE65 HE36); lia.
-- apply cond_ne_U. rewrite (U_ptrchk E 65 36 tms_Y (z_tm cx + 2 * J) (z_tm cx) J HE65 HE36 (HUY eq_refl)) by lia. rewrite U_SLit. change (zcanon 0) with 0. lia.
*
destruct (Hsw eq_refl) as (T0 & T1 & T2 & T3 & T4 & T5). destruct (Hrow mp ltac:(lia)) as [Hr1 Hr2].
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]]]].
-- apply (cond_ne_U E). rewrite (U_atom E 63 vLI HE63), U_SLit by lia. change (zcanon 0) with 0. exact T4.
-- apply cond_eq_U. rewrite (HUROW eq_refl), (U_mul_row64 E 43 25 mp (z_idl cx) HE43 HE25) by lia. exact T1.
-- apply (cond_geu E 66 0 36 0 (z_tm cx + 2 * J) (z_tm cx) HE66 HE36); lia.
-- apply cond_ne_U. rewrite (U_ptrchk E 66 36 tms_ROW (z_tm cx + 2 * J) (z_tm cx) J HE66 HE36 (HUROW eq_refl)) by lia. rewrite U_SLit. change (zcanon 0) with 0. lia.
-- apply cond_eq_U.
rewrite (U_addw_small E tms_ROW (SOff 61%nat 0) J c (HUROW eq_refl) (U_atom E 61 c HE61 ltac:(lia))) by lia.
rewrite (U_add_small E tms_ROW (SOff 61%nat 0) J c (HUROW eq_refl) (U_atom E 61 c HE61 ltac:(lia))) by lia. reflexivity.
-- apply (cond_geu E 67 0 36 0 (z_tm cx + 2 * (J + c)) (z_tm cx) HE67 HE36); lia.
-- apply cond_ne_U. rewrite (U_ptrchk E 67 36 tms_Y2 (z_tm cx + 2 * (J + c)) (z_tm cx) (J + c) HE67 HE36 (HUY2 eq_refl)) by lia. rewrite U_SLit. change (zcanon 0) with 0. lia.
-- apply (cond_geu E 12 0 33 0 (z_lm cx + 2 * q) (z_lm cx) HE12 HE33); lia.
*
destruct (Hfirst eq_refl) as (T0 & T1 & T2).
split; [|split; [|split; [|exact I]]].
-- apply (cond_eq_U E). rewrite (U_atom E 63 vLI HE63), U_SLit by lia. change (zcanon 0) with 0. exact T1.
-- apply (cond_geu E 64 0 34 0 (z_lc cx + q) (z_lc cx) HE64 HE34); lia.
-- apply (cond_geu E 11 0 35 0 (z_li cx + 2 * q) (z_li cx) HE11 HE35); lia.
-
unfold tmiss_alias. apply aalias_ok_app; [|apply aalias_ok_app].
+ cbn [alias_ok]. split; [|split; [|split; [|split; [|exact I]]]].
* apply (alias_b2i' E 37 41 60 (z_ld cx) lp HE37 HE41 HE60); lia.
* apply (alias_add E 34 14 64 (z_lc cx) q HE34 HE14 HE64); lia.
* apply (alias_add E 35 27 11 (z_li cx) (2 * q) HE35 HE24 HE11); lia.
* apply (alias_add E 33 27 12 (z_lm cx) (2 * q) HE33 HE24 HE12); lia.
+ destruct (is_map mc) eqn:Hm; [|exact I]. destruct (Hmap eq_refl) as (T0 & T1 & T2 & T3 & T4). cbn [alias_ok]. split; [|exact I].
apply (alias_base_sll1 E 36 65 tms_Y (z_tm cx) J HE36 (HUY eq_refl) HE65); lia.
+ destruct (is_sw mc) eqn:Hm; [|exact I]. destruct (Hsw eq_refl) as (T0 & T1 & T2 & T3 & _). cbn [alias_ok]. split; [|split; [|exact I]].
* apply (alias_sll1_base E 36 66 tms_ROW (z_tm cx) J HE36 (HUROW eq_refl) HE66); lia.
* apply (alias_base_sll1 E 36 67 tms_Y2 (z_tm cx) (J + c) HE36 (HUY2 eq_refl) HE67); lia. }
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_MISS) m (seg_rom trbsegs)) 17%bv (SOff 14 0) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE14, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H17)) as HS2.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_MISS) m (seg_rom trbsegs)) 5%bv (shp 16) HS2 eq_refl
ltac:(unfold shp; cbn [sv_denot ms_regs mkst]; rewrite HE16, HE21, !Z.add_0_r, !unsigned_lit_small by (unfold SB; lia); symmetry; exact H5)) as HS3.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_MISS) m (seg_rom trbsegs)) 6%bv (shp 11) HS3 eq_refl
ltac:(unfold shp; cbn [sv_denot ms_regs mkst]; rewrite HE11, HE21, !Z.add_0_r, !unsigned_lit_small by (unfold SB; lia); symmetry; exact H6)) as HS4.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_MISS) m (seg_rom trbsegs)) 29%bv (shp 12) HS4 eq_refl
ltac:(unfold shp; cbn [sv_denot ms_regs mkst]; rewrite HE12, HE21, !Z.add_0_r, !unsigned_lit_small by (unfold SB; lia); symmetry; exact H29)) as HS5.
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_MISS) m (seg_rom trbsegs)) 10%bv (SOff 16 0) HS5 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE16, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H10)) as HS.
clear HS1 HS2 HS3 HS4 HS5. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_tmiss0 alzw_ss] in HS.
subst m. rewrite <- restrict_mkst_fx in HS. exact HS.
Qed.
End S.
End b.
