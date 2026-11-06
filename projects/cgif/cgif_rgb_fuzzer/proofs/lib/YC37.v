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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31 YC2x YC2v YC35 YC2y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition PC_MISS : Z := 0x89da4.
Definition tin_facts (b : bool) : list (nat * afact) :=
[ (23%nat, mkAF 0 99999999 0); (28%nat, mkAF 1 100000000 0); (15%nat, mkAF 0 4095 0); (11%nat, APTR 0);
(60%nat, mkAF 0 255 0); (61%nat, APTR 1); (62%nat, mkAF 0 4095 0); (63%nat, APTR 0); (64%nat, mkAF 0 255 0);
(65%nat, APTR 1); (66%nat, mkAF 0 2046 0) ]
++ (if b then [ (67%nat, APTR 1); (68%nat, mkAF 0 4095 0) ] else []).
Definition tin_Y : sv := SAluw ALU_ADD (SMd M_MUL (SOff 66 (-1)) (SOff 25 0)) (SOff 60 0).
Definition tin_alias (b : bool) : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 56 0) (SAlu ALU_SLL (SOff 15 0) (SLit 1)), SOff 61 0);
(SAlu ALU_ADD (SOff 55 0) (SOff 15 0), SOff 63 0);
(SAlu ALU_ADD (SOff 54 0) (SAlu ALU_SLL (SOff 15 0) (SLit 1)), SOff 65 0) ]
++ (if b then [ (SAlu ALU_ADD (SOff 57 0) (SAlu ALU_SLL tin_Y (SLit 1)), SOff 67 0) ] else []).
Definition tin_conds (e : bool) : list acond := [ mkAC (if e then BC_LTU else BC_GEU) (SOff 60 0) (SOff 25 0) ].
Definition tin_pix : YQ0b.region := YQ0b.mkRegion (Some 11%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 60 0))].
Definition tin_regions (b : bool) : smem :=
[ tin_pix; reg16 61 62 false; reg8 63 64 false; reg16 65 66 false ] ++ (if b then [reg16 67 68 false] else []).
Definition ss_tin0 (e b : bool) : sstate :=
alzw_ss PC_INNER asr_fix false false (tin_regions b) (tin_facts b) (tin_conds e) (tin_alias b).
Definition acore_shape (sr : list sv) : bool := afix_shape sr.
Lemma alzw_regs_core_after : forall E E' ss ms regs ext cx,
st_ok trasegs E' ss ms -> acore_shape (ss_regs ss) = true ->
(forall n, (n < 32)%nat -> ew E' n = ew E n) -> E = Ereg regs ext ->
alzw_regs_core regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 <= 2 ^ 64 -> alzw_regs_core (ms_regs ms) cx.
Proof. exact alzw_regs_fix_after. Qed.
Definition afix_shapeI (sr : list sv) : bool := afix_shape sr.
Lemma alzw_regs_fix_afterI : forall E E' ss ms regs ext cx,
st_ok trasegs E' ss ms -> afix_shapeI (ss_regs ss) = true ->
(forall n, (n < 32)%nat -> ew E' n = ew E n) -> E = Ereg regs ext ->
alzw_regs_core regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 <= 2 ^ 64 ->
alzw_regs_fix (ms_regs ms) cx.
Proof. exact alzw_regs_fix_after. Qed.
Definition tin_pre (cx : lzw_acx) (regs : bvmap 5 word) (s1 q : Z) : Prop :=
getr regs 23 = w64 s1 /\ getr regs 15 = w64 q /\ getr regs 11 = w64 (z_img cx + s1) /\ getr regs 17 = w64 (z_img cx + s1) /\
getr regs 28 = w64 (z_nP cx - s1) /\ getr regs 16 = w64 (z_nP cx - 1).
Definition tmiss_pre (cx : lzw_acx) (X : lzw_abs) (regs : bvmap 5 word) (s1 q c : Z) : Prop :=
getr regs 23 = w64 s1 /\ getr regs 15 = w64 q /\ getr regs 5 = w64 q /\ getr regs 24 = w64 (2 * q) /\
getr regs 17 = w64 (z_img cx + s1) /\ getr regs 11 = w64 (z_img cx + s1) /\
getr regs 7 = alu64 ALU_ADD (alu64 ALU_SRL (w64 (z_img cx + s1)) (w64 3)) (w64 SB) /\
getr regs 12 = w64 (z_li cx + 2 * q) /\
getr regs 6 = alu64 ALU_ADD (alu64 ALU_SRL (w64 (z_li cx + 2 * q)) (w64 3)) (w64 SB) /\
getr regs 13 = w64 (z_lm cx + 2 * q) /\
getr regs 29 = alu64 ALU_ADD (alu64 ALU_SRL (w64 (z_lm cx + 2 * q)) (w64 3)) (w64 SB).
Inductive tin_out :=
| TIO_eidx
| TIO_cont (q' : Z)
| TIO_emitc (q' : Z)
| TIO_miss (c : Z).
Definition tio_pc (o : tin_out) : Z :=
match o with TIO_eidx => PC_EIDX | TIO_cont _ => PC_INNER | TIO_emitc _ => PC_EMITC | TIO_miss _ => PC_MISS end.
Definition tio_post (cx : lzw_acx) (X : lzw_abs) (s1 q : Z) (m : word -> option byte) (regs' : bvmap 5 word) (o : tin_out) : Prop :=
let nP := z_nP cx in let idl := z_idl cx in
match o with
| TIO_eidx => True
| TIO_cont q' => tin_pre cx regs' (s1 + 1) q' /\ 0 < q' < 4096 /\ s1 + 1 <= nP - 1
| TIO_emitc q' => getr regs' 23 = w64 (nP - 1) /\ getr regs' 15 = w64 q' /\ 0 < q' < 4096 /\ s1 = nP - 1 /\ getr regs' 30 = w64 (z_ctx cx + 60)
| TIO_miss c => tmiss_pre cx X regs' s1 q c /\ 0 <= c < idl /\ val_mem trasegs m (z_img cx + s1) 1 c
end.
Section S.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL.
Lemma tinner_iter : forall cx lyc Sc W memc mdc ly7 S7 W7 (regs : bvmap 5 word) memT mdT (regs0 : bvmap 5 word) X s1 q,
acx_ok cx -> acx_ranges cx -> acx_seps cx -> acx_blk (ablocks B ly7 S7) cx ->
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT mdT 7 ->
alzw_regs_core regs cx -> agen_at (mrestrict (w_H W7) memT) cx (la_lp X) (la_dp X) (la_mp X) ->
alzw_slots (mrestrict (w_H W7) memT) cx -> alzw_sslots (mrestrict (w_H W7) memT) cx -> tlzw_frame (mrestrict (w_H W7) memT) (z_sp cx) regs0 ->
atables_at (mrestrict (w_H W7) memT) cx X -> lzw_inv (z_idl cx) (z_nP cx) X ->
tin_pre cx regs s1 q -> la_s X < s1 <= z_nP cx - 1 -> 0 <= q < 4096 ->
SRr trasegs W7 (mkCfg (mkst regs (Z_to_bv 64 PC_INNER) memT (seg_rom trasegs)) mdT)
(fun W' c' => W' = W7 /\ exists regs' md' o,
c' = mkCfg (mkst regs' (Z_to_bv 64 (tio_pc o)) memT (seg_rom trasegs)) md' /\
ajournal trasegs B LZW_TSTK (z_sp cx) [] lyc Sc W memc mdc [] ly7 S7 W7 memT md' 7 /\
alzw_regs_core regs' cx /\ tio_post cx X s1 q (mrestrict (w_H W7) memT) regs' o).
Proof.
intros cx lyc Sc W memc mdc ly7 S7 W7 regs memT mdT regs0 X s1 q HCX HRG HSEP (HBg & HBi & HBt) HJ HFC HG HSL HSS HFR HT HI (H24 & H13 & H11 & H17 & H16 & H16n) Hs1 Hq.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs.
pose proof HJ as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof HCX as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
assert (HBti : In (z_ti cx, 2 * z_idl cx * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; right; left; reflexivity).
assert (HBlm : In (z_lm cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 2 right; left; reflexivity).
assert (HBlc : In (z_lc cx, 4096) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 3 right; left; reflexivity).
assert (HBli : In (z_li cx, 8192) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 4 right; left; reflexivity).
assert (HBtm : In (z_tm cx, 4098 * z_idl cx) (ablocks B ly7 S7)) by (apply HBt; cbv [acx_tabs lzw_tabs]; do 5 right; left; reflexivity).
pose proof HRG as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3). cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
pose proof (req_size_pos 8192 ltac:(lia)) as Hrq8. pose proof (req_size_pos 4096 ltac:(lia)) as Hrq4. pose proof (req_size_pos (4098 * z_idl cx) ltac:(lia)) as Hrqtm.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_bi cx) (z_Li cx) HAR HBi) as (_ & _ & _ & _ & Hbipres & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (z_lc cx) 4096 HAR HBlc) as (_ & _ & _ & _ & Hlcpres & _).
rewrite ?C1, ?C2, ?C3, ?C4, ?HTS, ?Has in *. clear C2 C3 C4 HTS Has.
destruct X as [TI LM LI TM s lp dp mp Cn R]. cbn [la_TI la_LM la_LI la_TM la_s la_lp la_dp la_mp] in *.
pose proof HI as (LenTI & LenLM & LenLI & LenTM & BTI & BLI & BLM & UTM & ATMrows & Hdp & Hmp & HA & HR0 & HRC & HCn & Hlp & Hs0).
pose proof (countA_nonneg LI LM) as HA0.
assert (HMRle : z_MR cx <= 26055).
{ assert (z_MR cx * 3838 <= z_MR cx * (4094 - z_idl cx)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
pose proof (lp_head_bound (z_idl cx) (z_nP cx) (z_MR cx) (mkLA TI LM LI TM s lp dp mp Cn R) ltac:(unfold lzw_par; lia) HI ltac:(cbn [la_s]; lia)) as Hlpb.
cbn [la_lp] in Hlpb. unfold cap in Hlpb.
set (m := mrestrict (w_H W7) memT) in *.
assert (Pimg : forall i, 0 <= i < z_nP cx -> YP0c.present m (z_img cx + i)).
{ intros i Hi. destruct (Hbipres (z_img cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem1 trasegs m (z_img cx + s1)) as (C & HCv & HC); [apply Pimg; lia|]. change (2 ^ 8) with 256 in HCv.
assert (Plc : forall i, 0 <= i < 4096 -> YP0c.present m (z_lc cx + i)).
{ intros i Hi. destruct (Hlcpres (z_lc cx + i) ltac:(lia)) as [[Hh [bb0 Hb0]] _]. exists bb0. subst m. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem1 trasegs m (z_lc cx + q)) as (vLC & HvLCv & HvLC); [apply Plc; lia|]. change (2 ^ 8) with 256 in HvLCv.
destruct (LI_read (z_idl cx) (z_nP cx) _ q HI Hq) as [HqLI HvLI]. cbn [la_LI] in HqLI, HvLI.
destruct (LM_read (z_idl cx) (z_nP cx) _ q HI Hq) as [HqLM HvLM]. cbn [la_LM la_mp] in HqLM, HvLM.
set (vLI := nth (Z.to_nat q) LI 0) in *. set (vLM := nth (Z.to_nat q) LM 0) in *.
destruct HT as (ATI & ALM & ALI & ATM).
destruct (arr16_nthZ trasegs m (z_li cx) LI q ALI ltac:(lia) HqLI) as [VLI _].
destruct (arr16_nthZ trasegs m (z_lm cx) LM q ALM ltac:(lia) HqLM) as [VLM _].
fold vLI in VLI. fold vLM in VLM.
assert (DvLI : vLI = nth (Z.to_nat q) LI 0) by reflexivity. assert (DvLM : vLM = nth (Z.to_nat q) LM 0) by reflexivity.
clearbody vLI vLM.
remember (C <? z_idl cx) as e eqn:He.
assert (HeT : e = true -> C < z_idl cx) by (intros ->; symmetry in He; apply Z.ltb_lt in He; exact He).
assert (HeF : e = false -> z_idl cx <= C) by (intros ->; symmetry in He; apply Z.ltb_ge in He; exact He).
remember (e && negb (vLM =? 0)) as b eqn:Hb.
assert (HbT : b = true -> e = true /\ 1 <= vLM /\ C < z_idl cx).
{ intros ->. symmetry in Hb. apply andb_prop in Hb as [B1 B2]. rewrite B1 in HeT. specialize (HeT eq_refl).
destruct (Z.eqb_spec vLM 0); [discriminate|]. split; [exact B1|]. lia. }
assert (HbF : b = false -> e = true -> vLM = 0).
{ intros -> He1. rewrite He1 in Hb. cbn in Hb. symmetry in Hb. apply Bool.negb_false_iff in Hb. apply Z.eqb_eq in Hb. exact Hb. }
remember ((vLM - 1) * z_idl cx + C) as j eqn:Hj.
assert (HTMj : b = true -> (Z.to_nat j < length TM)%nat /\ 0 <= nth (Z.to_nat j) TM 0 < 4096 /\ j + 1 <= 2049 * z_idl cx /\ 0 <= j).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi).
destruct (TM_read (z_idl cx) (z_nP cx) (mkLA TI LM LI TM s lp dp mp Cn R) vLM C ltac:(lia) HI ltac:(cbn; lia) ltac:(lia)) as (T1 & T2 & T3).
cbn [la_TM] in T1, T2. subst j. split; [exact T1|]. split; [exact T2|]. split; [exact T3 |].
apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia | lia]. }
assert (Hj21 : b = true -> 2 * j + 2 <= 4098 * z_idl cx /\ j < 2 ^ 20).
{ intros Hbt. destruct (HTMj Hbt) as (_ & _ & T3 & _). assert (2049 * z_idl cx <= 2049 * 256) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
remember (nth (Z.to_nat j) TM 0) as vTM eqn:HvTM.
assert (VTM : b = true -> val_mem trasegs m (z_tm cx + 2 * j) 2 vTM).
{ intros Hbt. destruct (HTMj Hbt) as (T1 & _ & _ & T4). rewrite HvTM. exact (proj1 (arr16_nthZ trasegs m (z_tm cx) TM j ATM T4 T1)). }
remember [Z_to_bv 64 C; Z_to_bv 64 (z_li cx + 2 * q); Z_to_bv 64 vLI; Z_to_bv 64 (z_lc cx + q); Z_to_bv 64 vLC;
Z_to_bv 64 (z_lm cx + 2 * q); Z_to_bv 64 vLM; Z_to_bv 64 (z_tm cx + 2 * j); Z_to_bv 64 vTM] as more eqn:Hmore.
remember (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) as E eqn:HE0.
assert (HE60 : ew E 60 = Z_to_bv 64 C) by (rewrite HE0, <- (Nat.add_0_r 60), (AE_more regs _ _ _ _ _ more 0), Hmore; reflexivity).
assert (HE61 : ew E 61 = Z_to_bv 64 (z_li cx + 2 * q)) by (rewrite HE0; change 61%nat with (60 + 1)%nat; rewrite (AE_more regs _ _ _ _ _ more 1), Hmore; reflexivity).
assert (HE62 : ew E 62 = Z_to_bv 64 vLI) by (rewrite HE0; change 62%nat with (60 + 2)%nat; rewrite (AE_more regs _ _ _ _ _ more 2), Hmore; reflexivity).
assert (HE63 : ew E 63 = Z_to_bv 64 (z_lc cx + q)) by (rewrite HE0; change 63%nat with (60 + 3)%nat; rewrite (AE_more regs _ _ _ _ _ more 3), Hmore; reflexivity).
assert (HE64 : ew E 64 = Z_to_bv 64 vLC) by (rewrite HE0; change 64%nat with (60 + 4)%nat; rewrite (AE_more regs _ _ _ _ _ more 4), Hmore; reflexivity).
assert (HE65 : ew E 65 = Z_to_bv 64 (z_lm cx + 2 * q)) by (rewrite HE0; change 65%nat with (60 + 5)%nat; rewrite (AE_more regs _ _ _ _ _ more 5), Hmore; reflexivity).
assert (HE66 : ew E 66 = Z_to_bv 64 vLM) by (rewrite HE0; change 66%nat with (60 + 6)%nat; rewrite (AE_more regs _ _ _ _ _ more 6), Hmore; reflexivity).
assert (HE67 : ew E 67 = Z_to_bv 64 (z_tm cx + 2 * j)) by (rewrite HE0; change 67%nat with (60 + 7)%nat; rewrite (AE_more regs _ _ _ _ _ more 7), Hmore; reflexivity).
assert (HE68 : ew E 68 = Z_to_bv 64 vTM) by (rewrite HE0; change 68%nat with (60 + 8)%nat; rewrite (AE_more regs _ _ _ _ _ more 8), Hmore; reflexivity).
pose proof (AE_sp regs cx lp dp mp regs0 more HFC) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HFC) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HFC) as HE27. pose proof (AE_idl regs cx lp dp mp regs0 more HFC) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE53. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE54.
pose proof (AE_li regs cx lp dp mp regs0 more) as HE56. pose proof (AE_lc regs cx lp dp mp regs0 more) as HE55.
pose proof (AE_tm regs cx lp dp mp regs0 more) as HE57. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE59.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE32.
rewrite <- HE0 in HE2, HE8, HE27, HE25, HE53, HE54, HE56, HE55, HE57, HE59, HE32.
assert (HE23 : ew E 23 = Z_to_bv 64 s1) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 23%bv 23) by reflexivity; exact H24).
assert (HE15 : ew E 15 = Z_to_bv 64 q) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 15%bv 15) by reflexivity; exact H13).
assert (HE11 : ew E 11 = Z_to_bv 64 (z_img cx + s1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 11%bv 11) by reflexivity; exact H11).
assert (HE28 : ew E 28 = Z_to_bv 64 (z_nP cx - s1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 28%bv 28) by reflexivity; exact H16).
assert (HE16 : ew E 16 = Z_to_bv 64 (z_nP cx - 1)) by (rewrite HE0, (AE_reg regs _ _ _ _ _ more 16%bv 16) by reflexivity; exact H16n).
assert (Hp0 : b = true -> 0 <= (vLM - 1) * z_idl cx <= j).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi).
assert (0 <= (vLM - 1) * z_idl cx) by (apply Z.mul_nonneg_nonneg; lia). rewrite Hj. lia. }
assert (HUY : b = true -> U E tin_Y = j).
{ intros Hbt. destruct (HbT Hbt) as (_ & Hm1 & HCi). destruct (HTMj Hbt) as (_ & _ & T3 & T4). specialize (Hj21 Hbt). specialize (Hp0 Hbt).
unfold tin_Y. rewrite (U_addw_small E _ (SOff 60 0) ((vLM - 1) * z_idl cx) C (U_mul_row64 E 66 25 vLM (z_idl cx) HE66 HE25 ltac:(lia) ltac:(lia))
(U_atom E 60 C HE60 ltac:(lia))) by lia. lia. }
assert (HS1 : st_ok trasegs E (ss_tin0 e b) (mkst regs (Z_to_bv 64 PC_INNER) m (seg_rom trasegs))).
{ unfold ss_tin0. rewrite HE0. apply (alzw_st_ok cx regs regs0 lp dp mp more m PC_INNER asr_fix false false); rewrite <- ?HE0.
- exact HCX. - exact HRG. - exact HFC. - exact HG. - exact HSL. - exact HSS. - exact HFR.
- intros X0; discriminate X0. - intros X0; discriminate X0.
- lia. - lia. - lia.
- rewrite HE0. apply (regs_ok_fix regs cx); [exact HFC | lia | lia].
- destruct b; vm_compute; reflexivity.
- unfold tin_regions. apply Forall_app. split.
+ constructor.
{ unfold region_ok, tin_pix. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE11, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply chunk_ok_val; [| | cbn; lia | rewrite Z.add_0_r; exact HC]; [|change (2 ^ (8 * Z.of_N 1)) with 256; lia].
cbn [sv_denot]. rewrite HE60, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
constructor. { eapply (region_ok_reg16 _ E m 61 62 false (z_li cx + 2 * q) vLI HE61 HE62); [lia | lia | lia | exact VLI | intros X0; discriminate X0]. }
constructor. { eapply (region_ok_reg8 _ E m 63 64 false (z_lc cx + q) vLC HE63 HE64); [lia | lia | lia | exact HvLC | intros X0; discriminate X0]. }
constructor. { eapply (region_ok_reg16 _ E m 65 66 false (z_lm cx + 2 * q) vLM HE65 HE66); [lia | lia | lia | exact VLM | intros X0; discriminate X0]. }
constructor.
+ destruct b; [|constructor]. destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
apply Forall_cons; [|apply Forall_nil].
apply (region_ok_reg16 _ E m 67 68 false (z_tm cx + 2 * j) vTM HE67 HE68); [lia | lia | lia | exact (VTM eq_refl) | intros X0; discriminate X0].
-
unfold tin_regions. destruct b.
+ destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, tin_pix, reg8, reg16, actx_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE8, HE11, HE61, HE63, HE65, HE67, !unsigned_lit_small by lia.
split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 3%nat 6%nat; lia|].
split; [septac HSEP 2%nat 6%nat; lia|]. split; [septac HSEP 5%nat 6%nat; lia | exact I].
+ cbn [all_disjoint app]; unfold extent_disjoint, tin_pix, reg8, reg16, actx_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE8, HE11, HE61, HE63, HE65, !unsigned_lit_small by lia.
split; [septac HSEP 6%nat 7%nat; lia|]. split; [septac HSEP 4%nat 6%nat; lia|]. split; [septac HSEP 3%nat 6%nat; lia|].
split; [septac HSEP 2%nat 6%nat; lia | exact I].
-
unfold tin_regions. destruct b.
+ destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [all_disjoint app]; unfold extent_disjoint, tin_pix, reg8, reg16, astk_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE2, HE11, HE61, HE63, HE65, HE67, !unsigned_lit_small by lia. repeat split; lia.
+ cbn [all_disjoint app]; unfold extent_disjoint, tin_pix, reg8, reg16, astk_region; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val app].
rewrite HE2, HE11, HE61, HE63, HE65, !unsigned_lit_small by lia. repeat split; lia.
- unfold tin_regions. destruct b.
+ destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, tin_pix, reg8, reg16; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite HE11, HE61, HE63, HE65, HE67, !unsigned_lit_small by lia.
split; [split; [septac HSEP 4%nat 7%nat; lia | split; [septac HSEP 3%nat 7%nat; lia | split; [septac HSEP 2%nat 7%nat; lia | split; [septac HSEP 5%nat 7%nat; lia | exact I]]]]|].
split; [split; [septac HSEP 3%nat 4%nat; lia | split; [septac HSEP 2%nat 4%nat; lia | split; [septac HSEP 4%nat 5%nat; lia | exact I]]]|].
split; [split; [septac HSEP 2%nat 3%nat; lia | split; [septac HSEP 3%nat 5%nat; lia | exact I]]|].
split; [split; [septac HSEP 2%nat 5%nat; lia | exact I]|]. split; exact I.
+ cbn [pairwise_disjoint all_disjoint app]; unfold extent_disjoint, tin_pix, reg8, reg16; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite HE11, HE61, HE63, HE65, !unsigned_lit_small by lia.
split; [split; [septac HSEP 4%nat 7%nat; lia | split; [septac HSEP 3%nat 7%nat; lia | split; [septac HSEP 2%nat 7%nat; lia | exact I]]]|].
split; [split; [septac HSEP 3%nat 4%nat; lia | split; [septac HSEP 2%nat 4%nat; lia | exact I]]|].
split; [split; [septac HSEP 2%nat 3%nat; lia | exact I]|]. split; exact I.
- unfold tin_facts. apply atoms_ok_app.
+ cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE23, HE28, HE15, HE11, HE60, HE61, HE62, HE63, HE64, HE65, HE66, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rli3].
* apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists q; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rlm3].
+ destruct b; [|exact I]. destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [atoms_ok]. unfold afact_ok, APTR. cbn [af_lo af_hi af_al2].
rewrite HE67, HE68, !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
repeat split; try lia.
apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [| exists j; lia].
apply (Z.divide_trans _ 16); [exists 8; reflexivity|]. apply Z.mod_divide; [lia | exact Rtm3].
- unfold tin_conds. cbn [conds_ok]. split; [|exact I].
destruct e.
+ specialize (HeT eq_refl). apply (cond_ltu E 60 0 25 0 C (z_idl cx) HE60 HE25); lia.
+ specialize (HeF eq_refl). apply (cond_geu E 60 0 25 0 C (z_idl cx) HE60 HE25); lia.
- unfold tin_alias. cbn [alias_ok app]. split; [|split; [|split]].
+ apply (alias_b2i' E 56 15 61 (z_li cx) q HE56 HE15 HE61); lia.
+ apply (alias_add E 55 15 63 (z_lc cx) q HE55 HE15 HE63); lia.
+ apply (alias_b2i' E 54 15 65 (z_lm cx) q HE54 HE15 HE65); lia.
+ destruct b; [|exact I]. destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl).
cbn [alias_ok]. split; [|exact I].
apply (alias_base_sll1 E 57 67 tin_Y (z_tm cx) j HE57 (HUY eq_refl) HE67); lia. }
pose proof (ast_ok_set_reg E _ (mkst regs (Z_to_bv 64 PC_INNER) m (seg_rom trasegs)) 17%bv (SOff 11 0) HS1 eq_refl
ltac:(cbn [sv_denot ms_regs mkst]; rewrite HE11, Z.add_0_r, unsigned_lit_small by lia; symmetry; exact H17)) as HS.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_tin0 alzw_ss] in HS.
change (mkst regs (Z_to_bv 64 PC_INNER) m (seg_rom trasegs)) with (restrict (w_H W7) (mkst regs (Z_to_bv 64 PC_INNER) memT (seg_rom trasegs))) in HS.
shok_auto SHOK (SOff 27 0) E (mrestrict (w_H W7) (ms_mem (mkst regs (Z_to_bv 64 PC_INNER) memT (seg_rom trasegs)))).
change memT with (ms_mem (mkst regs (Z_to_bv 64 PC_INNER) memT (seg_rom trasegs))) in HJ.
clear Pimg Plc Hbipres Hlcpres.
Local Ltac obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 vpix vli vlc vlm vtm :=
try (oblk HJ HBi HE11 HE27 vpix); try (oblk HJ HBli HE61 HE27 vli); try (oblk HJ HBlc HE63 HE27 vlc);
try (oblk HJ HBlm HE65 HE27 vlm); try (oblk HJ HBtm HE67 HE27 vtm);
try (lazymatch goal with HBgx : In (z_ctx ?cxx, 72) _, HE8x : ew _ 8 = Z_to_bv 64 (z_ctx ?cxx) |- range_addressable _ _ (U _ (SOff 8 _)) _ =>
oblk HJ HBgx HE8x HE27 (z_ctx cxx) end).
Local Ltac memro :=
lazymatch goal with HFx : frame_of _ _ _ (ms_mem _) |- _ => mem_eq_ro HFx end;
try match goal with H : frame_of _ _ _ _ |- _ => clear H end; try match goal with H : mem_grows _ _ |- _ => clear H end.
Local Ltac ucond := match goal with Hc : branch_taken _ _ _ = _ |- _ => aUcond Hc end.
Local Ltac leaf HS HJ HE0 HFC o :=
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl); cbn [ss_pc];
apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- exists regs' md' oo, mkCfg (mkst ?rg _ _ _) ?mdx = _ /\ _ => exists rg, mdx, o end;
split; [reflexivity|]; split; [exact HJ|];
split; [ lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 => lazymatch type of HE0 with ?E0 = _ =>
eapply (alzw_regs_core_after E0 E1 ss1 ms1 _ _ _ HS); [vm_compute; reflexivity | intros nn Hnn; rewrite ?ew_ewset_other by lia; reflexivity | exact HE0 | exact HFC | lia | lia] end end
| unfold tio_post, tin_pre, tmiss_pre; cbn [la_LI la_LM] ].
Local Ltac regs_tac HS :=
repeat match goal with |- _ /\ _ => split end;
lazymatch goal with
| |- getr (ms_regs _) 24%bv = w64 (2 * ?qq) =>
let R := fresh "R" in
rregU HS (24%bv : bv 5) (2 * qq)
ltac:(apply (U_sll1_small _ (SOff 15 0) qq);
[ apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; assumption | lia] | lia | lia ]) R;
exact R
| |- getr (ms_regs _) ?r = _ => aregv HS r
| |- val_mem _ _ _ _ _ => assumption
| |- _ => try lia
end.
Local Ltac found HS HJ SHOK HE0 HFC obtac child :=
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obtac; [awr_ok_tac|]; memro;
srr_branch_tok tratbl_lib_ok HS SHOK Bspan;
[ aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_INNER; obtac; [awr_ok_tac|]; memro; ucond;
leaf HS HJ HE0 HFC (TIO_cont child)
| aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_EMITC; obtac; [awr_ok_tac|]; memro; ucond;
leaf HS HJ HE0 HFC (TIO_emitc child) ].
Local Ltac lm_subtree b HS HJ SHOK HE0 HFC obtac vTM C :=
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obtac; [awr_ok_tac|]; memro;
srr_branch_tok tratbl_lib_ok HS SHOK Bspan;
[
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_MISS; obtac; [awr_ok_tac|]; memro; ucond;
leaf HS HJ HE0 HFC (TIO_miss C)
| ucond;
lazymatch b with
| false => exfalso; lia
| true => aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obtac; [awr_ok_tac|]; memro;
srr_branch_tok tratbl_lib_ok HS SHOK Bspan;
[ aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_MISS; obtac; [awr_ok_tac|]; memro; ucond;
leaf HS HJ HE0 HFC (TIO_miss C)
| ucond; found HS HJ SHOK HE0 HFC obtac vTM ]
end ].
destruct b.
- destruct (HbT eq_refl) as (He1 & Hm1 & HCi). destruct e; [|discriminate He1]. specialize (HeT eq_refl).
destruct (HTMj eq_refl) as (T1 & T2 & T3 & T4). specialize (Hj21 eq_refl). specialize (Hp0 eq_refl).
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j); [awr_ok_tac|].
memro.
srr_branch_tok tratbl_lib_ok HS SHOK Bspan.
+
ucond.
lm_subtree true HS HJ SHOK HE0 HFC ltac:(obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j)) vTM C; regs_tac HS.
+ ucond.
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j); [awr_ok_tac|].
memro.
srr_branch_tok tratbl_lib_ok HS SHOK Bspan.
*   ucond.
found HS HJ SHOK HE0 HFC ltac:(obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j)) vLI; regs_tac HS.
*   ucond.
lm_subtree true HS HJ SHOK HE0 HFC ltac:(obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j)) vTM C; regs_tac HS.
- destruct e.
2:{
specialize (HeF eq_refl).
aj_run_to_tok tratbl_lib_ok HS HJ SHOK Bspan PC_EIDX; obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j); [awr_ok_tac|].
memro. leaf HS HJ HE0 HFC TIO_eidx. exact I. }
specialize (HeT eq_refl). specialize (HbF eq_refl eq_refl).
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j); [awr_ok_tac|].
memro.
srr_branch_tok tratbl_lib_ok HS SHOK Bspan.
+ ucond.
lm_subtree false HS HJ SHOK HE0 HFC ltac:(obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j)) vTM C; regs_tac HS.
+ ucond.
aj_run_tok tratbl_lib_ok HS HJ SHOK Bspan; obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j); [awr_ok_tac|].
memro.
srr_branch_tok tratbl_lib_ok HS SHOK Bspan.
* ucond.
found HS HJ SHOK HE0 HFC ltac:(obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j)) vLI; regs_tac HS.
* ucond.
lm_subtree false HS HJ SHOK HE0 HFC ltac:(obls HJ HBi HBli HBlc HBlm HBtm HE11 HE61 HE63 HE65 HE67 HE27 (z_img cx + s1) (z_li cx + 2 * q) (z_lc cx + q) (z_lm cx + 2 * q) (z_tm cx + 2 * j)) vTM C; regs_tac HS.
all: match goal with |- ?g => idtac "INNER-LEFT" g end.
Qed.
End S.
End a.
