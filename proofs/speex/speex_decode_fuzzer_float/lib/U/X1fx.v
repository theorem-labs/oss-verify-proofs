(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf X1bs X1c2 X1bq X1bu X1cc X1cb.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m5 X1go. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1nq X1mc X1fy.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1fs.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1r3 X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac slia ::= nb_unbox_junk; cbv delta [SBSTATE_SIZEOF HOUT_BYTES]; lost_conj.

Lemma lost_fp_sub : forall (s : sbd_state bptr) (S OUT lo usp : Z) (a : sb_addrs),
sub_fp [(lo, usp); (OUT, OUT + 8000); (S, S + 160); (a_msp a, a_msp a + 64); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)]
((lo, usp) :: (OUT, OUT + HOUT_BYTES) :: blocks_ivs (sb_blocks s S a)).
Proof.
intros. unfold sub_fp, sb_blocks, blocks_ivs, SBSTATE_SIZEOF, HOUT_BYTES. cbn [map blk_addr blk_size fst snd outside].
unfold outside. cbn. intros x H. tauto.
Qed.

Section F.
Context {RCEIL : RunCeiling}.
Hypothesis H_iir : iir_mem16_8_stmt.
Hypothesis H_qmf : qmf_synth_stmt.

#[using="H_iir H_qmf"] Lemma sb_decode_lost_proof : sb_decode_lost_stmt.
Proof.
unfold sb_decode_lost_stmt. intros until m.
intros SC JOK INV BUFS OUTA LOUT LAP ND LBR CEILO CEIL AOS ST LO SP63 -> -> -> -> MI FRM OUT4.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as Hmode Hfs Hffs Hsfs Hnbs Hlpc Hfirst Hrate Henh Hesm Hsid Hisv | sf_fb; destruct sfP_ as (Hmode & Hfs & Hffs & Hsfs & Hnbs & Hlpc & Hfirst & Hrate & Henh & Hesm & Hsid & Hisv) ].
pose proof JOK as sfP_; first [ sf_destruct 10%nat sfP_ as Lp1 Lp2 Lg0 Lg1 Lexc Loq Liq Lmsp Lpg Ler | sf_fb; destruct sfP_ as (Lp1 & Lp2 & Lg0 & Lg1 & Lexc & Loq & Liq & Lmsp & Lpg & Ler) ].
unfold SBLOST_DEPTH in LO. unfold A_sb_decode_lost. unfold HOUT_BYTES in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL', CEILO.
assert (HFS : nl (sbd_frame_size s = 160 \/ sbd_frame_size s = 320)) by (rewrite Hfs; destruct Hmode as [-> | ->]; cbn; apply nl_i; auto).
assert (BFS : 160 <= sbd_frame_size s <= 320) by (pose proof (nl_e _ HFS); lia).
assert (BSFS : 40 <= sbd_subframeSize s <= 80) by (rewrite Hsfs; destruct Hmode as [-> | ->]; cbn; lia).
clear Hmode.
first [ pose proof (sb_ranges s S a LBR) as sfP_; sf_destruct 9%nat sfP_ as RS RG0 RG1 REX ROQ RIQ RPG RER RMS | sf_fb; destruct (sb_ranges s S a LBR) as (RS & RG0 & RG1 & REX & ROQ & RIQ & RPG & RER & RMS) ].

assert (LS : 0 < S /\ S + 160 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RS; lia).
assert (LG0 : 0 < a_g0 a /\ a_g0 a + 256 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RG0; lia).
assert (LG1 : 0 < a_g1 a /\ a_g1 a + 256 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RG1; lia).
assert (LEX : 0 < a_exc a /\ a_exc a + 4 * sbd_subframeSize s <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in REX; lia).
assert (LOQ : 0 < a_oq a /\ a_oq a + 32 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in ROQ; lia).
assert (LIQ : 0 < a_iq a /\ a_iq a + 32 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RIQ; lia).
assert (LPG : 0 < a_pg a /\ a_pg a + 16 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RPG; lia).
assert (LER : 0 < a_er a /\ a_er a + 16 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RER; lia).
assert (LMS : 0 < a_msp a /\ a_msp a + 64 <= alloc_ceiling) by (unfold rblock_range, alloc_ceiling in RMS; lia).
pose proof (rbr_al _ _ RS) as [S8 _]. pose proof (rbr_al _ _ RIQ) as [_ IQ4]. pose proof (rbr_al _ _ RMS) as [_ MS4].
pose proof (rbr_al _ _ RG0) as [_ G04]. pose proof (rbr_al _ _ RG1) as [_ G14].
clear RS REX ROQ RIQ RPG RER RMS.
pose proof (sb_pairs_apart s S a LAP ND) as PA.
first [ sf_destruct 36%nat PA as P01 P02 P03 P04 P05 P06 P07 P08 P12 P13 P14 P15 P16 P17 P18 P23 P24 P25 P26 P27 P28 P34 P35 P36 P37 P38 P45 P46 P47 P48 P56 P57 P58 P67 P68 P78 | sf_fb; destruct PA as (P01 & P02 & P03 & P04 & P05 & P06 & P07 & P08 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P23 & P24 & P25 & P26 & P27 & P28 & P34 & P35 & P36 & P37 & P38 & P45 & P46 & P47 & P48 & P56 & P57 & P58 & P67 & P68 & P78) ].
clear LAP ND LBR.

unfold apart in AOS.
pose proof BUFS as sfP_; first [ sf_destruct 8%nat sfP_ as G0C G1C EXC OQC IQC MSPC PGC ERC | sf_fb; destruct sfP_ as (G0C & G1C & EXC & OQC & IQC & MSPC & PGC & ERC) ].
destruct (u8arr_as_f32 m OUT outb 2000%nat OUTA ltac:(lia)) as (ows & Lows & OWC). clear OUTA.
pose proof (rw_cells_bound _ _ _ _ SC) as BS. rewrite sb_cells_size in BS.
pose proof (munch_refl [(lo, bv_unsigned sp); (OUT, OUT + 8000); (S, S + 160); (a_msp a, a_msp a + 64); (a_g0 a, a_g0 a + 256); (a_g1 a, a_g1 a + 256)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.

pose proof (conj EXC (conj OQC (conj PGC ERC))) as HIDE. clear EXC OQC PGC ERC BUFS.
assert (USP64 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
unfold sb_cells in SC.
zstep. carve_frame 64%nat ST.
destruct (rw_cells_CB_C8s rsegs _ _ 8%nat _ FR) as (fw & Lfw & FR'); clear FR.
destruct fw as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|? ?]]]]]]]]]; cbn in Lfw; try lia. cbn [map] in FR'. rename FR' into FR.
do 7 zstep. do 4 zstep.

zstep. rewrite land7_mod8, S8. zstep. if_false_x. zstep. if_false_x.
zstep. rewrite sx32_small by (unfold int31; lia). zstep. zstep. zstep. zstep.

zstep. rewrite sx32_small by (unfold int31; lia). zstep. if_false_x.
do 15 zstep.
pose proof (rw_cells_bound _ _ _ _ OWC) as BO. rewrite cells_size_f32, Lows in BO.
rewrite (sgtz_mask (sbd_frame_size s)) by lia.
rewrite (land_m64 OUT) by lia. replace (0 <? OUT) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
chunk_splitk SC at 20%nat as SC1. chunk_splitk SC at 1%nat as SCL.
pose proof (u32arr_of_f32 rsegs _ _ _ OWC) as ARR. clear OWC.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (munch_refl [(OUT, OUT + 4 * Z.of_nat 2000%nat)] mc) as MUL; pose proof (wmono_refl rsegs mc) as WML;
call (lost_noise_loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z.to_nat (sbd_frame_size s)) 0 (sbd_frame_size s)
OUT S 2000%nat ows (sj_last_ener j) [] mc mc);
[ lia | lia | lia | lia | exact ARR | exact Lows | exact OUT4 | exact SCL | lia | lia | exact MUL | exact WML | exact MI | exact FRM | ] end.
clear MUL WML. try rename MI0 into MI. clear FRM.
match goal with H : u32arr rsegs _ OUT ?c, L : length ?c = 2000%nat |- _ => rename H into ARR2; rename L into Lcur; rename c into cur end.
match goal with H : rw_cells rsegs _ (S + 128) [C4 _] |- _ => rename H into SCL2 end.
match goal with H : frm0 ?f |- _ => rename H into FRM end.

chunk_cat SCL2 SC. chunk_cat SC1 SCL2. rename SC1 into SC.

zstep.

zstep. rewrite ?(land_m64 OUT) by lia.
bato 0x2fe74.
zstep. rewrite Hlpc. rewrite (sx32_lit 8) by lia. do 5 zstep.

pose proof (f32_of_u32arr rsegs _ _ _ ARR2) as XO. clear ARR2.
pose proof (f32_split rsegs _ _ cur (Z.to_nat (sbd_frame_size s)) ltac:(rewrite Lcur; lia) XO) as [XO1 XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (sbd_frame_size s)) cur) (Z.to_nat (sbd_frame_size s)) ltac:(rewrite length_skipn, Lcur; lia) XO2) as [XO2a XO3].
clear XO2 XO.
replace (OUT + 4 * Z.of_nat (Z.to_nat (sbd_frame_size s)) + 4 * Z.of_nat (Z.to_nat (sbd_frame_size s))) with (OUT + 8 * sbd_frame_size s) in XO3 by lia.
replace (OUT + 4 * Z.of_nat (Z.to_nat (sbd_frame_size s))) with (OUT + 4 * sbd_frame_size s) in XO2a by lia.
set (owsA := firstn (Z.to_nat (sbd_frame_size s)) cur) in *.
assert (LA : length owsA = Z.to_nat (sbd_frame_size s)) by (subst owsA; rewrite length_firstn, Lcur; lia).
set (owsB := firstn (Z.to_nat (sbd_frame_size s)) (skipn (Z.to_nat (sbd_frame_size s)) cur)) in *.
assert (LB : length owsB = Z.to_nat (sbd_frame_size s)) by (subst owsB; rewrite length_firstn, length_skipn, Lcur; lia).
set (owsC := skipn (Z.to_nat (sbd_frame_size s)) (skipn (Z.to_nat (sbd_frame_size s)) cur)) in *.
assert (LC : Z.of_nat (length owsC) = 2000 - 2 * sbd_frame_size s) by (subst owsC; rewrite !length_skipn, Lcur; lia).
clearbody owsA owsB owsC. clear Lcur.

pose proof (f32_split rsegs _ _ (sj_msp j) 8%nat ltac:(rewrite Lmsp; lia) MSPC) as [BM1 BM2]. clear MSPC.
replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) in BM2 by lia.
assert (LM1 : length (firstn 8 (sj_msp j)) = 8%nat) by (rewrite length_firstn, Lmsp; reflexivity).
assert (LM2 : length (skipn 8 (sj_msp j)) = 8%nat) by (rewrite length_skipn, Lmsp; reflexivity).
call (H_iir (OUT + 4 * sbd_frame_size s) (a_iq a) (OUT + 4 * sbd_frame_size s) (a_msp a) (sbd_frame_size s) lo
owsB (sj_iq j) owsB (firstn 8 (sj_msp j)) stk8);
[ exact XO2a | exact LB | exact IQC | exact Liq | exact BM1 | exact LM1 | left; split; reflexivity | lia
| unfold apart; lost_lia | unfold apart; lost_lia | unfold apart; lost_lia | unfold apart; lost_lia
| lia | clear - OUT4; Z.div_mod_to_equations; lia | lia | exact IQ4 | lia | clear - OUT4; Z.div_mod_to_equations; lia | lia | exact MS4
| rewrite USP64; exact ST | rewrite USP64; unfold IIR_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USP64; lia
| rewrite USP64; unfold apart; lost_lia | rewrite USP64; unfold apart; lost_lia
| rewrite USP64; unfold apart; lost_lia | rewrite USP64; unfold apart; lost_lia
| first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
| first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia] | first [reflexivity | f_equal; lia]
| first [reflexivity | f_equal; lia] | exact MI | exact FRM | ].
cbv beta delta [callR]. try rename MI0 into MI. clear FRM. try clear ST.
match goal with H : stk rsegs _ lo _ |- _ => rename H into ST end. rewrite ?USP64 in ST.
match goal with H : rw_cells _ _ (OUT + 4 * sbd_frame_size s) (f32 ?w), L : length ?w = _ |- _ => rename H into XO2b; rename L into LB2; rename w into owsB2 end.
match goal with H : rw_cells _ _ (a_msp a) (f32 ?w), L : length ?w = _ |- _ => rename H into BM1b; rename L into LM1b; rename w into msp1 end.
match goal with H : frm0 ?f |- _ => rename H into FRM end.
try clear XO2a; try clear LB; try clear BM1; try clear LM1.

pose proof (f32_join rsegs _ _ _ _ XO1 ltac:(rewrite LA; replace (OUT + 4 * Z.of_nat (Z.to_nat (sbd_frame_size s))) with (OUT + 4 * sbd_frame_size s) by lia; exact XO2b)) as XOY. clear XO1 XO2b.
assert (LY : length (owsA ++ owsB2) = Z.to_nat (2 * sbd_frame_size s)) by (rewrite length_app, LA, LB2; lia).
pose proof (f32_join rsegs _ _ _ _ BM1b ltac:(rewrite LM1b; replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) by lia; exact BM2)) as MSPC. clear BM1b BM2.
assert (Lmsp' : length (msp1 ++ skipn 8 (sj_msp j)) = 16%nat) by (rewrite length_app, LM1b, LM2; reflexivity).

zstep. rewrite sx32_small by (unfold int31; lia).
bato 0x2feb4.
zstep. rewrite Hffs. rewrite sx32_small by (unfold int31; lia).
do 9 zstep.
chunk_splitk FR at 1%nat as FR8.
call (H_qmf OUT (2 * sbd_frame_size s) (a_g0 a) (a_g1 a) lo (owsA ++ owsB2) (sj_g0 j) (sj_g1 j) stk8);
[ exact XOY | exact LY | pose proof (nl_e _ HFS); lia | exact G0C | exact Lg0 | exact G1C | exact Lg1
| rewrite USP64; exact FR8
| rewrite USP64; exact ST | rewrite USP64; unfold QMF_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USP64; lia
| unfold NB_GLOBALS_TOP; lia
| unfold rblock_range, NB_GLOBALS_TOP in RG0 |- *; lia | unfold rblock_range, NB_GLOBALS_TOP in RG1 |- *; lia
| rewrite USP64; unfold apart; lost_lia | rewrite USP64; unfold apart; lost_lia | rewrite USP64; unfold apart; lost_lia
| unfold apart; lost_lia | unfold apart; lost_lia | unfold apart; lost_lia
| reflexivity | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| exact MI | exact FRM | exact OUT4 | lia | exact G04 | lia | exact G14 | ].
cbv beta delta [callR]. try rename MI0 into MI. clear FRM. try clear ST.
match goal with H : rw_cells _ _ OUT (f32 ?w), L : length ?w = _ |- _ => rename H into XOY2; rename L into LY2; rename w into owsY end.
match goal with H : rw_cells _ _ (a_g0 a) (f32 ?w), L : length ?w = _ |- _ => rename H into G0C2; rename L into Lg02; rename w into g0' end.
match goal with H : rw_cells _ _ (a_g1 a) (f32 ?w), L : length ?w = _ |- _ => rename H into G1C2; rename L into Lg12; rename w into g1' end.
match goal with H : frm0 ?f |- _ => rename H into FRM end.
match goal with H : stk rsegs _ lo _ |- _ => rename H into ST end. rewrite USP64 in ST.
try clear XOY LY G0C G1C.
pose proof (f32_join rsegs _ _ _ _ XOY2 ltac:(rewrite LY2; replace (OUT + 4 * Z.of_nat (Z.to_nat (2 * sbd_frame_size s))) with (OUT + 8 * sbd_frame_size s) by lia; exact XO3)) as XO. clear XOY2 XO3.
assert (Lows' : length (owsY ++ owsC) = 2000%nat) by (rewrite length_app, LY2; lia).

zstep. if_false_x. zstep.
do 7 zstep. zstep. chunk_cat FR8 FR. release_frame FR8 ST (bv_unsigned sp). zstep.

first [ sf_destruct 4%nat HIDE as EXC OQC PGC ERC | sf_fb; destruct HIDE as (EXC & OQC & PGC & ERC) ].
pose proof (rw_cells_transport rsegs _ _ _ _ _ EXC MU WM ltac:(cbn [disjoint_from]; simpl_sizes; slia)) as EXC2.
pose proof (rw_cells_transport rsegs _ _ _ _ _ OQC MU WM ltac:(cbn [disjoint_from]; simpl_sizes; slia)) as OQC2.
pose proof (rw_cells_transport rsegs _ _ _ _ _ PGC MU WM ltac:(cbn [disjoint_from]; simpl_sizes; slia)) as PGC2.
pose proof (rw_cells_transport rsegs _ _ _ _ _ ERC MU WM ltac:(cbn [disjoint_from]; simpl_sizes; slia)) as ERC2.
clear EXC OQC PGC ERC.
pose proof (f32_as_u8arr _ _ _ XO) as [XOU LOU]. rewrite Lows' in LOU.
apply evt_done. unfold sb_decode_lost_post.
match goal with SCx : rw_cells rsegs ?mm S (_ :: _ :: _), _ : mem_inv rsegs ?mm |- _ =>
lazymatch type of SCx with context [C4 (sj_last_ener j) :: C4 ?sdw :: _] =>
eexists _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, mm,
(SBJ (sj_last_ener j) sdw (sj_pad1 j) (sj_pad2 j) g0' g1' (sj_exc j) (sj_oq j) (sj_iq j) (msp1 ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)),
(cells_bytes (f32 (owsY ++ owsC))) end end.
split; [unfold callR; cbn [c_t0 c_t1 c_t2 c_a1 c_a2 c_a3 c_a4 c_a5 c_a6 c_a7 c_t3 c_t4 c_t5 c_t6]; reflexivity|].
split. { eapply munch_weaken; [apply lost_fp_sub | unfold HOUT_BYTES; exact MU]. }
split; [exact WM|]. split; [exact MI|]. split; [exact FRM|]. split; [exact ST|].
split. { unfold sb_cells. cbn [set_sbd_first sbd_mode sbd_full_frame_size sbd_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled sbd_innov_save sbd_encode_submode sbd_submodeID sb_isave_ptr
sj_last_ener sj_seed sj_pad1 sj_pad2].
unfold sb_isave_ptr in SC. exact SC. }
split. { unfold sb_junk_ok. cbn [sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er set_sbd_first sbd_subframeSize].
repeat split; assumption. }
split. { unfold sb_bufs. cbn [sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].
exact (conj G0C2 (conj G1C2 (conj EXC2 (conj OQC2 (conj IQC (conj MSPC (conj PGC2 ERC2))))))). }
split; [exact XOU| unfold HOUT_BYTES; lia].
Qed.

#[using="H_iir H_qmf"] Lemma sb_decode_lost_proofX : sb_decode_lost_stmtX.
Proof. exact sb_decode_lost_proof. Qed.
End F.

Lemma sb_decode_lost_closed {RCEIL : RunCeiling} : iir_mem16_8_stmt -> sb_decode_lost_stmt.
Proof. intros HI. exact (sb_decode_lost_proof HI X1fs.qmf_synth_proof). Qed.
