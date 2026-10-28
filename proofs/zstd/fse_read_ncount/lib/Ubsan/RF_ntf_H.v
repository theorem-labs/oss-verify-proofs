(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast MallocModel_B F_ntf_B F_ntf_F F_ntf_H MallocKit_A3 MallocKit_B3.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_free_A RF_ntf_A RF_ntf_C.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation PHEAD := (Z_to_bv 64 (RCTX + sc * 8)).
Definition RAT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom usegs).
Definition rentry_cases (ms' : machine_state) : Prop :=
(ntf_cond st g i = false /\ mask <> 0 /\
exists t0 t1 t2 a0 a2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0x15954 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD a0 SELF a2 a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = false /\ mask = 0 /\
exists t0 t1 t2 a3 a5 a6 a7 s2x t3 t4 t5 t6,
RAT 0x15738 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) a3 G28 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = None /\
exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x157fc (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G a1 a2 a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x15790 (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD a3 a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
\/
(ntf_cond st g i = true /\ sc < 48 /\
exists nx, m_next mr = Some nx /\ nx <> g /\
exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6,
RAT 0x1570c (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G PHEAD HD (Z_to_bv 64 (conc st nx)) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms').
End POST.
Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists m1 junk,
rentry_cases ra sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
/\ stk usegs m1 lo (bv_unsigned sp + -96)
/\ rw_cells usegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra)
/\ rmrep st m1.
#[using="Type"] Lemma meta_word_sc52 mr : mw_ok mr ->
Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (meta_word mr) 52))) 58 = m_sizeclass mr.
Proof.
intros MW. pose proof (meta_word_range mr MW) as MWR. pose proof MW as (LI & FB & SCR & ML).
Local Ltac2 Set LiaHints.tbl := fun () => "0080=11427672333.811601703795.822069199602.833381437612.845081068754.856862877715.863348610430.88929260062.8 00000100200300400500600=00HSSSSSSS2LI2FBS2LI2FB3SCR".
rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. unfold meta_word.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) * 2 ^ 52)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2^52 + m_maplen mr * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) * 2 ^ 52) with ((m_last_idx mr + 32 * m_freeable mr) * 2^52 + m_sizeclass mr * 2^58) by lia.
rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma meta_word_mod32 mr : mw_ok mr -> meta_word mr mod 32 = m_last_idx mr.
Proof.
intros MW. pose proof MW as (LI & FB & SCR & ML). unfold meta_word.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=22703930437.746609756872.768569543065.7000001002006SSS2LI".
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -96)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation G28 := (Z_to_bv 64 (conc st g + 28)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation GUARD := (Z_to_bv 64 RSSP_GUARD).
Local Notation CTXW := (Z_to_bv 64 RCTX).
Local Notation POST := (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).
Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv usegs m.
Hypothesis LO : ATOP <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 96.
Definition rmid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
/\ stk usegs m1 lo (bv_unsigned sp + -96) /\ rw_cells usegs m1 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) /\ rmrep st m1.
#[using="i EH"] Lemma rmaskw_zero : maskw = 0 <-> mask = 0.
Proof. apply lor_sxv_zero; [apply (eh_freed _ _ _ EH) | apply (eh_avail _ _ _ EH)]. Qed.
#[using="Type"] Lemma rmaskw_range : 0 <= maskw < 2^64.
Proof. apply lor_range64; apply sxv_range. Qed.
Ltac rpost_common MU WM MI ST FR MR m1 junk :=
apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].
#[using="EH"] Lemma rntf_notall : forall (t0 t1 t2 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> ntf_cond st g i = false ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15730) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros (MU & WM & MI & ST & FR & MR) HC.
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof (rmeta_slot_bounds st m1 g MR (eh_slot _ _ _ EH)) as (GB0 & GB1 & GB2 & _). atop_facts.
st1. rewrite ?(unsigned_lit (conc st g)) by lia.
st1. Local Ltac2 Set LiaHints.tbl := fun () => "0040>16077671799.5635495598355.5667019247552.568931259039.56 00000100200:00@FSS4MWR'1KS4MWR'".
if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; unmask64 K.
-
rpost_common MU WM MI ST FR MR m1 junk.
left. split; [exact HC|]. split; [intros E; apply K, MZ, E|].
do 14 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
-
assert (M0 : mask = 0) by (apply MZ; lia).
rpost_common MU WM MI ST FR MR m1 junk.
right; left. split; [exact HC|]. split; [exact M0|].
do 12 eexists. unfold RAT, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="EH"] Lemma rntf_fge : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> okay_to_free st g = true ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 a5 a6 a7 CTXW s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x156e8) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros (MU & WM & MI & ST & FR & MR) HALL OKT.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
unfold RCTX in *. atop_facts.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
assert (HC : ntf_cond st g i = true) by (rewrite ntf_cond_unfold, HALLb, OKT; reflexivity).
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>16075583950.8020897545591.7729784416474.8034217400197.8144434640635.7944434640889.8148095868254.7749130514066.8152033399223.8052033474951.8259308628566.7559308628566.7959308628695.8059976465927.806700790536.81 00000900C00D00S00Z00a00e00i00n01301701>01F01O01PS3G503SCRS5ATOPR2B1SS3GB03GB15ATOPRS2N02N1S2N02N1S2B0S2K5S3G50S3G50S2K3S2N02K3S3G502K4S3G503SCRS".
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
rmeta_chunk MR MSL CH.
st1. clear CH.
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
- destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. lia. }
specialize (G50 HC ltac:(congruence)).
st1. st1. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. lia. }
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_active_read st m1 sc (wa (RCTX + 80 + 8 * sc)) MR ltac:(lia) eq_refl) as RDA. unfold RCTX in RDA.
replace (wa (324152 + 80 + 8 * sc)) with (Z_to_bv 64 (324152 + sc * 8 + 80)) in RDA by (unfold wa; f_equal; lia).
st1. clear RDA.
st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
+ pose proof (NINJ ltac:(lia)) as ->.
rpost_common MU WM MI ST FR MR m1 junk.
do 3 right; left. split; [exact HC|]. split; [exact NX|]. split; [lia|].
do 12 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
+ assert (NE : nx <> g) by (intros ->; apply K5; reflexivity).
rpost_common MU WM MI ST FR MR m1 junk.
do 4 right. split; [exact HC|]. split; [lia|]. exists nx. split; [exact NX|]. split; [exact NE|].
do 11 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
- st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. lia. }
rpost_common MU WM MI ST FR MR m1 junk.
do 2 right; left. split; [exact HC|]. split; [exact NX|].
do 14 eexists. unfold RAT, RCTX, RSSP_GUARD. cbv delta [mkR]. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="EH"] Lemma rntf_okchk : forall (t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 : word) m1 junk,
rmid_ctx m1 junk -> mask + bit i = mask_upto (m_last_idx mr) -> m_freeable mr <> 0 ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) a4 (Z_to_bv 64 (meta_word mr)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15638) fc None m1 (seg_rom usegs)).
Proof.
intros until junk. intros MC HALL FRNZ. pose proof MC as (MU & WM & MI & ST & FR & MR).
pose proof rmaskw_range as MWR'. pose proof rmaskw_zero as MZ.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR. pose proof (meta_word_lt4096 _ MW) as M4.
pose proof (rmeta_slot_bounds st m1 g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
atop_facts.
assert (HALLb : (mask + bit i =? mask_upto (m_last_idx mr)) = true) by (apply Z.eqb_eq; exact HALL).
Local Ltac2 Set LiaHints.tbl := fun () => "0140?1021090280.86  11264020429.10111899380396.99 15524707589.86 15526887604.84 16073326931.81 16073481288.86 16073486922.10116073539944.85 16075578389.84 16075578389.86 16075578774.85 16075583565.86 16075584200.78 16075585474.99 16088068200.85 20035158812.10020391243517.10020391243646.99 20897545591.93 21606382214.85 23834020845.99 24624355554.97 26912248502.86 29315069148.84 29709730541.97 29713640445.86 29784418006.99 30386944003.10132665339679.95 32813721440.86 34217400068.91 34217400068.95 34595564048.10034705803648.85 36424092992.76 36436663440.86 36438760653.86 36438760782.85 37657799404.78 39918411166.10040823396172.85 40829527628.85 42048681435.84 44434640760.95 48095868254.93 49130513939.95 49771033641.10051962820296.84 52033399602.78 52037199928.78 55860257713.84 55860257713.86 57685087760.84 59308628949.91 59310733137.86 59314955108.96 59963964939.79 59976464395.99 59976845609.80 63944815795.84 67098893166.99 67497085089.85 67507419553.85 6753670684.85  67788976708.96 67795291514.95 8569958523.99  00000100D00V00h01801=01A01E01T01X01\01d02702<02D02S02T02Y02k03C03D03V03i04;04<04Q04R04S04f04g05905V06306E06R06[06i07707E07P07b07c07d07e08:08L08^09009;09F09S09a09o0:40:J0:\0;00;A0;R0;c0;h0<:0<E0<P0<Q0<V0<[0<\SS2FB2ML3FRZ3MLF3K10S2FB2ML3FRZ3MLF2K8S2FB2ML3FRZ2SZ3MLFS2FB2ML3FRZ4MLNZS3MWRS2MLS2LIS3SCR2FB3FRZ2SZS2MLS2MLS2LI3MWRS2FB2ML3FRZ3MLF3GSRS3SCRS3SCR2LIS3MWR2FB3FRZ2SZSS3USGS2FB2ML3FRZ3MLF2BRS2FB2ML5ATOPR3FRZ3MLF2B1SS2FB2ML3FRZ3MLF2BRS2FB2ML3FRZ3MLF3SR'S2FB2ML3FRZ3MLF2K5SS2FB2ML3FRZ3MLF2Sa2SbSSS2FB2ML3FRZ3MLF3K10FS2FB2ML3FRZ3MLF2K5S2FB2ML3GB03GB15ATOPR3FRZ3MLFS2FB2ML3GB03GB15ATOPR3FRZ3MLFS2FB2ML3FRZ3MLF2K9S2FB3FRZ4MW5RS4FRNZ2FBS2FB2ML3FRZ2KmS2FB2ML3FRZ2KmS2LI2FB3FRZ2KlS2FB3FRZ2K2S2FB2ML3FRZ3MLF2K9SSSS2FB2ML3FRZ3MLF2N02N1S2FB2ML3FRZ3MLF2B0S2FB2ML3FRZ3MLF2K6S2LI2FB2ML3FRZ3MLFS2FB3FRZ2SZS2FB3FRZ2K2S2FB3FRZ4SC48S2FB2ML3FRZ2KmS2FB2ML3FRZ2KmS3MWRS2FB2ML3GB03FRZ3MLF2K6S2FB2ML3FRZ2Km3Km2S2FB2ML3FRZ3MLF2K71ES2FB3SCR3FRZ4SC48S2FB3SCR3FRZ4SC48S2FB3SCR3FRZ4SC48S3MWRS2FB2ML3FRZ3MLF2K8S2FB3FRZ2SZS2FB3FRZ2SZSS3SCRS3SCRS".
assert (FRZ : (m_freeable mr =? 0) = false) by (apply Z.eqb_neq; lia).
st1. st1. st1.
st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
{
eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ. replace (48 <=? sc) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
assert (SC48 : sc < 48) by lia. clear K2.
assert (NB48 : (48 <=? sc) = false) by (apply Z.leb_gt; lia).
specialize (USG SC48).
pose proof (size_class_range sc ltac:(lia)) as SZ.
assert (RS' : ov_read_bytes usegs m1 (Z_to_bv 64 (68784 + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))).
{ replace (Z_to_bv 64 (68784 + 2 * sc)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
st1. rewrite (meta_word_last_idx _ MW). st1. rewrite (meta_word_maplen _ MW). st1. st1.
assert (K690 : forall (t0' : word),
m_maplen mr <> 0 ->
evt usegs POST
(MS (mkR ra sp' gp tp t0' t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (get_stride mr)) (Z_to_bv 64 68784) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 324152) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1568c) fc None m1 (seg_rom usegs))).
{ intros t0' MLNZ.
assert (MLF : (m_maplen mr =? 0) = false) by (apply Z.eqb_neq; exact MLNZ).
assert (GSR : 0 < get_stride mr < 2^64).
{ unfold get_stride. destruct (m_last_idx mr =? 0), (m_maplen mr =? 0); cbn [andb negb]; unfold UNIT; lia. }
st1. rewrite ?(unsigned_lit sc), ?(Z.shiftl_mul_pow2 sc 1) by lia. change (2 ^ 1) with 2. st1.
replace (68784 + sc * 2) with (68784 + 2 * sc) by lia.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
st1. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia.
{ eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (get_stride mr <? UNIT * size_class sc) with true by (symmetry; apply Z.ltb_lt; unfold UNIT; lia). reflexivity. }
assert (STRF : (get_stride mr <? UNIT * size_class sc) = false) by (apply Z.ltb_ge; unfold UNIT; lia).
assert (OKF : okay_to_free st g =
if negb (optr_eqb (m_next mr) (Some g)) then true
else if negb (is_bouncing sc st) then true
else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false).
{ rewrite okf_unfold, FRZ, NB48, STRF, MLF. reflexivity. }
rmeta_chunk MR MSL CH.
st1. clear CH.
assert (NXW : forall nx, m_next mr = Some nx -> 0 < conc st nx /\ conc st nx < 2^64 /\ (conc st nx = conc st g -> nx = g)).
{ intros nx Hnx. pose proof (HNX nx Hnx) as MSn. pose proof (rmeta_slot_bounds st m1 nx MR MSn) as (B0 & B1 & _).
split; [lia|]. split; [lia|]. intros E. apply (rconc_meta_inj st m1 g nx MR MSL MSn). exact E. }
destruct (m_next mr) as [nx|] eqn:NX; unfold pw; cbn [oconc]; unfold wz.
2:{ st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. 2:{ exfalso. lia. }
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF. reflexivity. }
destruct (NXW nx eq_refl) as (N0 & N1 & NINJ).
st1. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
{ assert (NE : nx <> g) by (intros ->; apply K6; reflexivity).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). rewrite OKF.
cbn [optr_eqb]. rewrite (aptr_eqb_neq nx g NE). reflexivity. }
pose proof (NINJ ltac:(lia)) as Enx. subst nx.
rewrite optr_eqb_refl in OKF. cbn [negb] in OKF.
st1. rewrite ?(unsigned_lit sc) by lia. st1.
st1. if_cases K7; zify_cond K7.
{ assert (NR : sc_in_seq_range sc = false) by (apply (proj1 (seq_range_test sc ltac:(lia))); exact K7).
unfold is_bouncing in OKF. rewrite NR in OKF. cbn [andb negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
assert (SR : sc_in_seq_range sc = true).
{ destruct (sc_in_seq_range sc) eqn:E; [reflexivity|]. exfalso. apply (proj2 (seq_range_test sc ltac:(lia))) in E. lia. }
assert (SR' : 7 <= sc < 39).
{ unfold sc_in_seq_range in SR. apply andb_true_iff in SR. destruct SR as [Sa Sb]. apply Z.leb_le in Sa. apply Z.ltb_lt in Sb. lia. }
unfold is_bouncing in OKF. rewrite SR in OKF. cbn [andb] in OKF.
st1.
pose proof (rmrep_bounces_read st m1 (sc - 7) (wa (RCTX + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB. unfold RCTX, wa in RDB.
pose proof (BND (sc - 7)) as BR.
replace (Z_to_bv 64 (324152 + 880 + (sc - 7))) with (Z_to_bv 64 (324152 + (sc + -7) + 880)) in RDB by (f_equal; lia).
st1. clear RDB. st1.
st1. if_cases K8; zify_cond K8; rewrite ?b8_unsigned, ?unsigned_lit in K8 by lia.
{ replace (100 <=? bounces st (sc - 7)) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [negb] in OKF.
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
replace (100 <=? bounces st (sc - 7)) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [negb] in OKF.
st1. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1.
pose proof (rmrep_usage_read st m1 sc (wa (RCTX + 464 + 8 * sc)) MR ltac:(lia) eq_refl) as RDU. unfold RCTX in RDU.
replace (wa (324152 + 464 + 8 * sc)) with (Z_to_bv 64 (324152 + sc * 8 + 464)) in RDU by (unfold wa; f_equal; lia).
st1. clear RDU.
st1. rewrite ?(unsigned_lit (m_last_idx mr)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8. st1. st1.
st1. if_cases K9; zify_cond K9; rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia.
{ replace (9 * (m_last_idx mr + 1) <=? usage st sc) with false in OKF by (symmetry; apply Z.leb_gt; lia). cbn [andb] in OKF.
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC). }
replace (9 * (m_last_idx mr + 1) <=? usage st sc) with true in OKF by (symmetry; apply Z.leb_le; lia). cbn [andb] in OKF.
st1. st1. if_cases K10; zify_cond K10; rewrite ?unsigned_lit in K10 by lia.
- replace (m_last_idx mr + 1 <? 20) with false in OKF by (symmetry; apply Z.ltb_ge; lia).
assert (HC : ntf_cond st g i = false) by (rewrite ntf_cond_unfold, HALLb, OKF; reflexivity).
eapply (rntf_notall _ t1 t2 _ _ _ _ _ t3 t4 t5 t6 m1 junk MC HC).
- replace (m_last_idx mr + 1 <? 20) with true in OKF by (symmetry; apply Z.ltb_lt; lia).
eapply (rntf_fge _ t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL). exact OKF. }
assert (K678 :
(m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt usegs POST
(MS (mkR ra sp' gp tp t0 t1 t2 s0 GUARD G SELF (Z_to_bv 64 sc) (Z_to_bv 64 maskw) (Z_to_bv 64 (m_last_idx mr)) (Z_to_bv 64 (meta_word mr)) (Z_to_bv 64 68784) (Z_to_bv 64 (m_maplen mr)) (Z_to_bv 64 324152) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x15674) fc None m1 (seg_rom usegs))).
{ intros COND.
assert (STR : get_stride mr = 16 * size_class sc).
{ unfold get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }
assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 _ MW). st1.
st1. try rewrite (Z.mod_small (size_class sc)) by lia.
st1. rewrite ?(unsigned_lit (size_class sc)), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- eapply (rntf_fge t0 t1 t2 _ _ _ _ t3 t4 t5 t6 m1 junk MC HALL).
rewrite okf_unfold, FRZ, NB48. cbn [orb].
replace (m_maplen mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
destruct (get_stride mr <? UNIT * size_class sc); reflexivity.
- replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 (get_stride mr)) by (rewrite STR; f_equal; lia).
apply K690. lia. }
st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
{ apply K678. left. lia. }
st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
{ apply K678. right. lia. }
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite land_pgmask by lia. rewrite (meta_word_pg _ MW). st1.
st1. if_cases Km2; zify_cond Km2; rewrite ?unsigned_lit in Km2 by lia. 2:{ exfalso. lia. }
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 (get_stride mr)).
2:{ unfold get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
apply K690. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="EH MI0 LO LOLE"] Lemma rntf_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st m -> stk usegs m lo (bv_unsigned sp) ->
evt usegs POST
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 G (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x155d4) fc None m (seg_rom usegs)).
Proof.
intros until t6. intros MR ST.
pose proof EH as [MSL MW AV FRD HI SC63 HNX HHD [BND USG] G50 G51 G1].
pose proof MW as (LI & FB & SCR & ML).
pose proof (meta_word_range _ MW) as MWR.
pose proof (rmeta_slot_bounds st m g MR MSL) as (GB0 & GB1 & GB2 & _).
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof rmaskw_range as MWR'.
pose proof MR as (_ & _ & (_ & _ & _ & G4 & G5) & _).
unfold RGOT_SSP, RSSP_GUARD in *. atop_facts. unfold wz in G4.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
st1. Local Ltac2 Set LiaHints.tbl := fun () => "00[0>11552300008.8011552300008.8211552300008.8311805467289.8011805467289.8211805467289.8316075706354.7416077671799.7517151130279.8317995455655.8219970277031.822124193155.82 30546037383.7930547914802.7832127996803.8234806984771.7536180999398.7336438766096.7837678271015.7543059266230.714339538087.83 49705053714.8049705053714.8249705053714.8350827569594.745114850435.83 51576684520.8051576684520.8251576684520.8355866553043.7557680763535.7559115498267.7559192637571.8061305990311.8062302209411.8263045761903.7463856323923.8063856323923.8263856323923.8366253577094.7467800019075.837130566823.82 8931259039.75 00000B00T00f00j00n01201>01C01D01E01F01G01K01O01P01T01U01X01Y01_01`01h02002802902:02L02^03003603;03D03E03F03G03N03R03V03Z03a03b03c03iS2LO4LOLE5ATOPR2HBS2LO4LOLE5ATOPR2HBS2LO4LOLE5ATOPR2HBS2HBS2HBS2HBS2AV3FRD3MWRS3MWRSSSSS2LIS2LISS2FBSS1KSS4LOLESS3SPR2HBS3SPR2HBS3SPR2HBFSS2LO4LOLE5ATOPR2HBS2LO4LOLE5ATOPR2HBS2LO4LOLE5ATOPR2HBS2FB1KS3MWRS2LO4LOLESSSS2HI2LIS2HBS2HBS2HBS2HI2LISSS4MWR'".
carve_frame 96%nat ST. st1. st1. st1. st1. st1.
st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
clear MR G4 G5.
lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -96) (CB 48 ?j :: _) |- _ => set (junk48 := j) in H; clearbody junk48; rename H into FR end.
rmeta_chunk MR1 MSL CH.
st1. st1. st1. rewrite ?sx32_wz_sxv by lia. st1.
st1. rewrite ?(unsigned_lit i) by lia. rewrite (sllw1_word i) by lia.
st1. rewrite ?(unsigned_lit (meta_word mr)) by lia.
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
st1. rewrite (meta_word_freeable _ MW).
st1. rewrite (meta_word_sc52 _ MW).
clear CH.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MC : rmid_ctx mX junk48) by (split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST|]; split; [exact FR|exact MR1]) end.
st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
{ assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold, okf_unfold. replace (m_freeable mr =? 0) with true by (symmetry; apply Z.eqb_eq; lia). apply andb_false_r. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC). }
st1. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite ?(unsigned_lit (Z.lor _ _)) by (apply lor_range64; apply sxv_range).
rewrite addw_word. replace (maskw + sxv (2 ^ i)) with (sxv (2 ^ i) + maskw) by lia.
st1. st1. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (sllw2_word (meta_word mr)) by lia. rewrite (meta_word_mod32 _ MW).
st1. rewrite addiw_m1_word.
pose proof (sxv_range (sxv (2 ^ i) + maskw)) as R1. pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as R2.
st1. if_cases K2; zify_cond K2; rewrite ?wz_unsigned in K2 by (apply sxv_range).
- assert (HC : ntf_cond st g i = false).
{ rewrite ntf_cond_unfold. replace (mask + bit i =? mask_upto (m_last_idx mr)) with false; [reflexivity|].
symmetry. apply Z.eqb_neq. unfold bit, mask_upto. intros E. apply K2.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))). exact E. }
eapply (rntf_notall t0 t1 t2 _ _ _ _ _ t3 t4 t5 t6 _ junk48 MC HC).
-
apply (proj1 (free_all_test (m_freed mr) (m_avail mr) i (m_last_idx mr) FRD AV HI ltac:(lia))) in K2.
eapply (rntf_okchk t0 t1 t2 _ _ _ t3 t4 t5 t6 _ junk48 MC); [unfold bit, mask_upto; exact K2 | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ENTRY.
End CANSEC1.
