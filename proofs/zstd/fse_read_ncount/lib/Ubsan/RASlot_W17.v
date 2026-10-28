(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W17.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RAllocSlot_iface RASlot_I RMallocKit_A3 RF_ntf_A RF_malloc_bigw RASlot_W2 RASlot_W4.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rmm_call_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt usegs (fun ms' =>
ms' = MS (mkR (Z_to_bv 64 0x166a4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
(Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x16684) fc None m (seg_rom usegs)).
Proof.
intros. unfold rmmap_entry.
step. step. step. step. step. step. step. step.
apply evt_done. reflexivity.
Qed.
#[using="Type"] Lemma rmm_ret_fail_walk :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
evt usegs (fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x167cc) fc None m (seg_rom usegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x166a4) fc None m (seg_rom usegs)).
Proof.
intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
apply evt_done. reflexivity.
Qed.
Section MMOK.
Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= ATOP.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.
#[using="SC CNT SZ ND NDA XA XA2 MST REC HC CR"] Lemma rmm_ret_ok_walk :
forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
rmrep st2 m -> mem_inv usegs m ->
evt usegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x166fc) fc None m' (seg_rom usegs)
/\ munch [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 RMLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x166a4) fc None m (seg_rom usegs)).
Proof.
intros until m. intros MR MI.
pose proof (munch_refl [(G, G + 40); (RCTX + 12, RCTX + 16)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof (rmeta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
unfold RCTX, RMLOCK in *. atop_facts.
step. Local Ltac2 Set LiaHints.tbl := fun () => "00\0>10824572241.7011899637627.6512378521055.7213243977942.7815764576006.7417212484973.6317978446710.5917980828837.6018189295651.7418192971005.7321910439335.8629007610482.713067974865.70 31195403481.7234324489854.7135499711534.7337798740099.5737926108622.7138521271298.6741352056401.7041388557870.7345093649260.6445249807107.7745763346440.7745763430326.674587217297.70 4783703437.73 47871016736.7849234157850.7749437953845.7751503707745.7354383518033.6354383848065.5955347816901.6355906581388.725808319357.59 58686917929.7259314923118.5760855002975.7761081688940.7262125365601.5965104156229.5968060829559.677762923258.60 00000400800<00[00d00e00i00m01801A01E01F01M01R01X01Y01j02102202702G02H02Q02U02V02Z02b02l03003403503903=03A03F03G03P03`03g03k03l040041045S2K1S2CRS2GES2SZ2ND3NDA2XA3XA25ATOPR4ND121HS3CNT3MNRSS2SZS2SZS3MNR3NE01nS3MNR3NE0S2H0SS2D02D1S3CNTS2D01HSS2ND2XA3XA25ATOPRS3CNT1HSS3CNTS3CNT2SZ3MNR3NE0SS4Gpos2HBS2HBSS2K1S2D03NE0S2SZ3NDA1HS2HBS2HBSS2NDS2NDS2CRS3CNTSS3CNT3MNRS2ND3XA25ATOPR1KS2GI2HBS2LTSS2SZSS2SZ".
if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
clear K.
step.
rmchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
rmeta_open G MUa WMa.
step.
step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
rewrite (divu_word 4080 size) by lia.
pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
set (d := 4080 / size) in *.
pose proof MR as (_ & (CX1 & _) & _). unfold rctx_head_cells, rsecw in CX1. rewrite HC in CX1. unfold RCTX in CX1.
step. rewrite (sx32_wz_sxv c) by lia.
step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
{ unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
Z.div_mod_to_equations. lia. }
step.
lazymatch goal with H : rw_cells usegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
[ unfold upd_meta; rewrite REC; eapply rmrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
| clear MUa WMa H ] end.
set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
pose proof (rw_cells_store_ok_at usegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (324144 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
clear CX1.
st1.
rewrite le4_swrap_succ by lia.
assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
pose proof (rmrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold RCTX in MR4 end.
clear MR3.
rraw_store_finish0 (324152 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
assert (E4 : mm_st4 st2 nd mt = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
{ unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
rewrite <- E4 in MR4.
assert (C4' : c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1)) by (rewrite E4; reflexivity).
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
evt usegs (fun ms' => exists (a3' a4' : word) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
(Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (mm_ai cnt size)) a3' a4' a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 324144) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x166fc) fc None m' (seg_rom usegs)
/\ munch [(G, G + 40); (324152 + 12, 324152 + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ rmrep (mm_st4 st2 nd mt) m' /\ c_mmap_counter (ctx (mm_st4 st2 nd mt)) = u32 (c + 1))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
(Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 324144) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x166e8) fc None mX (seg_rom usegs))) end.
{ intros a2v mn Hmn ->.
assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
replace (cnt + -1) with (cnt - 1) by lia.
assert (AI : mm_ai cnt size = (if mn =? 0 then 0 else mn - 1)).
{ unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
destruct (Z.ltb_spec cnt d) as [LT|GE].
- replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
- replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
destruct (Z.eqb_spec d 0) as [E0|NE0].
+ rewrite E0. reflexivity.
+ replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
= Z_to_bv 64 (mm_ai cnt size)).
{ rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
destruct (Z.eqb_spec mn 0) as [E0|NE0].
- rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
- rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
rewrite EA2.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
-
eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
-
step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End MMOK.
End CANSEC1.
