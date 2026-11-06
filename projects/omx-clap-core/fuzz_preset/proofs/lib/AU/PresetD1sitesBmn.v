(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29: the MEMNORM KEEP of the printf sites (lane CwSites, open row of the interface
   a working branch 446222ec0601). The loop needs `memnorm tfibsegs mem -> memnorm tfibsegs mem'` across the
   driver's printf call, and no call rule can derive it from a post stated through views (YGcallMxmn.v header), so
   the walk itself must carry it. This file re-runs lib/Reusable/YE3mcf.v's two vfprintf walks and lib/Reusable/YE3hcf.v's two
   interceptor call lemmas with that conjunct, from the SAME proof text:
   - vf_icpt_memcpy_ext_mn / vf_icpt_memset_mn: YE3hcf.v:540-684 / :830-982, with the intrinsic premise taken in
     a Theorem Labs lane's keep form YGcallMxmn.aintrin_realizes_xm (which states the keep as its last post conjunct)
     instead of YCf0.aintrin_realizes0;
   - tfib_vfprintf_stdout_first_mn / _next_mn: YE3mcf.v:537-1043 / :1044-1547, with one keep premise added to the
     continuation and the keep threaded step by step: a symbolic-runner phase by YGcallMxmn.memnorm_frame_of, the
     TIOCGWINSZ ioctl by its rule's `ms_mem ms' = ms_mem ms`, the writev by memnorm_frame_of_ecall (below, the
     st_ok_ecall twin of memnorm_frame_of, same proof), each interceptor call by the xm keep.
   YGcallMxmn.v is taken by path from a working branch 8e33ecc4965b (blob 87de220caca2); YAkMemnorm.v
   comes with the interface commit. MN.memnorm = YAkMemnorm.memnorm.
   THIS FILE is port/a2b.py's output (sha256 f5113cbc90e5) of lib/A/PresetD1sitesAmn.v, with two hand changes in
   code: lib/A's AImgFacts import is dropped (B's YE3mcf states STDOUT_BUFA itself and has no such import), and
   the three rodata literals of the walk that a2b has no map for are the B image's: 84005 -> 84014,
   68468 -> 68476, 84006 -> 84015 (YE3mcf.v's own values; A's are AE3mcf.v's). The B cf walks are lane CwPreB's,
   a working branch 30644fdd1332.
   rule 24: proves function vfprintf (reuse search: the internal file idx-cfcopy-walks.txt / the internal file idx-fwrite-fprintf.txt exit=0; PORT of
   the released cgif walk via CwPreB's cf copy; checker IcptCheck 04:27Z CONFIRM)
   rule 24: proves no function (kind: driver layer) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0d2cf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YCf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YE34 YF0l YE3e YE3f YE3g YE6g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YE2pcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE3i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YE3hcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YE22cf YF0xcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YE20.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YE2ycf YE7fcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YE3mcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YE20.v / YE08.v end with this flag true and YF0v.v (in YGcallMxmn's closure) sets it false, so this file states
   its own value, the one YE3mcf's proofs ran under (cw-lanes-brief 23:40Z). *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.
Module MX := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YGcallMxmn.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* YGcallMxmn.v:629 memnorm_frame_of, at a state stopped in an ecall (st_ok_ecall, YP0l.v:112, the same nine
   conjuncts as st_ok): the writev node's frame. The proof is YGcallMxmn's, unchanged. *)
Lemma memnorm_frame_of_ecall : forall (segs : list Segment) (H : word -> bool) E ss (ms : machine_state) (m' : word -> option byte),
MN.memnorm segs (ms_mem ms) -> st_ok_ecall segs E ss (restrict H ms) -> frame_of E (ss_mem ss) (ms_mem ms) m' ->
MN.memnorm segs m'.
Proof.
intros segs H E ss ms m' (Hi & Ht) HS HF.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & ROK & _) & _).
assert (HW : forall a : word, in_wrange E (ss_mem ss) (bv_unsigned a) -> wview segs (YK04.mrestrict H (ms_mem ms)) a <> None).
{ intros a (r & Hin & Hr).
  pose proof (proj1 (Forall_forall _ _) ROK r Hin) as Hok. unfold region_ok in Hok.
  destruct Hok as (_ & _ & Hw & _).
  specialize (Hw (bv_unsigned a - YP09.base_val E (YP09.r_base r)) ltac:(lia)).
  unfold writable_at in Hw.
  replace (YP09.base_val E (YP09.r_base r) + (bv_unsigned a - YP09.base_val E (YP09.r_base r))) with (bv_unsigned a) in Hw by lia.
  rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
assert (HN : forall a : word, ms_mem ms a = None -> YK04.mrestrict H (ms_mem ms) a = None).
{ intros a Ea. unfold YK04.mrestrict. destruct (H a); [reflexivity | exact Ea]. }
split.
- intros a b Ea. destruct (ms_mem ms a) as [b0|] eqn:E0; [exact (Hi a b0 E0)|].
  destruct (MX.in_wrange_dec E (ss_mem ss) (bv_unsigned a)) as [Hin|Hout].
  + exact (MX.ak_wview_not_ro segs (YK04.mrestrict H (ms_mem ms)) a (HW a Hin) (HN a E0)).
  + rewrite (HF a Hout), E0 in Ea. discriminate.
- intros a b Ea. destruct (ms_mem ms a) as [b0|] eqn:E0; [exact (Ht a b0 E0)|].
  destruct (MX.in_wrange_dec E (ss_mem ss) (bv_unsigned a)) as [Hin|Hout].
  + left. exact (MX.ak_wview_absent_seg segs (YK04.mrestrict H (ms_mem ms)) a (HW a Hin) (HN a E0)).
  + rewrite (HF a Hout), E0 in Ea. discriminate.
Qed.

(* the numeral value of a generated constant: no typed address, so port/a2b.py gives the B twin *)
Local Ltac zval x := let v := eval vm_compute in x in exact v.
Local Ltac GEO := unfold FMT_d, PAD_OFF, OSP_FX, OSP_PC, RA_FX, STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, FILE_SZ, BUFEND in *; lia.
Section S.
Variable B : asyms.
Hypothesis TL : TfibSyms B.
Hypothesis LAWS : AR_laws_cf tfibsegs B.
(* the two intrinsic texts in a Theorem Labs lane's keep form: the rows' owners pay the keep from their own runs *)
Hypothesis AMEMCPYM : MX.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OCpy (pc_wrap_memcpy (as_code B)).
Hypothesis AMEMSETM : MX.aintrin_realizes_xm tfibsegs B (ARcf tfibsegs B) OSet (pc_wrap_memset (as_code B)).
Let HBcode := ts_code B TL.

Lemma vf_icpt_memcpy_ext_mn : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp
(dsv xsv nsv : sv) (d x n : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memcpy (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = dsv -> sv_denot E dsv = Z_to_bv 64 d ->
sr_get (ss_regs ss) 11 = xsv -> sv_denot E xsv = Z_to_bv 64 x ->
sr_get (ss_regs ss) 12 = nsv -> sv_denot E nsv = Z_to_bv 64 n ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 0 <= d -> (d + n <= sp0 - VF_STK \/ sp0 <= d) -> d + n <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
0 <= x -> x + n <= 2 ^ 47 -> (x + n <= sp0 + osp - ESTACK \/ sp0 + osp <= x) ->
(d + n <= x \/ x + n <= d) -> amem_range d n -> amem_range x n ->
(forall r, In r rest -> d + n <= base_val E (YP09.r_base r) + YP09.r_lo r \/ base_val E (YP09.r_base r) + YP09.r_hi r <= d) ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, x <= a < x + n -> aview tfibsegs (w_H W) (ms_mem ms) a <> None) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x n) ->
(forall a, d <= a < d + n -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a /\ ~ aowned B ly S a) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) d n) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
ARcf tfibsegs B ly S [] W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall i, 0 <= i < n -> aview tfibsegs (w_H W) (ms_mem ms2) (d + i) = aview tfibsegs (w_H W) (ms_mem ms) (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (d <= a < d + n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a) /\
(MN.memnorm tfibsegs (ms_mem ms) -> MN.memnorm tfibsegs (ms_mem ms2))).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp dsv xsv nsv d x n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 Hda S11 Hxa S12 Hna Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hd0 Hdband Hdhi Hn Hra Hra4 Hx0 Hxhi Hxs Hxd Hamd Hamx Hrdisj Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres Hsrc Hra_x Hhull_x Hdw Hra_d Hhull_d.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = ltac:(zval ESTACK)) by reflexivity. assert (HVF : VF_STK = ltac:(zval VF_STK)) by reflexivity.
pose proof (amc_layout B ly S [] _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 d) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10; exact Hda).
assert (R11 : getr regsT 11 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; exact Hxa).
assert (R12 : getr regsT 12 = w64 n) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; exact Hna).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
pose proof (alc_zshadow _ _ LAWS ly S [] W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMCPYM as AM. unfold MX.aintrin_realizes_xm, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ apply (AM ly S [] W regsT (ms_mem ms) md d x n).
-
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
-   intros a Ha. rewrite HspT. destruct (Hdw a Ha) as [Hw1 Hw2]. split; [exact Hw1|]. split; [exact Hw2 | lia].
- exact Hamd.
- exact Hra_d.
- exact Hhull_d.
-   split; [lia|]. split; [lia|]. split.
+ intros a Ha. rewrite HspT. split; [apply Hsrc; exact Ha | lia].
+ split; [lia|]. split; [exact Hamx|]. split; [exact Hra_x | exact Hhull_x]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2 & HMN).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split; [|split; [|split]]]]].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memcpy (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+
split; [exact Hwf2|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; lia.
--
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. pose proof (Hrdisj r Hr) as Hdj. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha, Hdj; cbn [base_val] in Ha, Hdj; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- exact Heff.
- intros a Hr Hs Hd. apply Hfr; lia.
- exact Hpres2.
- exact HMN.
Qed.

Lemma vf_icpt_memset_mn : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp o (c : Z) n,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc_wrap_memset (as_code B) -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
sr_get (ss_regs ss) 10 = SOff 2 o -> sr_get (ss_regs ss) 11 = SLit c -> 0 <= c < 256 -> sr_get (ss_regs ss) 12 = SLit (Z.of_nat n) ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp o (repeat c n))) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= o -> o + Z.of_nat n <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> (YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43) \/
(YP09.r_base r = Some 12%nat /\ 0 <= YP09.r_lo r /\ bv_unsigned (ew E 12) + YP09.r_hi r <= 2 ^ 47 /\
sp0 <= bv_unsigned (ew E 12) + YP09.r_lo r)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
ARcf tfibsegs B ly S [] W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly -> sp0 < kHighMemEnd ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp o (repeat c n)) (restrict (w_H W) ms2) /\
ARcf tfibsegs B ly S [] W (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ (sp0 + o <= a < sp0 + o + Z.of_nat n) ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a) /\
(MN.memnorm tfibsegs (ms_mem ms) -> MN.memnorm tfibsegs (ms_mem ms2))).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp o c n HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 S10 S11 Hc S12 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hon Hra Hra4 Hrest HrestW
HAR Hsp44 Hsp16 Hstk Htop HtopS Hpres.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = ltac:(zval ESTACK)) by reflexivity. assert (HVF : VF_STK = ltac:(zval VF_STK)) by reflexivity.
pose proof (amc_layout B ly S [] _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (R10 : getr regsT 10 = w64 (sp0 + o)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 10 HS), S10. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R11 : getr regsT 11 = w64 c) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 11 HS), S11; reflexivity).
assert (R12 : getr regsT 12 = w64 (Z.of_nat n)) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 12 HS), S12; reflexivity).
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
assert (Hzl : length (repeat c n) = n) by apply repeat_length.
pose proof (alc_zshadow _ _ LAWS ly S [] W memT md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR ltac:(left; reflexivity)) as Hz.
cbn [fst snd] in Hz.
pose proof AMEMSETM as AM. unfold MX.aintrin_realizes_xm, cfg_at in AM.
rewrite Hshape. unfold memT in *.
eapply SRr_mono.
{ apply (AM ly S [] W regsT (ms_mem ms) md (sp0 + o) c (Z.of_nat n)).
-
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4].
- exact R10. - exact R11. - exact R12.
- lia. - lia. - lia.
-   intros a Ha. rewrite HspT. split; [apply apresent_writable; apply Hpres; lia|]. split; [| lia].
exact (alc_stack _ _ LAWS ly S [] W (ms_mem ms) md a HAR ltac:(lia)).
-
right. unfold kHighMemBeg, kHighMemEnd in *. lia.
-
intros y Hy. exists 0. split; [|left; reflexivity].
unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (y / 8 - ly_stk_lo ly / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. lia.
-   intros Hn s Hs. unfold zero_shadow in Hz. unfold page_aligned in Lplo, Lphi.
replace s with (shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + (s - shadow_of_addr SHADOW_OFF (ly_stk_lo ly))) by lia.
rewrite Hz; [discriminate|]. unfold shadow_of_addr, shadow_addr in *.
clear - Hs Hn Lplo Lphi Hstk Htop Ltop Hosp1 Hosp2 Hon HVF HES. unfold SHADOW_OFF in *. lia.
-   exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsbm & Ha0 & Heff & Hfr & Hpres2 & HMN).
rewrite HspT in Hfr. unfold memT in *.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [|split; [exact HP | split; [|split]]]].
-
rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 (pc_wrap_memset (as_code B))) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+
split; [exact Hwf2|]. split.
* constructor.
--
destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply apresent_writable. apply Hpres2. apply Hpres. lia. }
apply Forall_app. split.
++ apply Forall_forall. intros ch Hch. destruct (lit_chunks_In _ _ _ Hch) as (j & Hj & ->).
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
assert (Hi0 : i = 0) by lia. subst i. rewrite Z.add_0_r.
specialize (Heff (Z.of_nat j) ltac:(lia)). unfold aview in Heff. rewrite Z.mod_small in Heff by lia.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem2) (sp0 + o + Z.of_nat j)) as [cb|] eqn:Hc2; [|discriminate].
cbn [option_map] in Heff. injection Heff as Heff.
exists cb. split; [| rewrite <- Hc2; f_equal; lia]. cbn [cbyte sv_denot]. unfold YP09.byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite nth_repeat_lt by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_bv8_mod64.
f_equal. apply bv_eq. rewrite unsigned_lit8_small by lia. symmetry. exact Heff.
++ apply Forall_forall. intros ch Hch. apply filter_In in Hch as [Hch Hk].
apply andb_prop in Hk as [Hk1 Hk2]. apply Z.leb_le in Hk1. unfold chunk_out in Hk2.
pose proof (proj1 (Forall_forall _ _) Hcs ch Hch) as Hck.
pose proof (chunk_inside_facts _ ch (proj1 (forallb_forall _ _) Hci0 ch Hch)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. apply Hfr; [lia| |].
** apply orb_prop in Hk2. destruct Hk2 as [Hk2|Hk2]; apply Z.leb_le in Hk2; lia.
** lia.
--
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros ch Hch. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr ch Hch) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val ch); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. apply Hfr;
destruct (Hrest r Hr) as [(Hrb & Hrl & Hrh) | (Hrb & Hrl & Hrh & Hrs)]; rewrite Hrb in Ha; cbn [base_val] in Ha; lia.
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- rewrite <- Hsbm'. exact HAR2.
- intros a Hr Hs Hd. apply Hfr; lia.
- exact Hpres2.
- exact HMN.
Qed.

Theorem tfib_vfprintf_stdout_first_mn : forall ly S (W : world tfibsegs) regs mem md ch ap cval T,
ecall_pre_cf tfibsegs B ly S [] W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_pristine (mrestrict (w_H W) mem) ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
fdchan (Z_to_bv 64 1) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
ARcf tfibsegs B ly S [] W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid STDOUT_BUFA (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut STDOUT_BUFA (STDOUT_BUFA + 1) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
(MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs mem') ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) [48; 10])) T).
Proof.
intros ly S W regs mem md ch ap cval T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP HBown Hgot Hcan Hcv Hro Hra_b Hhull_b Hch HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = ltac:(zval ESTACK)) by reflexivity. assert (HVF : VF_STK = ltac:(zval VF_STK)) by reflexivity.
assert (HFF : F_STDOUT = ltac:(zval F_STDOUT)) by reflexivity. assert (HFS : FILE_SZ = ltac:(zval FILE_SZ)) by reflexivity.
assert (HBF : STDOUT_BUFA = ltac:(zval STDOUT_BUFA)) by reflexivity. assert (HBS : STDOUT_BSZ = ltac:(zval STDOUT_BSZ)) by reflexivity.
assert (HFD : FMT_d = ltac:(zval FMT_d)) by reflexivity. assert (HPO : PAD_OFF = ltac:(zval PAD_OFF)) by reflexivity. assert (HOX : OSP_FX = ltac:(zval OSP_FX)) by reflexivity.
pose proof (amc_layout B ly S [] _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (MUT := vo_mut STDOUT_BUFA (STDOUT_BUFA + 1)) in *.
assert (MUTimg : forall a, MUT a -> img_byte_ok tfibsegs a = true) by (intros a Ha; apply (vo_mut_img STDOUT_BUFA (STDOUT_BUFA + 1) a); [lia | unfold STDOUT_BSZ; lia | exact Ha]).
assert (MUTdec : forall a, MUT a \/ ~ MUT a) by (intros a; apply vo_mut_dec).
assert (HFownM : forall a, MUT a -> ~ aowned B ly S a) by (intros a [Ha|Ha]; apply HBown; [left; exact Ha | right; unfold STDOUT_BSZ; lia]).
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vo_entry0 W regs mem ap cval Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP Hgot Hcan Hcv Hro) as HS0.
set (EL := [Z_to_bv 64 0; Z_to_bv 64 cval]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs EL) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
set (EA := Ereg regs EL) in *.
clear HE0 EE.
pose proof (VO_init B ly S W sp0 mem md MUT HAR Hpres) as VO0.
assert (MN0 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs mem) by (intros Hm0; exact Hm0).
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 ss_vo0 o_st1 _ _ _ HS0 o_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1.
assert (MN1 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms1)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E0 ss_vo0); [| exact HS0 | exact HF1]; exact (MN0 Hm0)).
clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VO1 : VO B ly S W sp0 mem md MUT (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms1) mat1 VO0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vo_windows_sound E0 ss_vo0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vo_windows_sound E0 ss_vo0 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E0 o_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VO0 HF1 HFr1.
assert (SRA1' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms1)) SHADOW_OFF FMT_d 0) by (intros y Hy; lia).
assert (SHU1' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms1)) FMT_d 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E0 o_st1 ms1 _ ly S sp0 o_r01 o_rest1 34 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit FMT_d) (SLit 0) (STDOUT_BUFA) (FMT_d) 0
HS1 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO1) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E0 sp0 ap o_rest1 (STDOUT_BUFA) 0 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E0 sp0 ap o_rest1 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vo_rest_w E0 o_rest1 ltac:(vm_compute; reflexivity))
(proj1 VO1) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO1)))
ltac:(intros a Ha; lia) SRA1' SHU1'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI1).
intros W1' c1' _ HAI1' (-> & ms1' & mat1' & -> & HS1' & HAR1' & HP1' & Heff1' & Hfr1' & Hpm1' & HMNx2). cbn [cfg_model] in HAI1'.
assert (MN2 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms1')) by (intros Hm0; exact (HMNx2 (MN1 Hm0))).
rewrite wvb_wvb in HAI1', HAR1' |- *.
change (vf_after_icpt 34 o_st1 RA_FX OSP_FX 0 []) with o_af1 in HS1'.
assert (VO1' : VO B ly S W sp0 mem md MUT (ms_mem ms1') (with_vm_backing (m_vm_lazy md) mat1' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms1) _ (ms_mem ms1') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- exact VO1.
- exact HAR1'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat1' mat1 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr1'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm1'. }
remember (havoc E0 34 (map (getr (ms_regs ms1')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 34)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (HAE1 : env_agree 32 EA E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS1 VO1 SRA1' SHU1' Heff1'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 o_af1 o_st2 _ _ _ HS1' o_run2) HAI1').
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2.
assert (MN3 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms2)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E1 o_af1); [| exact HS1' | exact HF2]; exact (MN2 Hm0)).
clear HS1'.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VO2 : VO B ly S W sp0 mem md MUT (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms2) mat2 VO1') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vo_windows_sound E1 o_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vo_windows_sound E1 o_af1 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E1 o_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VO1' HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF 68476 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) 68476 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E1 o_st2 ms2 _ ly S sp0 o_r02 o_rest2 50 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit 68476) (SLit 0) (STDOUT_BUFA) (68476) 0
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO2) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E1 sp0 ap o_rest2 (STDOUT_BUFA) 0 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E1 sp0 ap o_rest2 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vo_rest_w E1 o_rest2 ltac:(vm_compute; reflexivity))
(proj1 VO2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO2)))
ltac:(intros a Ha; lia) SRA2' SHU2'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Heff2' & Hfr2' & Hpm2' & HMNx4). cbn [cfg_model] in HAI2'.
assert (MN4 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms2')) by (intros Hm0; exact (HMNx4 (MN3 Hm0))).
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 50 o_st2 RA_FX OSP_FX 0 []) with o_af2 in HS2'.
assert (VO2' : VO B ly S W sp0 mem md MUT (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- exact VO2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E1 50 (map (getr (ms_regs ms2')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 50)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (HAE2 : env_agree 32 EA E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS2 VO2 SRA2' SHU2' Heff2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 o_af2 o_st3 _ _ _ HS2' o_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3.
assert (MN5 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms3)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E2 o_af2); [| exact HS2' | exact HF3]; exact (MN4 Hm0)).
clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VO3 : VO B ly S W sp0 mem md MUT (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms3) mat3 VO2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vo_windows_sound E2 o_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vo_windows_sound E2 o_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E2 o_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VO2' HF3 HFr3.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memset_mn W E2 o_st3 ms3 _ ly S sp0 o_r03 o_rest3 66 RA_PAD OSP_PC PAD_OFF 48 1%nat
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_PC; lia) ltac:(unfold OSP_PC, PAD_OFF; lia) ltac:(unfold PAD_OFF; cbn; lia) ltac:(unfold RA_PAD; lia) ltac:(reflexivity)
(vo_rest_ok E2 sp0 ap o_rest3 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vo_rest_w E2 o_rest3 ltac:(vm_compute; reflexivity))
(proj1 VO3) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VO3)))) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3' & HMNx6). cbn [cfg_model] in HAI3'.
assert (MN6 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms3')) by (intros Hm0; exact (HMNx6 (MN5 Hm0))).
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 66 o_st3 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)) with o_af3 in HS3'.
assert (VO3' : VO B ly S W sp0 mem md MUT (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_PC - ESTACK <= a < sp0 + OSP_PC) \/ (sp0 + PAD_OFF <= a < sp0 + PAD_OFF + 1))).
- exact VO3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a Ha. left. unfold vf_band, OSP_PC, PAD_OFF in *. lia.
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; cbn; exact H'].
- exact Hpm3'. }
remember (havoc E2 66 (map (getr (ms_regs ms3')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 66)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (HAE3 : env_agree 32 EA E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3 HS3 VO3.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 o_af3 o_st4 _ _ _ HS3' o_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4.
assert (MN7 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms4)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E3 o_af3); [| exact HS3' | exact HF4]; exact (MN6 Hm0)).
clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VO4 : VO B ly S W sp0 mem md MUT (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms4) mat4 VO3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vo_windows_sound E3 o_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vo_windows_sound E3 o_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E3 o_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VO3' HF4 HFr4.
pose proof HS4 as HSc4. destruct HSc4 as (_ & _ & _ & _ & _ & _ & _ & Hmem4 & _). cbn [restrict ms_mem] in Hmem4.
assert (PAD4 : aview tfibsegs (w_H W) (ms_mem ms4) (sp0 + PAD_OFF) = Some 48).
{ replace (sp0 + PAD_OFF) with (sp0 + PAD_OFF + Z.of_nat 0) by lia.
apply (lit_buf_aview W E3 (ms_mem ms4) (ss_mem o_st4) (SOff 2 PAD_OFF) (sp0 + PAD_OFF) 1 [48] Hmem4 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) ltac:(repeat constructor; lia) 0%nat ltac:(lia)). }
clear Hmem4.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms4) _ sp0 (sp0 + PAD_OFF) 1 (proj1 VO4) Hstk Htop ltac:(unfold PAD_OFF; lia) ltac:(unfold PAD_OFF; lia) ltac:(lia)) as [SRA4' SHU4'].
destruct (vo_shadow_xfer B ly S W sp0 mem md STDOUT_BUFA (STDOUT_BUFA + 1) (ms_mem ms4) _ STDOUT_BUFA STDOUT_BSZ STDOUT_BUFA 1 VO4 ltac:(unfold STDOUT_BSZ; lia) Hstk Hra_b Hhull_b
ltac:(unfold STDOUT_BUFA; lia) ltac:(lia) ltac:(unfold STDOUT_BSZ; lia) ltac:(rewrite KHI; unfold STDOUT_BUFA, STDOUT_BSZ; lia)) as [DRA4' DHU4'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E3 o_st4 ms4 _ ly S sp0 o_r04 o_rest4 82 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SOff 2 PAD_OFF) (SLit 1) (STDOUT_BUFA) (sp0 + PAD_OFF) 1
HS4 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO4) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E3 sp0 ap o_rest4 (STDOUT_BUFA) 1 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E3 sp0 ap o_rest4 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vo_rest_w E3 o_rest4 ltac:(vm_compute; reflexivity))
(proj1 VO4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO4)))
ltac:(intros a Ha; replace a with (sp0 + PAD_OFF) by lia; rewrite PAD4; discriminate) SRA4' SHU4'
ltac:(intros a Ha; split; [apply stdout_buf_writable; unfold STDOUT_BSZ; lia | apply HBown; right; unfold STDOUT_BSZ; lia]) ltac:(exact DRA4') ltac:(exact DHU4')) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Heff4' & Hfr4' & Hpm4' & HMNx8). cbn [cfg_model] in HAI4'.
assert (MN8 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms4')) by (intros Hm0; exact (HMNx8 (MN7 Hm0))).
rewrite wvb_wvb in HAI4', HAR4' |- *.
change (vf_after_icpt 82 o_st4 RA_FX OSP_FX 0 []) with o_af4 in HS4'.
assert (VO4' : VO B ly S W sp0 mem md MUT (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 1))).
- exact VO4.
- exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr4'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm4'. }
assert (BUF04' : aview tfibsegs (w_H W) (ms_mem ms4') (STDOUT_BUFA) = Some 48).
{ rewrite <- PAD4, <- (Z.add_0_r STDOUT_BUFA), <- (Z.add_0_r (sp0 + PAD_OFF)). apply (Heff4' 0). lia. }
remember (havoc E3 82 (map (getr (ms_regs ms4')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 82)%nat -> ew E4 j = ew E3 j) by (intros j Hj; rewrite HE4; apply ew_havoc_old; exact Hj).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp3).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (rewrite OLD4 by (cbv; lia); exact G3_3).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (rewrite OLD4 by (cbv; lia); exact G4_3).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (rewrite OLD4 by (cbv; lia); exact G12_3).
assert (HAE4 : env_agree 32 EA E4)
by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4 HS4 VO4 SRA4' SHU4' Heff4'.
clear PAD4 DRA4' DHU4'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 o_af4 o_st5 _ _ _ HS4' o_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5.
assert (MN9 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms5)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E4 o_af4); [| exact HS4' | exact HF5]; exact (MN8 Hm0)).
clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VO5 : VO B ly S W sp0 mem md MUT (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms5) mat5 VO4') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E4 o_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
assert (BUF05 : aview tfibsegs (w_H W) (ms_mem ms5) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF04'. apply aview_eq_of. apply HFr5. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 o_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO4' HF5 HFr5 BUF04'.
assert (SRA5' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms5)) SHADOW_OFF (sp0 + PAD_OFF) 0) by (intros y Hy; lia).
assert (SHU5' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms5)) (sp0 + PAD_OFF) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E4 o_st5 ms5 _ ly S sp0 o_r05 o_rest5 98 RA_FX OSP_FX
(SLit (STDOUT_BUFA + 1)) (SOff 2 PAD_OFF) (SLit 0) (STDOUT_BUFA + 1) (sp0 + PAD_OFF) 0
HS5 ltac:(rewrite HBcode; reflexivity) eq_refl Usp4 G3_4 G4_4 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp4; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO5) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E4 sp0 ap o_rest5 (STDOUT_BUFA + 1) 0 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E4 sp0 ap o_rest5 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hap2)
(vo_rest_w E4 o_rest5 ltac:(vm_compute; reflexivity))
(proj1 VO5) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO5)))
ltac:(intros a Ha; lia) SRA5' SHU5'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI5).
intros W5' c5' _ HAI5' (-> & ms5' & mat5' & -> & HS5' & HAR5' & HP5' & Heff5' & Hfr5' & Hpm5' & HMNx10). cbn [cfg_model] in HAI5'.
assert (MN10 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms5')) by (intros Hm0; exact (HMNx10 (MN9 Hm0))).
rewrite wvb_wvb in HAI5', HAR5' |- *.
change (vf_after_icpt 98 o_st5 RA_FX OSP_FX 0 []) with o_af5 in HS5'.
assert (VO5' : VO B ly S W sp0 mem md MUT (ms_mem ms5') (with_vm_backing (m_vm_lazy md) mat5' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms5) _ (ms_mem ms5') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA + 1) <= a < (STDOUT_BUFA + 1) + 0))).
- exact VO5.
- exact HAR5'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat5' mat5 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr5'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm5'. }
assert (BUF05' : aview tfibsegs (w_H W) (ms_mem ms5') (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF05. apply Hfr5'; [GEO | GEO | GEO]. }
remember (havoc E4 98 (map (getr (ms_regs ms5')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 98)%nat -> ew E5 j = ew E4 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp4).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_4).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_4).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_4).
assert (HAE5 : env_agree 32 EA E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5 HS5 VO5 SRA5' SHU5' Heff5' BUF05.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 o_af5 o_st6 _ _ _ HS5' o_run6) HAI5').
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6.
assert (MN11 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms6)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E5 o_af5); [| exact HS5' | exact HF6]; exact (MN10 Hm0)).
clear HS5'.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VO6 : VO B ly S W sp0 mem md MUT (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms6) mat6 VO5') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present_ecall W E5 o_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUF06 : aview tfibsegs (w_H W) (ms_mem ms6) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF05'. apply aview_eq_of. apply HFr6. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 o_af5 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO5' HF6 HFr6 BUF05'.
eapply (srz_sym_ioctl_enotty W E5 o_st6 ms6 _ (Z_to_bv 64 1) ch _ HAI6 HS6 eq_refl ltac:(vm_compute; reflexivity) eq_refl
ltac:(eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same]) eq_refl ltac:(vm_compute; reflexivity)).
intros ms6r HS6r Hmm6r.
assert (MN12 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms6r)) by (intros Hm0; rewrite Hmm6r; exact (MN11 Hm0)).
change (resume o_st6 (SLit (2 ^ 64 - 25)) (ss_mem o_st6) (ss_facts o_st6)) with o_af6 in HS6r.
assert (VO6r : VO B ly S W sp0 mem md MUT (ms_mem ms6r) (with_vm_backing (m_vm_lazy md) mat6 md)) by (rewrite Hmm6r; exact VO6).
assert (BUF06r : aview tfibsegs (w_H W) (ms_mem ms6r) (STDOUT_BUFA) = Some 48) by (rewrite Hmm6r; exact BUF06).
clear HS6 VO6 BUF06.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 o_af6 o_st7 _ _ _ HS6r o_run7) HAI6).
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7.
assert (MN13 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms7)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E5 o_af6); [| exact HS6r | exact HF7]; exact (MN12 Hm0)).
clear HS6r.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VO7 : VO B ly S W sp0 mem md MUT (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7) mat7 VO6r) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present_ecall W E5 o_st7 ms7 sp0 HS7 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUF07 : aview tfibsegs (w_H W) (ms_mem ms7) (STDOUT_BUFA) = Some 48).
{ rewrite <- BUF06r. apply aview_eq_of. apply HFr7. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 o_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO6r HF7 HFr7 BUF06r.
pose proof HS7 as HSc7. destruct HSc7 as (_ & _ & _ & _ & _ & _ & Hregs7 & Hmem7 & HG7). cbn [restrict ms_mem] in Hmem7.
pose proof (lit_buf_sound tfibsegs E5 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem o_st7) (SLit (F_STDOUT + 120)) 4 [1; 0; 0; 0] Hmem7
ltac:(vm_compute; reflexivity)) as Hfdrd. cbn [sv_denot] in Hfdrd.
pose proof (lit_buf_sound tfibsegs E5 (mrestrict (w_H W) (ms_mem ms7)) (ss_mem o_st7) (SLit 84071) 1 [10] Hmem7
ltac:(vm_compute; reflexivity)) as Hnlrd.
change (map (Z_to_bv 8) [48; 10]) with ([Z_to_bv 8 48] ++ map (Z_to_bv 8) [10]).
eapply (srz_sym_stdio_writev2 W E5 o_st7 ms7 _ (Z_to_bv 64 1) ch 0 2 (-1120) F_STDOUT _ (SLit STDOUT_BUFA) (SLit 1) (SLit 84071) (SLit 1)
([Z_to_bv 8 48]) (map (Z_to_bv 8) [10]) (map (Z_to_bv 8) [1; 0; 0; 0]) 114 T HAI7 HS7 eq_refl eq_refl eq_refl).
- reflexivity.
- eapply fdchan_sbm; [exact Hch | apply with_vm_backing_same].
- reflexivity.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite !U_SLit. reflexivity.
- match goal with |- U _ ?x = _ => let x' := eval vm_compute in x in change x with x' end. rewrite U_SLit. reflexivity.
- reflexivity.
- reflexivity.
- cbn. lia. - cbn. lia. - cbn. lia. - cbn. lia.
- vm_compute. reflexivity.
-   cbn [sv_denot]. change (word_to_nat (Z_to_bv 64 1)) with 1%nat.
apply (proj2 (rdn_mbytes tfibsegs _ 1%nat STDOUT_BUFA [Z_to_bv 8 48])). split; [reflexivity|].
intros i Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. destruct (aview_mbyte _ _ _ _ BUF07) as (b & Hb & Hbv).
rewrite Hb. cbn. f_equal. apply bv_eq. rewrite Hbv. reflexivity.
-   change (word_to_nat (sv_denot E5 (SLit 1))) with 1%nat. exact Hnlrd.
- rewrite !U_SLit. change (zcanon 1) with 1. lia.
- rewrite !U_SLit. change (zcanon STDOUT_BUFA) with STDOUT_BUFA. change (zcanon 1) with 1. unfold STDOUT_BUFA. lia.
- rewrite !U_SLit, Usp5. change (zcanon STDOUT_BUFA) with STDOUT_BUFA. change (zcanon 1) with 1. unfold STDOUT_BUFA. lia.
- rewrite !U_SLit. change (zcanon 84071) with 84071. change (zcanon 1) with 1. lia.
- rewrite !U_SLit, Usp5. change (zcanon 84071) with 84071. change (zcanon 1) with 1. lia.
- exact Hfdrd.
- vm_compute. reflexivity.
- unfold F_STDOUT. lia.
- unfold F_STDOUT. lia.
- rewrite Usp5. unfold F_STDOUT. lia.
- rewrite Usp5. lia.
- rewrite Usp5. lia.
- vm_compute. reflexivity.
-
intros ms7' ws7 mat7' HS7' HF7' HFr7' HAI7'. rewrite ?wvb_wvb in HAI7' |- *.
assert (MN14 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms7')) by (intros Hm0; eapply (memnorm_frame_of_ecall tfibsegs (w_H W) E5 o_st7); [| exact HS7 | exact HF7']; exact (MN13 Hm0)).
change (wl_after o_st7 0 (-1120) 114) with o_af7 in HS7'.
remember (havoc E5 114 ws7) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 114)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (HAE6 : env_agree 32 EA E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
assert (VO7' : VO B ly S W sp0 mem md MUT (ms_mem ms7') (with_vm_backing (m_vm_lazy md) mat7' md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7') mat7' VO7) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7'. intros Hin. destruct (vo_windows_sound E5 o_st7 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr7'. intros Hin. destruct (vo_windows_sound E5 o_st7 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E6 o_af7 ms7' sp0 HS7' ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear HE6 HS7 VO7 Hfdrd Hnlrd Hregs7 Hmem7 HG7 HF7' HFr7' BUF07.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 o_af7 o_st8 _ _ _ HS7' o_run8) HAI7').
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8.
assert (MN15 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms8)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E6 o_af7); [| exact HS7' | exact HF8]; exact (MN14 Hm0)).
clear HS7'.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VO8 : VO B ly S W sp0 mem md MUT (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms8) mat8 VO7') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vo_windows_sound E6 o_af7 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vo_windows_sound E6 o_af7 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E6 o_st8 ms8 sp0 HS8 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
clear VO7' HF8 HFr8.
assert (SRA8' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms8)) SHADOW_OFF 84072 0) by (intros y Hy; lia).
assert (SHU8' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms8)) 84072 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E6 o_st8 ms8 _ ly S sp0 o_r08 o_rest8 125 RA_FX OSP_FX
(SLit STDOUT_BUFA) (SLit 84072) (SLit 0) (STDOUT_BUFA) (84072) 0
HS8 ltac:(rewrite HBcode; reflexivity) eq_refl Usp6 G3_6 G4_6 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO8) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E6 sp0 ap o_rest8 (STDOUT_BUFA) 0 ltac:(vm_compute; reflexivity) G12_6 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E6 sp0 ap o_rest8 ltac:(vm_compute; reflexivity) G12_6 Hap1 Hap2)
(vo_rest_w E6 o_rest8 ltac:(vm_compute; reflexivity))
(proj1 VO8) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO8)))
ltac:(intros a Ha; lia) SRA8' SHU8'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8' & HMNx16). cbn [cfg_model] in HAI8'.
assert (MN16 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms8')) by (intros Hm0; exact (HMNx16 (MN15 Hm0))).
rewrite wvb_wvb in HAI8', HAR8' |- *.
change (vf_after_icpt 125 o_st8 RA_FX OSP_FX 0 []) with o_af8 in HS8'.
assert (VO8' : VO B ly S W sp0 mem md MUT (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((STDOUT_BUFA) <= a < (STDOUT_BUFA) + 0))).
- exact VO8.
- exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr8'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm8'. }
remember (havoc E6 125 (map (getr (ms_regs ms8')) CLOB)) as E7 eqn:HE7.
assert (OLD7 : forall j, (j < 125)%nat -> ew E7 j = ew E6 j) by (intros j Hj; rewrite HE7; apply ew_havoc_old; exact Hj).
assert (Usp7 : bv_unsigned (ew E7 2) = sp0) by (rewrite OLD7 by (cbv; lia); exact Usp6).
assert (G3_7 : ew E7 3 = w64 (as_gp B)) by (rewrite OLD7 by (cbv; lia); exact G3_6).
assert (G4_7 : ew E7 4 = w64 (as_tp B)) by (rewrite OLD7 by (cbv; lia); exact G4_6).
assert (G12_7 : bv_unsigned (ew E7 12) = ap) by (rewrite OLD7 by (cbv; lia); exact G12_6).
assert (HAE7 : env_agree 32 EA E7)
by (rewrite HE7; apply env_agree_havoc_ge; [cbv; lia | exact HAE6]).
clear HE7 HS8 VO8 SRA8' SHU8' Heff8'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E7 o_af8 o_st9 _ _ _ HS8' o_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9.
assert (MN17 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms9)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E7 o_af8); [| exact HS8' | exact HF9]; exact (MN16 Hm0)).
clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VO9 : VO B ly S W sp0 mem md MUT (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms9) mat9 VO8') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vo_windows_sound E7 o_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vo_windows_sound E7 o_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp7 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E7 o_st9 ms9 sp0 HS9 ltac:(vm_compute; reflexivity) Usp7 ltac:(lia)). }
clear VO8' HF9 HFr9.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms9) (v_jalr (getr (ms_regs ms9) 1) 0) (ms_mem ms9) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI9 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E7); [exact HS9 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VO9 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS9 (1%bv : bv 5) Q1.
rewrite OLD7, OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E7 _ _ 10 HS9) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end. cbn [sv_denot] in Q10.
replace (v_jalr (getr (ms_regs ms9) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat9 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat9 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms9) (ms_mem ms9) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (alc_frame _ _ LAWS ly S [] W (ms_mem ms9) _ (ms_mem ms9) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (YE2ycf.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E7 _ _ regs _ HS9 HAE7 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS9 as (_ & _ & _ & _ & _ & _ & _ & Hmem9 & _).
split.
-- unfold ofile_is, stdout_fields1.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem o_st9) _ _ _ Hmem9); vm_compute; reflexivity).
-- eapply (val_mem_of_lit E7 (mrestrict (w_H W) (ms_mem ms9)) (ss_mem o_st9) _ _ _ Hmem9); vm_compute; reflexivity.
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
* exact MN17.
Qed.

Theorem tfib_vfprintf_stdout_next_mn : forall ly S (W : world tfibsegs) regs mem md ap cval wp T,
ecall_pre_cf tfibsegs B ly S [] W regs mem md ->
2 ^ 44 <= spZ regs -> ly_stk_lo ly + VF_STK <= spZ regs ->
(forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDOUT -> getr regs 11 = w64 FMT_d -> getr regs 12 = w64 ap ->
spZ regs <= ap -> ap + 8 <= 2 ^ 47 -> ap mod 8 = 0 ->
val_mem tfibsegs (mrestrict (w_H W) mem) ap 8 0 ->
stdout_mid wp (mrestrict (w_H W) mem) -> STDOUT_BUFA <= wp -> wp + 2 <= STDOUT_BUFA + STDOUT_BSZ ->
(forall a, vo_file a \/ STDOUT_BUFA <= a < STDOUT_BUFA + STDOUT_BSZ -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF STDOUT_BUFA STDOUT_BSZ ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) STDOUT_BUFA STDOUT_BSZ ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF FMT_d 4 ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) FMT_d 4 ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
ARcf tfibsegs B ly S [] W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 2 ->
stdout_mid (wp + 2) (mrestrict (w_H W) mem') ->
aview tfibsegs (w_H W) mem' wp = Some 48 -> aview tfibsegs (w_H W) mem' (wp + 1) = Some 10 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_band (spZ regs) a -> ~ vo_mut wp (wp + 2) a ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vo_mut wp (wp + 2) a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
(MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs mem') ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs mem md) T.
Proof.
intros ly S W regs mem md ap cval wp T HPRE Hsp44 Hstk Hpres Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP Hwp1 Hwp2 HBown Hgot Hcan Hcv Hro Hra_b Hhull_b Hra_f Hhull_f HAI0 HK.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = ltac:(zval ESTACK)) by reflexivity. assert (HVF : VF_STK = ltac:(zval VF_STK)) by reflexivity.
assert (HFF : F_STDOUT = ltac:(zval F_STDOUT)) by reflexivity. assert (HFS : FILE_SZ = ltac:(zval FILE_SZ)) by reflexivity.
assert (HBF : STDOUT_BUFA = ltac:(zval STDOUT_BUFA)) by reflexivity. assert (HBS : STDOUT_BSZ = ltac:(zval STDOUT_BSZ)) by reflexivity.
assert (HFD : FMT_d = ltac:(zval FMT_d)) by reflexivity. assert (HPO : PAD_OFF = ltac:(zval PAD_OFF)) by reflexivity. assert (HOX : OSP_FX = ltac:(zval OSP_FX)) by reflexivity.
assert (HBE : BUFEND = ltac:(zval BUFEND)) by reflexivity.
pose proof (amc_layout B ly S [] _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
set (sp0 := spZ regs) in *. assert (HtopS : sp0 < kHighMemEnd) by (rewrite KHI; lia).
assert (Hsp47 : sp0 <= 2 ^ 47) by lia.
set (MUT := vo_mut wp (wp + 2)) in *.
assert (MUTimg : forall a, MUT a -> img_byte_ok tfibsegs a = true) by (intros a Ha; apply (vo_mut_img wp (wp + 2) a); [lia | lia | exact Ha]).
assert (MUTdec : forall a, MUT a \/ ~ MUT a) by (intros a; apply vo_mut_dec).
assert (HFownM : forall a, MUT a -> ~ aowned B ly S a) by (intros a [Ha|Ha]; apply HBown; [left; exact Ha | right; lia]).
unfold cfg_at. change (w64 A_vfprintf) with (Z_to_bv 64 A_vfprintf).
pose proof (vo_entry1 W regs mem ap cval wp Hsp44 Hsp47 Hal16 ltac:(intros a Ha; apply Hpres; exact Ha) Ha0 Ha1 Ha2 Hap1 Hap2 Hap8 Harg
HFP ltac:(lia) Hgot Hcan Hcv Hro) as HS0.
set (EL := [Z_to_bv 64 0; Z_to_bv 64 cval; Z_to_bv 64 wp]) in *.
remember (Ereg regs EL) as E0 eqn:HE0.
assert (EE : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r)
by (intros i r Hi; rewrite HE0; exact (ew_Ereg_nat regs _ i r Hi)).
pose proof (EE 1%nat (1%bv : bv 5) eq_refl) as E0_1.
assert (Usp0 : bv_unsigned (ew E0 2) = sp0) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (G3_0 : ew E0 3 = w64 (as_gp B)) by (rewrite (EE 3%nat (3%bv : bv 5) eq_refl); exact Hgp).
assert (G4_0 : ew E0 4 = w64 (as_tp B)) by (rewrite (EE 4%nat (4%bv : bv 5) eq_refl); exact Htp).
assert (G12_0 : bv_unsigned (ew E0 12) = ap) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl), Ha2; apply unsigned_lit_small; lia).
assert (A34_0 : bv_unsigned (ew E0 34) = wp) by (rewrite HE0; pose proof (ew_Ereg_extra regs EL 2) as X; cbn [nth Nat.add EL] in X; rewrite X; apply unsigned_lit_small; lia).
assert (HAE0 : env_agree 32 (Ereg regs EL) E0) by (rewrite HE0; split; [intros i Hi; reflexivity | reflexivity]).
set (EA := Ereg regs EL) in *.
clear HE0 EE.
pose proof (VO_init B ly S W sp0 mem md MUT HAR Hpres) as VO0.
assert (MN0 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs mem) by (intros Hm0; exact Hm0).
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 ss_vo1 n_st1 _ _ _ HS0 n_run1) HAI0).
intros W1 c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1.
assert (MN1 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms1)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E0 ss_vo1); [| exact HS0 | exact HF1]; exact (MN0 Hm0)).
clear HS0.
rewrite ?wvb_wvb in HAI1 |- *.
assert (VO1 : VO B ly S W sp0 mem md MUT (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms1) mat1 VO0) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF1. intros Hin. destruct (vo_windows_sound E0 ss_vo1 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr1. intros Hin. destruct (vo_windows_sound E0 ss_vo1 sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E0 n_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VO0 HF1 HFr1.
pose proof (st_ok_add_cond tfibsegs E0 n_st1 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0) HS1 ltac:(rewrite branch_geu_U, U_SLit; change (zcanon 0) with 0; apply Bool.negb_true_iff; apply Z.ltb_ge; pose proof (U_range E0 (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND)))); lia)) as HS1c.
change (YP06.add_cond n_st1 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 0))) with n_st1c in HS1c. clear HS1.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E0 n_st1c n_st2 _ _ _ HS1c n_run2) HAI1).
intros W2 c2 _ HAI2 (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). cbn [cfg_model] in HAI2.
assert (MN2 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms2)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E0 n_st1c); [| exact HS1c | exact HF2]; exact (MN1 Hm0)).
clear HS1c.
rewrite ?wvb_wvb in HAI2 |- *.
assert (VO2 : VO B ly S W sp0 mem md MUT (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms2) mat2 VO1) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF2. intros Hin. destruct (vo_windows_sound E0 n_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr2. intros Hin. destruct (vo_windows_sound E0 n_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E0 n_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VO1 HF2 HFr2.
assert (SRA2' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms2)) SHADOW_OFF (FMT_d) 0) by (intros y Hy; lia).
assert (SHU2' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms2)) (FMT_d) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E0 n_st2 ms2 _ ly S sp0 n_r02 n_rest2 35 RA_FX OSP_FX
(SOff 34 0) (SLit FMT_d) (SLit 0) (wp) (FMT_d) 0
HS2 ltac:(rewrite HBcode; reflexivity) eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A34_0; reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO2) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E0 sp0 ap n_rest2 (wp) 0 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E0 sp0 ap n_rest2 ltac:(vm_compute; reflexivity) G12_0 Hap1 Hap2)
(vo_rest_w E0 n_rest2 ltac:(vm_compute; reflexivity))
(proj1 VO2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO2)))
ltac:(intros a Ha; lia) SRA2' SHU2'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI2).
intros W2' c2' _ HAI2' (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Heff2' & Hfr2' & Hpm2' & HMNx3). cbn [cfg_model] in HAI2'.
assert (MN3 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms2')) by (intros Hm0; exact (HMNx3 (MN2 Hm0))).
rewrite wvb_wvb in HAI2', HAR2' |- *.
change (vf_after_icpt 35 n_st2 RA_FX OSP_FX 0 []) with n_af2 in HS2'.
assert (VO2' : VO B ly S W sp0 mem md MUT (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms2) _ (ms_mem ms2') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 0))).
- exact VO2.
- exact HAR2'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm2'. }
remember (havoc E0 35 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 35)%nat -> ew E1 j = ew E0 j) by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (G12_1 : bv_unsigned (ew E1 12) = ap) by (rewrite OLD1 by (cbv; lia); exact G12_0).
assert (A34_1 : bv_unsigned (ew E1 34) = wp) by (rewrite OLD1 by (cbv; lia); exact A34_0).
assert (HAE1 : env_agree 32 EA E1)
by (rewrite HE1; apply env_agree_havoc_ge; [cbv; lia | exact HAE0]).
clear HE1 HS2 VO2 SRA2' SHU2' Heff2'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E1 n_af2 n_st3 _ _ _ HS2' n_run3) HAI2').
intros W3 c3 _ HAI3 (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). cbn [cfg_model] in HAI3.
assert (MN4 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms3)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E1 n_af2); [| exact HS2' | exact HF3]; exact (MN3 Hm0)).
clear HS2'.
rewrite ?wvb_wvb in HAI3 |- *.
assert (VO3 : VO B ly S W sp0 mem md MUT (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms3) mat3 VO2') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF3. intros Hin. destruct (vo_windows_sound E1 n_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr3. intros Hin. destruct (vo_windows_sound E1 n_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E1 n_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VO2' HF3 HFr3.
assert (SRA3' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms3)) SHADOW_OFF (68476) 0) by (intros y Hy; lia).
assert (SHU3' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms3)) (68476) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E1 n_st3 ms3 _ ly S sp0 n_r03 n_rest3 51 RA_FX OSP_FX
(SOff 34 0) (SLit 68476) (SLit 0) (wp) (68476) 0
HS3 ltac:(rewrite HBcode; reflexivity) eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A34_1; reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO3) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E1 sp0 ap n_rest3 (wp) 0 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E1 sp0 ap n_rest3 ltac:(vm_compute; reflexivity) G12_1 Hap1 Hap2)
(vo_rest_w E1 n_rest3 ltac:(vm_compute; reflexivity))
(proj1 VO3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO3)))
ltac:(intros a Ha; lia) SRA3' SHU3'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI3).
intros W3' c3' _ HAI3' (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Heff3' & Hfr3' & Hpm3' & HMNx5). cbn [cfg_model] in HAI3'.
assert (MN5 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms3')) by (intros Hm0; exact (HMNx5 (MN4 Hm0))).
rewrite wvb_wvb in HAI3', HAR3' |- *.
change (vf_after_icpt 51 n_st3 RA_FX OSP_FX 0 []) with n_af3 in HS3'.
assert (VO3' : VO B ly S W sp0 mem md MUT (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms3) _ (ms_mem ms3') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 0))).
- exact VO3.
- exact HAR3'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm3'. }
remember (havoc E1 51 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 51)%nat -> ew E2 j = ew E1 j) by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (G12_2 : bv_unsigned (ew E2 12) = ap) by (rewrite OLD2 by (cbv; lia); exact G12_1).
assert (A34_2 : bv_unsigned (ew E2 34) = wp) by (rewrite OLD2 by (cbv; lia); exact A34_1).
assert (HAE2 : env_agree 32 EA E2)
by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE1]).
clear HE2 HS3 VO3 SRA3' SHU3' Heff3'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E2 n_af3 n_st4 _ _ _ HS3' n_run4) HAI3').
intros W4 c4 _ HAI4 (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). cbn [cfg_model] in HAI4.
assert (MN6 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms4)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E2 n_af3); [| exact HS3' | exact HF4]; exact (MN5 Hm0)).
clear HS3'.
rewrite ?wvb_wvb in HAI4 |- *.
assert (VO4 : VO B ly S W sp0 mem md MUT (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms4) mat4 VO3') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF4. intros Hin. destruct (vo_windows_sound E2 n_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr4. intros Hin. destruct (vo_windows_sound E2 n_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E2 n_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VO3' HF4 HFr4.
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memset_mn W E2 n_st4 ms4 _ ly S sp0 n_r04 n_rest4 67 RA_PAD OSP_PC PAD_OFF 48 1%nat
HS4 ltac:(rewrite HBcode; reflexivity) eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(lia) ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_PC; lia) ltac:(unfold OSP_PC, PAD_OFF; lia) ltac:(unfold PAD_OFF; cbn; lia) ltac:(unfold RA_PAD; lia) ltac:(reflexivity)
(vo_rest_ok E2 sp0 ap n_rest4 ltac:(vm_compute; reflexivity) G12_2 Hap1 Hap2)
(vo_rest_w E2 n_rest4 ltac:(vm_compute; reflexivity))
(proj1 VO4) Hsp44 Hal16 Hstk Htop HtopS (proj1 (proj2 (proj2 VO4)))) HAI4).
intros W4' c4' _ HAI4' (-> & ms4' & mat4' & -> & HS4' & HAR4' & HP4' & Hfr4' & Hpm4' & HMNx7). cbn [cfg_model] in HAI4'.
assert (MN7 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms4')) by (intros Hm0; exact (HMNx7 (MN6 Hm0))).
rewrite wvb_wvb in HAI4', HAR4' |- *.
change (vf_after_icpt 67 n_st4 RA_PAD OSP_PC PAD_OFF (repeat 48 1%nat)) with n_af4 in HS4'.
assert (VO4' : VO B ly S W sp0 mem md MUT (ms_mem ms4') (with_vm_backing (m_vm_lazy md) mat4' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms4) _ (ms_mem ms4') _
(fun a => (sp0 + OSP_PC - ESTACK <= a < sp0 + OSP_PC) \/ (sp0 + PAD_OFF <= a < sp0 + PAD_OFF + 1))).
- exact VO4.
- exact HAR4'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat4' mat4 md). apply with_vm_backing_same.
- intros a Ha. left. unfold vf_band, OSP_PC, PAD_OFF in *. lia.
- intros a Hr Hna. apply Hfr4'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; cbn; exact H'].
- exact Hpm4'. }
remember (havoc E2 67 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 67)%nat -> ew E3 j = ew E2 j) by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (G12_3 : bv_unsigned (ew E3 12) = ap) by (rewrite OLD3 by (cbv; lia); exact G12_2).
assert (A34_3 : bv_unsigned (ew E3 34) = wp) by (rewrite OLD3 by (cbv; lia); exact A34_2).
assert (HAE3 : env_agree 32 EA E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3 HS4 VO4.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 n_af4 n_st5 _ _ _ HS4' n_run5) HAI4').
intros W5 c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5.
assert (MN8 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms5)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E3 n_af4); [| exact HS4' | exact HF5]; exact (MN7 Hm0)).
clear HS4'.
rewrite ?wvb_wvb in HAI5 |- *.
assert (VO5 : VO B ly S W sp0 mem md MUT (ms_mem ms5) (with_vm_backing (m_vm_lazy md) mat5 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms5) mat5 VO4') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF5. intros Hin. destruct (vo_windows_sound E3 n_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr5. intros Hin. destruct (vo_windows_sound E3 n_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E3 n_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VO4' HF5 HFr5.
pose proof (st_ok_add_cond tfibsegs E3 n_st5 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1) HS5 ltac:(rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A34_3; unfold M64; lia); rewrite A34_3; change (zcanon 1) with 1; apply Bool.negb_true_iff; apply Z.ltb_ge; lia)) as HS5c.
change (YP06.add_cond n_st5 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (0 - BUFEND))) (SLit 1))) with n_st5c in HS5c. clear HS5.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E3 n_st5c n_st6 _ _ _ HS5c n_run6) HAI5).
intros W6 c6 _ HAI6 (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). cbn [cfg_model] in HAI6.
assert (MN9 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms6)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E3 n_st5c); [| exact HS5c | exact HF6]; exact (MN8 Hm0)).
clear HS5c.
rewrite ?wvb_wvb in HAI6 |- *.
assert (VO6 : VO B ly S W sp0 mem md MUT (ms_mem ms6) (with_vm_backing (m_vm_lazy md) mat6 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms6) mat6 VO5) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF6. intros Hin. destruct (vo_windows_sound E3 n_st5c sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr6. intros Hin. destruct (vo_windows_sound E3 n_st5c sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E3 n_st6 ms6 sp0 HS6 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia)). }
clear VO5 HF6 HFr6.
pose proof HS6 as HSc6. destruct HSc6 as (_ & _ & _ & _ & _ & _ & _ & Hmem6 & _). cbn [restrict ms_mem] in Hmem6.
assert (PAD6 : aview tfibsegs (w_H W) (ms_mem ms6) (sp0 + PAD_OFF) = Some 48).
{ replace (sp0 + PAD_OFF) with (sp0 + PAD_OFF + Z.of_nat 0) by lia.
apply (lit_buf_aview W E3 (ms_mem ms6) (ss_mem n_st6) (SOff 2 PAD_OFF) (sp0 + PAD_OFF) 1 [48] Hmem6 ltac:(vm_compute; reflexivity)
ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) ltac:(repeat constructor; lia) 0%nat ltac:(lia)). }
clear Hmem6.
destruct (vf_stack_shadow B LAWS W ly S (ms_mem ms6) _ sp0 (sp0 + PAD_OFF) 1 (proj1 VO6) Hstk Htop ltac:(unfold PAD_OFF; lia) ltac:(unfold PAD_OFF; lia) ltac:(lia)) as [SRA6' SHU6'].
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms6) _ STDOUT_BUFA STDOUT_BSZ wp 1 VO6 ltac:(lia) Hstk Hra_b Hhull_b
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [DRA6' DHU6'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E3 n_st6 ms6 _ ly S sp0 n_r06 n_rest6 83 RA_FX OSP_FX
(SOff 34 0) (SOff 2 PAD_OFF) (SLit 1) (wp) (sp0 + PAD_OFF) 1
HS6 ltac:(rewrite HBcode; reflexivity) eq_refl Usp3 G3_3 G4_3 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite Z.add_0_r, A34_3; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp3; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO6) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E3 sp0 ap n_rest6 (wp) 1 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E3 sp0 ap n_rest6 ltac:(vm_compute; reflexivity) G12_3 Hap1 Hap2)
(vo_rest_w E3 n_rest6 ltac:(vm_compute; reflexivity))
(proj1 VO6) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO6)))
ltac:(intros a Ha; replace a with (sp0 + PAD_OFF) by lia; rewrite PAD6; discriminate) SRA6' SHU6'
ltac:(intros a Ha; split; [apply stdout_buf_writable; lia | apply HBown; right; lia]) ltac:(exact DRA6') ltac:(exact DHU6')) HAI6).
intros W6' c6' _ HAI6' (-> & ms6' & mat6' & -> & HS6' & HAR6' & HP6' & Heff6' & Hfr6' & Hpm6' & HMNx10). cbn [cfg_model] in HAI6'.
assert (MN10 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms6')) by (intros Hm0; exact (HMNx10 (MN9 Hm0))).
rewrite wvb_wvb in HAI6', HAR6' |- *.
change (vf_after_icpt 83 n_st6 RA_FX OSP_FX 0 []) with n_af6 in HS6'.
assert (VO6' : VO B ly S W sp0 mem md MUT (ms_mem ms6') (with_vm_backing (m_vm_lazy md) mat6' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms6) _ (ms_mem ms6') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp) <= a < (wp) + 1))).
- exact VO6.
- exact HAR6'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat6' mat6 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr6'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm6'. }
assert (BUFA6' : aview tfibsegs (w_H W) (ms_mem ms6') (wp) = Some 48).
{ rewrite <- PAD6, <- (Z.add_0_r wp), <- (Z.add_0_r (sp0 + PAD_OFF)). apply (Heff6' 0). lia. }
remember (havoc E3 83 (map (getr (ms_regs ms6')) CLOB)) as E4 eqn:HE4.
assert (OLD4 : forall j, (j < 83)%nat -> ew E4 j = ew E3 j) by (intros j Hj; rewrite HE4; apply ew_havoc_old; exact Hj).
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp3).
assert (G3_4 : ew E4 3 = w64 (as_gp B)) by (rewrite OLD4 by (cbv; lia); exact G3_3).
assert (G4_4 : ew E4 4 = w64 (as_tp B)) by (rewrite OLD4 by (cbv; lia); exact G4_3).
assert (G12_4 : bv_unsigned (ew E4 12) = ap) by (rewrite OLD4 by (cbv; lia); exact G12_3).
assert (A34_4 : bv_unsigned (ew E4 34) = wp) by (rewrite OLD4 by (cbv; lia); exact A34_3).
assert (HAE4 : env_agree 32 EA E4)
by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
clear HE4 HS6 VO6 SRA6' SHU6' Heff6'.
clear PAD6 DRA6' DHU6'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 n_af6 n_st7 _ _ _ HS6' n_run7) HAI6').
intros W7 c7 _ HAI7 (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). cbn [cfg_model] in HAI7.
assert (MN11 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms7)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E4 n_af6); [| exact HS6' | exact HF7]; exact (MN10 Hm0)).
clear HS6'.
rewrite ?wvb_wvb in HAI7 |- *.
assert (VO7 : VO B ly S W sp0 mem md MUT (ms_mem ms7) (with_vm_backing (m_vm_lazy md) mat7 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms7) mat7 VO6') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF7. intros Hin. destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr7. intros Hin. destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E4 n_st7 ms7 sp0 HS7 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
assert (BUFA7 : aview tfibsegs (w_H W) (ms_mem ms7) (wp) = Some 48).
{ rewrite <- BUFA6'. apply aview_eq_of. apply HFr7. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 n_af6 sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO6' HF7 HFr7 BUFA6'.
pose proof (st_ok_add_cond tfibsegs E4 n_st7 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0) HS7 ltac:(rewrite branch_geu_U, U_SLit; change (zcanon 0) with 0; apply Bool.negb_true_iff; apply Z.ltb_ge; pose proof (U_range E4 (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND)))); lia)) as HS7c.
change (YP06.add_cond n_st7 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 0))) with n_st7c in HS7c. clear HS7.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E4 n_st7c n_st8 _ _ _ HS7c n_run8) HAI7).
intros W8 c8 _ HAI8 (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). cbn [cfg_model] in HAI8.
assert (MN12 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms8)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E4 n_st7c); [| exact HS7c | exact HF8]; exact (MN11 Hm0)).
clear HS7c.
rewrite ?wvb_wvb in HAI8 |- *.
assert (VO8 : VO B ly S W sp0 mem md MUT (ms_mem ms8) (with_vm_backing (m_vm_lazy md) mat8 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms8) mat8 VO7) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF8. intros Hin. destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr8. intros Hin. destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E4 n_st8 ms8 sp0 HS8 ltac:(vm_compute; reflexivity) Usp4 ltac:(lia)). }
assert (BUFA8 : aview tfibsegs (w_H W) (ms_mem ms8) (wp) = Some 48).
{ rewrite <- BUFA7. apply aview_eq_of. apply HFr8. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E4 n_st7c sp0 _ ltac:(vm_compute; reflexivity) Usp4 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO7 HF8 HFr8 BUFA7.
assert (SRA8' : range_addressable (aview tfibsegs (w_H W) (ms_mem ms8)) SHADOW_OFF (sp0 + PAD_OFF) 0) by (intros y Hy; lia).
assert (SHU8' : 0 < 0 -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms8)) (sp0 + PAD_OFF) 0) by (intros H0; lia).
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E4 n_st8 ms8 _ ly S sp0 n_r08 n_rest8 99 RA_FX OSP_FX
(SOff 34 1) (SOff 2 PAD_OFF) (SLit 0) (wp + 1) (sp0 + PAD_OFF) 0
HS8 ltac:(rewrite HBcode; reflexivity) eq_refl Usp4 G3_4 G4_4 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite A34_4; reflexivity) eq_refl ltac:(cbn [sv_denot]; rewrite Usp4; reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO8) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E4 sp0 ap n_rest8 (wp + 1) 0 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E4 sp0 ap n_rest8 ltac:(vm_compute; reflexivity) G12_4 Hap1 Hap2)
(vo_rest_w E4 n_rest8 ltac:(vm_compute; reflexivity))
(proj1 VO8) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO8)))
ltac:(intros a Ha; lia) SRA8' SHU8'
ltac:(intros a Ha; lia) ltac:(intros y Hy; lia) ltac:(intros H0; lia)) HAI8).
intros W8' c8' _ HAI8' (-> & ms8' & mat8' & -> & HS8' & HAR8' & HP8' & Heff8' & Hfr8' & Hpm8' & HMNx13). cbn [cfg_model] in HAI8'.
assert (MN13 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms8')) by (intros Hm0; exact (HMNx13 (MN12 Hm0))).
rewrite wvb_wvb in HAI8', HAR8' |- *.
change (vf_after_icpt 99 n_st8 RA_FX OSP_FX 0 []) with n_af8 in HS8'.
assert (VO8' : VO B ly S W sp0 mem md MUT (ms_mem ms8') (with_vm_backing (m_vm_lazy md) mat8' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms8) _ (ms_mem ms8') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp + 1) <= a < (wp + 1) + 0))).
- exact VO8.
- exact HAR8'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat8' mat8 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr8'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm8'. }
assert (BUFA8' : aview tfibsegs (w_H W) (ms_mem ms8') (wp) = Some 48).
{ rewrite <- BUFA8. apply Hfr8'; [GEO | GEO | GEO]. }
remember (havoc E4 99 (map (getr (ms_regs ms8')) CLOB)) as E5 eqn:HE5.
assert (OLD5 : forall j, (j < 99)%nat -> ew E5 j = ew E4 j) by (intros j Hj; rewrite HE5; apply ew_havoc_old; exact Hj).
assert (Usp5 : bv_unsigned (ew E5 2) = sp0) by (rewrite OLD5 by (cbv; lia); exact Usp4).
assert (G3_5 : ew E5 3 = w64 (as_gp B)) by (rewrite OLD5 by (cbv; lia); exact G3_4).
assert (G4_5 : ew E5 4 = w64 (as_tp B)) by (rewrite OLD5 by (cbv; lia); exact G4_4).
assert (G12_5 : bv_unsigned (ew E5 12) = ap) by (rewrite OLD5 by (cbv; lia); exact G12_4).
assert (A34_5 : bv_unsigned (ew E5 34) = wp) by (rewrite OLD5 by (cbv; lia); exact A34_4).
assert (HAE5 : env_agree 32 EA E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
clear HE5 HS8 VO8 SRA8' SHU8' Heff8' BUFA8.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 n_af8 n_st9 _ _ _ HS8' n_run9) HAI8').
intros W9 c9 _ HAI9 (-> & ms9 & mat9 & -> & HS9 & HF9 & HFr9). cbn [cfg_model] in HAI9.
assert (MN14 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms9)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E5 n_af8); [| exact HS8' | exact HF9]; exact (MN13 Hm0)).
clear HS8'.
rewrite ?wvb_wvb in HAI9 |- *.
assert (VO9 : VO B ly S W sp0 mem md MUT (ms_mem ms9) (with_vm_backing (m_vm_lazy md) mat9 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms9) mat9 VO8') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF9. intros Hin. destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr9. intros Hin. destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E5 n_st9 ms9 sp0 HS9 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUFA9 : aview tfibsegs (w_H W) (ms_mem ms9) (wp) = Some 48).
{ rewrite <- BUFA8'. apply aview_eq_of. apply HFr9. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 n_af8 sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO8' HF9 HFr9 BUFA8'.
pose proof (st_ok_add_cond tfibsegs E5 n_st9 _ BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1) HS9 ltac:(rewrite branch_geu_U, U_neg_off, U_SLit by (rewrite A34_5; unfold M64; lia); rewrite A34_5; change (zcanon 1) with 1; apply Bool.negb_true_iff; apply Z.ltb_ge; lia)) as HS9c.
change (YP06.add_cond n_st9 (mkAC BC_GEU (SAlu ALU_SUB (SLit 0) (SOff 34 (1 - BUFEND))) (SLit 1))) with n_st9c in HS9c. clear HS9.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E5 n_st9c n_st10 _ _ _ HS9c n_run10) HAI9).
intros W10 c10 _ HAI10 (-> & ms10 & mat10 & -> & HS10 & HF10 & HFr10). cbn [cfg_model] in HAI10.
assert (MN15 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms10)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E5 n_st9c); [| exact HS9c | exact HF10]; exact (MN14 Hm0)).
clear HS9c.
rewrite ?wvb_wvb in HAI10 |- *.
assert (VO10 : VO B ly S W sp0 mem md MUT (ms_mem ms10) (with_vm_backing (m_vm_lazy md) mat10 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms10) mat10 VO9) as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF10. intros Hin. destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr10. intros Hin. destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E5 n_st10 ms10 sp0 HS10 ltac:(vm_compute; reflexivity) Usp5 ltac:(lia)). }
assert (BUFA10 : aview tfibsegs (w_H W) (ms_mem ms10) (wp) = Some 48).
{ rewrite <- BUFA9. apply aview_eq_of. apply HFr10. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E5 n_st9c sp0 _ ltac:(vm_compute; reflexivity) Usp5 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO9 HF10 HFr10 BUFA9.
pose proof HS10 as HSc10. destruct HSc10 as (_ & _ & _ & _ & _ & _ & _ & Hmem10 & _). cbn [restrict ms_mem] in Hmem10.
assert (NL10 : aview tfibsegs (w_H W) (ms_mem ms10) 84071 = Some 10).
{ change 84071 with (84071 + Z.of_nat 0).
apply (lit_buf_aview W E5 (ms_mem ms10) (ss_mem n_st10) (SLit 84071) 84071 1 [10] Hmem10 ltac:(vm_compute; reflexivity) eq_refl ltac:(repeat constructor; lia) 0%nat ltac:(lia)). }
clear Hmem10.
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms10) _ FMT_d 4 84071 1 VO10 ltac:(lia) Hstk Hra_f Hhull_f
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [SRA10' SHU10'].
destruct (vo_shadow_xfer B ly S W sp0 mem md wp (wp + 2) (ms_mem ms10) _ STDOUT_BUFA STDOUT_BSZ (wp + 1) 1 VO10 ltac:(lia) Hstk Hra_b Hhull_b
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite KHI; lia)) as [DRA10' DHU10'].
eapply (SRr_srealizes tfibsegs W _ _ _
(vf_icpt_memcpy_ext_mn W E5 n_st10 ms10 _ ly S sp0 n_r010 n_rest10 115 RA_FX OSP_FX
(SOff 34 1) (SLit 84071) (SLit 1) (wp + 1) (84071) 1
HS10 ltac:(rewrite HBcode; reflexivity) eq_refl Usp5 G3_5 G4_5 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
eq_refl ltac:(cbn [sv_denot]; rewrite A34_5; reflexivity) eq_refl ltac:(reflexivity) eq_refl ltac:(reflexivity)
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_FX; lia) ltac:(unfold OSP_FX; lia) ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(lia)
ltac:(unfold RA_FX; lia) ltac:(reflexivity)
ltac:(GEO) ltac:(GEO) ltac:(GEO) ltac:(GEO)
ltac:(left; unfold kLowMemEnd; GEO)
ltac:(first [left; unfold kLowMemEnd; GEO | eapply (vf_stack_amem B); [exact (proj1 VO10) | exact Hstk | exact HtopS | GEO | GEO]])
(vo_rest_disj E5 sp0 ap n_rest10 (wp + 1) 1 ltac:(vm_compute; reflexivity) G12_5 Hap1 Hsp44 ltac:(GEO) ltac:(GEO) ltac:(lia))
(vo_rest_ok E5 sp0 ap n_rest10 ltac:(vm_compute; reflexivity) G12_5 Hap1 Hap2)
(vo_rest_w E5 n_rest10 ltac:(vm_compute; reflexivity))
(proj1 VO10) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VO10)))
ltac:(intros a Ha; replace a with 84071 by lia; rewrite NL10; discriminate) SRA10' SHU10'
ltac:(intros a Ha; split; [apply stdout_buf_writable; lia | apply HBown; right; lia]) ltac:(exact DRA10') ltac:(exact DHU10')) HAI10).
intros W10' c10' _ HAI10' (-> & ms10' & mat10' & -> & HS10' & HAR10' & HP10' & Heff10' & Hfr10' & Hpm10' & HMNx16). cbn [cfg_model] in HAI10'.
assert (MN16 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms10')) by (intros Hm0; exact (HMNx16 (MN15 Hm0))).
rewrite wvb_wvb in HAI10', HAR10' |- *.
change (vf_after_icpt 115 n_st10 RA_FX OSP_FX 0 []) with n_af10 in HS10'.
assert (VO10' : VO B ly S W sp0 mem md MUT (ms_mem ms10') (with_vm_backing (m_vm_lazy md) mat10' md)).
{ eapply (VO_splice B ly S W sp0 mem md MUT (ms_mem ms10) _ (ms_mem ms10') _
(fun a => (sp0 + OSP_FX - ESTACK <= a < sp0 + OSP_FX) \/ ((wp + 1) <= a < (wp + 1) + 1))).
- exact VO10.
- exact HAR10'.
- rewrite <- (wvb_collapse (m_vm_lazy md) mat10' mat10 md). apply with_vm_backing_same.
- intros a [Ha|Ha]; [left; unfold vf_band, OSP_FX in *; lia | right; unfold MUT, vo_mut; GEO].
- intros a Hr Hna. apply Hfr10'; [exact Hr | intros H'; apply Hna; left; exact H' | intros H'; apply Hna; right; exact H'].
- exact Hpm10'. }
assert (BUFA10' : aview tfibsegs (w_H W) (ms_mem ms10') (wp) = Some 48).
{ rewrite <- BUFA10. apply Hfr10'; [GEO | GEO | GEO]. }
assert (BUFB10' : aview tfibsegs (w_H W) (ms_mem ms10') (wp + 1) = Some 10).
{ replace (wp + 1) with (wp + 1 + 0) by lia. rewrite (Heff10' 0) by lia. rewrite Z.add_0_r. exact NL10. }
remember (havoc E5 115 (map (getr (ms_regs ms10')) CLOB)) as E6 eqn:HE6.
assert (OLD6 : forall j, (j < 115)%nat -> ew E6 j = ew E5 j) by (intros j Hj; rewrite HE6; apply ew_havoc_old; exact Hj).
assert (Usp6 : bv_unsigned (ew E6 2) = sp0) by (rewrite OLD6 by (cbv; lia); exact Usp5).
assert (G3_6 : ew E6 3 = w64 (as_gp B)) by (rewrite OLD6 by (cbv; lia); exact G3_5).
assert (G4_6 : ew E6 4 = w64 (as_tp B)) by (rewrite OLD6 by (cbv; lia); exact G4_5).
assert (G12_6 : bv_unsigned (ew E6 12) = ap) by (rewrite OLD6 by (cbv; lia); exact G12_5).
assert (A34_6 : bv_unsigned (ew E6 34) = wp) by (rewrite OLD6 by (cbv; lia); exact A34_5).
assert (HAE6 : env_agree 32 EA E6)
by (rewrite HE6; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
clear HE6 HS10 VO10 SRA10' SHU10' Heff10' BUFA10.
clear NL10 DRA10' DHU10'.
eapply (SRr_srealizes tfibsegs W _ _ _ (vf_phase W E6 n_af10 n_st11 _ _ _ HS10' n_run11) HAI10').
intros W11 c11 _ HAI11 (-> & ms11 & mat11 & -> & HS11 & HF11 & HFr11). cbn [cfg_model] in HAI11.
assert (MN17 : MN.memnorm tfibsegs mem -> MN.memnorm tfibsegs (ms_mem ms11)) by (intros Hm0; eapply (MX.memnorm_frame_of tfibsegs (w_H W) E6 n_af10); [| exact HS10' | exact HF11]; exact (MN16 Hm0)).
clear HS10'.
rewrite ?wvb_wvb in HAI11 |- *.
assert (VO11 : VO B ly S W sp0 mem md MUT (ms_mem ms11) (with_vm_backing (m_vm_lazy md) mat11 md)).
{ pose proof (VO_run B LAWS ly S W sp0 mem md MUT MUTimg MUTdec HFownM Hstk Htop _ _ (ms_mem ms11) mat11 VO10') as VR.
rewrite ?wvb_wvb in VR. apply VR.
- intros x Hx1 Hx2. apply HF11. intros Hin. destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- intros x Hx1 Hx2. apply HFr11. intros Hin. destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [exact (Hx1 Hw) | exact (Hx2 (or_introl Hw))].
- apply (vf_band_present W E6 n_st11 ms11 sp0 HS11 ltac:(vm_compute; reflexivity) Usp6 ltac:(lia)). }
assert (BUFA11 : aview tfibsegs (w_H W) (ms_mem ms11) (wp) = Some 48).
{ rewrite <- BUFA10'. apply aview_eq_of. apply HFr11. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
assert (BUFB11 : aview tfibsegs (w_H W) (ms_mem ms11) (wp + 1) = Some 10).
{ rewrite <- BUFB10'. apply aview_eq_of. apply HFr11. rewrite unsigned_lit_small by GEO. intros Hin.
destruct (vo_windows_sound E6 n_af10 sp0 _ ltac:(vm_compute; reflexivity) Usp6 Hin) as [Hw|Hw]; [unfold vf_band in Hw; GEO | unfold vo_file, F_STDOUT, FILE_SZ in Hw; GEO]. }
clear VO10' HF11 HFr11 BUFA10' BUFB10'.
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms11) (v_jalr (getr (ms_regs ms11) 1) 0) (ms_mem ms11) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md) mat' md)) T); [ | exact HAI11 | ].
{ eapply (SRr_ret_at tfibsegs tfibmusl_tbl tfibmusl_tbl_ok Hwx W E6); [exact HS11 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros WR cR _ HAIR (-> & matR & ->). cbn [cfg_model] in HAIR.
destruct VO11 as (HAR9 & Hsbm9 & Hpb9 & Hfr9 & Hpm9).
rreg HS11 (1%bv : bv 5) Q1.
rewrite OLD6, OLD5, OLD4, OLD3, OLD2, OLD1 in Q1 by (cbv; lia). rewrite E0_1 in Q1.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E6 _ _ 10 HS11) as Q10. cbn [ms_regs restrict] in Q10.
match type of Q10 with _ = sv_denot _ ?v => let v' := eval vm_compute in v in change v with v' in Q10 end. cbn [sv_denot] in Q10.
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (w64 (raZ regs))
by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
assert (SBMR : same_but_materialized (with_vm_backing (m_vm_lazy md) mat11 md) (with_vm_backing (m_vm_lazy md) matR md))
by (rewrite <- (wvb_collapse (m_vm_lazy md) matR mat11 md); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBMR) as MF.
apply (HK (ms_regs ms11) (ms_mem ms11) (with_vm_backing (m_vm_lazy md) matR md)).
* apply (alc_frame _ _ LAWS ly S [] W (ms_mem ms11) _ (ms_mem ms11) _ HAR9); [intros; reflexivity | intros a Hv; exact Hv | apply MF | apply MF | apply MF | exact (YE2ycf.hs_kept_refl _ _)].
* exact (aregs_preserved_of_st_ok _ E6 _ _ regs _ HS11 HAE6 ltac:(vm_compute; reflexivity)).
* apply with_vm_backing_same.
* rewrite Q10. reflexivity.
* destruct HS11 as (_ & _ & _ & _ & _ & _ & _ & Hmem11 & _).
split.
-- unfold ofile_is, stdout_fields1.
repeat apply Forall_cons; try apply Forall_nil;
(eapply (val_mem_of_lit E6 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem n_st11) _ _ _ Hmem11); vm_compute; reflexivity).
-- exact (val_mem_of_chunk8 E6 (mrestrict (w_H W) (ms_mem ms11)) (ss_mem n_st11) 1%nat (F_STDOUT + 40) (SOff 34 2) (wp + 2) Hmem11
ltac:(vm_compute; reflexivity) ltac:(cbn [sv_denot]; rewrite A34_6; reflexivity) ltac:(lia)).
* exact BUFA11.
* exact BUFB11.
* exact Hfr9.
* exact Hpm9.
* exact HAIR.
* exact MN17.
Qed.

End S.
End g.
