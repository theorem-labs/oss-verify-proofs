(* check_round_trip (fs.asan-ubsan 0x81b9c, build B), WALK LANE D2, segment 36: B 0x82418 -> 0x8249c, `mv s4, s2`, the
   shadow stores of the frame's objects and the first fuzz_free.
   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 6cf61486dca lib/A/FSH_crt_segD2_s36.v)
   PORT SOURCE: a working branch 6cf61486dca proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD2_s36.v, itself
   PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd21.v
   (stage St21, the same fuzz_free (back) call). The function-level lookup is the one quoted in the lane head
   (internal path) (checker a Theorem Labs lane, role check, CONFIRM). Same
   Definition / Lemma names and statement shapes as the A file, over image B; B twin written by a Theorem Labs
   lane.
   A -> B (MEASURED, crt.A.s / crt.B.s, by instruction meaning):
     entry boundary crtD2_INV_36           A 0x822bc                          B 0x82418
     text moved for segment 37             (A reads text from slot 0x30)      B 0x82418 `mv s4, s2` (s4 := atom 18)
     poison value                          A 0x822bc `addi s2, zero, -8`      B 0x8241c `addi s2, zero, -8`
     the shadow stores                     A 29 `sb s2, off(s3)` (SF = s3,    B 29 `sb s2, off(s10)` 0x82420..0x82490
                                             atom 19) 0x822c0..0x82330          (SF = s10, atom 26)
     a0 = back                             A `mv a0, s9` (atom 25)            B 0x82494 `mv a0, s9` (atom 25)
     the call                              A 0x82338 `jal fuzz_free`          B 0x82498 `jal fuzz_free`
     return / next boundary crtD2_INV_37   A 0x8233c                          B 0x8249c
   Non-mechanical changes: crtD2_ss36_ff_r also states s4 = atom 18 (text) and s3 = atom 19 (F) at the call, which give
   crtD2_INV_37's B register conjuncts `ew E 19 = F` (crt_INV_T's s3) and `ew E 20 = text` (segment 37's
   `mv a0, s4`) through the callee-saved s3 / s4; crtD2_w36's shadow region is atom 26's (A: 19); the read-only view
   at the next boundary is FSH_crt_site.crt_rom (A: s37's crtD2ff_rom, a local copy of it).

   Why the generic crt_seg_call does not cover it: crt_seg_call runs from crt_ss2 r0, which holds only the saved words
   and the s1 slots - the run's stores land in the frame's SHADOW region, which crt_ss2 does not have, and the
   frame's shadow lies below alloc_ceiling, so crt_hcall's `same_below .. alloc_ceiling` is false across this run.
   The step is therefore the base's crt_seg_call_full (FSH_crt_site.v): the run is FSH_crt_segD.v's
   crt_seg36_run (a journal / ARU step from the FULL four-region crt_ss36, write window crt_awr_ok), the flag word is
   read off the frame region at the call state, and the callee's part (crt_hcall_full) gets the run's two frame_of
   facts in place of same_below. What this file adds on top of that, beyond s37's shared fuzz_free core: the run's
   write window (the saved words, the s1 slots, the frame and its shadow) holds no image byte and no byte of a live
   block (crtD2_w36), so fs's statics and back's / text's blocks reach the call memory unchanged (crtD2_rblock_frame).

   What St21 of d25a984c903 does at this call, restated in S0's form: the callee frees back's reader block
   (back - HEAD, dec_size tb2 + HEAD) and its user-poisoned head; text's block is a different live block, outside the
   callee's footprint, so it and its head survive; g_live goes down by dec_size tb2. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret
FSW_frame FSW_frame3 FSW_rd FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_segD FSH_crt_segD2 FSH_crt_segD2_s37.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the call-site state crt_ss36_ff (MEASURED): the four regions with the frame region's flag chunk untouched (the
   stores go to region 3, the shadow), pc A_fuzz_free, ra 0x8249c, a0 = atom 25 (back), s8 = atom 24 (same),
   s4 = atom 18 (text, B's `mv s4, s2`), s3 = atom 19 (F) ---- *)
Lemma crtD2_ss36_ff_site4 : crt_csite4 crt_ss36_ff A_fuzz_free 0x8249c.
Proof. unfold crt_csite4. repeat split; vm_compute; reflexivity. Qed.
Lemma crtD2_ss36_ff_r : sr_get (ss_regs crt_ss36_ff) 10%bv = SOff 25 0 /\ sr_get (ss_regs crt_ss36_ff) 24%bv = SOff 24 0 /\
  sr_get (ss_regs crt_ss36_ff) 20%bv = SOff 18 0 /\ sr_get (ss_regs crt_ss36_ff) 19%bv = SOff 19 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

Section s36. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis FUZZ_FREE : @fuzz_free_spec fx rc SK tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- the run's write window: the saved words [sp0 - 104, sp0) and the s1 slots [sp1 + 0x10, sp1 + 0x58) lie above
   alloc_ceiling, the frame [F, F + 512) is no image byte (YCbq.frm_img) and apart from every live block
   (YCbq.sep_block_frame), and its shadow [SF, SF + 64) lies in the shadow band, above the image and off every live
   block (FSW_rd.fsw_ablock_off_shadow). So neither an image byte nor a block byte is written by the run. ---- *)
Lemma crtD2_w36 : forall cx E k ly3 S3 U3 (W3 : world tfibsegs) mem md3,
  crt_E cx E ->
  crt_J SK B cx ly3 S3 W3 (unpoison U3 mem) md3 k -> ARU tfibsegs B ly3 S3 U3 W3 mem md3 ->
  frames S3 = (3, c_pos cx) :: frames (c_S cx) ->
  (forall a, in_img tfibsegs a -> ~ in_wrange E (ss_mem crt_ss36) a) /\
  (forall q m a, In (q, m) (ablocks B ly3 S3) -> q <= a < q + req_size m -> ~ in_wrange E (ss_mem crt_ss36) a).
Proof.
intros cx E k ly3 S3 U3 W3 mem md3 HE HJ HARU Hfr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 YM05.alloc_ceiling_val) as HCV.
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E26 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (H0 : 192 <= spZ (c_regs cx)) by lia.
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & _ & _).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (crt_F_ly cx _ ly3 Hly) as EF.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) HAR Hin3) as (HF0 & HFc & _).
rewrite EF in HF0, HFc. rewrite crt_frame3 in HFc.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
pose proof (shadow_addr_bounds (crt_F cx + 511) ltac:(rewrite C4; lia)) as (_ & HS3b).
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSF64 : crt_SF cx + 64 <= shadow_addr (crt_F cx + 511) + 1)
  by (unfold crt_SF, shadow_addr; Z.div_mod_to_equations; lia).
assert (HSFhi : crt_SF cx + 64 <= 17594333495296) by (rewrite C2 in HS3b; lia).
assert (E47 : bv_unsigned (ew E 47) = crt_F cx) by (rewrite (crt_E_F cx E HE); apply wz; lia).
assert (RG : forall a, in_wrange E (ss_mem crt_ss36) a ->
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/ (crt_sp1 cx + 16 <= a < crt_sp1 cx + 88) \/
  (crt_F cx <= a < crt_F cx + 512) \/ (crt_SF cx <= a < crt_SF cx + 64)).
{ intros a (r & Hr & Hra).
  unfold crt_ss36, crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs, crt_ret_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    unfold fs_ret_s0_region, crt_slot_region, crt_frame_region, crt_shadow_region in Hra;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra.
  - rewrite E8 in Hra. left. lia.
  - rewrite E9 in Hra. right. left. lia.
  - rewrite E47, crt_frame3 in Hra. right. right. left. lia.
  - rewrite E26, crt_frame3 in Hra. change (512 / 8) with 64 in Hra. right. right. right. lia. }
split.
- intros a Ha Hw. pose proof (crt_img_range a Ha) as Hai.
  destruct (RG a Hw) as [Hr | [Hr | [Hr | Hr]]]; [lia | lia | | lia].
  exact (frm_img tfibsegs B LAWS ly3 S3 W3 _ md3 3 (c_pos cx) a HAR Hin3 ltac:(rewrite EF, crt_frame3; lia) Ha).
- intros q m a Hq Ha Hw.
  destruct (fsw_ablock_low B ly3 S3 W3 _ md3 q m HAR Hq) as (Hq4096 & Hqc & _).
  destruct (RG a Hw) as [Hr | [Hr | [Hr | Hr]]]; [lia | lia | |].
  + pose proof (sep_block_frame tfibsegs B LAWS ly3 S3 W3 _ md3 q m 3 (c_pos cx) HAR Hq Hin3) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF, crt_frame3 in D. lia.
  + apply (fsw_ablock_off_shadow B ly3 S3 W3 _ md3 q m HAR Hq a Ha). unfold SHADOW_OFF.
    change (2 ^ 44) with 17592186044416. lia.
Qed.

(* ---- a reader block whose head word is outside a run's write window keeps fs_rblock across the run (the run's
   frame_of on the restricted memory) ---- *)
Lemma crtD2_rblock_frame : forall E rs ly S (W : world tfibsegs) (m m' : word -> option byte) p n,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, p - HEAD <= a < p - HEAD + 8 -> ~ in_wrange E rs a) -> 0 <= p - HEAD -> p - HEAD + 8 < 2 ^ 64 ->
  fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly S W m' p n.
Proof.
intros E rs ly S W m m' p n HF HN H0 H64 (Hin & Hal & Hn & Hv).
split; [exact Hin|]. split; [exact Hal|]. split; [exact Hn|].
intros j Hj. unfold mbyte. rewrite HF; [exact (Hv j Hj)|].
rewrite wz by lia. apply HN. lia.
Qed.

(* ================= segment 36: the shadow stores and fuzz_free (back) =================
   The callee's own part (FSH_crt_site.crt_hcall_full): from crtD2_INV_36 at the boundary memory, through the run
   (crtD2_w36 / crtD2_rblock_frame: text's and back's blocks and fs's statics are untouched), fuzz_free_spec at
   p := back, n := dec_size tb2 (s37's crtD2ff_call), then crtD2_INV_37 at the return: back's block and its head are
   gone, text's block survives the call (it is a different live block, outside the callee's footprint), g_live is down
   by dec_size tb2, s3 = F and s4 = text ride through the callee-saved registers, and the read-only view is
   FSH_crt_site.crt_rom's. ---- *)
Lemma crtD2_hcall36 : crt_hcall_full SK B (crt_ss_ret 0x82418 crt_cs1 crt_csF) crt_ss36_ff A_fuzz_free 0x8249c
  STK_fuzz_free (crtD2_INV_36 B) (crtD2_INV_37 B).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 regsC memC mdC HB HE HINV HJ HARU Hfr HF HFr RG HPRE HFRL HTOP.
destruct HINV as (E19 & E18 & (same & nsame & back & live & peak & cnt & E24 & E25 & Hbl & Hhd & Hheads & Hrbt & Hrbb &
  Hgl & _ & Hlive & Hcnt & Hk)).
unfold crtD2_blocks, crtD2_L4 in Hbl. cbv zeta in Hbl. unfold crtD2_heads in Hhd.
pose proof (ARU_AR tfibsegs B _ _ _ _ _ _ HARU) as HAR.
destruct crtD2_ss36_ff_r as (G10 & G24 & G20 & G19).
pose proof (crt_live0 B cx HB) as Hl0.
set (len := Z.of_nat (length (c_bs cx))) in *.
set (enc := FSH_Fn_writer.enc_size len) in *.
set (dec := FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx))) in *.
set (tb := (c_text cx - HEAD, enc + HEAD)) in *.
set (bb := (back - HEAD, dec + HEAD)) in *.
(* the run's write window holds no image byte and no block byte *)
destruct (crtD2_w36 cx E k ly3 S3 U3 W3 memC mdC HE HJ HARU Hfr) as (NWI & NWB).
assert (KI : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W3) memC a = aview tfibsegs (w_H W3) (ms_mem ms3) a)
  by exact (crt_img_frame E (ss_mem crt_ss36) (w_H W3) (ms_mem ms3) memC HFr NWI).
(* both blocks are live at the call (the run keeps the block list: the journal's S3 is the boundary's) *)
pose proof Hrbt as (Htin & _ & Henc & _). pose proof Hrbb as (Hbin & _ & Hdec & _).
destruct (fsw_ablock_low B ly3 S3 W3 _ mdC _ _ HAR Htin) as (Ht4096 & Htc & _).
destruct (fsw_ablock_low B ly3 S3 W3 _ mdC _ _ HAR Hbin) as (Hb4096 & Hbc & _).
pose proof (req_size_pos (enc + HEAD) ltac:(unfold HEAD; lia)) as (_ & Htr).
pose proof (req_size_pos (dec + HEAD) ltac:(unfold HEAD; lia)) as (_ & Hbr).
pose proof (@alloc_ceiling_lt rc) as HC47.
assert (HrbtC : fs_rblock tfibsegs B ly3 S3 W3 memC (c_text cx) enc).
{ apply (crtD2_rblock_frame E (ss_mem crt_ss36) ly3 S3 W3 (ms_mem ms3) memC (c_text cx) enc HFr);
    [| lia | unfold HEAD in *; change (2 ^ 64) with 18446744073709551616;
             change (2 ^ 47) with 140737488355328 in HC47; lia | exact Hrbt].
  intros a Ha. apply (NWB _ _ a Htin). unfold HEAD in *. lia. }
assert (HrbbC : fs_rblock tfibsegs B ly3 S3 W3 memC back dec).
{ apply (crtD2_rblock_frame E (ss_mem crt_ss36) ly3 S3 W3 (ms_mem ms3) memC back dec HFr);
    [| lia | unfold HEAD in *; change (2 ^ 64) with 18446744073709551616;
             change (2 ^ 47) with 140737488355328 in HC47; lia | exact Hrbb].
  intros a Ha. apply (NWB _ _ a Hbin). unfold HEAD in *. lia. }
pose proof (crt_glob_keep W3 (ms_mem ms3) memC live peak cnt SIZE_MAXZ KI Hgl) as HglC.
(* back's block is not one of the entry's, and it is not text's: the boundary's list holds each once *)
assert (Hbl' : Permutation (ablocks B ly3 S3)
  ((ablocks B (c_ly cx) (c_S cx) ++ [tb; (c_want cx, enc); (same, nsame)]) ++ bb :: []))
  by (rewrite <- app_assoc; exact Hbl).
pose proof (crtD2_once B ly3 S3 W3 (unpoison U3 memC) mdC _ [] bb HAR Hbl') as Honce.
assert (Hnent : ~ In bb (ablocks B (c_ly cx) (c_S cx)))
  by (intros H; apply Honce; apply in_or_app; left; apply in_or_app; left; exact H).
assert (Hne : tb <> bb)
  by (intros Heq; apply Honce; apply in_or_app; left; apply in_or_app; right; left; exact Heq).
assert (Hhd' : Permutation U3 ((c_U cx ++ [(c_text cx - HEAD, HEAD)]) ++ (back - HEAD, HEAD) :: []))
  by (rewrite <- app_assoc; exact Hhd).
assert (HUin : In (back - HEAD, HEAD) U3).
{ apply (Permutation_in _ (Permutation_sym Hhd')). apply in_or_app. right. left. reflexivity. }
assert (Ha0 : YK11.getr regsC 10%bv = Z_to_bv 64 back) by (rewrite RG, G10, fsw_SOff0; exact E25).
assert (Hk1 : k + 1 <= EV_check_round_trip) by (unfold EV_fuzz_free, CRT_EV_WRAP in Hk; lia).
destruct (crtD2ff_call SK B FUZZ_FREE cx k ly3 S3 U3 W3 regsC memC mdC back dec live peak cnt HB HJ HARU
  Hfr HPRE Ha0 HUin Hheads HrbbC ltac:(lia) HglC Hnent Hk1)
  as (FPc & kc & P & HSR & HFP & HFL & HK).
exists FPc, kc, P. split; [exact HSR|]. split; [exact HFP|]. split; [exact HFL|].
intros W' c' HPc.
destruct (HK W' c' HPc) as (ly' & S' & U' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HP & Ekc & HFB &
  (l1 & l2 & El1 & El2) & (V1 & V2 & HV & EU') & Hheads' & Hgl').
exists ly', S', U', regs', mem', md'.
split; [exact Ec|]. split; [exact HJc|]. split; [exact OK'|]. split; [exact PO'|]. split; [exact HP|].
intros HJ' HARU'. subst kc.
(* text's block is outside the callee's footprint, so it survives the call *)
assert (HrbtR : fs_rblock tfibsegs B ly' S' W' mem' (c_text cx) enc).
{ apply (fs_rblock_kept_call B STK_fuzz_free (spZ regsC) FPc ly3 S3 U3 W3 memC mdC ly' S' U' W' mem' md' 1
    (c_text cx) enc HJc HARU OK' PO'); [|exact HrbtC].
  intros x Hx. exact (HFB (c_text cx - HEAD) (enc + HEAD) Htin Hne x ltac:(lia)). }
unfold crtD2_INV_37. cbn [ms_mem mkst]. cbv zeta.
(* B's two register conjuncts: s3 = F and s4 = text (the run's `mv s4, s2`), through the callee-saved s3 / s4 *)
split.
{ rewrite (ew_Ereg_nat regs' (crt_extra cx) 19 19%bv eq_refl).
  assert (R19 : YK11.getr regs' 19%bv = YK11.getr regsC 19%bv) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
  rewrite R19, RG, G19, fsw_SOff0. exact E19. }
split.
{ rewrite (ew_Ereg_nat regs' (crt_extra cx) 20 20%bv eq_refl).
  assert (R20 : YK11.getr regs' 20%bv = YK11.getr regsC 20%bv) by exact (HP 20 ltac:(unfold acallee_saved; lia)).
  rewrite R20, RG, G20, fsw_SOff0. exact E18. }
exists same, nsame, (live - dec), peak, cnt.
split.
{ rewrite (ew_Ereg_nat regs' (crt_extra cx) 24 24%bv eq_refl).
  assert (R24 : YK11.getr regs' 24%bv = YK11.getr regsC 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
  rewrite R24, RG, G24, fsw_SOff0. exact E24. }
split.
{ unfold crtD2_blocks. rewrite El2. fold bb in El1. rewrite El1 in Hbl'.
  pose proof (Permutation_app_inv l1 l2 (ablocks B (c_ly cx) (c_S cx) ++ [tb; (c_want cx, enc); (same, nsame)]) [] bb
    Hbl') as X.
  rewrite app_nil_r in X. exact X. }
split.
{ unfold crtD2_heads. rewrite EU'. rewrite HV in Hhd'.
  pose proof (Permutation_app_inv V1 V2 (c_U cx ++ [(c_text cx - HEAD, HEAD)]) [] (back - HEAD, HEAD) Hhd') as X.
  rewrite app_nil_r in X. exact X. }
split; [exact Hheads'|].
split; [exact HrbtR|].
split; [exact Hgl'|].
split; [exact (crt_rom SK B IMG cx (k + 1) ly' S' U' W' mem' md' HB HJ' HARU')|].
split; [unfold enc, len in Hlive; lia|].
split; [exact Hcnt|].
unfold EV_fuzz_free in *. lia.
Qed.

(* ---- the segment lemma ---- *)
Lemma crtD2_seg36 : crt_from SK B crt_ss37 (crtD2_INV_37 B) -> crt_from SK B crt_ss36 (crtD2_INV_36 B).
Proof.
intros NEXT.
exact (crt_seg_call_full SK B 0x82418 A_fuzz_free 0x8249c crt_ss36_ff (crtD2_INV_36 B) (crtD2_INV_37 B) STK_fuzz_free
  (crt_seg36_run SK B) crtD2_ss36_ff_site4 ltac:(lia) ltac:(reflexivity) (proj1 (proj2 crtD2_stk_pos))
  crtD2_stk_fuzz_free crtD2_hcall36 NEXT).
Qed.
End s36.

Print Assumptions crtD2_seg36.
