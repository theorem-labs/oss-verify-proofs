(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its w6_disp,
   w6_tail_J, w6_case_gen and w6_cases: the two piece lemmas of ent_build's dispatch and of its cases 2 and 3,
   chained from block statements) for reac-pw/fuzz_headamp's image B: the piece statements are lib/AU/HPgSeg.v's
   hsu_piece_W6a_disp_stmt and hsu_piece_W6a_cases_stmt at image B's record, the block statements are
   lib/AU/HPgW6aBase.v's and are taken as premises, the generic helpers come from lib/AU/HPgCaseB.v and the case
   entry and join bridges from lib/AU/HPgCaseBJ.v instead of being restated, the frame object the dispatch fills is
   e62 at F+0x210, what is left of the input lives in registers (no real-frame cell), and a case leaves through one
   of four tail entries. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the two piece lemmas of the walk piece W6a of LLVMFuzzerTestOneInput (0x80c40), chained from the block
   statements of lib/AU/HPgW6aBase.v, which they take as premises. Proves no function (kind: segment lemma).

   THE DISPATCH (w6b_disp_of). From the pod loop's head C (0x81888): the head block (w6b_head_stmt: [R+0x158] := the
   pod index, e62's 13 shadow granules := 0, the memset of e62) and the kind block (w6b_kind_stmt: the kind byte,
   kind % 10, the branch to case 9 or the jump table) end at one of the switch's entries, where the state is the cut
   D of that kind (hsu_cut_D), or D0E (0x819c0) when no input is left. The cut's journal, frames, blocks and the bytes
   outside the callees' stack and hsu_E1 come from the cut C through the two blocks' posts; the registers of
   hsu_Rc0, the real-frame cells of hsu_Kc and the pod loop's cells are kept (the head writes only [R - ESTACK, R),
   [R+0x158, R+0x160), e62 and its shadow); e62's shadow is the pattern hsu_PJ and e62 holds 104 zeros.

   THE CASES 2 AND 3 (w6b_cases_of). From the cut D of kind % 10 = 2 (3), through lib/AU/HPgCaseBJ.v's case-entry
   facts (cj_D_facts, cj_D_input, cj_D_img over hsu_L_D): the case's head block (w6b_c2_stmt / w6b_c3_stmt); on an
   odd m the fuzz_u32 read-ahead block (lib/AU/HPgSteps.v hdu_u32_block2 / hdu_u32_block3) and the tail from its
   exit (w6b_tail2u_stmt / w6b_tail3u_stmt); on an even m the tail from the case's own exit (w6b_tail2_stmt /
   w6b_tail3_stmt). The tail ends at J, where cj_J_of gives hsu_cut_J with e62 holding Layout.ent_mem of
   Model.ent_build's pod (cj_e62_tyszv: the three stored words over the 92 zero bytes the memset left).

   THE REGISTERS AND CELLS this file names (image B): s1 = x9 = R, s3 = x19 = shadow_addr F, s11 = x27 = SHADOW_OFF,
   s4 = x20 = &e62 (at C and at J), s5 = x21 = the cursor at C, s10 = x26 = what is left at C, a1 = x11 = the pod
   index at C, s7 = x23 = -8 at C and pp inside a case; the case entry's a7 / s2 / t1 / s4 / a6 (x17 / x18 / x6 /
   x20 / x16) as HPgSeg.hsu_L_D states them; at a tail's entry a1 = x11 the value, a2 = x12 what is left, s2 = x18
   the cursor, a4 = x14 = 4. Real-frame cells: [R+0x130] = F + 0x210, [R+0x138] = pp + Layout.OFF_LEN,
   [R+0x148] = pp, [R+0x158] = the pod index. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgCaseB HPgCaseBJ HPgW6aBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* membership in a literal list *)
Local Ltac w6g_mem := cbn [In]; repeat first [left; reflexivity | right].
(* membership in a case entry's list (HPgSeg.hsu_L_D) *)
Local Ltac w6g_inD := cbv [hsu_L_D hsu_L_Dc hsu_Rc0 hsu_Kc app]; w6g_mem.
(* a register of cj_kregs is not x0 *)
Local Ltac w6g_nz Hrg :=
  clear - Hrg; unfold cj_kregs in Hrg; cbn [In] in Hrg;
  repeat (destruct Hrg as [<-|Hrg]; [vm_compute; intros X; discriminate X|]); destruct Hrg.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* ======================================== what the head block writes ========================================
   w6b_head_wr R F: the callee's stack [R - ESTACK, R), the cell [R+0x158, R+0x160), e62's 13 shadow granules and
   e62 itself; all of it in the callees' stack or the image's first write range (HPgImgB hi_w1), apart from pp and
   from the frame's other shadow granules. *)
Lemma w6b_hw_E1 : forall e a, w6b_head_wr (e_R e) (e_F e) a ->
(e_R e - T_SEG_STK <= a < e_R e) \/ hd_inw e (hi_w1 headamp_himg_B) a.
Proof.
intros e a H. unfold w6b_head_wr in H. destruct H as [H|[H|[H|H]]].
- left. unfold T_SEG_STK, ASTACK, ESTACK in *. lia.
- right. apply cb_inw1. right. right. lia.
- right. apply cb_inw1. right. left. lia.
- right. apply cb_inw1. left. lia.
Qed.

Lemma w6b_hw_pp : forall R F pp i, cb_geo R F pp -> 0 <= i < Layout.PP_SIZE ->
0 <= pp + i < 2 ^ 64 /\ ~ w6b_head_wr R F (pp + i).
Proof.
intros R F pp i G Hi. pose proof (@asan_consts rc) as (C1 & _).
destruct G as (G1 & G2 & _ & _ & G5 & G6 & G7 & G8 & _ & G10 & G11 & G12 & G13 & _).
unfold w6b_head_wr, T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *. lia.
Qed.

(* the dispatch's facts at its end, from the head's end across the kind block, which writes no byte: e62's shadow,
   the first block and e62's 104 zero bytes *)
Lemma w6b_kept3 : forall (cx : hsu_scx rsegs) sh ps es (W1 W3 : world rsegs) mem1 mem3,
cb_geo (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx)) ->
Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = Layout.PP_SIZE ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (fun _ : Z => False) a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W1) mem1 a) ->
hsu_fsh_at rsegs cx W1 mem1 (hsu_PJ headamp_himg_B) ->
hm_bytes rsegs (w_H W1) mem1 (e_pp (x_e rsegs cx)) (pc_image (PbCut sh ps (Some es))) ->
hm_bytes rsegs (w_H W1) mem1 (e_F (x_e rsegs cx) + HSU_E62) (zeros 104) ->
hsu_fsh_at rsegs cx W3 mem3 (hsu_PJ headamp_himg_B) /\
hsu_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps (Some es))) /\
hsu_obj_at rsegs cx W3 mem3 HSU_E62 (zeros 104).
Proof.
intros cx sh ps es W1 W3 mem1 mem3 HG Hppl Hm3 HF1 HP1 HE1.
pose proof HG as (G1 & G2 & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
split; [|split].
- unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs (w_H W1) mem1 _ _ _ _ HF1). intros ii Hii. rewrite cj_PJ_len in Hii.
  pose proof (cb_fsh_low _ _ _ ii HG ltac:(lia)) as X. apply Hm3; [lia | exact (fun Y => Y)].
- unfold hsu_pp_at. change (hm_bytes rsegs (w_H W3) mem3 (e_pp (x_e rsegs cx)) (pc_image (PbCut sh ps (Some es)))).
  apply (hm_bytes_kept rsegs (w_H W1) mem1 _ _ _ _ HP1). intros x Hx. rewrite Hppl in Hx.
  pose proof (cb_pp_low _ _ _ (x - e_pp (x_e rsegs cx)) HG ltac:(lia)) as X. apply Hm3; [lia | exact (fun Y => Y)].
- unfold hsu_obj_at. change (hm_bytes rsegs (w_H W3) mem3 (e_F (x_e rsegs cx) + HSU_E62) (zeros 104)).
  apply (hm_bytes_kept rsegs (w_H W1) mem1 _ _ _ _ HE1). intros x Hx.
  change (Z.of_nat (length (zeros 104))) with 104 in Hx. unfold HSU_E62 in Hx.
  pose proof (cb_frame_low _ _ _ (x - e_F (x_e rsegs cx)) HG ltac:(lia)) as X. apply Hm3; [lia | exact (fun Y => Y)].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.

(* ======================================== W6a, the cases 2 and 3 ======================================== *)
(* the tail from one of its four entries, and the cut J it ends at: the case's blocks before it wrote no byte and
   kept the registers of cj_kregs, so the state at the tail's entry is the case entry's but for its registers *)
Lemma w6b_tail_J : forall (c3 : bool) (pc0 : Z), w6b_tail_stmt B MT c3 pc0 ->
forall cx POST rest i k sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 lyT ST WT regsT memT mdT rJ vm v,
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_from_J rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k ->
(length ps = i)%nat -> (length es = k)%nat ->
hsu_cut_D rsegs B MT headamp_himg_B cx sh np ps cnt es rest rr r kd ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyT ST WT memT mdT (x_k rsegs cx) ->
frames ST = frames S2 -> Permutation (ablocks B lyT ST) (ablocks B ly2 S2) -> same_io md2 mdT -> mo_le MT S2 ST 0 ->
(forall rg, In rg cj_kregs -> getr regsT (Z_to_bv 5 rg) = getr regs2 (Z_to_bv 5 rg)) ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H WT) memT a = aview rsegs (w_H W2) mem2 a) ->
getr regsT 20 = w64 (e_F (x_e rsegs cx) + 0x210) -> getr regsT 23 = w64 (e_pp (x_e rsegs cx)) ->
getr regsT 11 = w64 v -> getr regsT 12 = w64 (Z.of_nat (length rJ)) ->
getr regsT 18 = w64 (hsu_cur rsegs cx rest rJ) ->
(pc0 = W6B_T2 \/ pc0 = W6B_T3 -> getr regsT 14 = w64 4) ->
v mod 2 ^ 32 = vm mod 2 ^ 32 ->
(Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm), rJ) = ent_build rr ->
SRr rsegs WT (cfg_at rsegs pc0 regsT memT mdT) POST.
Proof.
intros c3 pc0 HT cx POST rest i k sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 lyT ST WT regsT memT mdT rJ vm v
  HST HJ Hlp Hle HD HJT HfT HpT HioT HmoT HkT HmT T20 T23 T11 T12 T18 T14 Hv Hed.
pose proof (@alloc_ceiling_lt rc) as Hac. pose proof (@asan_consts rc) as (Hceil & _).
assert (HTS : T_SEG_STK = 16384) by reflexivity.
pose proof (cj_D_facts B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HST HD)
  as (HJ2 & R2 & R3 & R4 & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
      & Hpp & Hpp1 & Hpp2 & Hsep & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
pose proof (proj1 (proj2 HD)) as HAT. unfold hsu_at_cx in HAT.
(* the context at the tail's entry *)
assert (HlyT : frame_addr lyT 4 (x_pos rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx)).
{ pose proof HJT as (_ & HlT & _). pose proof HJ2 as (_ & Hl2 & _).
  rewrite (cj_frame_addr_le _ _ _ 4 (x_pos rsegs cx) HlT), (cj_frame_addr_le _ _ _ 4 (x_pos rsegs cx) Hl2).
  reflexivity. }
assert (HrT : forall a, in_rom rsegs a -> aview rsegs (w_H WT) memT a = aview rsegs (w_H W2) mem2 a).
{ intros a (sg & Hsg & _ & Ha). apply HmT.
  assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hsg | exact Ha]).
  pose proof (img_segs_low a Himg) as Hl. unfold kLowMemEnd in Hl. lia. }
assert (HCTX : cb_ctx B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyT ST WT memT mdT
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx)).
{ unfold cb_ctx. split; [exact HJT|]. split; [exact BR4|]. split; [exact BR2|]. split; [exact BR5|].
  split; [exact Hown|]. split; [rewrite HlyT; exact EF2|].
  exact (hm_rom_kept rsegs W2 WT mem2 memT HromD HrT). }
(* the registers and the cell the tail reads *)
assert (T2 : getr regsT 2 = w64 (e_R (x_e rsegs cx))).
{ rewrite <- R2. exact (HkT 2 ltac:(unfold cj_kregs; w6g_mem)). }
assert (T9 : getr regsT 9 = w64 (e_R (x_e rsegs cx))).
{ rewrite <- (cb_at_reg _ _ _ _ _ 9 (e_R (x_e rsegs cx)) (9%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
  exact (HkT 9 ltac:(unfold cj_kregs; w6g_mem)). }
assert (T138 : val_mem rsegs (mrestrict (w_H WT) memT) (e_R (x_e rsegs cx) + 0x138) 8
  (e_pp (x_e rsegs cx) + Layout.OFF_LEN)).
{ pose proof (cb_at_cell8 _ _ _ _ _ XR 0x138 (e_pp (x_e rsegs cx) + Layout.OFF_LEN) HAT ltac:(w6g_inD)) as X.
  cbn [hd_xv] in X.
  apply (val_mem_kept rsegs (w_H W2) (w_H WT) mem2 memT _ _ _); [|exact X].
  intros kk Hk. apply HmT. lia. }
pose proof (HT (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyT ST WT memT mdT regsT
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx) (e_pp (x_e rsegs cx)) (Z.of_nat (length rJ)) v
  (hsu_cur rsegs cx rest rJ) HCTX T2 T9 T20 T11 T12 T18 T14 T138) as HTT.
eapply SRr_bind; [exact HTT|]. clear HTT.
intros WJ cJ HwJ (lyJ & SJ & regsJ & memJ & mdJ & -> & HJJ & HrJ & HfJ & HpJ & HioJ & HmoJ & HmJ &
  (J6 & J13 & J18 & Vt & Vs & Vv)).
unfold hsu_from_J in HJ.
apply (HJ lyJ SJ WJ regsJ memJ mdJ sh np ps cnt es rr rJ (Ent (if c3 then POD_FLOAT else POD_INT) 4 (le32 vm))
  Hlp Hle).
apply (cj_J_of B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 lyJ SJ WJ regsJ memJ mdJ _ rJ []
  HST HD MTL eq_refl HJJ).
- rewrite HfJ. exact HfT.
- eapply Permutation_trans; [exact HpJ | exact HpT].
- exact (same_io_trans _ _ _ HioT HioJ).
- exact (mle_station MT _ _ _ 0 0 MTL HmoT HmoJ).
- intros rg Hrg. rewrite <- (HkT rg Hrg).
  apply HrJ; [w6g_nz Hrg | exact (cj_clob_keep [6; 10; 13; 14; 18]%bv rg eq_refl Hrg)].
- exact J13.
- exact J6.
- exact J18.
- rewrite (cb_kept_bv regsT regsJ _ (20%bv : bv 5) HrJ ltac:(vm_compute; reflexivity)). exact T20.
- rewrite (cb_kept_bv regsT regsJ _ (23%bv : bv 5) HrJ ltac:(vm_compute; reflexivity)). exact T23.
- intros a Ha Hn. rewrite (HmJ a Ha); [exact (HmT a Ha)|].
  intros Hw. apply Hn. right. right. unfold w6b_tail_wr in Hw. unfold HSU_E62. lia.
- (* e62: the type, the size 4, the value's four bytes, and the 92 zero bytes the memset left *)
  apply cj_e62_tyszv.
  + destruct c3; exact Vt.
  + replace (e_F (x_e rsegs cx) + HSU_E62 + 4) with (e_F (x_e rsegs cx) + 0x214) by (unfold HSU_E62; lia). exact Vs.
  + replace (e_F (x_e rsegs cx) + HSU_E62 + 8) with (e_F (x_e rsegs cx) + 0x218) by (unfold HSU_E62; lia).
    apply (proj1 (cb_val_mod32 _ _ vm)). rewrite <- Hv. exact Vv.
  + intros ii Hii.
    assert (Hr : 0 <= e_F (x_e rsegs cx) + HSU_E62 + 12 + ii < 2 ^ 64) by (unfold HSU_E62; lia).
    rewrite (HmJ _ Hr) by (unfold w6b_tail_wr, HSU_E62; lia).
    rewrite (HmT _ Hr). unfold aview.
    replace (e_F (x_e rsegs cx) + HSU_E62 + 12 + ii) with (e_F (x_e rsegs cx) + HSU_E62 + (12 + ii)) by lia.
    rewrite (Ez (12 + ii) ltac:(lia)). reflexivity.
- exact Hed.
Qed.

(* one of the two cases, from its entry D to J *)
Lemma w6b_case_gen : forall c3 : bool,
w6b_case_stmt B MT c3 ->
hdu_u32_stmt B MT (if c3 then W6B_U3 else W6B_U2) (if c3 then W6B_U3E else W6B_U2E) ->
w6b_tail_stmt B MT c3 (if c3 then W6B_U3E else W6B_U2E) ->
w6b_tail_stmt B MT c3 (if c3 then W6B_T3 else W6B_T2) ->
forall cx POST rest i k kd, kd mod 10 = (if c3 then 3 else 2) ->
hsu_start_M01 rsegs B headamp_himg_B cx rest ->
hsu_from_J rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k ->
hsu_from_D rsegs B MT headamp_himg_B headamp_bld_B cx POST rest i k kd.
Proof.
intros c3 HC HU HTU HTT cx POST rest i k kd Hkd HST HJ.
unfold hsu_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hlp Hle HD.
pose proof (@alloc_ceiling_lt rc) as Hac.
pose proof HD as ((_ & HINc & _) & HAT & _ & _ & _ & Hsrr & Hfu & _ & Hrr).
unfold hsu_at_cx in HAT.
destruct rr as [|b r0]; [exfalso; exact (Hrr eq_refl)|].
cbn [Cursor.fuzz_u8] in Hfu. injection Hfu as Ekd Er. subst kd r0.
assert (Epc : hsu_pc_D headamp_bld_B (bv_unsigned b) = (if c3 then W6B_D3 else W6B_D2))
  by (unfold hsu_pc_D; rewrite Hkd; destruct c3; reflexivity).
rewrite Epc.
pose proof (cj_D_facts B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HST HD)
  as (HJ2 & R2 & R3 & R4 & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp
      & Hpp & Hpp1 & Hpp2 & Hsep & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
pose proof (cj_D_input B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HST HD) as (Hig & Hira & _ & Hiam & Hidis).
pose proof (cj_D_img B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HST HD) as (_ & Hglobs & _).
(* the cursor after the kind byte is at least 2 *)
assert (Hc0 : 0 < hsu_cur rsegs cx rest r - 1).
{ destruct HINc as (_ & _ & _ & _ & _ & Hsrc0 & _). destruct Hsrr as (j & Hj & E).
  assert (Hl : length (skipn j rest) = S (length r)) by (rewrite <- E; reflexivity).
  rewrite length_skipn in Hl. unfold hsu_cur. lia. }
(* the registers and cells at D *)
assert (D9 : getr regs2 9 = w64 (e_R (x_e rsegs cx)))
  by exact (cb_at_reg _ _ _ _ _ 9 (e_R (x_e rsegs cx)) (9%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D27 : getr regs2 27 = w64 SHADOW_OFF)
  by exact (cb_at_reg _ _ _ _ _ 27 SHADOW_OFF (27%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D17 : getr regs2 17 = w64 (hsu_cur rsegs cx rest r - 1))
  by exact (cb_at_reg _ _ _ _ _ 17 (hsu_cur rsegs cx rest r - 1) (17%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D18 : getr regs2 18 = w64 (hsu_cur rsegs cx rest r))
  by exact (cb_at_reg _ _ _ _ _ 18 (hsu_cur rsegs cx rest r) (18%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D6 : getr regs2 6 = w64 (Z.of_nat (length r) + 1))
  by exact (cb_at_reg _ _ _ _ _ 6 (Z.of_nat (length r) + 1) (6%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D20 : getr regs2 20 = w64 (Z.of_nat (length r)))
  by exact (cb_at_reg _ _ _ _ _ 20 (Z.of_nat (length r)) (20%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D16 : getr regs2 16 = w64 1)
  by exact (cb_at_reg _ _ _ _ _ 16 1 (16%bv : bv 5) HAT ltac:(w6g_inD) eq_refl).
assert (D130 : val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x130) 8 (e_F (x_e rsegs cx) + 0x210)).
{ pose proof (cb_at_cell8 _ _ _ _ _ XR 0x130 (e_F (x_e rsegs cx) + HSU_E62) HAT ltac:(w6g_inD)) as X.
  cbn [hd_xv] in X. exact X. }
assert (D148 : val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x148) 8 (e_pp (x_e rsegs cx))).
{ pose proof (cb_at_cell8 _ _ _ _ _ XR 0x148 (e_pp (x_e rsegs cx)) HAT ltac:(w6g_inD)) as X.
  cbn [hd_xv] in X. exact X. }
(* the input after the kind byte *)
assert (HIN : w6b_in W2 mem2 (e_R (x_e rsegs cx)) (hsu_cur rsegs cx rest r) r).
{ unfold w6b_in. split; [exact Hig|]. split; [exact Hira|]. split; [lia|]. split; [lia|].
  split; [exact Hiam|]. intros a Ha. exact (proj1 (Hidis a Ha)). }
assert (HCIN : w6b_case_in W2 mem2 regs2 (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (e_pp (x_e rsegs cx))
  (hsu_cur rsegs cx rest r) r).
{ unfold w6b_case_in.
  refine (conj R2 (conj D9 (conj D27 (conj D17 (conj D18 (conj D6 (conj D20 (conj D16
    (conj D130 (conj D148 (conj Hc0 HIN))))))))))). }
(* the context at D and the table's shadow *)
assert (HCTX : cb_ctx B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx)).
{ unfold cb_ctx. split; [exact HJ2|]. split; [exact BR4|]. split; [exact BR2|]. split; [exact BR5|].
  split; [exact Hown|]. split; [exact EF2 | exact HromD]. }
assert (HRT : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (if c3 then W6B_FLOATS else W6B_INTS)
  (if c3 then 84 else 56)).
{ destruct w6b_tables_glob as [Gi Gf]. destruct c3; [exact (Hglobs _ _ Gf) | exact (Hglobs _ _ Gi)]. }
(* ---------------- the case's head block ---------------- *)
pose proof (HC (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly2 S2 W2 mem2 md2 regs2
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx) (e_pp (x_e rsegs cx)) (hsu_cur rsegs cx rest r) r
  HCTX HCIN HRT) as HC1.
eapply SRr_bind; [exact HC1|]. clear HC1.
intros WH cH HwH HPOST. cbv beta in HPOST.
revert HPOST. destruct (Z.odd (fst (Cursor.fuzz_u8 r))) eqn:Eodd; intros HPOST.
- (* m odd: the fuzz_u32 block, then the tail from its exit *)
  destruct r as [|m r1]; [cbn in Eodd; discriminate Eodd|].
  cbn [Cursor.fuzz_u8 fst snd] in HPOST, Eodd.
  destruct HPOST as (lyH & SH & regsH & memH & mdH & -> & HJH & HrH & HfH & HpH & HioH & HmoH & HmH &
    (H12 & H18 & H20 & H23)).
  cbn [length] in Hc2, D6, D20, Hira, Hiam, Hidis.
  assert (H6 : getr regsH 6 = w64 (Z.of_nat (length r1) + 2)).
  { rewrite (cb_kept_bv regs2 regsH _ (6%bv : bv 5) HrH ltac:(vm_compute; reflexivity)), D6. f_equal. lia. }
  assert (H16 : getr regsH 16 = w64 1)
    by (rewrite (cb_kept_bv regs2 regsH _ (16%bv : bv 5) HrH ltac:(vm_compute; reflexivity)); exact D16).
  assert (H17 : getr regsH 17 = w64 (hsu_cur rsegs cx rest (m :: r1) + 1 - 2)).
  { rewrite (cb_kept_bv regs2 regsH _ (17%bv : bv 5) HrH ltac:(vm_compute; reflexivity)), D17. f_equal. lia. }
  assert (H27 : getr regsH 27 = w64 SHADOW_OFF)
    by (rewrite (cb_kept_bv regs2 regsH _ (27%bv : bv 5) HrH ltac:(vm_compute; reflexivity)); exact D27).
  (* the bytes after m, at the head's end *)
  assert (Hrng : forall x, hsu_cur rsegs cx rest (m :: r1) <= x < hsu_cur rsegs cx rest (m :: r1) + Z.of_nat (S (length r1)) ->
    0 <= x < 2 ^ 47) by (intros x Hx; lia).
  assert (HgH : garr8 rsegs (mrestrict (w_H WH) memH) (hsu_cur rsegs cx rest (m :: r1) + 1)
    (map (fun x : byte => bv_unsigned x) r1)).
  { change (hm_bytes rsegs (w_H WH) memH (hsu_cur rsegs cx rest (m :: r1) + 1) r1).
    pose proof (proj1 (hm_bytes_app rsegs (w_H W2) mem2 (hsu_cur rsegs cx rest (m :: r1)) [m] r1) Hig) as [_ X].
    change (Z.of_nat (length [m])) with 1 in X.
    apply (hm_bytes_kept rsegs (w_H W2) mem2 _ _ _ _ X).
    intros x Hx. apply HmH; [|tauto]. pose proof (Hrng x ltac:(lia)). lia. }
  assert (HraH : range_addressable (aview rsegs (w_H WH) memH) SHADOW_OFF (hsu_cur rsegs cx rest (m :: r1) + 1)
    (Z.of_nat (length r1))).
  { apply (hm_ra_kept rsegs (w_H W2) mem2 _ _ _ _ _).
    - apply (ra_sub _ _ _ _ _ _ Hira); lia.
    - intros x Hx. apply HmH; [|tauto].
      pose proof (hm_shadow_band x ltac:(pose proof (Hrng x ltac:(lia)); pose proof (@asan_consts rc) as (_ & _ & _ & EHE & _); lia))
        as Hb.
      pose proof (@asan_consts rc) as (_ & _ & EHB & _ & ELE). lia. }
  pose proof (HU (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) lyH SH WH memH mdH (x_k rsegs cx) regsH
    (hsu_cur rsegs cx rest (m :: r1) + 1) (Z.of_nat (length r1)) (Z.of_nat (length r1) + 2) r1 eq_refl eq_refl
    HJH H6 H12 H16 H17 H18 H27 ltac:(lia) ltac:(lia) HgH HraH) as HU1.
  eapply SRr_bind; [exact HU1|]. clear HU1.
  intros WU cU HwU (lyU & SU & regsU & memU & mdU & -> & HJU & HrU & HfU & HpU & HioU & HmoU & HmU &
    (U11 & U12 & U18 & U27)).
  apply (w6b_tail_J c3 (if c3 then W6B_U3E else W6B_U2E) HTU cx POST rest i k sh np ps cnt es (b :: m :: r1)
    (m :: r1) (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2 lyU SU WU regsU memU mdU (snd (Cursor.fuzz_u32 r1))
    (fst (Cursor.fuzz_u32 r1)) (fst (Cursor.fuzz_u32 r1)) HST HJ Hlp Hle HD HJU).
  + rewrite HfU. exact HfH.
  + eapply Permutation_trans; [exact HpU | exact HpH].
  + exact (same_io_trans _ _ _ HioH HioU).
  + exact (mle_station MT _ _ _ 0 0 MTL HmoH HmoU).
  + intros rg Hrg.
    rewrite (HrU (Z_to_bv 5 rg) ltac:(w6g_nz Hrg) (cj_clob_keep [11; 12; 13; 14; 15; 18]%bv rg eq_refl Hrg)).
    exact (HrH (Z_to_bv 5 rg) ltac:(w6g_nz Hrg) (cj_clob_keep w6b_case_clob rg eq_refl Hrg)).
  + intros a Ha. rewrite (HmU a). exact (HmH a Ha (fun X => X)).
  + rewrite (cb_kept_bv regsH regsU _ (20%bv : bv 5) HrU ltac:(vm_compute; reflexivity)). exact H20.
  + rewrite (cb_kept_bv regsH regsU _ (23%bv : bv 5) HrU ltac:(vm_compute; reflexivity)). exact H23.
  + exact U11.
  + rewrite fuzz_u32_rest_len. exact U12.
  + rewrite U18. f_equal. unfold hsu_cur. rewrite fuzz_u32_rest_len. cbn [length]. lia.
  + intros [E|E]; destruct c3; unfold W6B_U3E, W6B_U2E, W6B_T2, W6B_T3 in E; lia.
  + reflexivity.
  + rewrite (w6b_ent_build c3 b (m :: r1) Hkd). unfold w6b_rest_of. cbn [Cursor.fuzz_u8 fst snd].
    rewrite Eodd. reflexivity.
- (* m even (or no byte): the tail from the case's own exit *)
  destruct HPOST as (lyH & SH & regsH & memH & mdH & -> & HJH & HrH & HfH & HpH & HioH & HmoH & HmH &
    ((v & H11 & Hv) & H12 & H14 & H18 & H20 & H23)).
  apply (w6b_tail_J c3 (if c3 then W6B_T3 else W6B_T2) HTT cx POST rest i k sh np ps cnt es (b :: r) r
    (bv_unsigned b) ly2 S2 W2 regs2 mem2 md2 lyH SH WH regsH memH mdH (snd (Cursor.fuzz_u8 r))
    (w6b_even_val c3 (fst (Cursor.fuzz_u8 r))) v HST HJ Hlp Hle HD HJH).
  + exact HfH.
  + exact HpH.
  + exact HioH.
  + exact HmoH.
  + intros rg Hrg. exact (HrH (Z_to_bv 5 rg) ltac:(w6g_nz Hrg) (cj_clob_keep w6b_case_clob rg eq_refl Hrg)).
  + intros a Ha. exact (HmH a Ha (fun X => X)).
  + exact H20.
  + exact H23.
  + exact H11.
  + exact H12.
  + rewrite H18. f_equal. unfold hsu_cur. rewrite Cursor.fuzz_u8_spec. cbn [snd]. rewrite length_skipn. lia.
  + intros _. exact H14.
  + exact Hv.
  + rewrite (w6b_ent_build c3 b r Hkd). revert Eodd. unfold w6b_rest_of.
    destruct (Cursor.fuzz_u8 r) as [m r1]. cbn [fst snd]. intros Eodd. rewrite Eodd. reflexivity.
Qed.

Theorem w6b_cases_of :
w6b_c2_stmt B MT -> w6b_c3_stmt B MT -> w6b_tail2u_stmt B MT -> w6b_tail2_stmt B MT ->
w6b_tail3u_stmt B MT -> w6b_tail3_stmt B MT ->
hsu_piece_W6a_cases_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros HC2 HC3 HT2u HT2 HT3u HT3 cx POST rest i k kd Hst Hin HJ.
cbn [In] in Hin. destruct Hin as [H2|[H3|[]]].
- exact (w6b_case_gen false HC2 (hdu_u32_block2 B MT MTL LAWS) HT2u HT2 cx POST rest i k kd (eq_sym H2) Hst HJ).
- exact (w6b_case_gen true HC3 (hdu_u32_block3 B MT MTL LAWS) HT3u HT3 cx POST rest i k kd (eq_sym H3) Hst HJ).
Qed.

(* ======================================== W6a, the dispatch ======================================== *)
Theorem w6b_disp_of : w6b_head_stmt B MT -> w6b_kind_stmt B MT ->
hsu_piece_W6a_disp_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
intros HH HK cx POST rest i k HST HD HD0E.
unfold hsu_from_C. intros lyC SC WC regsC memC mdC sh np ps cnt es r Hlp Hle HC.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
pose proof HST as (HP & _ & _ & HIN).
pose proof HC as (HB & HAT & HFSH & HPP).
pose proof HB as (HCORE & _ & HSUF & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hesw & Hesl & _).
destruct (cb_geo_of B MT cx _ _ _ _ _ _ _ _ HP HCORE) as (HG & HFa & HspZ).
pose proof (cb_ctx_of B MT cx _ _ _ _ _ _ _ HP HCORE) as HCTX0.
pose proof (cb_pp_len sh ps es Hwf Hesw Hesl) as Hppl.
unfold hsu_at_cx in HAT.
pose proof HAT as HATs. unfold hsu_at in HATs. apply Forall_app in HATs as [HATp _].
(* the registers the head reads, at C *)
assert (A9 : getr regsC 9 = w64 (e_R (x_e rsegs cx)))
  by exact (cb_at_reg _ _ _ _ _ 9 (e_R (x_e rsegs cx)) (9%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A19 : getr regsC 19 = w64 (shadow_addr (e_F (x_e rsegs cx))))
  by exact (cb_at_reg _ _ _ _ _ 19 (shadow_addr (e_F (x_e rsegs cx))) (19%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A27 : getr regsC 27 = w64 SHADOW_OFF)
  by exact (cb_at_reg _ _ _ _ _ 27 SHADOW_OFF (27%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A11 : getr regsC 11 = w64 (Z.of_nat (length es)))
  by exact (cb_at_reg _ _ _ _ _ 11 (Z.of_nat (length es)) (11%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A20 : getr regsC 20 = w64 (e_F (x_e rsegs cx) + HSU_E62))
  by exact (cb_at_reg _ _ _ _ _ 20 (e_F (x_e rsegs cx) + HSU_E62) (20%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A21 : getr regsC 21 = w64 (hsu_cur rsegs cx rest r))
  by exact (cb_at_reg _ _ _ _ _ 21 (hsu_cur rsegs cx rest r) (21%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A26 : getr regsC 26 = w64 (Z.of_nat (length r)))
  by exact (cb_at_reg _ _ _ _ _ 26 (Z.of_nat (length r)) (26%bv : bv 5) HAT ltac:(cb_unf; cb_mem) eq_refl).
assert (A234 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 ->
  getr regsC (Z_to_bv 5 q) = getr (x_regs rsegs cx) (Z_to_bv 5 q)) by (destruct HCORE as (_ & Hq & _); exact Hq).
pose proof HP as (_ & _ & HR2 & HR3 & HR4 & _).
assert (A2 : getr regsC 2 = w64 (e_R (x_e rsegs cx))) by (rewrite <- HR2; exact (A234 2 ltac:(lia))).
assert (A3 : getr regsC 3 = w64 (as_gp B)) by (rewrite <- HR3; exact (A234 3 ltac:(lia))).
assert (A4 : getr regsC 4 = w64 (as_tp B)) by (rewrite <- HR4; exact (A234 4 ltac:(lia))).
(* the input at C *)
destruct (cb_in_now B MT cx rest _ lyC SC WC regsC memC mdC HP HIN HCORE HFSH eq_refl) as (HgC & HraC & _).
(* ---------------- the head block ---------------- *)
pose proof (HH (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) lyC SC WC memC mdC regsC
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx) (Z.of_nat (length es)) (hsu_P0 headamp_himg_B)
  HCTX0 A2 A9 A19 A3 A4 A11 A20 HFSH eq_refl) as HH1.
eapply SRr_bind; [exact HH1|]. clear HH1.
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 &
  (_ & H158 & HFSH1 & HE0)).
assert (HCORE1 : hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly1 S1 W1 regs1 mem1 md1).
{ apply (cb_core_step B MT MTL cx _ lyC SC WC regsC memC mdC ly1 S1 W1 regs1 mem1 md1
    (w6b_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) HCORE HJ1).
  - intros q Hq. apply (cb_reg_kept regsC regs1 cb_caller_saved q Hr1).
    destruct Hq as [->|[->| ->]]; vm_compute; reflexivity.
  - exact Hf1.
  - exact Hp1.
  - exact Hio1.
  - exact Hmo1.
  - exact Hm1.
  - intros a Ha. rewrite HspZ. unfold hsu_E1.
    destruct (w6b_hw_E1 (x_e rsegs cx) a Ha) as [X|X]; [left; exact X | right; left; exact X]. }
pose proof (cb_ctx_of B MT cx _ _ _ _ _ _ _ HP HCORE1) as HCTX1.
(* the registers the kind block reads, kept by the call (callee-saved) *)
assert (B2 : getr regs1 2 = w64 (e_R (x_e rsegs cx)))
  by (rewrite (cb_kept_bv regsC regs1 cb_caller_saved (2%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A2).
assert (B9 : getr regs1 9 = w64 (e_R (x_e rsegs cx)))
  by (rewrite (cb_kept_bv regsC regs1 cb_caller_saved (9%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A9).
assert (B27 : getr regs1 27 = w64 SHADOW_OFF)
  by (rewrite (cb_kept_bv regsC regs1 cb_caller_saved (27%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A27).
assert (B21 : getr regs1 21 = w64 (hsu_cur rsegs cx rest r))
  by (rewrite (cb_kept_bv regsC regs1 cb_caller_saved (21%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A21).
assert (B26 : getr regs1 26 = w64 (Z.of_nat (length r)))
  by (rewrite (cb_kept_bv regsC regs1 cb_caller_saved (26%bv : bv 5) Hr1 ltac:(vm_compute; reflexivity)); exact A26).
(* the input at the cursor after the head *)
pose proof (cb_in_kept B cx rest r (w6b_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) WC memC W1 mem1
  HP HIN HSUF HG HgC HraC (fun a Ha => w6b_hw_E1 (x_e rsegs cx) a Ha) Hm1) as HIN1.
(* the kept registers and cells of the pod loop, at the head's end; R+0x158 holds the pod index *)
assert (HATp1 : hsu_at rsegs (w_H W1) mem1 regs1 (x_e rsegs cx) (hsu_L_pod rsegs cx sh np ps cnt rest r)).
{ apply (cb_atl_tr (w6b_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) cb_caller_saved (w_H WC) memC _ _ regsC
    _ _ _ Hr1 Hm1); [cb_sides HG (w6b_head_wr (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx))) | exact HATp]. }
assert (HAT1 : hsu_at rsegs (w_H W1) mem1 regs1 (x_e rsegs cx)
  (hsu_L_Dc rsegs cx sh np ps cnt es ++ [(LReg 23, -8); (LReg 21, hsu_cur rsegs cx rest r)])).
{ unfold hsu_at.
  apply (cb_fsub _ (hsu_L_pod rsegs cx sh np ps cnt rest r ++ [(LCell XR 0x158, Z.of_nat (length es))])).
  - apply Forall_app. split; [exact HATp1|]. apply Forall_cons; [|apply Forall_nil].
    cbv beta. cbn [fst snd hd_at hd_xv]. exact H158.
  - cb_subs. }
(* e62's shadow, the first block and e62's zero bytes, at the head's end *)
assert (HFSH1' : hsu_fsh_at rsegs cx W1 mem1 (hsu_PJ headamp_himg_B)) by exact HFSH1.
assert (HE1 : hm_bytes rsegs (w_H W1) mem1 (e_F (x_e rsegs cx) + HSU_E62) (zeros 104)).
{ apply (hm_memset_bytes rsegs (w_H W1) mem1 _ 0 104). intros ii Hii. exact (HE0 ii Hii). }
assert (HPP1 : hm_bytes rsegs (w_H W1) mem1 (e_pp (x_e rsegs cx)) (pc_image (PbCut sh ps (Some es)))).
{ apply (hm_bytes_kept rsegs (w_H WC) memC _ _ _ _ HPP). intros x Hx. rewrite Hppl in Hx.
  destruct (w6b_hw_pp _ _ _ (x - e_pp (x_e rsegs cx)) HG ltac:(lia)) as [Hb Hw].
  replace x with (e_pp (x_e rsegs cx) + (x - e_pp (x_e rsegs cx))) by lia. exact (Hm1 _ Hb Hw). }
(* ---------------- the kind block ---------------- *)
pose proof (HK (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) ly1 S1 W1 mem1 md1 regs1
  (e_R (x_e rsegs cx)) (e_F (x_e rsegs cx)) (x_pos rsegs cx) (hsu_cur rsegs cx rest r) r
  HCTX1 B2 B9 B27 B21 B26 HIN1) as HK1.
eapply SRr_bind; [exact HK1|]. clear HK1.
intros W3 c3 Hw3 [(Hr0 & HPOST) | (b & r' & Hr & HPOST)].
- (* no input left: D0E *)
  subst r.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 & _).
  assert (SD3 : Forall (cb_side []%bv (fun _ => False) (x_e rsegs cx))
    (hsu_L_Dc rsegs cx sh np ps cnt es ++ [(LReg 23, -8); (LReg 21, hsu_cur rsegs cx rest [])]))
    by (cb_sides HG (fun _ : Z => False)).
  destruct (cb_blkE_step B MT MTL cx []%bv (fun _ => False) _ ly1 S1 W1 regs1 mem1 md1 ly3 S3 W3 regs3 mem3 md3
    HCORE1 HJ3 Hr3 Hf3 Hp3 Hio3 Hmo3 Hm3 (fun a (Ha : False) => False_ind _ Ha) eq_refl eq_refl eq_refl SD3 HAT1)
    as [HCORE3 HAT3].
  destruct (w6b_kept3 cx sh ps es W1 W3 mem1 mem3 HG Hppl Hm3 HFSH1' HPP1 HE1) as (HFSH3 & HPP3 & HE3).
  unfold hsu_from_D0E in HD0E.
  apply (HD0E ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es Hlp Hle).
  unfold hsu_cut_D0E.
  split; [exact (cb_pod_base_mv B MT cx sh np ps cnt es rest [] [] [] _ _ _ _ _ _ _ _ _ _ _ _ HB HCORE3 HSUF)|].
  split.
  { unfold hsu_at_cx, hsu_at. pose proof HAT3 as HAT3f. unfold hsu_at in HAT3f.
    apply (cb_fsub _ _ _ HAT3f). cb_subs. }
  split; [exact HFSH3|]. split; [exact HPP3 | exact HE3].
- (* the kind byte b: the entry of kind % 10 *)
  subst r.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hr3 & Hf3 & Hp3 & Hio3 & Hmo3 & Hm3 &
    (K17 & K18 & K6 & K20 & K7 & K16 & K13)).
  assert (SD3 : Forall (cb_side w6b_kind_clob (fun _ => False) (x_e rsegs cx))
    (hsu_L_Dc rsegs cx sh np ps cnt es ++ [(LReg 23, -8); (LReg 21, hsu_cur rsegs cx rest (b :: r'))]))
    by (cb_sides HG (fun _ : Z => False)).
  destruct (cb_blkE_step B MT MTL cx w6b_kind_clob (fun _ => False) _ ly1 S1 W1 regs1 mem1 md1 ly3 S3 W3 regs3 mem3
    md3 HCORE1 HJ3 Hr3 Hf3 Hp3 Hio3 Hmo3 Hm3 (fun a (Ha : False) => False_ind _ Ha) eq_refl eq_refl eq_refl SD3 HAT1)
    as [HCORE3 HAT3].
  destruct (w6b_kept3 cx sh ps es W1 W3 mem1 mem3 HG Hppl Hm3 HFSH1' HPP1 HE1) as (HFSH3 & HPP3 & HE3).
  pose proof HAT3 as HAT3f. unfold hsu_at in HAT3f.
  assert (Ecur : hsu_cur rsegs cx rest r' = hsu_cur rsegs cx rest (b :: r') + 1)
    by (unfold hsu_cur; cbn [length]; lia).
  rewrite (w6b_case_pc_D (bv_unsigned b)).
  unfold hsu_from_D in HD.
  apply (HD (bv_unsigned b) ly3 S3 W3 regs3 mem3 md3 sh np ps cnt es (b :: r') r' Hlp Hle).
  unfold hsu_cut_D.
  split; [exact (cb_pod_base_mv B MT cx sh np ps cnt es rest (b :: r') (b :: r') r' _ _ _ _ _ _ _ _ _ _ _ _ HB HCORE3
    (cb_suffix_tl rest b r' HSUF))|].
  split.
  { unfold hsu_at_cx, hsu_at, hsu_L_D. apply Forall_app. split; [apply (cb_fsub _ _ _ HAT3f); cb_subs|].
    apply Forall_app. split.
    { apply Forall_cons.
      { cbv beta. cbn [fst snd hd_at]. rewrite Ecur.
        replace (hsu_cur rsegs cx rest (b :: r') + 1 - 1) with (hsu_cur rsegs cx rest (b :: r')) by lia. exact K17. }
      apply Forall_cons; [cbv beta; cbn [fst snd hd_at]; rewrite Ecur; exact K18|].
      apply Forall_cons; [cbv beta; cbn [fst snd hd_at]; exact K6|].
      apply Forall_cons; [cbv beta; cbn [fst snd hd_at]; exact K20|].
      apply Forall_nil. }
    apply Forall_app. split.
    { apply Forall_cons; [cbv beta; cbn [fst snd hd_at]; exact K7|].
      apply Forall_cons; [cbv beta; cbn [fst snd hd_at]; exact K16|].
      apply Forall_cons; [exact (cb_at_get _ _ _ _ _ (LReg 23) (-8) HAT3 ltac:(cb_unf; cb_mem))|].
      apply Forall_nil. }
    destruct (bv_unsigned b mod 10 =? 9) eqn:E9; [apply Forall_nil|].
    apply Forall_cons; [|apply Forall_nil]. cbv beta. cbn [fst snd hd_at].
    destruct K13 as [K9|K13]; [apply Z.eqb_neq in E9; contradiction|].
    transitivity (w64 (sext8 (bv_unsigned b))); [exact K13|]. f_equal.
    unfold sext8. pose proof (Cursor.byte_range b) as Hb.
    destruct (Z.ltb_spec (bv_unsigned b) 128) as [Hl|Hl].
    - rewrite (Z.div_small (bv_unsigned b) 128) by lia. lia.
    - rewrite <- (Z.div_unique (bv_unsigned b) 128 1 (bv_unsigned b - 128)) by lia. lia. }
  split; [exact HFSH3|]. split; [exact HPP3|]. split; [exact HE3|].
  split; [exact HSUF|]. split; [reflexivity|]. split; [exact (Cursor.byte_range b)|].
  discriminate.
Qed.

End d.
End b.

Check w6b_disp_of.
Check w6b_cases_of.
Print Assumptions w6b_disp_of.
Print Assumptions w6b_cases_of.
