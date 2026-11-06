(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module names changed; 222 of its 422 lines of code are new or changed and 1492 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cps.v, with its module names changed; 303 of its 370 lines of code are new or changed and 355 lines of the source are left out. *)
(* write_value's CONTAINER arms (fs.asan image A, write_value 0x83d84): the two TAIL jumps to put of the closing
   bracket, which end the arm. From the OPEN point with n = 0 (ZZwv_inv.wvc_invO, segment ZZwv_runs1.wvc_seg_open_empty)
   and from the CLOSE point (ZZwv_inv.wvc_invC, segment ZZwv_runs2.wvc_seg_closeN), the arm's run reaches put
   (0x8418c) with write_value's frame popped, the entry ra and callee-saved registers restored, a0 = o, a1 = the
   closing literal (']' at 0x21220, '}' at 0x21200), a2 = 1; put's post, composed with the arm's journal from the
   entry by ZZwv_defs.wvc_tail_otJ, is the arm's own post FSW_write_value.wv_post.
   Template (the leaf arms' same step, not a copied proof): FSW_write_value.wv_tail_put / wv_jump / wv_tail_post.
   Beyond the Section block of ZZwv_step.v (copied verbatim), each lemma takes as plain premises the entry facts the
   tail hands back to the caller: the entry fpreU (ret_ok / raZ of regs0 and the entry frame chain at s0),
   spZ regs0 = wf_sp F (the arm's F fixes wf_sp := the entry sp), write_value_spec_at's s0 premise
   (s0 < alloc_ceiling \/ s0 = o \/ o + 48 <= s0), fs_img_facts (the closing literal's bytes) and put_spec.
   Rule 24: no function proved here (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat
FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model FSW_writer_kit
FSH_Fn_reader FSW_rd FSupoisonStack FSW_pj ZZwv_defs ZZwv_inv ZZwv_kit ZZwv_comp ZZwv_tree ZZwv_call ZZwv_call2
ZZwv_call3 ZZwv_res ZZwv_ret ZZwv_runs2 ZZwv_runs1 ZZwv_step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_write_value.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Hypothesis HSS : FsShadowSyms B.
(* the arm instance: its fixed data and the entry state *)
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
(* the entry facts the arms' callers discharge once *)
Hypothesis HE_sp16 : wf_sp F mod 16 = 0.
Hypothesis HE_ot16 : wf_ot F mod 16 = 0.
Hypothesis HE_oot : wf_o F + 32 <= wf_ot F.
Hypothesis HE_o8 : wf_o F mod 8 = 0.
Hypothesis HE_top : wf_ot F <= ly_top ly0.
Hypothesis HE_top47 : ly_top ly0 <= 2 ^ 47.
Hypothesis HE_lo : alloc_ceiling + STK_write_value (wf_m F) <= wf_sp F.
Hypothesis HE_gp : YK11.getr regs0 3%bv = w64 (as_gp B).
Hypothesis HE_tp : YK11.getr regs0 4%bv = w64 (as_tp B).
Hypothesis HE_cap0 : 0 <= wf_cap0 F.
Hypothesis HE_capl : wf_cap0 F <= wf_live F.
Hypothesis HE_cnt0 : 0 <= wf_cnt0 F.
Hypothesis HE_p : 0 <= wf_p F < alloc_ceiling.
Hypothesis HE_d : 0 <= wf_d F.
Hypothesis HE_dd : wf_d F + Z.of_nat (PjTree.depth (wf_t F)) <= 2 ^ 31 - 1.
Hypothesis HE_room : Z.of_nat (length (wf_text0 F)) + Z.of_nat (length (concat (wvc_WP F))) + 1 <= WMAX.
Hypothesis HE_bud : wbudget_pre S0 (wf_cap0 F) (wf_cnt0 F) (wf_live F) (WriterApp.putN (wvc_st0 F) (wvc_WP F)).
Hypothesis HE_frl : Z.of_nat (length (frames S0)) <= FRL_CRT_CALLEE.
Hypothesis HE_foot : forall x, wf_o F <= x < wf_ot F -> ~ PjStruct.pj_foot (wf_v F) (wf_D F) x.
Hypothesis HE_plain : jv_plain (wf_t F).
Hypothesis HE_ty :
  (wf_ty F = 5 /\ exists items, wf_t F = PjTree.JArr items /\ wf_n F = Z.of_nat (length items) /\ wf_keys F = 0) \/
  (wf_ty F = 6 /\ exists members, wf_t F = PjTree.JObj members /\ wf_n F = Z.of_nat (length members)).
Hypothesis HE_hdr : exists num capn,
  PjStruct.pj_hdr tfibsegs (rdW W0 mem0) (wf_v F) (wf_ty F) num (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) capn.
Hypothesis HE_n : 0 <= wf_n F < 2 ^ 54.
Hypothesis HE_kk : 0 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   0 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling.

(* ================= the frame chain at the jump ================= *)
(* put's fpreU at the tail jump reads the frame chain from write_value's ENTRY s0 (restored from the frame) over the
   memory at the jump. s0 < alloc_ceiling: the empty chain. s0 = o: the one-node clause at o that wvc_sem carries at
   this memory (at o = sp + 8 the entry chain itself is impossible: achain's second disjunct needs sp + 16 <= s0).
   o + 48 <= s0: the entry chain reads only words at or above s0 - 16 >= o + 32, which the arm kept (wkeep below ot,
   the journal above it). *)
Lemma wvct_chain : forall ch0 ly S U (W : world tfibsegs) memJ mdJ k buf st regsJ,
  fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0 ->
  spZ regs0 = wf_sp F ->
  (s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0) ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memJ) mdJ k ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ buf st ->
  spZ regsJ = wf_sp F -> s0Z regsJ = s0Z regs0 ->
  exists ch, achain ly (aview tfibsegs (w_H W) (unpoison U memJ)) (spZ regsJ) (s0Z regsJ) ch.
Proof.
intros ch0 ly S U W memJ mdJ k buf st regsJ HPRE0 Hsp0 HS0w HJ HARU HSEM EspJ Es0J.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ buf st HSEM) as Hosp.
pose proof HPRE0 as ((HAP0 & _) & _).
pose proof HAP0 as (_ & _ & _ & _ & _ & _ & _ & Hch0 & _).
pose proof (fsw_ARU B _ ly0 S0 U0 W0 regs0 mem0 md0 ch0 (proj1 HPRE0)) as HARU0.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & Hkeep & _).
assert (Etop : ly_top ly = ly_top ly0) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
rewrite EspJ, Es0J. rewrite Hsp0 in Hch0.
destruct HSEM as (_ & _ & _ & _ & _ & _ & _ & HWK & _ & _ & _ & _ & _ & _ & _ & _ & _ & H8 & HC & _).
destruct HS0w as [Hlo | [Ho | Hhi]].
- exists []. apply achain_low. exact Hlo.
- rewrite Ho in Hch0 |- *.
  destruct HC as [(Eo & _) | (H16 & nfp & Hnfp & Hend)].
  + exfalso. destruct Hch0 as [([H | [H | H]] & _) | (H1 & _)]; [lia | lia | exact (H HE_o8) | lia].
  + pose proof (wvc_rdword_range _ _ _ _ H8) as R8. pose proof (wvc_rdword_range _ _ _ _ Hnfp) as R16.
    destruct (wvc_achain ly _ (wf_sp F) (wf_o F) (wf_ra8 F) nfp H8 Hnfp Hend ltac:(lia) ltac:(lia) H16
      ltac:(lia) ltac:(rewrite Etop; lia) HE_o8) as (ch & Hch & _).
    exists ch. exact Hch.
- exists ch0.
  assert (AV : forall x, wf_o F + 32 <= x < ly_top ly0 ->
    aview tfibsegs (w_H W) (unpoison U memJ) x = aview tfibsegs (w_H W0) (unpoison U0 mem0) x).
  { intros x Hx.
    destruct (Z_lt_le_dec x (wf_ot F)) as [Hlt | Hge].
    - rewrite (aview_unpoison_out tfibsegs _ U memJ x (zwk_p_stack_not_ush B ly S U W memJ mdJ x HARU ltac:(lia))).
      rewrite (aview_unpoison_out tfibsegs _ U0 mem0 x
        (zwk_p_stack_not_ush B ly0 S0 U0 W0 mem0 md0 x HARU0 ltac:(lia))).
      unfold aview. destruct (HWK x ltac:(lia) ltac:(lia)) as (E1 & _). rewrite E1. reflexivity.
    - apply Hkeep; [lia | unfold wvc_STK; lia]. }
  apply (achain_ly_top ly0 ly _ _ _ _ Etop).
  destruct Hch0 as [Hc | (H1 & H2 & H3 & H4 & H5)]; [left; exact Hc | right].
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
  apply (fpchain_ext (rdword (aview tfibsegs (w_H W0) (unpoison U0 mem0)))); [| lia | exact H4].
  intros a Ha1 Ha2. apply rdword_ext. intros kk Hkk. apply AV. lia.
Qed.

(* ================= the tail call of put, at the jump ================= *)
(* The jump state after either end segment: write_value's frame popped (sp = the entry sp), gp / tp and the
   thirteen frame-saved registers (ra and the callee-saved s-registers) the entry's, a0 = o, a1 = the closing
   literal, a2 = 1; the arm's journal from the entry and the writer facts after the pieces Pd. put's spec at the
   jump, and its post composed with the arm's journal (wvc_tail_otJ), give the arm's post. *)
Lemma wvct_jump : forall ch0 Pd ly S U (W : world tfibsegs) memJ mdJ buf regsJ,
  fs_img_facts tfibsegs B -> put_spec B tfibsegs ->
  fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0 ->
  spZ regs0 = wf_sp F ->
  (s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0) ->
  wvc_WP F = Pd ++ [if wf_ty F =? 6 then [125] else [93]] ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memJ) mdJ (wevk (wf_cap0 F) (wvc_stP F Pd)) ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ buf (wvc_stP F Pd) ->
  YK11.getr regsJ 2%bv = Z_to_bv 64 (wf_sp F) ->
  YK11.getr regsJ 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsJ 4%bv = YK11.getr regs0 4%bv ->
  (forall j : nat, (j < 13)%nat ->
     YK11.getr regsJ (nth j wvc_saved 0%bv) = YK11.getr regs0 (nth j wvc_saved 0%bv)) ->
  YK11.getr regsJ 10%bv = w64 (wf_o F) -> YK11.getr regsJ 11%bv = w64 (wvc_close (wf_ty F)) ->
  YK11.getr regsJ 12%bv = w64 1 ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regsJ memJ mdJ)
    (FSW_write_value.wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros ch0 Pd ly S U W memJ mdJ buf regsJ IMG HPUT HPRE0 Hsp0 HS0w HWP HJ HARU HSEM RJ2 RJ3 RJ4 RJS RJ10 RJ11 RJ12.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & HSTKp & _).
assert (SKp0 : 0 <= STK_put) by (vm_compute; discriminate).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ buf _ HSEM) as Hosp.
pose proof (proj1 HARU) as HAR.
pose proof HPRE0 as ((HAP0 & _) & _).
pose proof HAP0 as (_ & Hret0 & Hra40 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Etop : ly_top ly = ly_top ly0) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
(* ---- the registers at the jump are the entry's ---- *)
assert (P2 : YK11.getr regsJ 2%bv = YK11.getr regs0 2%bv).
{ rewrite RJ2, <- Hsp0. unfold spZ. apply Z_to_bv_bv_unsigned. }
assert (P3 := RJ3). assert (P4 := RJ4).
pose proof (RJS 0%nat ltac:(lia)) as P27. pose proof (RJS 1%nat ltac:(lia)) as P26.
pose proof (RJS 2%nat ltac:(lia)) as P25. pose proof (RJS 3%nat ltac:(lia)) as P24.
pose proof (RJS 4%nat ltac:(lia)) as P23. pose proof (RJS 5%nat ltac:(lia)) as P22.
pose proof (RJS 6%nat ltac:(lia)) as P21. pose proof (RJS 7%nat ltac:(lia)) as P20.
pose proof (RJS 8%nat ltac:(lia)) as P19. pose proof (RJS 9%nat ltac:(lia)) as P18.
pose proof (RJS 10%nat ltac:(lia)) as P9. pose proof (RJS 11%nat ltac:(lia)) as P8.
pose proof (RJS 12%nat ltac:(lia)) as P1.
cbn [nth wvc_saved] in P27, P26, P25, P24, P23, P22, P21, P20, P19, P18, P9, P8, P1.
assert (HP : aregs_preserved regs0 regsJ).
{ intros r Hr.
  assert (Hr0 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
  clear Hr. repeat (destruct Hr0 as [-> | Hr0]; [assumption|]). subst r. assumption. }
assert (Esp : spZ regsJ = wf_sp F) by (unfold spZ; rewrite P2; exact Hsp0).
assert (S0J : s0Z regsJ = s0Z regs0) by (unfold s0Z; rewrite P8; reflexivity).
assert (RA : raZ regsJ = raZ regs0) by (unfold raZ; rewrite P1; reflexivity).
(* ---- the writer facts at the jump ---- *)
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & _ & _ & _ & _ & _ & _ & _ & HBIN & HB0 & HRO & H8 &
  HC & HU0).
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _).
destruct HGL as (peak & Hpk & HG).
assert (Hcap0i : wf_cap0 F <= WriterApp.w_cap (wvc_stP F Pd)) by exact (wv_cap_mono (wvc_st0 F) Pd HE_cap0).
(* ---- put's fpreU at the jump ---- *)
destruct (wvct_chain ch0 ly S U W memJ mdJ _ buf _ regsJ HPRE0 Hsp0 HS0w HJ HARU HSEM Esp S0J) as (chJ & HchJ).
assert (HPREJ : fpreU tfibsegs B STK_put ly S U W regsJ memJ mdJ chJ).
{ apply (fsw_fpreU_atFP B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 U W0 (unpoison U0 mem0) md0 [] ly S W memJ mdJ
    _ regsJ STK_put (wf_sp F - wf_ot F) chJ HJ HARU HRO).
  - rewrite Esp. lia.
  - rewrite Zminus_mod, HE_sp16, HE_ot16. reflexivity.
  - lia.
  - exact SKp0.
  - unfold wvc_STK. lia.
  - rewrite P1. exact Hret0.
  - rewrite RA. exact Hra40.
  - rewrite P3. exact HE_gp.
  - rewrite P4. exact HE_tp.
  - exact HchJ. }
(* ---- the closing literal ---- *)
set (bs := if wf_ty F =? 6 then [125] else [93]) in *.
assert (Hcl : 4096 <= wvc_close (wf_ty F) <= 0x21220)
  by (unfold wvc_close, WVC_RBRACE, WVC_RBRACKET; destruct (wf_ty F =? 6); lia).
assert (Hlen : Z.of_nat (length bs) = 1) by (unfold bs; destruct (wf_ty F =? 6); reflexivity).
pose proof (FSW_write_value.wv_rom_view B STK_put ly S U W regsJ memJ mdJ chJ IMG (proj1 HPREJ) HRO) as HROMV.
assert (HZB : zbytes_at tfibsegs W memJ (wvc_close (wf_ty F)) bs).
{ apply (FSW_write_value.wv_rom_zbytes W memJ); [exact HROMV|].
  unfold bs, wvc_close, WVC_RBRACE, WVC_RBRACKET. destruct (wf_ty F =? 6); vm_compute; reflexivity. }
assert (HSRC : wsrc_kept B tfibsegs ly S U W memJ buf (wvc_close (wf_ty F)) bs).
{ right; right; right. exists bs. split; [|apply Nat.le_succ_diag_r].
  unfold bs, wvc_close, WVC_RBRACE, WVC_RBRACKET. destruct (wf_ty F =? 6); cbn; tauto. }
assert (HBOK : WriterSpec.bytes_ok bs).
{ unfold WriterSpec.bytes_ok, bs. apply Forall_forall. intros c Hc.
  destruct (wf_ty F =? 6); cbn in Hc; destruct Hc as [<- | []]; lia. }
(* ---- put's tail call ---- *)
eapply SRr_mono.
{ apply (HPUT ly S U W regsJ memJ mdJ chJ (wf_ot F) (wf_o F) (wvc_close (wf_ty F)) 1 buf
    (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.w_failed (wvc_stP F Pd)) (WriterApp.w_text (wvc_stP F Pd)) bs
    (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F) peak (WriterApp.w_cnt (wvc_stP F Pd))
    (WriterApp.w_fail (wvc_stP F Pd)) HPREJ HHD).
  - rewrite Hfrs. cbn [app]. lia.
  - exact RJ10.
  - exact RJ11.
  - exact RJ12.
  - exact HOUT.
  - exact HG.
  - exact HU0.
  - rewrite Esp. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - rewrite Etop. exact HE_top.
  - destruct HC as [(Eo & Hra) | (H16 & nfp & Hnfp & Hend)].
    + left. rewrite Esp, RA. split; [exact Eo | exact Hra].
    + right. rewrite Esp. split; [exact H16|]. exists (wf_ra8 F), nfp.
      split; [exact H8|]. split; [exact Hnfp | exact Hend].
  - intros a Ha. rewrite Esp in Ha.
    apply (fsw_apresent_unpoison B ly S U W memJ mdJ a HARU); [lia|].
    apply Hpres. unfold wvc_STK. lia.
  - exact HZB.
  - exact HSRC.
  - exact Hlen.
  - exact HBOK.
  - lia.
  - left. lia.
  - pose proof HE_room as HR. rewrite HWP in HR.
    pose proof (wv_room_mid (wvc_st0 F) Pd [bs]) as HM.
    assert (Lb : length (concat [bs]) = 1%nat) by (unfold bs; destruct (wf_ty F =? 6); reflexivity).
    rewrite Lb in HM. change (WriterApp.w_text (wvc_st0 F)) with (wf_text0 F) in HM.
    unfold wvc_stP. lia.
  - destruct HBK as (Hw & _). exact Hw.
  - lia.
  - pose proof HE_bud as HB. rewrite HWP in HB.
    pose proof (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
      Pd [bs] HE_cap0 HB Hnev ltac:(destruct HBK as (_ & Hbb & _); exact Hbb) HCNT) as HBP.
    replace (wf_live F + WriterApp.w_cap (wvc_stP F Pd) - wf_cap0 F)
      with (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F Pd)) by lia.
    exact HBP. }
(* ---- put's post is the arm's post ---- *)
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
subst st'.
exists (wvc_stP F (Pd ++ [bs])), buf', U'.
split.
{ change (WriterValue.wvpieces (wf_t F) (negb (wf_p F =? 0)) (wf_d F)) with (wvc_WP F). rewrite HWP. reflexivity. }
split.
{ exact (wv_uswap_trans B ly S W (unpoison U memJ) mdJ U0 U U' (wf_buf0 F) buf buf' (wf_cap0 F)
    (WriterApp.w_cap (wvc_stP F Pd)) HAR (proj1 (proj2 HARU)) HHD HB0 HE_cap0 Hcap0i HUS Hus). }
unfold wpost in Hwp |- *.
rewrite Hsp0.
change (STK_write_value (wf_m F) + (wf_ot F - wf_sp F)) with (wvc_STK F).
change (FS_PSTAT_FP ++ wbuf_fp (wf_buf0 F) (wf_cap0 F)) with (wvc_FP F).
assert (ESP : wevk (wf_cap0 F) (wvc_stP F (Pd ++ [bs])) =
  wevk (wf_cap0 F) (wvc_stP F Pd) +
  wevk (WriterApp.w_cap (wvc_stP F Pd)) (WriterApp.put1 (wv_rst (wvc_stP F Pd)) bs))
  by exact (wv_wevk_split (wvc_st0 F) Pd [bs] eq_refl HE_cap0).
rewrite ESP.
apply (ZZwv_defs.wvc_tail_otJ B (wvc_STK F) (STK_put + (wf_ot F - spZ regsJ)) (wf_ot F) (wvc_FP F)
  (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap (wvc_stP F Pd))) ly0 S0 U0 W0 W mem0 md0 ly S U memJ mdJ regs0 regsJ
  _ _ U' _ W' c' HJ HARU).
- rewrite Esp. unfold wvc_STK. lia.
- exact P1.
- exact HP.
- exact (wv_fp_sub_swap B ly0 S0 ly S W (unpoison U memJ) mdJ (wf_buf0 F) (wf_cap0 F) buf
    (WriterApp.w_cap (wvc_stP F Pd)) HAR HBS HBIN ltac:(lia) wvc_pstat_img).
- eapply FSW_write_value.wv_fpostU_mono; [exact Hwp|].
  cbv beta. intros ly' S' regs' mem' md' HJc OK' PO' HP' (Q1 & Q2 & Q3 & Q4 & Q5 & _).
  assert (Hcnt : wf_cnt0 F + wcalls (WriterApp.putN (wvc_stP F Pd) [bs]) < 2 ^ 64).
  { pose proof HE_bud as (_ & _ & _ & HB4). rewrite HWP in HB4.
    unfold wvc_stP. rewrite <- WriterApp.putN_app. exact HB4. }
  destruct (wvc_sem_call B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ mdJ buf (wvc_stP F Pd) [bs] ly' S' U' W' mem'
    md' buf' (STK_put + (wf_ot F - spZ regsJ)) _ (spZ regsJ) peak HSEM HARU HE_cap0 Hcap0i HE_cnt0 Hcnt Hlo' HE_oot
    Hpk HJc OK' PO' Hus Q1 Q2 Q3 Q4 ltac:(rewrite Esp; lia) Q5) as (_ & HSEM').
  assert (HSEM2 : wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly' S' U' W' mem' buf' (wvc_stP F (Pd ++ [bs])))
    by (unfold wvc_stP; rewrite WriterApp.putN_app; exact HSEM').
  destruct HSEM2 as (HOUT' & HGL' & _ & _ & HBS' & HBK' & _ & HWK' & HN' & _).
  split; [exact HOUT'|]. split; [exact HBK'|]. split; [exact HBS'|].
  split; [exact HWK'|]. split; [exact HN'|]. exact HGL'.
Qed.

(* ================= (1) the OPEN point with n = 0: the TAIL jump to put of ']' / '}' ================= *)
(* model: the arm's pieces are [[91]] ++ [[93]] ([[123]] ++ [[125]] for an object, ZZwv_tree.wv_pieces_arr / _obj
   with no item); the OPEN point has written the first, this put writes the last *)
Lemma wvc_empty_tail : forall ch0 ly S U (W : world tfibsegs) ms mdc buf,
  fs_img_facts tfibsegs B -> put_spec B tfibsegs ->
  fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0 ->
  spZ regs0 = wf_sp F ->
  (s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0) ->
  wf_n F = 0 ->
  wvc_invO B F ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (FSW_write_value.wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros ch0 ly S U W ms mdc buf IMG HPUT HPRE0 Hsp0 HS0w Hn0 HINV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
unfold wvc_invO in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & _ & _ & _ & R3 & R4 & _ & Hsp).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
assert (Hty56 : wf_ty F = 5 \/ wf_ty F = 6)
  by (destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty).
assert (HWP : wvc_WP F = [if wf_ty F =? 6 then [123] else [91]] ++ [if wf_ty F =? 6 then [125] else [93]]).
{ unfold wvc_WP. destruct HE_ty as [(Hty & items & Ht & Hn & _) | (Hty & members & Ht & Hn)]; rewrite Ht, Hty.
  - destruct items as [|x items]; [reflexivity | cbn [length] in Hn; lia].
  - destruct members as [|x members]; [reflexivity | cbn [length] in Hn; lia]. }
set (E := Ereg (ms_regs ms)
  (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F) 0)) in *.
apply (wvc_seg_open_empty B W ms mdc E (wf_ty F) (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F) ly0 S0 W0
  (unpoison U0 mem0) md0 [] ly S U _ _ HAT Hty56).
- unfold E. rewrite fsw_ew_xatom. cbn [nth wvc_xs app]. rewrite Hn0. reflexivity.
- unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' HJ HARU HFR R1 R2 R3' R4' R10 R11 R12 RS Ems.
  rewrite Ems.
  pose proof (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU HFR
    Hlo' ltac:(lia) ltac:(lia)) as HSEMJ.
  apply (wvct_jump ch0 [if wf_ty F =? 6 then [123] else [91]] ly S U W (ms_mem ms') mdc' buf (ms_regs ms')
    IMG HPUT HPRE0 Hsp0 HS0w HWP HJ HARU HSEMJ).
  + exact R2.
  + rewrite R3'. unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl). exact R3.
  + rewrite R4'. unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl). exact R4.
  + intros j Hj.
    assert (Hj' : nth_error wvc_saved j = Some (nth j wvc_saved 0%bv))
      by (apply nth_error_nth'; cbn [length wvc_saved]; lia).
    rewrite (RS j _ Hj'). unfold E. apply wvr1_xs_saved. exact Hj.
  + rewrite R10. unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl). exact R8.
  + exact R11.
  + exact R12.
Qed.

(* ================= (2) the CLOSE point: the TAIL jump to put of ']' / '}' ================= *)
Lemma wvc_close_tail : forall ch0 Pd ly S U (W : world tfibsegs) ms mdc buf,
  fs_img_facts tfibsegs B -> put_spec B tfibsegs ->
  fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0 ->
  spZ regs0 = wf_sp F ->
  (s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0) ->
  wvc_WP F = Pd ++ [if wf_ty F =? 6 then [125] else [93]] ->
  wvc_invC B F Pd ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (FSW_write_value.wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros ch0 Pd ly S U W ms mdc buf IMG HPUT HPRE0 Hsp0 HS0w HWP HINV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 176) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
assert (Hlo' : alloc_ceiling <= wf_sp F - WVC_F) by lia.
unfold wvc_invC in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & _ & _ & _ & _ & R3 & R4 & _ & _ & _ & _ & _ & _ & _ & Hsp & _).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
assert (Hty56 : wf_ty F = 5 \/ wf_ty F = 6)
  by (destruct HE_ty as [(Hty & _) | (Hty & _)]; [left | right]; exact Hty).
set (E := Ereg (ms_regs ms)
  (fs_extraT ++ wvc_xs regs0 (wf_str F) (wf_kids F) (wf_keys F) (wf_n F) (wf_d F) (wf_keys F + 8 * wf_n F) 0)) in *.
apply (wvc_seg_closeN B W ms mdc E (wf_ty F) (wf_p F) (wvc_STK F) (wf_ot F) (wf_sp F) (wvc_FP F) ly0 S0 W0
  (unpoison U0 mem0) md0 [] ly S U _ _ HAT Hty56).
- unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- lia.
- intros ms' mdc' Ems HJ HARU HFR R1 R10 R11 R12 R2 R3' R4' RS.
  rewrite Ems.
  pose proof (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU HFR
    Hlo' ltac:(lia) ltac:(lia)) as HSEMJ.
  apply (wvct_jump ch0 Pd ly S U W (ms_mem ms') mdc' buf (ms_regs ms') IMG HPUT HPRE0 Hsp0 HS0w HWP HJ HARU HSEMJ).
  + exact R2.
  + rewrite R3'. unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl). exact R3.
  + rewrite R4'. unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl). exact R4.
  + intros j Hj. rewrite (RS j Hj). unfold E. apply wvr1_xs_saved. exact Hj.
  + rewrite R10. unfold E. rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl). exact R8.
  + exact R11.
  + exact R12.
Qed.

End A.
