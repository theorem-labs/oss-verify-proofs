(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_write_value.v, with its module paths and module names changed; 518 of its 589 lines of code are new or changed and 1621 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/ZZwv_cent.v, with its module paths, module names and numbers changed; 280 of its 349 lines of code are new or changed and 520 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the CLOSING TAIL PUT of the lib/B (fs.asan-ubsan) container arms of
   write_value: from the open invariant with n = 0 (the empty container, which jumps straight to 0x842c4) or from
   the close invariant after the closing indent (ZZwvB_arm.wvc_invN), the engine run to the TAIL jump to put
   (j at 0x84440, write_value's frame popped and its callee-saved registers restored), that put with the closing
   bracket, and the arm's post (FSW_write_value_entry.wv_post).
   The tail composition is FSW_write_value_entry.wvc_tail_otJ (the caller's journal at the jump already holds the
   arm's calls), not the leaf arms' wv_tail_post (which starts from a journal of length 0).
   Image A has no twin of this file: its container arms are unproved.
   rule 24: proves no function (kind: segment lemma) - the closing step of the container arms of write_value B.
   Rule 24 (proof-index, a Theorem Labs lane, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_rd FSW_pj FSH_Fn_writer
FSW_write_value_entry ZZwvB_defs ZZwvB_comp ZZwvB_kit ZZwvB_tree ZZwvB_inv ZZwvB_call ZZwvB_call2 ZZwvB_call3
ZZwvB_ret ZZwvB_res ZZwvB_runs1 ZZwvB_runs2 ZZwvB_step ZZwvB_arm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HPUT : put_spec B tfibsegs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section St.
Variable F : wvc_fix.
Variables (ly0 : alayout) (S0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs) (mem0 : word -> option byte)
  (md0 : Model) (regs0 : bvmap 5 word).
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
Hypothesis HE_kk : 0 < wf_n F -> 4096 <= wf_kids F /\ wf_kids F + 56 * wf_n F <= alloc_ceiling /\
                   (wf_ty F = 6 -> 4096 <= wf_keys F /\ wf_keys F + 8 * wf_n F <= alloc_ceiling).
Hypothesis HE_capM : wf_cap0 F <= WMAX.
Hypothesis HE_s0 : s0Z regs0 < alloc_ceiling \/ s0Z regs0 = wf_o F \/ wf_o F + 48 <= s0Z regs0.
(* the entry sp and the entry's own premise (a Theorem Labs lane 07:5xZ: the tail put returns to the entry ra and needs its frame
   chain; wv_arr / wv_obj set wf_sp F := spZ regs and carry the entry fpreU) *)
Hypothesis HE_sp : spZ regs0 = wf_sp F.
Hypothesis HE_pre : exists ch0, fpreU tfibsegs B (STK_write_value (wf_m F)) ly0 S0 U0 W0 regs0 mem0 md0 ch0.

(* ---- the closing literal ']' / '}': its bytes in .rodata, an fs read-only string, by computation ---- *)
Lemma wvc_close_lit : forall ty (W : world tfibsegs) mem, ty = 5 \/ ty = 6 -> rom_view tfibsegs W mem ->
  zbytes_at tfibsegs W mem (wvc_close ty) (if ty =? 6 then [125] else [93]) /\
  In (wvc_close ty, if ty =? 6 then [125] else [93]) FS_RO_STRS /\
  WriterSpec.bytes_ok (if ty =? 6 then [125] else [93]) /\ 4096 <= wvc_close ty /\ wvc_close ty + 1 <= 2 ^ 32.
Proof.
intros ty W mem [-> | ->] HR.
all: split; [apply wv_rom_zbytes; [exact HR | vm_compute; reflexivity]|].
all: split; [unfold wvc_close, WVC_RBRACE, WVC_RBRACKET; cbn; tauto|].
all: split; [unfold WriterSpec.bytes_ok; cbn; constructor; [cbv beta; lia | constructor]|].
all: unfold wvc_close, WVC_RBRACE, WVC_RBRACKET; cbn; lia.
Qed.

(* ---- the callee-saved registers, one by one ---- *)
Lemma wvc_pres_list : forall regs regs' : bvmap 5 word,
  (forall r : bv 5, In r CALLEE_SAVED -> YK11.getr regs' r = YK11.getr regs r) -> aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. apply H.
unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [->|Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* ---- the TAIL put at the jump (j at 0x84440): write_value's frame popped (sp = the entry sp), ra and the
   callee-saved registers reloaded from the frame slots 88 .. 184 (the entry's, xatom 5 .. 17), a0 = o, a1 = the
   closing literal, a2 = 1. The journal from the entry already holds the arm's calls (pieces P), so the composition
   is wvc_tail_otJ; the writer facts after put are ZZwvB_call3.wvc_sem_call's, at the model state P ++ the close ----
   The entry chain at s0 (put's fpreU) is the entry's own (HE_pre), read at the jump: s0 < alloc_ceiling gives the
   empty chain; s0 = o the one-node chain at o (wvc_achain; o = sp + 8 has no chain at the entry, so it is ruled
   out); o + 48 <= s0 the entry's records, whose words lie at or above o + 32, kept by wkeep below ot and by the
   journal above it. *)
Lemma wvc_close_put : forall P ly S U (W : world tfibsegs) regsJ memJ mdJ buf,
  wvc_WP F = P ++ wvc_PCLOSE F ->
  ajournal tfibsegs B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 W0 (unpoison U0 mem0) md0 []
    ly S W (unpoison U memJ) mdJ (wevk (wf_cap0 F) (wvc_stP F P)) ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  wvc_sem B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ buf (wvc_stP F P) ->
  (forall j, (j < 13)%nat -> YK11.getr regsJ (nth j wvc_saved 0%bv) = YK11.getr regs0 (nth j wvc_saved 0%bv)) ->
  YK11.getr regsJ 2%bv = Z_to_bv 64 (wf_sp F) ->
  YK11.getr regsJ 3%bv = YK11.getr regs0 3%bv -> YK11.getr regsJ 4%bv = YK11.getr regs0 4%bv ->
  YK11.getr regsJ 10%bv = w64 (wf_o F) -> YK11.getr regsJ 11%bv = w64 (wvc_close (wf_ty F)) ->
  YK11.getr regsJ 12%bv = w64 1 ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regsJ memJ mdJ)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros P ly S U W regsJ memJ mdJ buf HWP HJ HARU HSEM HSAV R2 R3 R4 G10 G11 G12.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_stk (wf_m F)) as (HSTKF & HSTKp & _).
assert (SKp0 : 0 <= STK_put) by (vm_compute; discriminate).
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ buf _ HSEM) as Hosp.
destruct HE_pre as (ch0 & HPRE0).
pose proof HPRE0 as (HPREU0 & _).
pose proof HPREU0 as (HAP0 & _ & _).
pose proof HAP0 as (_ & Hra0 & Hra40 & _ & _ & _ & _ & Hch0 & _).
pose proof (fsw_ARU B _ ly0 S0 U0 W0 regs0 mem0 md0 ch0 HPREU0) as HARU0.
pose proof HJ as (HARJ & Hly & _ & _ & _ & Hfrs & Hnev & _ & HOUTK & _ & _ & _ & _ & HPRES & HSTK & _ & _).
assert (Etop : ly_top ly = ly_top ly0) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & E & _); exact E).
pose proof HSTK as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
(* ---- the registers at the jump ---- *)
assert (HP : aregs_preserved regs0 regsJ).
{ apply wvc_pres_list. intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
  all: first
    [ exact R3 | exact R4
    | rewrite R2, <- HE_sp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
    | exact (HSAV 0%nat ltac:(lia)) | exact (HSAV 1%nat ltac:(lia)) | exact (HSAV 2%nat ltac:(lia))
    | exact (HSAV 3%nat ltac:(lia)) | exact (HSAV 4%nat ltac:(lia)) | exact (HSAV 5%nat ltac:(lia))
    | exact (HSAV 6%nat ltac:(lia)) | exact (HSAV 7%nat ltac:(lia)) | exact (HSAV 8%nat ltac:(lia))
    | exact (HSAV 9%nat ltac:(lia)) | exact (HSAV 10%nat ltac:(lia)) | exact (HSAV 11%nat ltac:(lia)) ]. }
assert (R1 : YK11.getr regsJ 1%bv = YK11.getr regs0 1%bv) by exact (HSAV 12%nat ltac:(lia)).
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regsJ r = YK11.getr regs0 r)
  by (intros r Hr; exact (fsw_pres regs0 regsJ r HP Hr)).
assert (Esp : spZ regsJ = wf_sp F).
{ unfold spZ. rewrite (PR 2%bv ltac:(apply (wvc_cs_z _ 2); [reflexivity | lia])). exact HE_sp. }
assert (S0J : s0Z regsJ = s0Z regs0).
{ unfold s0Z. rewrite (PR 8%bv ltac:(apply (wvc_cs_z _ 8); [reflexivity | lia])). reflexivity. }
(* ---- the writer facts at the jump ---- *)
pose proof HSEM as (HOUT & HGL & HHD & HUS & HBS & HBK & HCNT & HWK & HN & HPO & HNB & HUL & HD & HROOT & HBIN & HB0 &
  HRO & H8 & HC & HU0).
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _).
destruct HGL as (peak & Hpk & HG).
assert (Hcap0i : wf_cap0 F <= WriterApp.w_cap (wvc_stP F P)) by exact (wv_cap_mono (wvc_st0 F) P HE_cap0).
(* ---- the bytes at and above o + 32 are the entry's ---- *)
assert (KEEP : forall a, wf_o F + 32 <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U memJ) a = aview tfibsegs (w_H W0) (unpoison U0 mem0) a).
{ intros a Ha. destruct (Z_lt_le_dec a (wf_ot F)) as [Hlt | Hge].
  - rewrite (aview_unpoison_out tfibsegs _ U memJ a (zwk_p_stack_not_ush B ly S U W memJ mdJ a HARU ltac:(lia))).
    rewrite (aview_unpoison_out tfibsegs _ U0 mem0 a
      (zwk_p_stack_not_ush B ly0 S0 U0 W0 mem0 md0 a HARU0 ltac:(lia))).
    destruct (HWK a ltac:(lia) ltac:(lia)) as (E1 & _). unfold aview. rewrite E1. reflexivity.
  - apply HOUTK; [lia | unfold wvc_STK; lia]. }
(* ---- the entry chain at s0, at the jump ---- *)
assert (HCHJ : exists chJ, achain ly (aview tfibsegs (w_H W) (unpoison U memJ)) (spZ regsJ) (s0Z regsJ) chJ).
{ rewrite Esp, S0J. rewrite HE_sp in Hch0.
  destruct HE_s0 as [Hlo0 | [Ho0 | Hhi0]].
  - exists []. apply achain_low. exact Hlo0.
  - rewrite Ho0 in Hch0 |- *.
    destruct HC as [(Eo & _) | (H16 & nfp & Hnfp & Hend)].
    + exfalso. destruct Hch0 as [([Hx | [Hx | Hx]] & _) | (Hx & _)]; lia.
    + pose proof (wvc_rdword_range _ _ _ _ H8) as RG8. pose proof (wvc_rdword_range _ _ _ _ Hnfp) as RG16.
      destruct (wvc_achain ly (aview tfibsegs (w_H W) (unpoison U memJ)) (wf_sp F) (wf_o F) (wf_ra8 F) nfp H8 Hnfp
        Hend ltac:(lia) ltac:(lia) H16 ltac:(lia) ltac:(lia) HE_o8) as (chJ & HchJ & _).
      exists chJ. exact HchJ.
  - exists ch0. apply (achain_ly_top ly0 ly _ _ _ _ Etop).
    destruct Hch0 as [Hc | (H1 & H2 & H3 & H4 & H5)]; [left; exact Hc|].
    right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
    eapply fpchain_ext; [| |exact H4]; [|lia].
    intros a Ha1 Ha2. apply rdword_ext. intros kk Hkk. apply KEEP. lia. }
destruct HCHJ as (chJ & HchJ).
(* ---- put's premise at the jump ---- *)
assert (HPREJ : fpreU tfibsegs B STK_put ly S U W regsJ memJ mdJ chJ).
{ apply (fsw_fpreU_atFP B (wvc_STK F) (wf_ot F) (wvc_FP F) ly0 S0 U W0 (unpoison U0 mem0) md0 [] ly S W memJ mdJ
    (wevk (wf_cap0 F) (wvc_stP F P)) regsJ STK_put (wf_sp F - wf_ot F) chJ HJ HARU HRO).
  - rewrite Esp. lia.
  - rewrite Zminus_mod, HE_sp16, HE_ot16. reflexivity.
  - lia.
  - exact SKp0.
  - unfold wvc_STK. lia.
  - rewrite R1. exact Hra0.
  - unfold raZ. rewrite R1. exact Hra40.
  - rewrite R3. exact HE_gp.
  - rewrite R4. exact HE_tp.
  - exact HchJ. }
assert (Hty : wf_ty F = 5 \/ wf_ty F = 6) by (destruct HE_ty as [(H & _) | (H & _)]; [left | right]; exact H).
destruct (wvc_close_lit (wf_ty F) W memJ Hty (wv_rom_view B _ ly S U W regsJ memJ mdJ chJ IMG (proj1 HPREJ) HRO))
  as (HZB & HIN & HBOK & HSA).
(* ---- the model split at the close ---- *)
assert (Hcnt : wf_cnt0 F + wcalls (WriterApp.putN (wvc_stP F P) (wvc_PCLOSE F)) < 2 ^ 64).
{ pose proof HE_bud as (_ & _ & _ & HB4). rewrite HWP, WriterApp.putN_app in HB4. exact HB4. }
assert (EST : WriterApp.putN (wvc_st0 F) (wvc_WP F) = WriterApp.putN (wvc_stP F P) (wvc_PCLOSE F)).
{ rewrite HWP, WriterApp.putN_app. reflexivity. }
assert (ESP : wevk (wf_cap0 F) (WriterApp.putN (wvc_stP F P) (wvc_PCLOSE F)) =
  wevk (wf_cap0 F) (wvc_stP F P) +
  wevk (WriterApp.w_cap (wvc_stP F P)) (WriterApp.putN (wv_rst (wvc_stP F P)) (wvc_PCLOSE F))).
{ pose proof (wv_wevk_split (wvc_st0 F) P (wvc_PCLOSE F) eq_refl HE_cap0) as E.
  rewrite WriterApp.putN_app in E. exact E. }
(* ---- put of the closing bracket ---- *)
eapply SRr_mono.
{ apply (HPUT ly S U W regsJ memJ mdJ chJ (wf_ot F) (wf_o F) (wvc_close (wf_ty F)) 1 buf
    (WriterApp.w_cap (wvc_stP F P)) (WriterApp.w_failed (wvc_stP F P)) (WriterApp.w_text (wvc_stP F P))
    (if wf_ty F =? 6 then [125] else [93]) (wf_live F + WriterApp.w_cap (wvc_stP F P) - wf_cap0 F) peak
    (WriterApp.w_cnt (wvc_stP F P)) (WriterApp.w_fail (wvc_stP F P)) HPREJ HHD).
  - rewrite Hfrs. cbn [app]. lia.
  - exact G10.
  - exact G11.
  - exact G12.
  - exact HOUT.
  - exact HG.
  - exact HU0.
  - rewrite Esp. lia.
  - exact HE_oot.
  - exact HE_ot16.
  - rewrite Etop. exact HE_top.
  - rewrite Esp. unfold raZ. rewrite R1.
    destruct HC as [(Eo & Hra) | (H16 & nfp & Hnfp & Hend)]; [left; split; [exact Eo | exact Hra] | right].
    split; [exact H16|]. exists (wf_ra8 F), nfp. split; [exact H8|]. split; [exact Hnfp | exact Hend].
  - intros a Ha. rewrite Esp in Ha.
    apply (fsw_apresent_unpoison B ly S U W memJ mdJ a HARU); [rewrite C3; lia|].
    apply HPRES. unfold wvc_STK. lia.
  - exact HZB.
  - right; right; right. exists (if wf_ty F =? 6 then [125] else [93]).
    split; [exact HIN | apply Nat.le_succ_diag_r].
  - destruct (wf_ty F =? 6); reflexivity.
  - exact HBOK.
  - split; lia.
  - left. lia.
  - pose proof (wv_room_mid (wvc_st0 F) P (wvc_PCLOSE F)) as RM. rewrite <- HWP in RM.
    assert (L1 : length (concat (wvc_PCLOSE F)) = 1%nat)
      by (unfold wvc_PCLOSE; destruct (wf_ty F =? 6); reflexivity).
    rewrite L1 in RM. change (WriterApp.w_text (wvc_st0 F)) with (wf_text0 F) in RM.
    unfold wvc_stP. lia.
  - exact (proj1 HBK).
  - lia.
  - pose proof HE_bud as HB. rewrite HWP in HB.
    pose proof (wv_budget_pre_mid S0 S (wf_cap0 F) (wf_cnt0 F) (wf_live F) (wf_failed0 F) (wf_text0 F) (wf_fail0 F)
      P (wvc_PCLOSE F) HE_cap0 HB Hnev (proj1 (proj2 HBK)) HCNT) as HM.
    replace (wf_live F + WriterApp.w_cap (wvc_stP F P) - wf_cap0 F)
      with (wf_live F - wf_cap0 F + WriterApp.w_cap (wvc_stP F P)) by lia.
    exact HM. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp). subst st'.
exists (WriterApp.putN (wvc_st0 F) (wvc_WP F)), buf', U'.
split; [reflexivity|].
split.
{ exact (wv_uswap_trans B ly S W (unpoison U memJ) mdJ U0 U U' (wf_buf0 F) buf buf' (wf_cap0 F)
    (WriterApp.w_cap (wvc_stP F P)) HARJ (proj1 (proj2 HARU)) HHD HB0 HE_cap0 Hcap0i HUS Hus). }
unfold wpost in Hwp |- *.
rewrite HE_sp, EST, ESP.
apply (wvc_tail_otJ B (wvc_STK F) (STK_put + (wf_ot F - spZ regsJ)) (wf_ot F) (wvc_FP F)
  (FS_PSTAT_FP ++ wbuf_fp buf (WriterApp.w_cap (wvc_stP F P))) ly0 S0 U0 W0 W mem0 md0 ly S U memJ mdJ regs0 regsJ
  (wevk (wf_cap0 F) (wvc_stP F P))
  (wevk (WriterApp.w_cap (wvc_stP F P)) (WriterApp.putN (wv_rst (wvc_stP F P)) (wvc_PCLOSE F))) U' _ W' c' HJ HARU).
- rewrite Esp. unfold wvc_STK. lia.
- exact R1.
- exact HP.
- exact (wv_fp_sub_swap B ly0 S0 ly S W (unpoison U memJ) mdJ (wf_buf0 F) (wf_cap0 F) buf
    (WriterApp.w_cap (wvc_stP F P)) HARJ HBS HBIN ltac:(lia) wvc_pstat_img).
- eapply (wv_fpostU_mono B); [exact Hwp|].
  intros ly' S' regs' mem' md' HJc OK' PO' HP' HQ.
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
  destruct (wvc_sem_call B F ly0 S0 U0 W0 mem0 regs0 ly S U W memJ mdJ buf (wvc_stP F P) (wvc_PCLOSE F)
    ly' S' U' W' mem' md' buf' (STK_put + (wf_ot F - spZ regsJ)) _ (spZ regsJ) peak
    HSEM HARU HE_cap0 Hcap0i HE_cnt0 Hcnt ltac:(lia) HE_oot Hpk HJc OK' PO' Hus Q1 Q2 Q3 Q4 ltac:(lia) Q5)
    as (_ & HSEM').
  destruct HSEM' as (HOUT' & HGL' & _ & _ & HBS' & HBK' & _ & HWK' & HN' & _).
  split; [exact HOUT'|]. split; [exact HBK'|]. split; [exact HBS'|]. split; [exact HWK'|].
  split; [exact HN' | exact HGL'].
Qed.

(* ---- the EMPTY container: at the open point with n = 0, image B jumps to 0x842c4 and TAIL-puts the closing
   bracket (the separator slot is written before the n test, so the run also splits on pretty) ---- *)
Lemma wvc_arm_empty : forall ly S U (W : world tfibsegs) ms mdc buf,
  wf_n F = 0 ->
  wvc_WP F = wvc_POPEN F ++ wvc_PCLOSE F ->
  wvc_invO B F ly0 S0 U0 W0 mem0 md0 regs0 W ms mdc ly S U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros ly S U W ms mdc buf Hn0 HWP HINV.
unfold wvc_invO in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R3 & R4 & Hsp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
assert (Hty : wf_ty F = 5 \/ wf_ty F = 6) by (destruct HE_ty as [(H & _) | (H & _)]; [left | right]; exact H).
eapply (wvc_seg_open_empty B) with (p := wf_p F) (spF := wf_sp F); [exact HAT | exact Hty | | | | | | |].
- rewrite fsw_ew_xatom. cbn [nth wvc_xs app]. rewrite Hn0. reflexivity.
- rewrite (ew_Ereg_nat _ _ 19 19%bv eq_refl). exact R19.
- lia.
- rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- intros ms' mdc' HJ' HARU' HFR R1' R2' R3' R4' R10' R11' R12' RSAV Ems.
  rewrite Ems.
  apply (wvc_close_put (wvc_POPEN F) ly S U W (ms_regs ms') (ms_mem ms') mdc' buf HWP HJ' HARU').
  + exact (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU' HFR
      ltac:(lia) ltac:(lia) ltac:(lia)).
  + intros j Hj.
    assert (Hn : nth_error wvc_saved j = Some (nth j wvc_saved 0%bv))
      by (apply nth_error_nth'; unfold wvc_saved; cbn [length]; lia).
    rewrite (RSAV j _ Hn). exact (wvr1_xs_saved _ _ _ _ _ _ _ _ _ j Hj).
  + exact R2'.
  + rewrite R3'. exact (eq_trans (ew_Ereg_nat _ _ 3 3%bv eq_refl) R3).
  + rewrite R4'. exact (eq_trans (ew_Ereg_nat _ _ 4 4%bv eq_refl) R4).
  + rewrite R10'. exact (eq_trans (ew_Ereg_nat _ _ 8 8%bv eq_refl) R8).
  + exact R11'.
  + exact R12'.
Qed.

(* ---- the NON-EMPTY container: at the close point (after the closing indent) the arm TAIL-puts the bracket ---- *)
Lemma wvc_arm_close : forall Pd ly S U (W : world tfibsegs) ms mdc buf,
  wvc_WP F = Pd ++ wvc_PCLOSE F ->
  wvc_invN B F ly0 S0 U0 W0 mem0 md0 regs0 Pd W ms mdc ly S U buf ->
  SRr tfibsegs W (mkCfg ms mdc)
    (wv_post B (wf_m F) (wf_ot F) (wf_o F) (wf_v F) (wf_p F) (wf_d F) (wf_t F) (wf_D F) (wf_UL F)
       (wf_buf0 F) (wf_cap0 F) (wf_failed0 F) (wf_text0 F) (wf_live F) (wf_peak0 F) (wf_cnt0 F) (wf_fail0 F)
       regs0 ly0 S0 U0 W0 mem0 md0).
Proof.
intros Pd ly S U W ms mdc buf HWP HINV.
unfold wvc_invN in HINV. cbv zeta in HINV.
destruct HINV as (HAT & HSEM & R8 & R9 & R19 & R3 & R4 & Hsp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (wvc_stk (wf_m F)) as (HSTKF & _).
assert (HWF : WVC_F = 192) by reflexivity.
pose proof (wvc_sem_o_sp B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) buf _ HSEM) as Hosp.
assert (Hty : wf_ty F = 5 \/ wf_ty F = 6) by (destruct HE_ty as [(H & _) | (H & _)]; [left | right]; exact H).
eapply (wvc_seg_closeN B) with (spF := wf_sp F); [exact HAT | exact Hty | | | | |].
- rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). exact Hsp.
- lia.
- unfold wvc_STK. lia.
- lia.
- intros ms' mdc' Ems HJ' HARU' HFR R1' R10' R11' R12' R2' R3' R4' RSAV.
  rewrite Ems.
  apply (wvc_close_put Pd ly S U W (ms_regs ms') (ms_mem ms') mdc' buf HWP HJ' HARU').
  + exact (wvc_sem_run B F ly0 S0 U0 W0 mem0 regs0 ly S U W (ms_mem ms) (ms_mem ms') mdc' buf _ HSEM HARU' HFR
      ltac:(lia) ltac:(lia) ltac:(lia)).
  + intros j Hj. rewrite (RSAV j Hj). exact (wvr1_xs_saved _ _ _ _ _ _ _ _ _ j Hj).
  + exact R2'.
  + rewrite R3'. exact (eq_trans (ew_Ereg_nat _ _ 3 3%bv eq_refl) R3).
  + rewrite R4'. exact (eq_trans (ew_Ereg_nat _ _ 4 4%bv eq_refl) R4).
  + rewrite R10'. exact (eq_trans (ew_Ereg_nat _ _ 8 8%bv eq_refl) R8).
  + exact R11'.
  + exact R12'.
Qed.

End St.
End A.
