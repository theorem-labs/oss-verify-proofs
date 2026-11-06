(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module names changed; 190 of its 221 lines of code are new or changed and 223 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the segment S_MF_EXIT of its walk, 57 instructions from the cut
   EXIT 0x86e70 to the `ret` 0x86f50 (the G2 walk owner's guide/MF-CUTS-A.md section 3 "Epilogue" and section 4). Lane
   the TAIL / EXIT segment lane of the G2 walk owner's G2. No call: the side-stack frame is released inline.

   What the code does, on the side-stack frame path (FB = FAKE = s8 <> 0; mf_core):
     0x86e70-0x86e7c  a0 = 0x45e0360e; a1 = 112(s1) = FB; FB + 0 = a0 (the retired-frame magic)
     0x86e80          `beqz s8` not taken (s8 = FB >= 4096)
     0x86e84-0x86ec4  the frame's 16 shadow bytes at s10 = shadow(FB) = 0xf5 (the bytes are marked unusable)
     0x86ec8-0x86ecc  a0 = 120(s8), the flag pointer in the frame's last word; the flag byte = 0 (the inline release;
                      kit astack_free_law / frame_flag_lawP through PaLibF.v aj_flag_store_pi, guide 2.6)
     0x86ed0          `j 0x86f14`
     0x86f14-0x86f4c  sp = s0 - 288; ra, s0 .. s11 loaded back from sp0 - 8 .. sp0 - 104; sp = sp0
     0x86f50          `ret`
   The post is apost_baseF at this segment's FP state through PaFx.v apost_baseF_of_base (no FP state change): the
   journal with the frame released (stack_free_state 1 pos), the callee-saved registers back, the mconf block
   unchanged by the epilogue (mf_tx_mconf, lib/A/Prog/m_file_k.v) and so holding mf_final v, and the frame
   form sa_noalloc (the layout kept, the state the entry's up to st_fs).
   Closed against G2 FINAL at 6f783602b5e3 (the image-A owner's contracts, round 5). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the shared list of the G2 walk owner's m_file walk (the m_file cut-statement lane, list (a)): the seed's listing objects, and the frame's
   inline release (the kit's model laws, astack_free_law, frame_flag_lawP; guide 2.6) *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* the contract's post at the return, from the state the epilogue leaves: the journal with the frame released,
   the callee-saved registers back, every byte outside mf_win as at the cut *)
Lemma mf_exit_post : forall v lyc Sc (Wc : world SEGS) memc mdc pos regs' mem' md',
mf_cx B v -> mf_ls v lyc Sc -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mf_final v) ->
ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [] lyc (stack_free_state 1 pos Sc) Wc mem' md' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a -> rdW Wc mem' a = rdW Wc memc a) ->
aregs_preserved (mv_regs v) regs' ->
MF_POST B v Wc (mkCfg (mkst regs' (getr (mv_regs v) 1) mem' (seg_rom SEGS)) md').
Proof.
intros v lyc Sc Wc memc mdc pos regs' mem' md' CX LS CORE HJ' K HP.
pose proof CORE as (_ & HPerm & _ & _ & _ & _ & Hmc & _).
unfold MF_POST. apply (apost_baseF_of_base SEGS). unfold apost_base.
exists lyc, (stack_free_state 1 pos Sc), regs', mem', md'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|]. split.
- exact (mf_tx_mconf B v lyc Sc Wc memc mdc mem' pos MF_LOW_OFF (mf_final v) (mf_final v) CX CORE K Hmc).
- split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPerm|].
  destruct LS as (Ely & fS & ES). split; [exact Ely|].
  exists (st_fs (stack_free_state 1 pos Sc)). rewrite ES. reflexivity.
Qed.

(* the state's form, computed *)
Ltac mfx_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* S_MF_EXIT at one FP state *)
Lemma mf_exit_at : MF_EXIT_stmt B.
Proof.
unfold MF_EXIT_stmt. intros v lyc Sc Wc regs1 memc mdc pos CX LS CORE RA R24.
pose proof pa_segs_low as Hsegs.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (al_frames SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & _ & HFSpres).
destruct (FFL _ _ _ _ _ 1 pos HAR Hin) as (HFLp & _ & _ & HFL4096 & _ & _).
change (fs_frame_bytes 1 / 8) with 16 in HFSpres.
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof CX as (HPRE & _). pose proof HPRE as (_ & Hra & _ & Hgp & Htp & _).
pose proof (mf_regs_base_of_ex B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
(* the flag cell is the runtime's: outside the frame and its shadow *)
assert (SF1 : flag_addr lyc 1 pos + 1 <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= flag_addr lyc 1 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (frame_addr lyc 1 pos)) as [h | h]; [left; lia|].
  destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (frame_addr lyc 1 pos + 128)) as [h' | h']; [|right; lia].
  exfalso. exact (F4 _ (conj h h') F5). }
assert (SS1 : flag_addr lyc 1 pos + 1 <= SHADOW_OFF + frame_addr lyc 1 pos / 8 \/
  SHADOW_OFF + frame_addr lyc 1 pos / 8 + 16 <= flag_addr lyc 1 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (SHADOW_OFF + frame_addr lyc 1 pos / 8)) as [h | h]; [left; lia|].
  destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 16)) as [h' | h']; [|right; lia].
  exfalso. destruct (HFSpres (flag_addr lyc 1 pos - (SHADOW_OFF + frame_addr lyc 1 pos / 8)) ltac:(lia)) as [_ Hno].
  apply Hno. unfold shadow_addr. replace (SHADOW_OFF + frame_addr lyc 1 pos / 8 +
    (flag_addr lyc 1 pos - (SHADOW_OFF + frame_addr lyc 1 pos / 8))) with (flag_addr lyc 1 pos) by lia. exact F5. }
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (mf_final v) None 0 [] MF_EXIT false false [] true
  false [] true CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia) ltac:(intros Hf; discriminate Hf)
  ltac:(lia) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos None 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos None 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 3%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E34, E35, E36.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = flag_addr lyc 1 pos) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the spill slots read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. mfx_norm HS1.
(* s8 = FB (atom 34), s10 = shadow(FB) (atom 36) *)
apply (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff 34 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E34; cbn [ms_regs restrict mkst];
     rewrite R24; reflexivity].
mfx_norm HS1.
apply (ast_ok_pi_set_reg_fp E _ _ (26%bv : bv 5) (SOff 36 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E36; cbn [ms_regs restrict mkst];
     rewrite R26; reflexivity].
mfx_norm HS1.
(* the flag cell, written by the release *)
assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 35%nat) 0 1 0 1 []) HS1 ltac:(vm_compute; reflexivity)).
clear HS1.
lapply HS2; clear HS2; [intros HS2|].
2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U35. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (flag_addr lyc 1 pos + o) with (flag_addr lyc 1 pos) by lia. cbn [restrict ms_mem mkst].
    apply (apresent_writable SEGS). exact HFLp. }
lapply HS2; clear HS2; [intros HS2|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U35, ?U2, ?U8, ?U34, ?U36.
    unfold mf_s1, SHADOW_OFF in *. repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
unfold mf_at.
(* the release and the return, one plain run to the `ret` *)
paj_run_flag_sh RUNF HS2 HJ.
- lia.
- intros a (r & Hr & Ha).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
  cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U34, ?U35, ?U36 in Ha;
    first [ exfalso; lia
    | right; lia
    | left; right; right; right; left; exists 1, pos; split; [left; reflexivity|];
      first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
            | right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; lia ] ] |]);
  destruct Hr.
- intros msr HSr. unfold st_ok_pi in HSr.
  pose proof (st_ok_mem_ok SEGS E _ msr HSr) as (_ & HOK & _).
  unfold abs_ss, setpc in HOK. cbn [ss_mem] in HOK.
  apply Forall_inv in HOK. destruct HOK as (_ & _ & _ & HC). apply Forall_inv in HC.
  destruct (HC 0 ltac:(split; [lia | cbv; reflexivity])) as (b & Hb1 & Hb2).
  cbn [base_val YP09.r_base YP09.c_off] in Hb2. rewrite U35 in Hb2.
  replace (flag_addr lyc 1 pos + 0 + 0) with (flag_addr lyc 1 pos) in Hb2 by lia. rewrite Hb2.
  cbn [YP09.cbyte YP09.c_val sv_denot] in Hb1. injection Hb1 as <-. vm_compute. reflexivity.
- lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
      rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc)
        (mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)) HFr _ a Ha HnW);
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U34, ?U35, ?U36 in Hr; unfold mf_win; lia |]);
      destruct Hinw | ] end.
  assert (E39 : ew E 39 = getr (mv_regs v) (1%bv : bv 5))
    by (change 39%nat with (32 + 7)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
  prreg HS2 (1%bv : bv 5) Q1.
  eapply (RET Wc _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbn [ms_regs ms_mem].
  unfold YK0s.ret_ok in Hra. rewrite Q1, E39, Hra.
  apply (mf_exit_post v lyc Sc Wc memc mdc pos _ _ _ CX LS CORE).
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
  + exact K.
  + unfold aregs_preserved. intros r Hr.
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
    clear Hr.
    repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
    (rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS2); cbn [ms_regs];
     lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
       let e := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with e end;
     cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned).
    all: try (lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
      let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite (EX j) by (unfold A_TEXT; lia);
      reflexivity end).
    all: first
    [ rewrite (EE 8%nat 8%bv eq_refl), R8; replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity);
      unfold w64, mv_sp, spZ; apply Z_to_bv_bv_unsigned
    | rewrite (EE 3%nat 3%bv eq_refl), R3; replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite Hgp; reflexivity
    | rewrite (EE 4%nat 4%bv eq_refl), R4; replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite Htp; reflexivity ].
Qed.
End e.
End f.
End d.

(* the segment at every FP state (m_file_m.v's S_MF_EXIT = MF_EXIT_F) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma s_mf_exit : S_MF_EXIT B.
Proof. intros fx0. exact (mf_exit_at (fx := fx0) B VOBJS ML ASF FFL). Qed.
(* inside the Sections: the segment's hypotheses as its assumptions *)
About s_mf_exit. Print Assumptions s_mf_exit.
End i.
End h.
End g.
About s_mf_exit. Print Assumptions s_mf_exit.
