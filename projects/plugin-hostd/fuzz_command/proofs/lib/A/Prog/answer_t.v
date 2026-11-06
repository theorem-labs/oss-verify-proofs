(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the JOIN segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a734
   .. 0x8a7bc): the call of hand_back on the frame's buffer, the shadow fill of the buffer, the retire word of the
   frame, the release of the class-7 frame and the epilogue, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/
   ACh2.v (cl_AFT2_okX: a seed over the saved registers, a program call through cl_callS, the frame's regions kept
   over it, and the return through paj_ret_at). The cut statement is lib/A/Prog/answer_s1.v's AN_JOIN_stmt. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
mix_call_c hand_back_c answer_c answer_s0 answer_s1 answer_t1.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
(* lia without the Euclidean-division equations: the flag value these proofs were checked with, which PaDenot.v
   gave them until an earlier commit made its redefinition Local *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ---- the symbolic state of the segment: the prologue's slots (read-only, one atom per saved register) and the
   frame's first word (the retire store's target) ---- *)
Definition at_extra (regs : bvmap 5 word) : list word := map (fun r => getr regs (Z_to_bv 5 r)) an_saved.
Definition at_slots : list YP09.chunk :=
map (fun j => YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13).
Definition at_R0 : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 at_slots.
Definition at_R1 : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [].
Definition at_regions : smem := [at_R0; at_R1].
Definition at_facts : facts := mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (25%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition at_Bx : sv := SOff 26 0.
(* the segment makes no inline check (no token), so the shadow span only has to miss the frame word's window *)
Definition at_Bspan : Z * Z := (2 ^ 63, 2 ^ 63).
Definition at_SH : list shent := [].
Definition at_ss : sstate := mkSS AN_JOIN sr_atoms at_regions None at_facts.
Definition at_E (regs1 regs : bvmap 5 word) : env := Eimg (Ereg regs1 (at_extra regs)).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is fixed (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's own hypotheses (answer_c.v:73-78) that this segment uses, word for word *)
Hypothesis THAND_BACK : forall fx0 : YK11.FPState, @thand_back_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_FREE7 : forall fx0 : YK11.FPState, @astack_free_realizes fx0 rc SEGS B (SIG CS___asan_stack_free_7) 7.
Hypothesis ASET_SHADOWF8 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG CS___asan_set_shadow_f8) 0xf8.
(* the per-binary walk facts, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
(* the image facts (CmdRecBase.v's cmd_img_facts); the record facts below are IMG's field and the CmdRecFacts.v
   lemmas, by exact *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img := cif_prog_img _ _ IMG.
Let RRO := RRO SEGS B LAWS HB IMG.
Let RPG := RPG SEGS B LAWS HB IMG.

Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* the seed: the symbolic state of the segment holds at the cut point *)
Lemma at_seed : forall (W : world SEGS) (regs regs1 : bvmap 5 word) (mem : word -> option byte) lya ly S md pos sp1,
AR SEGS B ly S W mem md ->
In (7, pos) (frames S) ->
astk_ok ANSWER_STK lya (spZ regs) ->
an_saved_ok (aview SEGS (w_H W) mem) (spZ regs) regs ->
an_regs_body B regs regs1 sp1 (frame_addr ly 7 pos) ->
st_ok_pi SEGS VAL (at_E regs1 regs) at_ss
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + AN_JOIN)) mem (seg_rom SEGS)))
/\ sh_ok SEGS at_Bx at_SH (at_E regs1 regs) (mrestrict (w_H W) mem).
Proof.
intros W regs regs1 mem lya ly S md pos sp1 HAR Hin Hstk HSAV HRG.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HRG as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R25 & R20 & R21 & R22 & R23 & R24 & R26).
assert (HFB : fs_frame_bytes 7 = 8192) by (vm_compute; reflexivity).
assert (HAS : 12288 <= ANSWER_STK <= 2 ^ 30) by (split; vm_compute; discriminate).
destruct (al_frames SEGS B LAWS ly S W mem md 7 pos HAR Hin) as (Hf32 & Happ & Hfpres & _).
destruct (frames_bounds SEGS B LAWS ly S W mem md 7 pos HAR Hin) as (Hf4096 & Hfceil & _).
rewrite HFB in Hfceil.
rewrite restrict_mkst_fx.
assert (HEI : img_env VAL A_LIM (at_E regs1 regs)) by (unfold at_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (at_E regs1 regs) n = getr regs1 r).
{ intros n r Hn. unfold at_E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 13)%nat -> ew (at_E regs1 regs) (32 + j) = nth j (at_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold at_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E8 : bv_unsigned (ew (at_E regs1 regs) 8) = spZ regs)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (E25 : bv_unsigned (ew (at_E regs1 regs) 25) = frame_addr ly 7 pos)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
split; [|unfold sh_ok, at_SH; apply Forall_nil].
unfold at_ss, at_regions. apply pa_entry_st_ok_full.
- unfold at_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold at_R0, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    lazymatch goal with |- Forall ?P ?l => let l2 := eval vm_compute in l in change (Forall P l2) end.
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
      let j := eval compute in (n - 32)%nat in
      apply (chunk_ok_val SEGS (at_E regs1 regs) _ (spZ regs) off 8 (SOff n 0)
               (bv_unsigned (ew (at_E regs1 regs) n)));
      [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | let HR := fresh "HR" in pose proof (bv_unsigned_in_range 64 (ew (at_E regs1 regs) n)) as HR;
        change (bv_modulus 64) with (2 ^ 64) in HR; zside
      | zside
      | replace (spZ regs + off) with (spZ regs - 8 - 8 * Z.of_nat j) by lia;
        change (ew (at_E regs1 regs) n) with (ew (at_E regs1 regs) (32 + j)%nat);
        rewrite (EX j ltac:(cbv; lia)); cbn [at_extra an_saved map nth];
        cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add];
        apply at_val_mem_of_aval; exact (HSAV j _ eq_refl) ] end.
  + unfold at_R1, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hfpres. lia.
- apply pairwise_disjoint_of_extents. unfold at_R0, at_R1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, E25.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold facts_ok, at_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E8, E25. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  repeat split; first [exact Hal16 | exact Hf32 | lia | exact I].
Qed.

(* the write set of a run of this segment: the prologue's slots are read-only and the frame's first word is a byte
   of the frame the walk holds *)
Local Ltac at_awr U25h HFEQ HFBh POS :=
let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
intros a (r & Hr & Ha); simpl in Hr;
destruct Hr as [Hr | [Hr | []]]; subst r;
cbn [at_R0 at_R1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
first
[ lia
| rewrite U25h in Ha; right; right; right; left; exists 7, POS; split; [left; reflexivity|];
  left; unfold in_zr; cbn [fst snd]; try rewrite HFEQ; rewrite HFBh; lia ].

Local Ltac at_awr0 :=
let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Ha := fresh "Ha" in
intros a (r & Hr & Ha); simpl in Hr;
destruct Hr as [Hr | []]; subst r;
cbn [at_R0 at_R1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia.

Lemma an_join_ok : AN_JOIN_stmt B MT.
Proof.
unfold AN_JOIN_stmt.
intros ly S W regs mem md ch c sh old e x chg R O lyc Sc Wc regs1 memc mdc pos sp1 HPRE HMID HRG R27 HBUF.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as [HAC1 HAC2].
assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 7 = 8192) by (vm_compute; reflexivity).
assert (HAS : 12288 <= ANSWER_STK <= 2 ^ 30) by (split; vm_compute; discriminate).
assert (HHB : 0 <= HAND_BACK_STK /\ HAND_BACK_STK + 144 <= ANSWER_STK)
  by (split; vm_compute; discriminate).
assert (HE2 : ESTACK + 144 <= ANSWER_STK) by (vm_compute; discriminate).
pose proof HPRE as (HFN & Hfr8 & HROD & HROK & H10 & H11 & H12 & HREP0 & HOLD0 & HSHP & HCALL & HEV & HLIVE & HMO &
  Hcr & Hshr & Holdr).
pose proof HFN as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMID as (HJ & HMLE & HPERM & Hsp1 & HSAV & HFLAG & HZS & HREP & HOLD).
pose proof HRG as (Rsp & Rgp & Rtp & R8 & R9 & R18 & R25 & R20 & R21 & R22 & R23 & R24 & R26).
pose proof HJ as (HAR & HLY & HSECS & HWLE & HIO & HFRS & HNEV & HK0 & JHI & JBLK & JIMG & JFRM & JGONE & JPRES & JSTK & JEXT & JQT).
assert (Hinf : In (7, pos) (frames Sc)) by (rewrite HFRS; left; reflexivity).
destruct (al_frames SEGS B LAWS lyc Sc Wc memc mdc 7 pos HAR Hinf) as (Hf32 & Happ & Hfpres & Hfshpres).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 7 pos HAR Hinf) as (Hf4096 & Hfceil & _).
rewrite HFB in Hfceil, Happ, Hfshpres.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
assert (HFni : forall y, frame_addr lyc 7 pos <= y < frame_addr lyc 7 pos + 8192 -> ~ in_img SEGS y).
{ intros y Hy. apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 7 pos y HAR Hinf). rewrite HFB. exact Hy. }
assert (HGRp : forall y, A_G_REC <= y < A_G_REC + REC_SIZE -> in_img SEGS y).
{ intros y Hy. apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
  split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hy; lia]. }
assert (HSPp : forall y, A_REC_SPILL <= y < A_REC_SPILL + SC_SIZE -> in_img SEGS y).
{ intros y Hy. apply cif_prog_img. exists (A_REC_SPILL, A_REC_SPILL + 56).
  split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hy; lia]. }
(* the realigned stack pointer *)
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hs1a & Hs1b & Hs1c).
rewrite <- Hsp1 in Hs1a, Hs1b, Hs1c.
assert (Hsplo : spZ regs - 144 <= sp1 <= spZ regs - 128) by lia.
(* the shadow of the frame *)
pose proof (shadow_addr_bounds (frame_addr lyc 7 pos) ltac:(lia)) as Hsb1.
pose proof (shadow_addr_bounds (frame_addr lyc 7 pos + 8192) ltac:(lia)) as Hsb2.
pose proof (shadow_range_end (frame_addr lyc 7 pos) 8192 ltac:(lia)) as Hse. try change (8192 / 8) with 1024 in Hse.
pose proof (shadow_mono (frame_addr lyc 7 pos) (frame_addr lyc 7 pos + 8192) ltac:(lia)) as Hsm.
assert (HshF : forall a, shadow_addr (frame_addr lyc 7 pos) <= a < shadow_addr (frame_addr lyc 7 pos) + 1024 ->
  ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)).
{ intros a Ha Hf. unfold shadow_addr, SHADOW_OFF in Ha.
  exact (fshadow_not_app (frame_addr lyc 7 pos) 1024 (frame_addr lyc 7 pos) 8192 a ltac:(lia) ltac:(lia) Happ Ha Hf). }
(* buf's shadow (the range __asan_set_shadow_f8 fills) misses the frame *)
assert (HnSh : forall a, frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192 ->
  ~ (shadow_addr (frame_addr lyc 7 pos) + 4 <= a < shadow_addr (frame_addr lyc 7 pos) + 4 + 512)).
{ intros a Ha Hs. exact (HshF a ltac:(lia) Ha). }
(* the recorder's blocks *)
assert (HOblk : forall pn, In pn O -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (at_rec_repA_O_blocks B lyc Sc _ _ _ pn HREP Hpn)).
assert (HFPblk : forall a, inFP (ablocks_fp (filter (fun pn => fst pn =? old) O)) a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. apply inFP_ablocks_fp_inv in Ha as (p & n & Hin & Hr). apply at_filter_in in Hin.
  destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HAR (HOblk (p, n) Hin)) as (_ & H4096 & Hcl & _). lia. }
assert (HSINK : ~ YI16.sink_open_fp (an_FP old O)).
{ unfold an_FP. apply sink_closed_cons; [cbn; unfold A_G_REC, OFF_ANSWER; lia|].
  apply sink_closed_cons; [cbn; unfold A_G_REC, OFF_STATE; lia|].
  apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hin. cbn [fst].
  apply at_filter_in in Hin.
  destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HAR (HOblk (p, n) Hin)) as (_ & H4096 & _). lia. }
assert (HnFProd : forall a, in_roP SEGS RLO RHI a -> ~ inFP (an_FP old O) a).
{ intros a Hro Hfp. unfold an_FP in Hfp. apply inFP_cons in Hfp as [Hr1 | Hfp].
  - apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960).
    split; [left; reflexivity|]. cbn [fst snd]. unfold OFF_ANSWER in Hr1. lia.
  - apply inFP_cons in Hfp as [Hr2 | Hfp].
    + apply (RPG a); [|exact Hro]. exists (A_G_REC, A_G_REC + 960).
      split; [left; reflexivity|]. cbn [fst snd]. unfold OFF_STATE in Hr2. lia.
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr). apply at_filter_in in Hin.
      apply (blk_img SEGS B LAWS lyc Sc Wc memc mdc p n a HAR (HOblk (p, n) Hin) Hr).
      destruct Hro as [(sg & Hs & _ & Hrr) | Hgot]; [exists sg; auto | exact (RRO a Hgot)]. }
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc memc)).
{ intros a Hro Ho He. rewrite (JIMG a); [exact (HROD a Hro Ho He) | | exact Ho | exact He |].
  - destruct Hro as [(sg & Hs & _ & Hrr) | Hgot]; [exists sg; auto | exact (RRO a Hgot)].
  - apply fp_spares_closed; [exact HSINK | exact (HnFProd a Hro)]. }
(* the answer text and its length *)
pose proof (at_rep_code B ly S _ _ _ HREP0) as Hcode.
assert (Htlen : Z.of_nat (length (snd (rec_answer R e x chg))) + 1 <= 4096).
{ unfold rec_answer. destruct (Z.eqb_spec (r_refuse R) 0) as [Hr0 | Hr0].
  - destruct (HSHP Hr0) as [_ Hfits]. unfold hand_back. cbn [snd].
    unfold fits, PHD_LINE_MAX in Hfits. lia.
  - unfold hand_back. cbn [snd]. pose proof (resp_length (r_code R) Hcode) as Hl. lia. }
assert (HtLMAX : Z.of_nat (length (snd (rec_answer R e x chg))) <= LMAX) by (unfold LMAX; lia).
(* the seed *)
destruct (at_seed Wc regs regs1 memc ly lyc Sc mdc pos sp1 HAR Hinf Hstk HSAV HRG) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (at_E regs1 regs)) by (unfold at_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (at_E regs1 regs) n = getr regs1 r).
{ intros n r Hn. unfold at_E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 13)%nat -> ew (at_E regs1 regs) (32 + j) = nth j (at_extra regs) (Z_to_bv 64 0)).
{ intros j Hj. unfold at_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (EXs : forall j m, (j < 13)%nat -> m = (32 + j)%nat -> ew (at_E regs1 regs) m = nth j (at_extra regs) (Z_to_bv 64 0))
  by (intros j m Hj ->; exact (EX j Hj)).
assert (Usp : bv_unsigned (ew (at_E regs1 regs) 8) = spZ regs)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew (at_E regs1 regs) 25) = frame_addr lyc 7 pos)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (at_E regs1 regs) 18) = frame_addr lyc 7 pos)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; lia).
set (E := at_E regs1 regs) in *.
(* 0x8a734 .. 0x8a738: a0 := buf, then the call of hand_back *)
paj_run_tok RUN HS HJ SHOK at_Bspan.
{ at_awr U25 (eq_refl : frame_addr lyc 7 pos = frame_addr lyc 7 pos) HFB pos. }
set (mdv1 := with_vm_backing _ _ _) in *; clearbody mdv1.
pmkst HS.
assert (HSIGHB : SIG CS_hand_back = BASE + AF_hand_back).
{ rewrite (SIGP CS_hand_back ltac:(cbn [In]; repeat first [left; reflexivity | right])).
  f_equal; try (vm_compute; reflexivity). }
rewrite HSIGHB.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (25%bv : bv 5) P25.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) ->
  rdW Wc (ms_mem ms) a = rdW Wc memc a)
by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
      (fun a => frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U25 in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Hsp' : spZ rg = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite P2, (EE 2%nat 2%bv eq_refl), Rsp; rewrite unsigned_lit_small by lia; lia);
assert (P3' : getr rg 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact Rgp);
assert (P4' : getr rg 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact Rtp);
assert (P10' : getr rg 10 = w64 (frame_addr lyc 7 pos + 32))
  by (rewrite P10, (EE 21%nat 21%bv eq_refl); exact R21);
assert (Hs0 : s0Z rg = spZ regs)
  by (unfold s0Z; rewrite P8, (EE 8%nat 8%bv eq_refl), R8; apply unsigned_lit_small; lia) end.
(* the frame chain at the call *)
assert (HCH : exists ch1, achain lyc (rdW Wc (ms_mem ms)) sp1 (spZ regs) ch1).
{ destruct (Z_lt_ge_dec (spZ regs) (ly_top lyc - 16)) as [Hlt | Hge].
  - pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
    assert (A1 : achain lyc (rdW W mem) (spZ regs) (s0Z regs) ch) by (eapply achain_ly_top; [exact Etop | exact Hch]).
    assert (A2 : ly_top lyc <= 2 ^ 64) by (rewrite Etop; lia).
    assert (A3 : forall a, spZ regs <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW W mem a).
    { intros a Ha. rewrite (KEEP1 a ltac:(lia) ltac:(lia)).
      apply JHI; [lia | lia |]. intros Hfp. unfold an_FP in Hfp.
      apply inFP_cons in Hfp as [Hr1 | Hfp]; [unfold A_G_REC, OFF_ANSWER in Hr1; lia|].
      apply inFP_cons in Hfp as [Hr2 | Hfp]; [unfold A_G_REC, OFF_STATE in Hr2; lia|].
      pose proof (HFPblk a Hfp). lia. }
    assert (A4 : rdword (rdW Wc (ms_mem ms)) (spZ regs - 8) = Some (raZ regs)).
    { apply (at_rdword_of_aval (w_H Wc) (ms_mem ms)); [|unfold raZ; apply bv_unsigned_in_range].
      eapply (at_aval_rng (rdW Wc memc) (rdW Wc (ms_mem ms)) (spZ regs - 144) (spZ regs));
        [intros y Hy; apply (KEEP1 y ltac:(lia) ltac:(lia)) | lia | cbn; lia |].
      replace (spZ regs - 8) with (spZ regs - 8 - 8 * Z.of_nat 0) by lia.
      exact (HSAV 0%nat 1 eq_refl). }
    assert (A5 : rdword (rdW Wc (ms_mem ms)) (spZ regs - 16) = Some (s0Z regs)).
    { apply (at_rdword_of_aval (w_H Wc) (ms_mem ms)); [|unfold s0Z; apply bv_unsigned_in_range].
      eapply (at_aval_rng (rdW Wc memc) (rdW Wc (ms_mem ms)) (spZ regs - 144) (spZ regs));
        [intros y Hy; apply (KEEP1 y ltac:(lia) ltac:(lia)) | lia | cbn; lia |].
      replace (spZ regs - 16) with (spZ regs - 8 - 8 * Z.of_nat 1) by lia.
      exact (HSAV 1%nat 8 eq_refl). }
    assert (A8 : spZ regs mod 8 = 0).
    { replace (spZ regs) with ((2 * (spZ regs / 16)) * 8) by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia).
      apply Z_mod_mult. }
    exists ((spZ regs, raZ regs, s0Z regs) :: ch).
    exact (achain_push lyc (rdW W mem) (rdW Wc (ms_mem ms)) (spZ regs) (s0Z regs) (raZ regs) ch sp1
             A1 A2 A3 A4 A5 Hra4 ltac:(lia) A8 Hlt ltac:(lia)).
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCH as (ch1 & HCH).
(* the premises of hand_back at the call *)
assert (HREPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) (an_R1 R e chg) O).
{ eapply (at_rec_repA_kept B lyc Sc lyc Sc (rdW Wc memc)); [exact HREP | | | | intros pn Hpn; exact Hpn].
  - intros y Hy. apply (KEEP1 y); [unfold A_G_REC, REC_SIZE in Hy; lia | intros Hf; exact (HFni y ltac:(lia) (HGRp y Hy))].
  - intros y Hy. apply (KEEP1 y); [unfold A_REC_SPILL, SC_SIZE in Hy; lia | intros Hf; exact (HFni y ltac:(lia) (HSPp y Hy))].
  - intros p n y Hin Hy.
    destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HAR Hin) as (_ & H4096 & Hcl & _).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 7 pos HAR Hin Hinf) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd.
    apply (KEEP1 y); lia. }
assert (HOLDc : aval_mem (rdW Wc (ms_mem ms)) (A_G_REC + OFF_ANSWER) 8 old).
{ eapply (at_aval_rng (rdW Wc memc) (rdW Wc (ms_mem ms)) A_G_REC (A_G_REC + REC_SIZE));
    [intros y Hy; apply (KEEP1 y); [unfold A_G_REC, REC_SIZE in Hy; lia | intros Hf; exact (HFni y ltac:(lia) (HGRp y Hy))]
     | unfold OFF_ANSWER; lia | unfold OFF_ANSWER, REC_SIZE; cbn; lia | exact HOLD]. }
assert (HBUFc : astr_atR (rdW Wc (ms_mem ms)) (frame_addr lyc 7 pos + 32) (snd (rec_answer R e x chg))).
{ eapply (at_str_rng (rdW Wc memc) (rdW Wc (ms_mem ms)) (frame_addr lyc 7 pos + 32)
            (frame_addr lyc 7 pos + 8192));
    [intros y Hy; apply (KEEP1 y); lia | lia | lia | exact HBUF]. }
assert (HRODcc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms))).
{ intros a Hro Ho He. rewrite (KEEP1 a).
  - exact (HRODc a Hro Ho He).
  - destruct Hro as [(sg & Hs & _ & Hrr) | Hgot];
      [pose proof (pa_img_range a ltac:(exists sg; auto)) | pose proof (pa_img_range a (RRO a Hgot))]; lia.
  - intros Hbad. apply (HFni a ltac:(lia)).
    destruct Hro as [(sg & Hs & _ & Hrr) | Hgot]; [exists sg; auto | exact (RRO a Hgot)]. }
assert (HFOBJ : afobj SEGS B lyc Sc Wc (ms_mem ms) (frame_addr lyc 7 pos + 32)
                  (Z.of_nat (length (snd (rec_answer R e x chg))) + 1)).
{ split; [exists 7, pos; split; [exact Hinf|]; split; [lia|]; split; [|rewrite HFB; lia]|].
  - replace (frame_addr lyc 7 pos) with ((4 * (frame_addr lyc 7 pos / 32)) * 8) by (pose proof (Z.div_mod (frame_addr lyc 7 pos) 32 ltac:(lia)); lia). apply Z_mod_mult.
  - split.
    + replace (frame_addr lyc 7 pos + 32) with ((4 * (frame_addr lyc 7 pos / 32) + 4) * 8) by (pose proof (Z.div_mod (frame_addr lyc 7 pos) 32 ltac:(lia)); lia).
      apply Z_mod_mult.
    + apply (at_ra_kept (rdW Wc memc)).
      * eapply (at_range_addressable_le _ _ _ 4096); [lia|].
        apply (zero_shadow_range (rdW Wc memc) SHADOW_OFF (frame_addr lyc 7 pos + 32) 4096);
          [replace (frame_addr lyc 7 pos + 32) with ((4 * (frame_addr lyc 7 pos / 32) + 4) * 8)
             by (pose proof (Z.div_mod (frame_addr lyc 7 pos) 32 ltac:(lia)); lia);
           apply Z_mod_mult | reflexivity | exact HZS].
      * intros y Hy. change (shadow_of_addr SHADOW_OFF y) with (shadow_addr y).
        pose proof (shadow_addr_bounds y ltac:(lia)) as Hsy.
        apply (KEEP1 (shadow_addr y)); lia. }
assert (HEVc : st_nev Sc + EV_HAND_BACK <= EV_MAX) by (unfold EV_ANSWER in HEV; lia).
assert (HLIVEc : blocks_bytes Sc + LIVE_HAND_BACK (snd (rec_answer R e x chg)) <= LIVE_MAX).
{ rewrite (at_blocks_bytes_perm B ly S lyc Sc HPERM). unfold LIVE_ANSWER in HLIVE. exact HLIVE. }
assert (HMOc : mo_ok MT Sc (XM_HAND_BACK MT (snd (rec_answer R e x chg)))).
{ eapply (mo_ok_step MT MTL S Sc 0); [|exact HMLE].
  replace (0 + XM_HAND_BACK MT (snd (rec_answer R e x chg)))
    with (XM_ANSWER MT (snd (rec_answer R e x chg))) by (unfold XM_ANSWER; lia). exact HMO. }
assert (HSRc : 0 <= frame_addr lyc 7 pos + 32 < 2 ^ 64) by lia.
(* the call *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  eapply (cl_callS_wide B LAWS Wc rg mm _ ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)]
            lyc Sc mdq 0 HAND_BACK_STK _ EV_HAND_BACK (sp1 - spZ regs)
            (getr rg 1) ch1 _ HJ) end.
  - exact Hsp'.
  - rewrite Zminus_mod, Hal16, Hs1c. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact P3'.
  - exact P4'.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - replace (spZ regs + (sp1 - spZ regs)) with sp1 by lia. rewrite Hs0. exact HCH.
  - intros HPRE1.
    apply (THAND_BACK fx lyc Sc Wc _ _ _ _ (frame_addr lyc 7 pos + 32) old
             (snd (rec_answer R e x chg)) (an_R1 R e chg) O HPRE1 HRODcc P10' HSRc HBUFc HtLMAX HFOBJ
             HREPc HOLDc Holdr HEVc HLIVEc HMOc).
  - intros a Hfp. unfold hand_back_c.thand_back_spec in THAND_BACK.
    apply inFP_cons in Hfp as [Hr1 | Hfp].
    + right. right. right. right. left.
      split; [exists (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8); split; [left; reflexivity | cbn; lia]|].
      split.
      * apply (HPROG B HB). exists (A_G_REC, A_G_REC + 960).
        split; [left; reflexivity | cbn [fst snd]; unfold OFF_ANSWER in Hr1; lia].
      * apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
        split; [left; reflexivity | cbn [fst snd]; unfold OFF_ANSWER in Hr1; lia].
    + apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr). pose proof Hin as Heq0; apply at_filter_in in Hin.
      right. left. split; [|exists p, n; split; [exact (HOblk (p, n) Hin) | exact Hr]].
      unfold an_FP. apply inFP_cons. right. apply inFP_cons. right.
      replace a with (p + (a - p)) by lia.
      eapply (inFP_ablocks_fp _ p n (a - p)); [exact Heq0|].
      split; [lia|]. lia.
  - intros ly2 S2 W2 regs2 mem2 md2 HK a Hfp Hw Hn.
    exfalso. apply inFP_cons in Hfp as [Hr1 | Hfp].
    + unfold A_G_REC, OFF_ANSWER in Hr1. lia.
    + pose proof (HFPblk a Hfp). lia. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
rewrite P1.
cbv zeta in HK3.
destruct HK3 as (p1 & p2 & O' & HQ10 & Hp24 & Hp12 & Hfresh & HBLKS & HREP3 & HO' & HSTR3 & HBB3 & HMLE3).
pose proof HJc3 as (HAR3 & HLY3 & _ & _ & _ & HFRS3 & HNEV3 & _ & K1 & K2 & K3 & K4 & KG & KP & _ & _ & _).
destruct (al_layout SEGS B LAWS lyc Sc Wc memc mdc ly3 HAR HLY3) as (HABeq & HFAeq & HOWeq).
assert (Hinf3 : In (7, pos) (frames S3)) by (rewrite HFRS3; exact Hinf).
assert (HFA3 : frame_addr ly3 7 pos = frame_addr lyc 7 pos) by (apply HFAeq).
destruct (al_frames SEGS B LAWS ly3 S3 W3 mem3 md3 7 pos HAR3 Hinf3) as (Hf32' & Happ' & Hfpres' & Hfshpres').
rewrite HFB, HFA3 in Hfpres', Hfshpres', Happ'.
(* the bytes the inner call kept: outside its footprint *)
assert (HFP1lo : forall a, inFP ((A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8)
                   :: ablocks_fp (filter (fun pn => fst pn =? old) O)) a -> 4096 <= a < alloc_ceiling).
{ intros a Hfp. apply inFP_cons in Hfp as [Hr1 | Hfp];
    [unfold A_G_REC, OFF_ANSWER in Hr1; lia | exact (HFPblk a Hfp)]. }
assert (KEEPC : forall a, frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192 ->
  rdW W3 mem3 a = rdW Wc (ms_mem ms) a).
{ intros a Ha. apply (K4 7 pos a Hinf); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite HFB; lia|].
  intros Hfp. apply inFP_cons in Hfp as [Hr1 | Hfp];
    [apply (HFni a ltac:(lia)); apply HGRp; unfold OFF_ANSWER, REC_SIZE in *; lia|].
  apply inFP_ablocks_fp_inv in Hfp as (p & n & Hin & Hr). apply at_filter_in in Hin.
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 7 pos HAR (HOblk (p, n) Hin) Hinf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB in Hd.
  destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HAR (HOblk (p, n) Hin)) as (_ & _ & _ & _ & _ & _ & _).
  lia. }
(* back at 0x8a73c: the state of the walk after the call *)
jafter_call_keep_pi HS 48%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - eapply (region_kept_stack_sub SEGS B);
      [exact HJc3 | exact HJ3 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia |].
    intros a Ha Hfp. pose proof (HFP1lo a Hfp). lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U25; intros a Ha.
    + apply (mbyte_of_aview SEGS). rewrite (KEEPC a ltac:(lia)). reflexivity.
    + intros _. apply (apresent_writable SEGS). apply Hfpres'. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 48 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 48)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (A52 : ew E3 52 = getr regs3 10) by (rewrite HE3; reflexivity).
clear HE3.
assert (Usp3 : bv_unsigned (ew E3 8) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
assert (U253 : bv_unsigned (ew E3 25) = frame_addr lyc 7 pos) by (rewrite OLD3 by lia; exact U25).
assert (SHOK3 : sh_ok SEGS at_Bx at_SH E3 (mrestrict (w_H W3) mem3)) by (unfold sh_ok, at_SH; apply Forall_nil).
(* 0x8a740 .. 0x8a748: the shadow fill of the buffer *)
paj_run_tok RUN HS HJ3 SHOK3 at_Bspan.
{ at_awr U253 HFA3 HFB pos. }
set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
lazymatch goal with Hfr : frame_of E3 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) ->
  rdW W3 (ms_mem ms0) a = rdW W3 mem3 a)
by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
      (fun a => frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin];
        [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp3, ?U253 in Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  eapply (aj_set_shadow_atS SEGS B LAWS Hsegs (SIG CS___asan_set_shadow_f8) 0xf8 (ASET_SHADOWF8 fx)
            W3 rg mm ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [(7, pos)] ly3 S3 mdq
            (0 + EV_HAND_BACK) 7 pos (shadow_addr (frame_addr lyc 7 pos) + 4) 512 (sp1 - spZ regs) _ HJ3) end.
  - left. reflexivity.
  - rewrite Q10, OLD3 by lia. rewrite (EE 22%nat 22%bv eq_refl). exact R22.
  - rewrite Q11. reflexivity.
  - lia.
  - rewrite HFA3. lia.
  - rewrite HFA3, HFB. change (8192 / 8) with 1024. lia.
  - unfold spZ at 1. rewrite Q2, OLD3 by lia. rewrite (EE 2%nat 2%bv eq_refl), Rsp.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hal16, Hs1c. reflexivity.
  - lia.
  - lia.
  - rewrite Q3, OLD3 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
  - rewrite Q4, OLD3 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold AN_JOIN; lia | reflexivity]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HF8a & HF8b & HF8c).
jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W3) mem4) HP4 [0; 1]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp3; intros a Ha.
    + apply (mbyte_of_aview SEGS). rewrite (HF8b a ltac:(lia) ltac:(lia)).
      reflexivity.
    + intros _. apply (apresent_writable SEGS).
      pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp4 & _).
      exact (Hp4 a ltac:(lia)).
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U253; intros a Ha.
    + apply (mbyte_of_aview SEGS). rewrite (HF8b a ltac:(lia) (HnSh a ltac:(lia))).
      reflexivity.
    + intros _. apply (apresent_writable SEGS).
      pose proof HJ4 as (HAR4 & _).
      destruct (al_frames SEGS B LAWS ly3 S3 W3 mem4 md4 7 pos HAR4 Hinf3) as (_ & _ & Hfp4 & _).
      apply Hfp4. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 64 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 64)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 8) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
assert (U254 : bv_unsigned (ew E4 25) = frame_addr lyc 7 pos) by (rewrite OLD4 by lia; exact U253).
assert (U184 : bv_unsigned (ew E4 18) = frame_addr lyc 7 pos) by (rewrite OLD4, OLD3 by lia; exact U18).
assert (SHOK4 : sh_ok SEGS at_Bx at_SH E4 (mrestrict (w_H W3) mem4)) by (unfold sh_ok, at_SH; apply Forall_nil).
(* 0x8a74c .. 0x8a758: the retire word of the frame, then the test of the frame pointer *)
paj_run_tok RUN HS HJ4 SHOK4 at_Bspan.
{ at_awr U254 HFA3 HFB pos. }
set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3.
psrr_branch_tok RUN BR HS SHOK4 at_Bspan.
- exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc.
  assert (Ew18 : ew E4 18 = Z_to_bv 64 (frame_addr lyc 7 pos))
    by (rewrite <- U184; symmetry; apply Z_to_bv_bv_unsigned).
  replace (U E4 (SLit 0)) with 0 in Hc by reflexivity.
  rewrite (U_atom_off E4 18 (frame_addr lyc 7 pos) 0 Ew18 ltac:(lia) ltac:(lia)) in Hc.
  lia.
- lazymatch goal with Hfr : frame_of E4 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) ->
    rdW W3 (ms_mem ms1) a = rdW W3 mem4 a)
  by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
        (fun a => frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) Hfr);
      [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4, ?U254 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn ]) end.
  paj_run_tok RUN HS HJ4 SHOK4 at_Bspan.
  { at_awr U254 HFA3 HFB pos. }
  set (mdv4 := with_vm_backing _ _ _) in *; clearbody mdv4.
  lazymatch goal with Hfr : frame_of E4 _ (mrestrict _ (ms_mem ms1)) (mrestrict _ _) |- _ =>
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) ->
    rdW W3 (ms_mem ms2) a = rdW W3 (ms_mem ms1) a)
  by (intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
        (fun a => frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) Hfr);
      [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp4, ?U254 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn ]) end.
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
  (* the bytes outside the frame's first word and buf's shadow, from hand_back's return to the call of the release *)
  assert (KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8) ->
    ~ (shadow_addr (frame_addr lyc 7 pos) + 4 <= a < shadow_addr (frame_addr lyc 7 pos) + 4 + 512) ->
    rdW W3 (ms_mem ms2) a = rdW W3 mem3 a).
  { intros a Ha Hn Hs. rewrite (KEEP4 a Ha Hn), (KEEP3 a Ha Hn), (HF8b a Ha Hs). exact (KEEP2 a Ha Hn). }
  (* the frame's bytes after its first word, from the frame's state at JOIN to the call of the release *)
  assert (KEEPF : forall a, frame_addr lyc 7 pos + 8 <= a < frame_addr lyc 7 pos + 8192 ->
    rdW W3 (ms_mem ms2) a = rdW Wc memc a).
  { intros a Ha. rewrite (KEEPM a ltac:(lia) ltac:(lia) (HnSh a ltac:(lia))), (KEEPC a ltac:(lia)).
    exact (KEEP1 a ltac:(lia) ltac:(lia)). }
  (* the flag word of the frame, still intact *)
  assert (HFLAG4 : rdword (rdW W3 (ms_mem ms2)) (frame_addr ly3 7 pos + fs_frame_bytes 7 - 8)
                   = Some (flag_addr ly3 7 pos)).
  { rewrite HFA3, HFB.
    assert (HFLeq : flag_addr ly3 7 pos = flag_addr lyc 7 pos).
    { pose proof HLY3 as (_ & _ & _ & _ & _ & EF & _). unfold flag_addr. rewrite EF. reflexivity. }
    rewrite HFLeq.
    rewrite (rdword_ext (rdW Wc memc) (rdW W3 (ms_mem ms2)) (frame_addr lyc 7 pos + 8192 - 8));
      [|intros k Hk; apply KEEPF; lia].
    rewrite HFB in HFLAG. exact HFLAG. }
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    eapply (aj_stack_free_atS SEGS B LAWS Hsegs ML FFL (SIG CS___asan_stack_free_7) 7 (ASTACK_FREE7 fx) ltac:(lia)
              W3 rg mm ANSWER_STK (spZ regs) (an_FP old O) ly S W mem md [] ly3 S3 mdq
              (0 + EV_HAND_BACK) pos 4256 (sp1 - spZ regs) _ HJ4) end.
    - rewrite T10, OLD4, OLD3 by lia. rewrite (EE 18%nat 18%bv eq_refl), R18, HFA3. reflexivity.
    - rewrite T11. reflexivity.
    - rewrite HFB. lia.
    - reflexivity.
    - exact HFLAG4.
    - unfold spZ at 1. rewrite T2, OLD4, OLD3 by lia. rewrite (EE 2%nat 2%bv eq_refl), Rsp.
      rewrite unsigned_lit_small by lia. lia.
    - rewrite Zminus_mod, Hal16, Hs1c. reflexivity.
    - lia.
    - lia.
    - rewrite T3, OLD4, OLD3 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Rgp.
    - rewrite T4, OLD4, OLD3 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Rtp.
    - exact T1.
    - apply ret_ok_codeptr_v; [unfold AN_JOIN; lia | reflexivity]. }
  cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HFRa & HFRb & HFRc).
  try change (4256 / 8) with 532 in HFRa, HFRb.
  jafter_call_keep_pi HS 80%nat regs5 (mrestrict (w_H W3) mem5) HP5 [0]%nat HS5.
  match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp4; intros a Ha;
      [|lia].
    apply (mbyte_of_aview SEGS).
    rewrite (HFRb a ltac:(lia) ltac:(rewrite HFA3; lia)).
    - reflexivity.
    - intros Heq. destruct (FFL ly3 S3 W3 mem3 md3 7 pos HAR3 Hinf3) as (_ & _ & _ & (_ & _ & Hfl)).
      lia.
    - lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
  remember (havoc E4 80 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
  assert (HEIe5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
  assert (OLD5 : forall n, (n < 80)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
  clear HE5.
  assert (SHOK5 : sh_ok SEGS at_Bx at_SH E5 (mrestrict (w_H W3) mem5)) by (unfold sh_ok, at_SH; apply Forall_nil).
  (* 0x8a76c .. 0x8a7bc: the epilogue *)
  paj_run_tok RUN HS HJ5 SHOK5 at_Bspan.
  { at_awr0. }
  set (mdv5 := with_vm_backing _ _ _) in *; clearbody mdv5.
  lazymatch goal with Hfr : frame_of E5 _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms3) a = rdW W3 mem5 a)
  by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) Hfr);
      [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]);
        destruct Hin
      | exact Ha | intros [] ]) end.
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  prreg HS (Z_to_bv 5 2) G2. prreg HS (Z_to_bv 5 3) G3. prreg HS (Z_to_bv 5 4) G4.
  prreg HS (Z_to_bv 5 8) G8. prreg HS (Z_to_bv 5 9) G9.
  prreg HS (Z_to_bv 5 18) G18. prreg HS (Z_to_bv 5 19) G19. prreg HS (Z_to_bv 5 20) G20.
  prreg HS (Z_to_bv 5 21) G21. prreg HS (Z_to_bv 5 22) G22. prreg HS (Z_to_bv 5 23) G23.
  prreg HS (Z_to_bv 5 24) G24. prreg HS (Z_to_bv 5 25) G25. prreg HS (Z_to_bv 5 26) G26.
  prreg HS (Z_to_bv 5 27) G27.
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold an_post, apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?dd = _ /\ _ =>
    exists ly3, (stack_free_state 7 pos S3), r, m, dd end.
  (* the configuration at the return *)
  split.
  { cbn [ms_regs]. rewrite F1, OLD5, OLD4, OLD3 by lia.
    rewrite (EXs 0%nat 32%nat ltac:(cbv; lia) eq_refl). cbn [at_extra an_saved map nth].
    replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity).
    unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split.
  { cbn [ms_mem]. eapply (ajournal_mono_k SEGS B);
      [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ5 | unfold EV_ANSWER; lia]. }
  split.
  { (* the callee-saved registers *)
    intros r Hr. unfold acallee_saved in Hr.
    assert (Hcs : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                  r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hcs as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - rewrite G2, OLD5, OLD4, OLD3 by lia. rewrite (EE 8%nat 8%bv eq_refl), R8.
      replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      unfold spZ. unfold w64. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite G3, OLD5, OLD4, OLD3 by lia. rewrite (EE 3%nat 3%bv eq_refl), Rgp.
      replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). symmetry. exact Hgp.
    - rewrite G4, OLD5, OLD4, OLD3 by lia. rewrite (EE 4%nat 4%bv eq_refl), Rtp.
      replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). symmetry. exact Htp.
    - rewrite G8, OLD5, OLD4, OLD3 by lia. rewrite (EXs 1%nat 33%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G9, OLD5, OLD4, OLD3 by lia. rewrite (EXs 2%nat 34%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G18, OLD5, OLD4, OLD3 by lia. rewrite (EXs 3%nat 35%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G19, OLD5, OLD4, OLD3 by lia. rewrite (EXs 4%nat 36%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G20, OLD5, OLD4, OLD3 by lia. rewrite (EXs 5%nat 37%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G21, OLD5, OLD4, OLD3 by lia. rewrite (EXs 6%nat 38%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G22, OLD5, OLD4, OLD3 by lia. rewrite (EXs 7%nat 39%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G23, OLD5, OLD4, OLD3 by lia. rewrite (EXs 8%nat 40%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G24, OLD5, OLD4, OLD3 by lia. rewrite (EXs 9%nat 41%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G25, OLD5, OLD4, OLD3 by lia. rewrite (EXs 10%nat 42%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G26, OLD5, OLD4, OLD3 by lia. rewrite (EXs 11%nat 43%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity.
    - rewrite G27, OLD5, OLD4, OLD3 by lia. rewrite (EXs 12%nat 44%nat ltac:(cbv; lia) eq_refl).
      cbn [at_extra an_saved map nth]. reflexivity. }
  (* the post-condition of answer *)
  unfold an_Q. cbv zeta.
  exists p1, p2, O'.
  (* the memory at the return keeps everything hand_back's post names *)
  assert (HBLKeq : ablocks B ly3 (stack_free_state 7 pos S3) = ablocks B ly3 S3)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (HFLown : aowned B ly3 S3 (flag_addr ly3 7 pos) /\ ~ in_img SEGS (flag_addr ly3 7 pos)).
  { destruct (FFL ly3 S3 W3 mem3 md3 7 pos HAR3 Hinf3) as (_ & Ho & (_ & Hni) & _). split; [exact Ho | exact Hni]. }
  assert (KEEPB : forall b n a, In (b, n) (ablocks B ly3 S3) -> b <= a < b + req_size n ->
    rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
  { intros b n a Hin Ha.
    destruct (al_blocks SEGS B LAWS ly3 S3 W3 mem3 md3 b n HAR3 Hin) as (_ & H4096 & Hcl & Hiapp & Hpr & _).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b n 7 pos HAR3 Hin Hinf3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFB, HFA3 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hiapp.
    rewrite (KEEP5 a ltac:(lia)).
    rewrite (HFRb a ltac:(lia) ltac:(rewrite HFA3; lia) ltac:(intros Heq; destruct (Hpr a Ha) as [_ Hno];
      apply Hno; rewrite Heq; exact (proj1 HFLown)) ltac:(lia)).
    exact (KEEPM a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KEEPG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
  { intros a Ha. unfold A_G_REC, REC_SIZE in Ha.
    assert (Hnimg : ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)).
    { intros Hbad. apply (frm_img SEGS B LAWS ly3 S3 W3 mem3 md3 7 pos a HAR3 Hinf3);
        [rewrite HFA3, HFB; lia|]. apply cif_prog_img. exists (A_G_REC, A_G_REC + 960).
      split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia]. }
    rewrite (KEEP5 a ltac:(lia)).
    rewrite (HFRb a ltac:(lia) ltac:(rewrite HFA3; lia)
      ltac:(intros Heq; apply (proj2 HFLown); rewrite <- Heq; apply cif_prog_img;
        exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC; lia])
      ltac:(lia)).
    exact (KEEPM a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KEEPS : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rdW W3 (ms_mem ms3) a = rdW W3 mem3 a).
  { intros a Ha. unfold A_REC_SPILL, SC_SIZE in Ha.
    assert (Hnimg : ~ (frame_addr lyc 7 pos <= a < frame_addr lyc 7 pos + 8192)).
    { intros Hbad. apply (frm_img SEGS B LAWS ly3 S3 W3 mem3 md3 7 pos a HAR3 Hinf3);
        [rewrite HFA3, HFB; lia|]. apply cif_prog_img. exists (A_REC_SPILL, A_REC_SPILL + 56).
      split; [right; left; reflexivity | cbn [fst snd]; unfold A_REC_SPILL; lia]. }
    rewrite (KEEP5 a ltac:(lia)).
    rewrite (HFRb a ltac:(lia) ltac:(rewrite HFA3; lia)
      ltac:(intros Heq; apply (proj2 HFLown); rewrite <- Heq; apply cif_prog_img;
        exists (A_REC_SPILL, A_REC_SPILL + 56); split; [right; left; reflexivity | cbn [fst snd]; unfold A_REC_SPILL; lia])
      ltac:(lia)).
    exact (KEEPM a ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (HPERMb : forall pn, In pn (ablocks B lyc Sc) <-> In pn (ablocks B ly S)).
  { intros pn. split; intros Hpn; [exact (Permutation_in pn HPERM Hpn)
    | exact (Permutation_in pn (Permutation_sym HPERM) Hpn)]. }
  assert (HHB2 : hand_back (an_R1 R e chg) (snd (rec_answer R e x chg)) = rec_answer R e x chg)
    by (symmetry; apply an_R1_answer).
  split; [cbn [ms_regs]; rewrite F10, OLD5, OLD4, A52 by lia; exact HQ10|].
  split; [exact Hp24|]. split; [exact Hp12|].
  split; [intros pn Hpn Hne; exact (Hfresh pn (proj2 (HPERMb pn) Hpn) Hne)|].
  split.
  { intros pn. rewrite HBLKeq, (HBLKS pn).
    split; intros [[Hin Hne] | Hpn]; try (right; exact Hpn);
      left; split; [apply HPERMb; exact Hin | exact Hne | apply HPERMb; exact Hin | exact Hne]. }
  split.
  { cbn [ms_mem]. rewrite HHB2 in HREP3.
    eapply (at_rec_repA_kept B ly3 S3 ly3 (stack_free_state 7 pos S3) (rdW W3 mem3));
      [exact HREP3 | exact KEEPG | exact KEEPS | exact KEEPB | rewrite HBLKeq; intros pn Hpn; exact Hpn]. }
  split; [exact HO'|].
  split.
  { cbn [ms_mem].
    pose proof (proj2 (HBLKS (p2, Z.of_nat (length (snd (rec_answer R e x chg))) + 1))
                (or_intror (or_intror eq_refl))) as Hin2.
    eapply (at_str_rng (rdW W3 mem3) (rdW W3 (ms_mem ms3)) p2
              (p2 + req_size (Z.of_nat (length (snd (rec_answer R e x chg))) + 1)));
      [intros y Hy; apply (KEEPB p2 (Z.of_nat (length (snd (rec_answer R e x chg))) + 1) y Hin2 Hy)
       | lia
       | pose proof (req_size_pos (Z.of_nat (length (snd (rec_answer R e x chg))) + 1) ltac:(lia)); lia
       | rewrite HHB2 in HSTR3; exact HSTR3]. }
  split.
  { (* the release of the frame leaves the live blocks; hand_back's blocks start from the entry's (permuted) *)
    rewrite (at_blocks_bytes_fold B ly3 (stack_free_state 7 pos S3)), HBLKeq, <- (at_blocks_bytes_fold B ly3 S3).
    rewrite (at_blocks_bytes_perm B ly S lyc Sc HPERM) in HBB3. unfold LIVE_ANSWER. exact HBB3. }
  { eapply (mle_weaken MT S (stack_free_state 7 pos S3) (0 + XM_HAND_BACK MT (snd (rec_answer R e x chg))));
      [exact MTL | | unfold XM_ANSWER; lia].
    unfold stack_free_state. apply (mo_le_set_fs_r MT MTFL).
    eapply (mo_le_trans MT MTL S Sc S3); [exact HMLE | exact HMLE3]. }
Qed.

End e.
End f.
End d.
