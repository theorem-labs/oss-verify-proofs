(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module paths changed; 453 of its 506 lines of code are new or changed and 528 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_scribble_encode_A_lib.v, with its module paths and module names changed; 242 of its 285 lines of code are new or changed and 463 lines of the source are left out. *)
(* Part M2 of segment M of check_text_scribble's walk in image B (check_text_scribble_B_mi.v): from the entry of
   diginet_scribble_text 0x86500 (bs_cut .. PC_C1) through its contract (cdcU_scribble_text_specX: the text q, the
   record's first n bytes, which hold 0xa5) to its return 0x84014, then 0x84014 bne a0,s10 (not taken: the bytes it
   used are the owed ones, the contract's premise owed = scribble_text_spec), 0x84018 .. 0x84024 a0 = ch, a1 = want,
   a2 = n, jal the compare wrapper: to its entry 0x42430 (bs_cut .. PC_C2). The callee writes the record's first n
   bytes and its own 16 bytes below sp1; the save area, the frame, its shadow, want and the record's other bytes are
   kept by its post's tcj_kept. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_base check_text_scribble_B_l.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_f check_text_scribble_B_mi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register at the stop: a literal, an atom fact, or a callee-saved register of the boundary (EC) *)
Ltac bsm_rf := rv; first
  [ reflexivity
  | rewrite ?sv_denot_SOff0; ewpeel;
    first [ assumption
          | lazymatch goal with EC : forall nn (r : bv 5), _ -> acallee_saved _ -> _ |- _ =>
              apply EC; [reflexivity | unfold acallee_saved; lia] end ] ].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis SCRT : cdcU_scribble_text_specX tfibsegs B MT PC_C1.

(* an object of the call state is one of a later state with the same blocks and more frames at the same addresses *)
Lemma bsm_tdst_mono : forall lyc Sc ly4 S4 q n, tdst_ok B lyc Sc q n ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly4 S4)) ->
  (forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S4)) ->
  (forall c p, frame_addr ly4 c p = frame_addr lyc c p) -> tdst_ok B ly4 S4 q n.
Proof.
intros lyc Sc ly4 S4 q n Hd Hb Hf Efa a Ha.
destruct (Hd a Ha) as [(bb & mm & Hin & Hr) | (cid & ps & Hin & Hr)].
- left. exists bb, mm. split; [exact (Hb bb mm Hin) | exact Hr].
- right. exists cid, ps. split; [exact (Hf cid ps Hin)|]. unfold frame_rng in *. rewrite Efa. exact Hr.
Qed.
(* a byte of a heap block or of a live frame of a state is present *)
Lemma bsm_tdst_present : forall ly S (W : world tfibsegs) mem md q n a,
  AR tfibsegs B ly S W mem md -> tdst_ok B ly S q n -> q <= a < q + n -> apresent (w_H W) mem a.
Proof.
intros ly S W mem md q n a HAR Hd Ha.
destruct (Hd a Ha) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS ly S W mem md bb m HAR Hin) as (_ & _ & _ & _ & Hbo & _).
  replace a with (bb + (a - bb)) by lia. exact (proj1 (Hbo (bb + (a - bb)) ltac:(lia))).
- destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hfb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Hfb a ltac:(lia))).
Qed.
(* a byte of a heap block or of a live frame of a state is not the runtime's own there *)
Lemma bsm_tdst_not_owned : forall ly S (W : world tfibsegs) mem md q n a,
  AR tfibsegs B ly S W mem md -> tdst_ok B ly S q n -> q <= a < q + n -> ~ aowned B ly S a.
Proof.
intros ly S W mem md q n a HAR Hd Ha.
destruct (Hd a Ha) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks _ _ LAWS ly S W mem md bb m HAR Hin) as (_ & _ & _ & _ & Hbo & _).
  replace a with (bb + (a - bb)) by lia. exact (proj2 (Hbo (bb + (a - bb)) ltac:(lia))).
- unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
  intros (_ & Hnc). apply Hnc. right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
Qed.
(* the shadow window of a sub-range of a range is inside the range's *)
Lemma bsm_hull_sub : forall (rd : Z -> option Z) x n m, 0 <= x -> 0 < n <= m ->
  shadow_hull_vis rd x m -> shadow_hull_vis rd x n.
Proof.
intros rd x n m Hx Hn Hh s Hs. apply Hh. split; [lia|].
assert (M : shadow_addr (x + n - 1) / 8 * 8 <= shadow_addr (x + m - 1) / 8 * 8).
{ apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|]. unfold shadow_addr.
  pose proof (Z.div_le_mono (x + n - 1) (x + m - 1) 8 ltac:(lia) ltac:(lia)). lia. }
lia.
Qed.
(* the bytes of an object of the call state, off a callee's write set, are kept by its post's tcj_kept *)
Lemma bsm_obj_kept_cj : forall T lyc Sc ly2 S2 (W2 : world tfibsegs) mem2 W3 mem3 sp (E : Z -> Prop) q n,
  tcj_kept tfibsegs B T ly2 S2 W2 mem2 W3 mem3 sp E -> tdst_ok B lyc Sc q n ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2)) ->
  (forall c p, In (c, p) (frames Sc) -> In (c, p) (frames S2)) ->
  (forall c p, frame_addr ly2 c p = frame_addr lyc c p) ->
  forall a, q <= a < q + n -> ~ E a -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a.
Proof.
intros T lyc Sc ly2 S2 W2 mem2 W3 mem3 sp E q n (_ & K2 & _ & K4 & _) Htd Hb Hf Efa a Ha HnE.
destruct (Htd a Ha) as [(bb & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- replace a with (bb + (a - bb)) by lia. apply (K2 bb m (a - bb) (Hb bb m Hin)); [lia|].
  replace (bb + (a - bb)) with a by lia. exact HnE.
- apply (K4 cid pos a (Hf cid pos Hin)); [left; unfold frame_rng, in_zr in *; cbn [fst snd] in *; rewrite Efa; exact Hr
  | exact HnE].
Qed.

Theorem bsm2_holds : forall g pos W2 c2, bs_pre B g -> bs_now B g -> bs_cut B MT g pos PC_C1 (P_C1 g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (bs_cut B MT g pos PC_C2 (P_C2 g pos)).
Proof.
intros g pos W2 c2 Hpre Hnow Hc.
destruct Hc as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HK & HP & Hni & Hio & Hmo & HC & HL).
destruct HL as (R1 & R10 & R11 & R12 & R20 & R26 & Hrec & Hwg).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as Hac.
pose proof HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & R27 & _).
pose proof Hpre as (HE & _ & Hstr & Hoq & Hoch & _ & (Hch0 & Hchn & Hchtd & Hchtw & _ & _ & Hcham & Hchwin) & _ & _ & _ &
  Hn & Hdisj & Howe & _).
pose proof HE as (_ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
pose proof (proj1 HE) as HJc. pose proof (proj1 HJc) as HARc.
destruct (bs_stack B g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (bs_frame B LAWS g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & Efl & HF0 & HFc & HF64 & HFapp & HFp).
pose proof HJ as (HAR2 & _).
specialize (Hnow pos ly2 S2 W2 mem2 md2 HJ HK HP Hni) as ((Htb & Htra) & Hchra2 & Hchhull2 & Hqhull2).
unfold TB_check_text_scribble, ESTACK in Hceil, Hwin, H46.
assert (Hsp1m : bs_sp1 g mod 16 = 0).
{ pose proof (Z.div_mod (bs_sp1 g) 32 ltac:(lia)) as D. rewrite Hsp1a, Z.add_0_r in D. rewrite D.
  replace (32 * (bs_sp1 g / 32)) with ((2 * (bs_sp1 g / 32)) * 16) by lia. apply Z_mod_mult. }
assert (Esp : spZ regs2 = bs_sp1 g) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hbl : forall b m, In (b, m) (ablocks B (bs_lyc g) (bs_Sc g)) -> In (b, m) (ablocks B ly2 S2))
  by (intros b m Hin; exact (Permutation_in _ (Permutation_sym HP) Hin)).
assert (Hfi : forall c p, In (c, p) (frames (bs_Sc g)) -> In (c, p) (frames S2))
  by (intros c p Hin; rewrite Hfr; right; exact Hin).
pose proof Hstr as (Hq0 & _ & Hz0 & (_ & Hqn & _ & _ & _ & Hqam & Hqwin)).
assert (Hlen1 : 1 <= bs_len g) by (unfold bs_len; destruct (bs_tb g); [destruct Hz0 | cbn [length]; lia]).
pose proof (bsf_owe_len (Z.to_nat (bs_n g)) (bs_tb g)) as HOL.
assert (HchS : bs_ch g + 24 <= bs_sp g - 8352 \/ bs_sp g <= bs_ch g)
  by (unfold coff_win, TB_check_text_scribble, ESTACK in Hchwin; lia).
assert (HqS : bs_q g + bs_len g <= bs_sp g - 8352 \/ bs_sp g <= bs_q g)
  by (unfold coff_win, TB_check_text_scribble, ESTACK in Hqwin; unfold bs_len; lia).
eapply SRr_bind.
{ apply (SCRT (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g) ((0, pos) :: bs_own g)
    ly2 S2 W2 mem2 md2 (bs_k g) regs2 (bs_q g) (bs_ch g) (bs_n g) (bs_tb g) (repeat 165 (Z.to_nat (bs_n g)))).
  - apply (cpw_entry B _ _ _ _ _ _ _ _ _ (bs_lyc g) (bs_Sc g)); [exact HJ | | | | | | | | exact Hev | exact HP | exact Hlive].
    + rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
    + rewrite R3. exact Hgp.
    + rewrite R4. exact Htp.
    + rewrite Esp. exact Hsp1m.
    + rewrite Esp. unfold TB_scribble_text. lia.
    + rewrite Esp. lia.
  - exact R10.
  - split; [exact Hq0|]. split; [exact Htb|]. split; [exact Hz0|].
    split; [lia|]. split; [unfold bs_len in Hqn; exact Hqn|].
    split; [intros a Ha; destruct (Htb (Z.to_nat (a - bs_q g)) ltac:(unfold bs_len in Ha; lia)) as (Va & Ba);
            rewrite Z2Nat.id in Va by lia; replace (bs_q g + (a - bs_q g)) with a in Va by lia;
            rewrite (aview_of_val_mem1 tfibsegs _ _ _ _ Va Ba); discriminate|].
    split; [exact Htra|]. split; [intros _; exact Hqhull2|]. split; [exact Hqam|].
    unfold coff_win. rewrite Esp. unfold TB_scribble_text. unfold bs_len in HqS. lia.
  - exact R11.
  - exact R12.
  - rewrite repeat_length. lia.
  - split; [lia|]. split; [lia|].
    split; [apply (bsm_tdst_mono (bs_lyc g) (bs_Sc g) ly2 S2 (bs_ch g) (bs_n g)); [| exact Hbl | exact Hfi | exact Efa];
            intros a Ha; apply Hchtd; lia|].
    split.
    { intros a Ha. destruct (Hchtw a ltac:(lia)) as (Haw & _ & _ & _).
      split; [apply (bsm_awr_mono _ _ _ _ _ _ _ _ _ _ _ Haw); [exact Hbl | apply incl_tl, incl_refl | exact Efa]|].
      split; [apply (bsm_tdst_present ly2 S2 W2 mem2 md2 (bs_ch g) 24 a HAR2);
              [apply (bsm_tdst_mono (bs_lyc g) (bs_Sc g)); [exact Hchtd | exact Hbl | exact Hfi | exact Efa] | lia]|].
      split; [|rewrite Esp; unfold ESTACK; lia].
      exact (bsm_tdst_not_owned ly2 S2 W2 mem2 md2 (bs_ch g) 24 a HAR2
        (bsm_tdst_mono (bs_lyc g) (bs_Sc g) ly2 S2 (bs_ch g) 24 Hchtd Hbl Hfi Efa) ltac:(lia)). }
    split; [intros x Hx; apply Hchra2; lia|].
    split; [intros Hn0; exact (bsm_hull_sub _ (bs_ch g) (bs_n g) 24 ltac:(lia) ltac:(lia) Hchhull2)|].
    split; [unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg in *; lia|].
    unfold coff_win. rewrite Esp. unfold TB_scribble_text. lia.
  - intros j Hj. rewrite repeat_length in Hj. rewrite (bsf_nth_repeat _ j 165 0 Hj).
    split; [|lia]. destruct (Hrec j ltac:(rewrite repeat_length; lia)) as (Vj & _).
    rewrite (bsf_nth_repeat 24 j 165 0 ltac:(lia)) in Vj. exact Vj.
  - unfold bs_len in *. lia. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & KT3 & (Ha0 & Hres)).
unfold EV_CDC in HJ3. rewrite Z.add_0_r in HJ3.
rewrite Esp in KT3. unfold TB_scribble_text in KT3.
rewrite R1.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact HP3.
assert (HSB : shadow_addr (bs_F g pos) = SB + bs_F g pos / 8) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (HF8 : 0 <= bs_F g pos / 8 <= bs_F g pos) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8b : bs_F g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
(* the bytes of the walk's own frame and of its shadow are fresh for the call state, the record's are not *)
assert (HFR : forall a, (bs_F g pos <= a < bs_F g pos + 64) \/ (SB + bs_F g pos / 8 <= a < SB + bs_F g pos / 8 + 8) ->
  cw_fresh B (bs_lyc g) (bs_Sc g) a).
{ intros a Ha. apply (cw_fresh_own B LAWS (bs_lyc g) (bs_Sc g) ly2 S2 W2 mem2 md2 0 pos a HAR2 Hfr HP Efa).
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (bs_F g pos). rewrite HSB.
  change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. destruct Ha; [left | right]; lia. }
assert (HRF : forall a, bs_ch g <= a < bs_ch g + 24 -> cw_fresh B (bs_lyc g) (bs_Sc g) a -> False)
  by (intros a Ha Hf; exact (bsl_apart B (bs_lyc g) (bs_Sc g) (bs_ch g) 24 a Hoch Hf a Ha eq_refl)).
(* what the callee kept: the save area (above its window), the frame and its shadow (off its write set) *)
assert (KOFF : forall a, (bs_sp g - 96 <= a < bs_sp g) \/ (bs_F g pos <= a < bs_F g pos + 64) \/
  (SB + bs_F g pos / 8 <= a < SB + bs_F g pos / 8 + 8) ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. pose proof KT3 as (K1 & _ & _ & K4 & _).
  assert (HnE : ~ (bs_ch g <= a < bs_ch g + bs_n g)).
  { intros Hr. destruct Ha as [Ha | Ha]; [lia | exact (HRF a ltac:(lia) (HFR a Ha))]. }
  destruct Ha as [Ha | [Ha | Ha]].
  - apply K1; [lia | lia | exact HnE].
  - apply (K4 0 pos a); [rewrite Hfr; left; reflexivity | | exact HnE].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes 0) with 64. fold (bs_F g pos). lia.
  - apply (K4 0 pos a); [rewrite Hfr; left; reflexivity | | exact HnE].
    right. unfold in_zr. cbn [fst snd]. rewrite Efa. fold (bs_F g pos). rewrite HSB. change (fs_frame_bytes 0 / 8) with 8.
    lia. }
(* the walk's kept invariant through the call *)
assert (KTc : tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W3 mem3 (bs_sp g)
  (bs_wr g)).
{ eapply (cw_kept_cj B LAWS) with (1 := HJc) (2 := HJ) (4 := HP) (10 := HK) (11 := KT3);
  [ rewrite Hfr; apply incl_tl, incl_refl | unfold TB_check_text_scribble, ESTACK; lia | lia
  | unfold TB_check_text_scribble, ESTACK; lia | lia
  | intros a Ha; cbv beta in Ha; right; left; split;
    [ unfold bs_wr; lia
    | intros Him; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ _ _ a HARc Hchtd ltac:(lia) Him) ] ]. }
(* the state at 0x84014 *)
set (E := Ereg regs3 (cw_extra [])).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs3 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (HS : st_ok tfibsegs E (mkSS 0x84014 sr_atoms [] None (mkFacts [(32%nat, mkAF SB SB 0)] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x84014) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite cw_ew_SB, unsigned_lit_small by (unfold SB; lia). unfold SB. split; [|exact I]. split; [lia|].
    split; [reflexivity | lia]. }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W3) mem3)) by constructor.
assert (EC : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> acallee_saved (Z.of_nat nn) -> ew E nn = getr regs2 r).
{ intros nn r Hnn Hcs. rewrite (EE nn r Hnn). pose proof (CS _ Hcs) as Hc. rewrite Hnn, !Z_to_bv_bv_unsigned in Hc.
  exact Hc. }
assert (E10 : ew E 10 = w64 (snd (bs_owe g)))
  by (rewrite (EE 10%nat 10%bv eq_refl), Ha0; unfold bs_owe; rewrite Howe; reflexivity).
assert (E26 : ew E 26 = w64 (snd (bs_owe g)))
  by (rewrite (EC 26%nat 26%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R26).
assert (E20 : ew E 20 = w64 (bs_ch g)) by (rewrite (EC 20%nat 20%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R20).
assert (E22 : ew E 22 = w64 (bs_F g pos + 32))
  by (rewrite (EC 22%nat 22%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R22).
assert (E19 : ew E 19 = w64 (bs_n g)) by (rewrite (EC 19%nat 19%bv eq_refl ltac:(unfold acallee_saved; lia)); exact R19).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a)
  by (intros; reflexivity).
assert (KP : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem3 a) by (intros; assumption).
(* 0x84014 bne a0,s10: not taken, the bytes used are the owed ones *)
cw_branch Hc.
{ exfalso. rewrite branch_ne_U, !U_SOff in Hc. ewpeel_in Hc. rewrite E10, E26, Z.eqb_refl in Hc. discriminate Hc. }
(* 0x84018 .. 0x84024: a0 = ch, a1 = want, a2 = n, jal the compare wrapper *)
cw_run_to ltac:(cbn [ss_mem]; apply awr_ok_nil) PC_C2. ctk_keep cw_kwr_ro.
apply SRr_ret.
lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict _ ?msv) |- context [mkCfg _ ?md4] =>
  pose proof (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl) as Hms;
  exists ly3, S3, (ms_regs msv), (ms_mem msv), md4;
  split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|]
end.
split; [exact HJ3|].
split.
{ apply (cw_kept_step B LAWS TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) W3 mem3
    _ (bs_sp g) (bs_wr g) (fun _ => False));
  [ unfold TB_check_text_scribble, ESTACK; lia | exact HARc | exact KTc | exact KE | intros a [] | exact KP ]. }
split; [exact (Permutation_trans HPerm3 HP)|].
split; [exact Hni|].
split; [eapply same_io_trans; [exact (same_io_trans _ _ _ Hio HIO3) | kio]|].
split; [pose proof (mle_station _ _ _ _ 0 0 MTL Hmo HMLE3) as HMOn; rewrite Z.add_0_r in HMOn; exact HMOn|].
split.
{ apply (bsm_common_keep g pos regs2 mem2 W2 _ _ W3 HC);
  [ bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf | bsm_rf
  | bsm_rf | bsm_rf | bsm_rf | intros a Ha; rewrite KE by (first [lia | tauto | unfold SB in *; lia]); exact (KOFF a Ha) ]. }
split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|]. split; [bsm_rf|].
pose proof (bsf_owe_len (Z.to_nat (bs_n g)) (bs_tb g)) as HOL2.
assert (HwL : length (fst (bs_owe g)) = Z.to_nat (bs_n g)) by exact HOL2.
split.
{ intros j Hj. unfold scribble_bytes in Hj |- *. rewrite length_app, repeat_length in Hj.
  fold (bs_owe g) in Hj |- *. rewrite HwL in Hj.
  destruct (Nat.lt_ge_cases j (Z.to_nat (bs_n g))) as [Hjl | Hjl].
  - rewrite app_nth1 by (rewrite HwL; exact Hjl).
    assert (Hl2 : length (fst (DgnLib.scribble_text_spec (bs_tb g) (bs_n g))) = Z.to_nat (bs_n g))
      by (rewrite <- Howe; exact HOL2).
    destruct (Hres j ltac:(rewrite Hl2; exact Hjl)) as (Vj & Bj).
    unfold bs_owe. rewrite Howe. split; [|exact Bj].
    apply (cw_val_mem_kept (w_H W3) (w_H W3) mem3 _ _ 1 _); [|exact Vj].
    intros x Hx. apply KE; [lia | tauto].
  - rewrite app_nth2 by (rewrite HwL; exact Hjl). rewrite HwL.
    rewrite (bsf_nth_repeat (Z.to_nat (24 - bs_n g)) (j - Z.to_nat (bs_n g)) 165 0 ltac:(lia)). split; [|lia].
    destruct (Hrec j ltac:(rewrite repeat_length; lia)) as (Vj & _).
    rewrite (bsf_nth_repeat 24 j 165 0 ltac:(lia)) in Vj.
    apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 _ _ 1 _); [|exact Vj].
    intros x Hx. cbn [Z.of_nat] in Hx. rewrite KE by (first [lia | tauto]).
    apply (bsm_obj_kept_cj TB_scribble_text (bs_lyc g) (bs_Sc g) ly2 S2 W2 mem2 W3 mem3 (bs_sp1 g)
      (fun x0 => bs_ch g <= x0 < bs_ch g + bs_n g) (bs_ch g) 24); [exact KT3 | exact Hchtd | exact Hbl | exact Hfi
      | exact Efa | lia | cbv beta; lia]. }
apply (bs_garr8_kept (w_H W2) (w_H W3) mem2 _); [|exact Hwg].
intros a Ha. rewrite HwL in Ha. rewrite KE by (first [lia | tauto]). apply KOFF. right; left. lia.
Qed.
End s.
