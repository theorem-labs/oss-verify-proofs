(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module names changed; 179 of its 264 lines of code are new or changed and 5980 lines of the source are left out. *)
(* h_glue (LLVMFuzzerTestOneInput_seg_H_hand3_stmt.v, h_glue_stmt): segment H of LLVMFuzzerTestOneInput's
   ASan+UBSan walk (image B) from the block's walk h_core_stmt. No instruction is stepped here. inv_G_end's acut
   gives h_core_stmt's premises; h_core_stmt's post hg_post gives inv_H_end at +0x128c (0x81a00): the journal
   and k are the post's, the meter goes through HMT0 and ameter_laws, the machine-frame slots and the saved
   words through rvs_k's first clause, the frame's bytes and shadow through its frame-zone clause, the input
   bytes through the post's own journal from the entry state (FP = [], so no byte of a block live at the entry
   and at the end changed), the fds and the fs through the journal's aos_step (FP = [] opens no sink), and
   `ef` from the post's garr8 (SlotModel.t_EF is that list). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
reac_identity_reac_ver_str LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv
LLVMFuzzerTestOneInput_seg_H_hand3_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel IdentSpec RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac hg_inr := cbn [In]; repeat (first [left; reflexivity | right]).

(* the written strings are short: hg_n2 v <= 72 *)
Lemma hg_dd_len : forall n x, (length (IdentSpec.dec_digits n x) <= n)%nat.
Proof.
induction n as [|n IH]; intros x; cbn [IdentSpec.dec_digits]; [cbn [length]; lia|].
rewrite length_app. cbn [length]. destruct (x <? 10); cbn [length]; [lia|].
specialize (IH (x / 10)). lia.
Qed.
Lemma hg_n2_le : forall v, 0 <= v < 65536 -> 0 <= hg_n2 v <= 72.
Proof.
intros v Hv. unfold hg_n2, hg_d1, IdentSpec.DEC. rewrite length_app, repeat_length.
assert (Hx : 0 <= v / 1000 <= 66) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
set (x := v / 1000) in *.
pose proof (Z.log2_le_lin x (proj1 Hx)) as Hl. pose proof (Z.log2_nonneg x) as Hl0.
pose proof (hg_dd_len (S (Z.to_nat (Z.log2 x))) x) as Hd.
set (L := length (IdentSpec.dec_digits (S (Z.to_nat (Z.log2 x))) x)) in *.
set (y := Z.log2 x) in *. change (Z.to_nat 1) with 1%nat.
clearbody L y x. clear - Hx Hl Hl0 Hd. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma hg_garr8_moved : forall segs H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros segs H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
Lemma hg_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma hg_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
Qed.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* the Section of the statement file, in its order *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

Lemma h_glue : h_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold h_glue_stmt, seg_H_stmt.
intros LAWS MTL HMT0 HSTK HEV HANY HCORE g pos mf W2 c2 HG.
unfold inv_G_end, acut in HG.
destruct HG as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfr & Hk & MLE & MOK & HC & HP).
destruct HP as (Hid & Hhb & Hsh & Hid3 & Hmid & Zf & Zef & V208 & R24 & R25 & R21 & R26 & R27 &
  V176 & V160 & V120 & V112).
destruct Hid as (Hidb & Hidz & Hidk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HPRE as (_ & _ & _ & _ & Hinp & Hlen & Hgin & _ & Hnev & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. Z.div_mod_to_equations. lia. }
(* ---- h_core_stmt's premises, from inv_G_end ---- *)
pose proof (HANY (e_pl g)) as Hv.
assert (CD : 0 <= SlotModel.t_cap_disp (e_pl g) < 2 ^ 64).
{ unfold SlotModel.t_cap_disp.
  pose proof (Z.mod_pos_bound (SlotModel.tb (e_pl g) 7) 64 ltac:(clear; lia)) as M. clear - M. lia. }
set (v := SlotModel.t_any_fw (e_pl g)) in *.
set (cd := SlotModel.t_cap_disp (e_pl g)) in *.
pose proof (hg_n2_le v Hv) as HN2.
assert (NEV : st_nev (e_S g) + (4 * Z.of_nat (m_nrec g) + 4) <= EV_MAX) by (clear - Hnev Hk HEV; lia).
assert (HSTKW : sp0 - LLVMF_STK <= mf - 2 * ESTACK) by (clear - Hmfb HSTK' Has HES; lia).
pose proof (HCORE LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 mem2 md2
  (4 * Z.of_nat (m_nrec g) + 4) regs2 pos mf SF v cd HJ Hfr eq_refl EFa NEV Rsp Rs1 Rgp Rtp Hmf32
  (proj1 Hmfb) (proj2 Hmfb) HSTKW R24 Hv R25 V208 V64 V120 CD Zf Zef) as HRUN.
apply (SRr_mono SEGS _ _ _ _ HRUN).
clear HRUN HCORE.
(* ---- inv_H_end at +0x128c, from hg_post ---- *)
intros W3 c3 _ HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfr3 & Hperm3 & HREG & R22 & HEF & HK).
destruct HK as (K1 & _ & _ & K4 & _).
pose proof HJ3 as (_ & _ & _ & _ & Hio3 & _ & _ & _ & _ & HB3 & _).
(* the machine frame and the saved words: rvs_k's first clause *)
assert (VMS : forall a (n : nat) val, mf <= a -> a + Z.of_nat n <= sp0 ->
  (a + Z.of_nat n <= mf + 208 \/ mf + 216 <= a) ->
  val_mem SEGS (rd W2 mem2) a n val -> val_mem SEGS (rd W3 mem3) a n val).
{ intros a n val H1 H2 H3 Hval.
  apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 a a n val); [|exact Hval].
  intros kk Hkk. apply K1.
  - clear - H1 H2 Hkk Hmf0 Hshi H47. lia.
  - clear - H1 Hkk. lia.
  - unfold hg_wrote. clear - H1 H3 Hkk HN2 HSF1 Hmf0. lia. }
(* the frame's bytes away from f and ef, and the frame's shadow: rvs_k's frame-zone clause *)
assert (FRK : forall a, ((SF <= a < SF + 464 \/ SF + 600 <= a < SF + 1024) \/ sh <= a < sh + 128) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (K4 4 pos a Hin4).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. change (shadow_addr SF) with sh.
    destruct Ha as [Ha | Ha]; [left; clear - Ha; lia | right; change (1024 / 8) with 128; clear - Ha; lia].
  - unfold hg_wrote. intros Hw. destruct Ha as [Ha | Ha].
    + clear - Ha Hw HN2 HSF1 Hmf0. lia.
    + assert (Ha' : 2147450880 + SF / 8 <= a < 2147450880 + SF / 8 + 128).
      { rewrite Esh in Ha. unfold SHADOW_OFF in Ha. clear - Ha. lia. }
      destruct Hw as [Hw | [Hw | Hw]].
      * apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia | exact HSFapp
          | exact Ha' | clear - Hw HN2; lia].
      * apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia | exact HSFapp
          | exact Ha' | clear - Hw HN2; lia].
      * clear - Ha Hw Hsh1 Hmf0. lia. }
assert (VMF : forall off (n : nat) val, 0 <= off ->
  (off + Z.of_nat n <= 464 \/ (600 <= off /\ off + Z.of_nat n <= 1024)) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n val -> val_mem SEGS (rd W3 mem3) (SF + off) n val).
{ intros off n val H0 H1 Hval.
  apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (SF + off) (SF + off) n val); [|exact Hval].
  intros kk Hkk. apply FRK. left. clear - H0 H1 Hkk. lia. }
assert (GF : forall off l, 0 <= off ->
  (off + Z.of_nat (length l) <= 464 \/ (600 <= off /\ off + Z.of_nat (length l) <= 1024)) ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W3 mem3) (SF + off) l).
{ intros off l H0 H1 Hg. apply (hg_garr8_moved SEGS (w_H W2) (w_H W3) mem2 mem3 _ l); [|exact Hg].
  intros kk Hkk. apply FRK. left. clear - H0 H1 Hkk. lia. }
assert (SHZ : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_zero W2 mem2 (SF + off) n -> sh_zero W3 mem3 (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_zero in *.
  apply (hg_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) mem3) SHADOW_OFF (SF + off) n);
    [|exact Hz].
  intros ii Hii. apply FRK. right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn Hii HSF0 HSF64. Z.div_mod_to_equations. lia. }
assert (SHB : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W3 mem3 (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_blk in *.
  apply (hg_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) mem3) SHADOW_OFF (SF + off) n);
    [|exact Hz].
  intros ii Hii. apply FRK. right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn Hii HSF0 HSF64. Z.div_mod_to_equations. lia. }
(* the blocks: the post's Permutation and inv_G_end's hblocks *)
assert (HPB : Permutation (ablocks B ly3 S3) ([] ++ ablocks B (e_ly g) (e_S g)))
  by exact (perm_trans Hperm3 (proj1 Hhb)).
(* the input bytes: the post's journal from the entry state, with FP = [] *)
assert (HINB : bytes_at8 W3 mem3 (e_p g) (e_pl g)).
{ unfold bytes_at8. apply (hg_garr8_moved SEGS (w_H (e_W g)) (w_H W3) (e_mem g) mem3 _ _); [|exact Hgin].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  apply (HB3 (e_p g) (e_n g) j Hine).
  - apply (Permutation_in _ (Permutation_sym HPB)). exact Hine.
  - unfold req_size. rewrite (proj2 (Z.eqb_neq (e_n g) 0)) by (clear - Hn0; lia). clear - Hj. lia.
  - intros (r & Hr & _). destruct Hr. }
(* the fds and the fs: the post's journal opens no sink *)
assert (Hnfp : ~ YI16.sink_open_fp []) by (intros (r & Hr & _); destruct Hr).
destruct (aos_step_closed [] (e_md g) md3 Hnfp Hio3) as (Efd & Efs & _ & _).
(* the meter: HMT0 and ameter_laws *)
assert (MLE3 : mo_le MT (e_S g) S3 ((4 * Z.of_nat (m_nrec g) + 4) * MEV MT)).
{ pose proof (mo_le_trans MT MTL _ _ _ _ _ MLE (HMT0 S2 S3)) as M. rewrite Z.add_0_r in M. exact M. }
assert (MOK3 : mo_ok MT S3 ((EV_LLVMF - (4 * Z.of_nat (m_nrec g) + 4)) * MEV MT)).
{ apply (mo_ok_step MT MTL S2 S3 0 _); [rewrite Z.add_0_l; exact MOK | exact (HMT0 S2 S3)]. }
unfold inv_H_end, acut.
exists ly3, S3, regs3, mem3, md3. cbv beta.
split; [reflexivity|]. split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfr|]. split; [exact Hk|].
split; [exact MLE3|]. split; [exact MOK3|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [rewrite (HREG 2%bv ltac:(hg_inr)); exact Rsp|].
  split; [rewrite (HREG 9%bv ltac:(hg_inr)); exact Rs1|].
  split; [rewrite (HREG 8%bv ltac:(hg_inr)); exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [rewrite (HREG 3%bv ltac:(hg_inr)); exact Rgp|].
  split; [rewrite (HREG 4%bv ltac:(hg_inr)); exact Rtp|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V16]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply VMF; [clear; lia | right; clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; unfold m_fds; rewrite Efd; reflexivity|].
  split; [unfold m_fs; rewrite Efs; reflexivity|].
  exact HINB. }
unfold id_at, mf_id3, mf_id, sh_reg.
change (SFa g pos) with SF.
split.
{ split; [|split].
  - apply GF; [unfold V_id; clear; lia | | exact Hidb].
    left. rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length.
    unfold V_id, RcIdentModel.ID_SIZE. clear. lia.
  - apply SHZ; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidz].
  - apply SHB; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidk]. }
split; [unfold hblocks; split; [exact HPB | exact (proj2 Hhb)]|].
split; [rewrite (HREG 23%bv ltac:(hg_inr)); exact Hsh|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact Hid3]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact Hmid]|].
split; [exact HEF|].
split; [rewrite (HREG 27%bv ltac:(hg_inr)); exact R27|].
split; [rewrite (HREG 21%bv ltac:(hg_inr)); exact R21|].
split; [rewrite (HREG 26%bv ltac:(hg_inr)); exact R26|].
split; [exact R22|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V176]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V160]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V120]|].
apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | clear; lia | exact V112].
Qed.

Check (h_glue : h_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
End c.
End b.
End a.
Print Assumptions h_glue.
