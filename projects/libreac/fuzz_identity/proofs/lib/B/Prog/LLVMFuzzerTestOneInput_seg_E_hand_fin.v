(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v; 136 of its 225 lines of code are new or changed and 5976 lines of the source are left out. *)
(* e_fin of seg_E (LLVMFuzzerTestOneInput_seg_E_hand_stmt.v, e_fin_stmt): the walk's post-condition e_post at
   0x817f4 (BASE + 0x1080), with the facts of inv_exit at 0x81764, gives inv_E_end. No run: the bytes the
   boundary states lie outside the calls' stack windows below mf and outside hw.have, so e_post's kept-bytes fact
   carries them; hw.have is e_post's own fact; the registers are e_post's. *)
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
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_E_hand_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_box_family_of_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section h.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma f_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
End h.
Lemma f_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma f_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
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
#[local] Notation ECOM := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).
#[local] Notation INV_E_END := (inv_E_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

#[local] Notation EFIN := (e_fin_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
  asink_none ameta_inv arodata_okS).

Lemma e_fin : EFIN.
Proof.
unfold e_fin_stmt.
intros HSTK LAWS AJ_NIL_IO g pos mf ly2 S2 W2 regs2 mem2 md2 W3 c3 Hfrs Hk MLE MOK HC Hid Hhw Hbl Hid3 Hmid Hcur R24
  Hpost.
destruct Hpost as (-> & regs3 & mem3 & md3 & -> & HJ3 & KEEP & VH & Q2 & Q3 & Q4 & Q8 & Q9 & Q25 & Q24 & Q23 & Q14).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem3 md3 4 pos HAR3 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem3 md3 4 pos HAR3 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. Z.div_mod_to_equations. lia. }
(* the machine frame and the saved words: kept *)
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H1 H2 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 a a n v); [|exact Hv].
  intros kk Hkk. apply KEEP; clear - H1 H2 Hkk Hmf0 Hmfb HSF0 HSF1 Hshi H47 C1; lia. }
(* the frame's bytes outside hw.have, and the frame's shadow: kept *)
assert (FRK : forall a, ((SF <= a < SF + 1024 /\ ~ (SF + 432 <= a < SF + 436)) \/ sh <= a < sh + 128) ->
  aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEP.
  - clear - Ha Hsh1 HSF0 HSF1 C1. lia.
  - clear - Ha Hsh1 HSF0 HSF1 Hmf0 C1. lia.
  - destruct Ha as [[_ Ha] | Ha]; [exact Ha|].
    intros Hw. apply (fshadow_not_app SF 128 SF 1024 a); [clear - HSF0; lia | clear - HSF1 C1; lia
    | exact HSFapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | clear - Hw; lia]. }
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  (off + Z.of_nat n <= 432 \/ 436 <= off) ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W2 mem3) (SF + off) n v).
{ intros off n v H0 H1 Hd Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem3 (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply FRK. left. clear - H0 H1 Hd Hkk. lia. }
assert (GF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  (off + Z.of_nat (length l) <= 432 \/ 436 <= off) ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W2 mem3) (SF + off) l).
{ intros off l H0 H1 Hd Hg. apply (f_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ l); [|exact Hg].
  intros kk Hkk. apply FRK. left. clear - H0 H1 Hd Hkk. lia. }
assert (SHZ : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_zero W2 mem2 (SF + off) n -> sh_zero W2 mem3 (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_zero in *.
  apply (f_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply FRK. right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn Hii HSF0 HSF64. Z.div_mod_to_equations. lia. }
assert (SHB : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W2 mem3 (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_blk in *.
  apply (f_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) mem3) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply FRK. right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn Hii HSF0 HSF64. Z.div_mod_to_equations. lia. }
(* the input block: a heap block (or empty), apart from the frame and below the stack *)
assert (HINB : bytes_at8 W2 mem3 (e_p g) (e_pl g)).
{ unfold bytes_at8 in *. apply (f_garr8_moved SEGS (w_H W2) (w_H W2) mem2 mem3 _ _); [|exact Hinb].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem3 md3 (e_p g) (e_n g) HAR3 Hine2) as (_ & Hp4096 & Hpce & Hpapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem3 md3 (e_p g) (e_n g) 4 pos HAR3 Hine2 Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  apply KEEP; clear - Hj Hpce Hp4096 Hrq Hdf Hmf0 C1; lia. }
(* the model *)
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
destruct Hid as (Hidb & Hidz & Hidk).
destruct Hhw as ((Hhwb & Hhwz & Hhwk) & _ & _).
change (SFa g pos) with SF in Hidb, Hidz, Hidk, Hhwb, Hhwz, Hhwk, VH.
unfold inv_E_end, acut.
exists ly2, S2, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact MLE|]. split; [exact MOK|].
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [rewrite Q2; exact Rsp|]. split; [rewrite Q9; exact Rs1|]. split; [rewrite Q8; exact Rs0|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply VMF; [clear; lia | clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
unfold id_at, hw_at, hw_mem, mf_id3, mf_id, sh_reg.
change (SFa g pos) with SF.
split.
{ split; [|split].
  - apply GF; [unfold V_id; clear; lia | | | exact Hidb];
    rewrite length_map; unfold m_id; rewrite SlotModel.rec_id_length; unfold V_id, RcIdentModel.ID_SIZE; clear; lia.
  - apply SHZ; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidz].
  - apply SHB; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidk]. }
split.
{ split; [split; [|split] | exact VH].
  - replace (SF + V_hw + 4) with (SF + 436) in * by (unfold V_hw; clear; lia).
    assert (Hl8 : length (m_hwb g (m_nrec g)) = 8%nat).
    { unfold m_hwb, SlotModel.rec_hwb.
      assert (H : match SlotModel.rec_hw (e_pl g) (m_nrec g) with Some h => length h = 8%nat | None => True end).
      { generalize (m_nrec g) as i. intros i. induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
        destruct ((SlotModel.rec_addr (e_pl g) i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k (e_pl g) i))
          eqn:Hc; [|exact IH].
        apply andb_prop in Hc as [_ Hkk]. apply Z.leb_le in Hkk.
        rewrite length_firstn, SlotModel.rec_pl_length. lia. }
      destruct (SlotModel.rec_hw (e_pl g) (m_nrec g)); [exact H | reflexivity]. }
    apply GF; [clear; lia | rewrite length_map, Hl8; clear; lia | rewrite length_map, Hl8; clear; lia | exact Hhwb].
  - apply SHZ; [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhwz].
  - apply SHB; [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhwk]. }
split; [exact Hbl|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hid3]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]|].
split; [exact Q23|].
split; [exact (SlotModel.rec_P7 (e_pl g) (SlotModel.nrecn (e_pl g)))|].
split; [rewrite Q25; exact (proj1 Hcur)|].
split; [rewrite Q24; exact R24|].
exact Q14.
Qed.

End c.
End b.
End a.
