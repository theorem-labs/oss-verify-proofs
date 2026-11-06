(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module paths, module names, addresses and numbers changed; 402 of its 492 lines of code are new or changed and 1053 lines of the source are left out. *)
(* Segment D6 of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan): the record's tail,
   0x81598..0x815ec (BASE + 0xe24 .. BASE + 0xe78, 21 slots). seg_D6 of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v:
   from the join inv_tail to inv_D6_end, the slot of the loop test.

   The code:
     0x81598 ld a0,120(s1)        the record's remaining length as stored after the header (mf+120)
     0x8159c sub s8,a0,s6         x24 := that - rec_k i (no boundary reads it)
     0x815a0 ld s7,160(s1)        x23 := the frame's shadow address (mf+160)
     0x815a4 li a0,-8
     0x815a8 .. 0x815cc           ten shadow stores of 0xf8 at s7 + 8, 14..18, 4..7 (`before` and `again` poisoned)
     0x815d0 mv a0,s11
     0x815d4 jal wrapper_free     the payload copy is freed (afree04_rule through YC85.afree04_sub, HUMF)
     0x815d8 ld a4,128(s1)        the record index i (mf+128)
     0x815dc addiw a4,a4,1        x14 := i + 1
     0x815e0 ld s9,112(s1)        x25 := the cursor after the record (mf+112)
     0x815e4 ld a0,96(s1)         x10 := nrec (mf+96)
     0x815e8 li a5,1              x15 := 1
   Both runs are plain runs (no checked access). The first writes only the frame's shadow window [s7 + 4, s7 + 19),
   which the journal's own frame (4, pos) covers; the second writes nothing.
   The B twin of lib/A/Prog/LLVMFuzzerTestOneInput_D6.v. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g.
(* YK1e is not loaded here: its own `env` would shadow the engine's in this file, so alu64_sub_lit is restated. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the address arithmetic of
   this segment (shadow_addr, the frame's 64-byte alignment) needs it, so this file turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The symbolic state at 0x81598. Region 0: the five machine-frame words the segment loads, base s1 (atom 9):
   mf+96 = nrec (atom 32), mf+112 = the cursor after the record (atom 33), mf+120 = the record's remaining
   length after the header, rec_Lp i (atom 34), mf+128 = i (atom 35), mf+160 = the frame's shadow address
   (atom 36); read-only. Region 1: the frame's shadow, base atom 36 (the value the run loads into s7), writable on
   the cells the ten stores hit. *)
Definition d6_mf : YP09.region := YP09.mkRegion (Some 9%nat) 96 168 96 96
  [YP09.mkChunk 96 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 8 (SOff 33 0));
   YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 128 (CVal 8 (SOff 35 0));
   YP09.mkChunk 160 (CVal 8 (SOff 36 0))].
Definition d6_sh : YP09.region := YP09.mkRegion (Some 36%nat) 0 128 4 19 [].
Definition d6_ss : sstate := mkSS 0xe24 sr_atoms [d6_mf; d6_sh] None (mkFacts [] [] []).

Section h.
Variable segs : list Segment.
Lemma d6_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (a + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
End h.
Lemma d6_zero_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < n / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  zero_shadow rd Bs a n -> zero_shadow rd' Bs a n.
Proof. intros rd rd' Bs a n Hk Hz i Hi. rewrite (Hk i Hi). exact (Hz i Hi). Qed.
Lemma d6_block_shadow_moved : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n Hk (H8 & Hn & Hb). split; [exact H8|]. split; [exact Hn|].
intros i Hi. rewrite (Hk i Hi). exact (Hb i Hi).
Qed.
Lemma d6_hwb_length : forall inp i, length (SlotModel.rec_hwb inp i) = 8%nat.
Proof.
intros inp i. unfold SlotModel.rec_hwb.
assert (H : match SlotModel.rec_hw inp i with Some h => length h = 8%nat | None => True end).
{ induction i as [|i IH]; cbn [SlotModel.rec_hw]; [exact I|].
  destruct ((SlotModel.rec_addr inp i =? RcIdentModel.ADDR_REAC_VERSION) && (8 <=? SlotModel.rec_k inp i)) eqn:Hc;
  [|exact IH].
  apply andb_prop in Hc as [_ Hk]. apply Z.leb_le in Hk.
  rewrite length_firstn, SlotModel.rec_pl_length. lia. }
destruct (SlotModel.rec_hw inp i); [exact H | reflexivity].
Qed.
Lemma d6_aluw_inc : forall i : Z, 0 <= i < 2 ^ 31 - 1 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (i + 1).
Proof.
intros i Hi. rewrite YK1g.aluw_addi_lit. apply bv_eq. rewrite v_addiw_small; rewrite ?unsigned_lit_small by lia; lia.
Qed.
(* The sub at 0x8159c, as the engine builds it: a multiply by -1 and an add (A's LLVMFuzzerTestOneInput_D6.v). *)
Lemma d6_md_neg : forall x : Z, mul_div M_MUL (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (- x).
Proof.
intros x. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.mul_mod by lia. f_equal. lia.
Qed.
(* With no input byte there is no record (nrec [] = input[0] mod 65 = 0). *)
Lemma d6_nrec_nil : SlotModel.nrec [] = 0.
Proof. reflexivity. Qed.

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
Variable LS : lib_shape.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* The record's tail, from the join to the loop test. The free's call chain is the entry's one frame record
   (sp0, RA_LLVMF, s0) when sp0 < ly_top - 16, else empty (chain_pre, YG00 bad_next); LLVMF_FREE_CTX holds the
   context of 0x815d4 in both shapes, so HUMF covers both through llvmf_univ_call / llvmf_univ_call0. *)
Theorem d6_run : forall g pos mf i pl W2 c2,
  inv_tail B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS g pos mf i pl W2 c2 ->
  SRr SEGS W2 c2 (inv_D6_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS
    asink_none ameta_inv arodata_okS g pos mf i).
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64s & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as ((Hi & Hbl & Hpl & Hid & V96n & Hfix & Hbef & Hmag & Hmid & V112 & V120 & V128 & R22 & R27 & Hcur)
  & Hhw).
unfold MEV in MLE, MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
(* the entry state *)
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
(* the journal at the start *)
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
(* the input block: a heap block, since a record exists (no input byte gives nrec = 0) *)
assert (Hpn : In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g))).
{ destruct Hinp as [[Hn0 _] | [_ Hine]]; [|exact Hine]. exfalso.
  assert (Hpl0 : e_pl g = []).
  { destruct (e_pl g) as [|b l] eqn:Epl; [reflexivity|]. try rewrite Epl in Hlen. cbn [length] in Hlen. lia. }
  unfold m_nrec, SlotModel.nrecn in Hi. rewrite Hpl0, d6_nrec_nil in Hi. cbn in Hi. lia. }
set (sp0 := e_sp0 g) in *.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
set (SF := SFa g pos) in *.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
(* the model *)
set (inp := e_pl g) in *.
set (k := SlotModel.rec_k inp i) in *.
set (nrec := SlotModel.nrec inp) in *.
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
pose proof (SlotModel.nrec_range inp) as Hnr. fold nrec in Hnr.
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp nrec in Hi. clear - Hi Hnr. lia. }
(* the input block's place, for the cursor's range *)
assert (Hpn2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hpn. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hpn2) as (_ & Hp4096 & Hpce & Hpapp & _).
assert (Hn0 : 0 <= e_n g) by (rewrite Hlen; lia).
pose proof (req_size_pos (e_n g) Hn0) as Hrq.
set (cur := e_p g + m_cur g (S i)) in *.
assert (Hcur64 : 0 <= cur < 2 ^ 64) by (unfold cur; clear - Hcur Hp4096 Hpce Hrq C1; lia).
(* the record's remaining length after the header, in mf+120: rec_Lp i = n - rec_body i, so after the sub at
   0x8159c x24 = rec_Lp i - rec_k i = n - rec_c (S i) *)
set (Lp := SlotModel.rec_Lp inp i) in *.
pose proof (SlotModel.rec_bounds inp i) as (_ & Hbod0 & Hbodk & HLp & _ & Hcs).
fold k Lp in Hbodk, HLp, Hcs.
assert (Hnlen : SlotModel.nlen inp = e_n g) by (unfold SlotModel.nlen; fold inp; rewrite Hlen; reflexivity).
rewrite Hnlen in HLp, Hbodk.
assert (HLp64 : 0 <= Lp < 2 ^ 64) by (clear - HLp Hbod0 Hbodk Hkr Hp4096 Hpce Hrq C1; lia).
assert (HLpk : Lp - k = e_n g - m_cur g (S i)).
{ unfold m_cur. fold inp. rewrite Hcs. clear - HLp. lia. }
(* the environment: atoms 32 .. 36 *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 nrec; Z_to_bv 64 cur; Z_to_bv 64 Lp; Z_to_bv 64 (Z.of_nat i);
  Z_to_bv 64 sh])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 nrec)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 cur)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Lp)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat i))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 sh)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 4)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U36 : bv_unsigned (ew E 36) = sh).
{ rewrite E36. apply unsigned_lit_small. clear - Hsh1 C1. lia. }
(* the symbolic state at 0x81598 *)
assert (HS : st_ok_pi SEGS VAL E d6_ss
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xe24)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold d6_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d6_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
      * apply (chunk_ok_val SEGS E _ mf 96 8 (SOff 32 0) nrec);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hnr; lia | lia | exact V96n].
      * apply (chunk_ok_val SEGS E _ mf 112 8 (SOff 33 0) cur);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hcur64 | lia | exact V112].
      * apply (chunk_ok_val SEGS E _ mf 120 8 (SOff 34 0) Lp);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact HLp64 | lia | exact V120].
      * apply (chunk_ok_val SEGS E _ mf 128 8 (SOff 35 0) (Z.of_nat i));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hi64; lia | lia | exact V128].
      * destruct Hfix as (_ & _ & _ & _ & _ & _ & _ & _ & _ & V160).
        apply (chunk_ok_val SEGS E _ mf 160 8 (SOff 36 0) sh);
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hsh1 C1; lia | lia | exact V160].
    + unfold d6_sh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U36. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) (sh + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d6_mf, d6_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U36.
    right. clear - Hsh1 Hmf0. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0xe24)) with (Z_to_bv 64 (BASE + 0xe24)).
(* ---- run 1: 0x81598 .. the free call at 0x815d4 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold d6_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold d6_mf, d6_sh in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  [lia|].
  rewrite U36 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
(* what run 1 kept: every byte outside the shadow window *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 4 <= a < sh + 19) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => sh + 4 <= x < sh + 19) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold d6_ss, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U9 in Hr; clear - Hr; lia | rewrite U36 in Hr; clear - Hr; lia]. }
clear HF HFr HG.
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
rewrite (EE 27%nat 27%bv eq_refl), R27 in R10. rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2.
rewrite (EE 3%nat 3%bv eq_refl), Rgp in R3. rewrite (EE 4%nat 4%bv eq_refl), Rtp in R4.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in R8.
pmkst HS. rewrite (pal_free B TL).
(* the free's premises *)
assert (Hinpl : In (pl, k) (ablocks B ly2 S2)).
{ destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). left. reflexivity. }
assert (HnotE : ~ In (pl, k) (ablocks B (e_ly g) (e_S g))).
{ intros Hin. destruct Hbl as [Hperm _]. apply in_split in Hin as (l1 & l2 & El).
  assert (Hp2 : Permutation (ablocks B ly2 S2) ((pl, k) :: (pl, k) :: l1 ++ l2)).
  { eapply Permutation_trans; [exact Hperm|]. cbn [app]. apply perm_skip. rewrite El.
    apply Permutation_sym, Permutation_middle. }
  pose proof (sep_blocks_perm SEGS B LAWS ly2 S2 W2 mem2 md2 (pl, k) (pl, k) (l1 ++ l2) HAR2 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos k ltac:(lia)).
  clear - Hd H. lia. }
assert (Hnev : st_nev S2 < EV_MAX).
{ unfold EV_LLVMF in HEV. clear - Hnev2 Hnev0 HEV Hi64. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
assert (MOKf : mo_ok MT S2 (mo_free MT)).
{ apply (mo_ok_le MT MTL S2 (mo_free MT) ((EV_LLVMF - (4 * Z.of_nat i + 3)) * (mo_malloc MT 256 + mo_free MT)) MOK).
  unfold EV_LLVMF. clear - HM0 HF0 Hi64. nia. }
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite R2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Ura : raZ (ms_regs ms) = BASE + 0xe64).
{ unfold raZ. rewrite R1. apply unsigned_lit_small. clear - HBASE. lia. }
(* the call chain: the entry's frame record at sp0 on top of the entry's own (empty) chain, or nothing when sp0
   is within 16 bytes of the stack's top *)
assert (HCH : exists ch, chain_pre ly2 (aview SEGS (w_H W2) (ms_mem ms)) (ms_regs ms) ch /\
  (ch = [] \/ ch = [(sp0, RA_LLVMF, s0Z (e_regs g))])).
{ assert (Ura4 : 4096 <= raZ (ms_regs ms)) by (rewrite Ura; clear - HBLO; lia).
  change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; reflexivity].
    eapply (achain_chain_pre ly2 _ mf sp0); [| rewrite Usp; clear - Hmf0; lia | exact Us0 | exact Ura4].
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
    pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
    pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply (achain_push ly2 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
    + rewrite ETop. clear - Htop1 H47. lia.
    + intros a Ha. apply F1; clear - Ha Hceil Hslo HSTK' Has; lia.
    + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
      apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 8) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
      intros kk Hkk. apply KEEP1; clear - Hkk Hmf0 Hmfb Hsh1 H47 Hshi C1; lia.
    + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
      apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 (ms_mem ms) (sp0 - 16) (sp0 - 16) 8 (s0Z (e_regs g)));
      [|exact Vs0].
      intros kk Hkk. apply KEEP1; clear - Hkk Hmf0 Hmfb Hsh1 H47 Hshi C1; lia.
    + rewrite <- Hraz. exact Hra4.
    + clear - Hceil Hslo HSTK' Has. lia.
    + clear - Hsp0al. lia.
    + exact Hlt.
    + clear - Hmfb. lia.
  - exists []. split; [|left; reflexivity].
    eapply (achain_chain_pre ly2 _ mf sp0 []); [| rewrite Usp; clear - Hmf0; lia | exact Us0 | exact Ura4].
    left. split; [right; left; exact Hge | reflexivity]. }
destruct HCH as (ch & Hchain & Hchs).
(* ---- the free of the payload copy, 0x815d4 ---- *)
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W2 (ms_regs ms) (ms_mem ms) LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i + 3) pl k (mf - sp0)
    (Z_to_bv 64 (BASE + 0xe64)) ch HJ Hinpl).
  - exact R10.
  - rewrite Usp. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - clear - Hmfb HSTK'. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hnev.
  - exact Hchain.
  - destruct Hchs as [-> | ->].
    + eapply (llvmf_univ_call0 B _ (LLVMF_FREE_CTX RA_LLVMF)); [exact HUMF|].
      rewrite Ura. unfold LLVMF_FREE_CTX. apply in_or_app. right. apply in_map_iff.
      exists 0xe64. split; [reflexivity|]. unfold LLVMF_FREE_RAS. cbn [In].
      repeat (first [left; reflexivity | right]).
    + eapply (llvmf_univ_call B RA_LLVMF _ (LLVMF_FREE_CTX RA_LLVMF)); [exact HUMF|].
      rewrite Ura. unfold LLVMF_FREE_CTX. apply in_or_app. left. apply in_map_iff.
      exists 0xe64. split; [reflexivity|]. unfold LLVMF_FREE_RAS. cbn [In].
      repeat (first [left; reflexivity | right]).
  - intros Hin. exfalso. exact (HnotE Hin).
  - exact MOKf. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & Ebl & Ebl2) & Hfrs3 & HK3 & MLE3 & HJf).
clear HJf.
(* back at 0x815d8: only the machine-frame region survives the call *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact U9 | clear - Hmfb; lia
  | clear - Hmfb HSTK' Has; lia | clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
(* ---- run 2: 0x815d8 .. 0x815ec ---- *)
paj_run_to_sh RUNTOP HS HJ3 0xe78.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia | apply awr_ok_nil]. }
(* what run 2 kept: everything (its only region is read-only) *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ (w_H W3) mem3 (ms_mem ms0) (fun _ => False) HFr); [|exact Ha|intros []].
  intros bb wlo whi aa Hin Hr. cbn in Hin. destruct Hin as [Eq | []]. injection Eq as <- <- <-. clear - Hr. lia. }
clear HF HFr HG.
(* what the free kept *)
pose proof HK3 as (K1 & K2 & _ & K4 & _).
assert (STACKK : forall a, mf <= a < sp0 -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite KEEP3 by (clear - Ha Hmf0 Hmfb Hshi H47 C1; lia).
  rewrite K1 by (clear - Ha Hmf0 Hmfb Hshi H47 C1; lia).
  apply KEEP1; clear - Ha Hmf0 Hsh1 Hmfb Hshi H47 C1; lia. }
assert (VMS : forall a (n : nat) v, mf <= a -> a + Z.of_nat n <= sp0 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 (ms_mem ms0)) a n v).
{ intros a n v H1 H2 Hv. apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem ms0) a a n v); [|exact Hv].
  intros kk Hkk. apply STACKK. clear - H1 H2 Hkk. lia. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 pl k HAR2 Hinpl) as (_ & Hpl4096 & Hplce & Hplapp & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 pl k 4 pos HAR2 Hinpl Hin4) as Hdf.
unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
assert (FRAMEK : forall a, (SF <= a < SF + 1024 \/ sh <= a < sh + 4 \/ sh + 19 <= a < sh + 128) ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha.
  rewrite KEEP3 by (clear - Ha Hsh1 HSF0 HSF1 C1; lia).
  rewrite (K4 4 pos a Hin4).
  - apply KEEP1; [clear - Ha Hsh1 HSF0 HSF1 C1; lia|].
    intros Hw. destruct Ha as [Ha | [Ha | Ha]]; [|clear - Ha Hw; lia | clear - Ha Hw; lia].
    apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp | | exact Ha].
    rewrite Esh in Hw. unfold SHADOW_OFF in Hw. clear - Hw. lia.
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. fold sh.
    destruct Ha as [Ha | [Ha | Ha]]; [left | right | right]; clear - Ha; lia.
  - cbn beta. intros Hp.
    destruct Ha as [Ha | [Ha | Ha]]; [clear - Ha Hp Hdf; lia | |];
    (apply (fshadow_not_app SF 128 pl (req_size k) a); [exact HSF0 | clear - HSF1 C1; lia | exact Hplapp | | exact Hp];
     rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia). }
assert (VMF : forall off (n : nat) v, 0 <= off -> off + Z.of_nat n <= 1024 ->
  val_mem SEGS (rd W2 mem2) (SF + off) n v -> val_mem SEGS (rd W3 (ms_mem ms0)) (SF + off) n v).
{ intros off n v H0 H1 Hv.
  apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem ms0) (SF + off) (SF + off) n v); [|exact Hv].
  intros kk Hkk. apply FRAMEK. left. clear - H0 H1 Hkk. lia. }
assert (GF : forall off l, 0 <= off -> off + Z.of_nat (length l) <= 1024 ->
  garr8 SEGS (rd W2 mem2) (SF + off) l -> garr8 SEGS (rd W3 (ms_mem ms0)) (SF + off) l).
{ intros off l H0 H1 Hg. apply (d6_garr8_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem ms0) _ l); [|exact Hg].
  intros kk Hkk. apply FRAMEK. left. clear - H0 H1 Hkk. lia. }
assert (SHF : forall off n, 152 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_zero W2 mem2 (SF + off) n -> sh_zero W3 (ms_mem ms0) (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_zero in *.
  apply (d6_zero_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply FRAMEK. right; right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn Hii HSF64. lia. }
assert (SHB : forall off n, 152 <= off -> off + n <= 1024 -> 0 <= n ->
  sh_blk W2 mem2 (SF + off) n -> sh_blk W3 (ms_mem ms0) (SF + off) n).
{ intros off n H0 H1 Hn Hz. unfold sh_blk in *.
  apply (d6_block_shadow_moved (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W3) (ms_mem ms0)) SHADOW_OFF (SF + off) n);
  [|exact Hz].
  intros ii Hii. apply FRAMEK. right; right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn Hii HSF64. lia. }
(* the input block: kept (FP is empty and the block is not the freed one) *)
assert (HINB : bytes_at8 W3 (ms_mem ms0) (e_p g) inp).
{ unfold bytes_at8 in *. apply (d6_garr8_moved SEGS (w_H W2) (w_H W3) mem2 (ms_mem ms0) _ _); [|exact Hinb].
  intros j Hj. rewrite length_map in Hj. rewrite <- Hlen in Hj.
  assert (Hne : (e_p g, e_n g) <> (pl, k)) by (intros Heq; rewrite Heq in Hpn; exact (HnotE Hpn)).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) pl k HAR2 Hpn2 Hinpl Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  rewrite KEEP3 by (clear - Hj Hpce Hp4096 Hrq C1; lia).
  rewrite (K2 (e_p g) (e_n g) j Hpn2); [| clear - Hj Hrq; lia | cbn beta; clear - Hj Hrq Hd; lia].
  apply KEEP1; [clear - Hj Hpce Hp4096 Hrq C1; lia|].
  intros Hw. apply (fshadow_not_app SF 128 (e_p g) (req_size (e_n g)) (e_p g + j));
  [exact HSF0 | clear - HSF1 C1; lia | exact Hpapp | | clear - Hj Hrq; lia].
  rewrite Esh in Hw. unfold SHADOW_OFF in Hw. clear - Hw. lia. }
(* the registers at 0x815ec *)
prreg HS (14%bv : bv 5) Q14. prreg HS (10%bv : bv 5) Q10. prreg HS (15%bv : bv 5) Q15. prreg HS (23%bv : bv 5) Q23.
prreg HS (25%bv : bv 5) Q25. prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9.
prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (24%bv : bv 5) Q24.
rewrite E34, (EE 22%nat 22%bv eq_refl), R22 in Q24.
change (w64 k) with (Z_to_bv 64 k) in Q24.
rewrite d6_md_neg, alu64_add_lit in Q24.
rewrite E35 in Q14. rewrite d6_aluw_inc in Q14 by (clear - Hi64; lia).
rewrite E32 in Q10. rewrite E36 in Q23. rewrite E33 in Q25.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
(* ---- the boundary at 0x815ec ---- *)
apply SRr_ret.
unfold inv_D6_end, acut. pmkst HS.
exists ly3, S3, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3).
split; [reflexivity|].
split; [replace (4 * Z.of_nat i + 4) with (4 * Z.of_nat i + 3 + 1) by (clear; lia); exact HJ3|].
split; [rewrite Hfrs3; exact Hfrs|].
split; [unfold EV_LLVMF; clear - Hi64; lia|].
split.
{ unfold MEV. eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE3)|]. clear - HM0 HF0. nia. }
split.
{ unfold MEV. apply (mo_ok_step MT MTL S2 S3 (mo_free MT)); [|exact MLE3].
  apply (mo_ok_le MT MTL _ _ _ MOK). unfold EV_LLVMF. clear - HM0 HF0 Hi64. nia. }
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Q3|]. split; [exact Q4|].
  repeat (split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | assumption]|]).
  split; [apply VMF; [clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
unfold sh_reg, rec_live, mf_fixed, mf_before, mf_again, mf_id, cur_at, id_at, hw_live, hw_mem, hblocks.
change (e_sp0 g) with sp0. change (SFa g pos) with SF.
split; [exact Hi|].
split; [rewrite Q14; unfold w64; f_equal; clear - Hi64; lia|].
split; [rewrite Q10; reflexivity|].
split; [exact Q15|].
split; [rewrite Q24; unfold w64; f_equal; clear - HLpk; lia|].
split; [rewrite Q23; reflexivity|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96n]|].
split.
{ destruct Hfix as (F32 & F48 & F56 & F72 & F80 & F88 & F104 & F136 & F144 & F160).
  repeat split; apply VMS; first [assumption | clear - Hmfb; lia]. }
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hbef]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmag]|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]|].
split.
{ split; [rewrite Q25; reflexivity | exact Hcur]. }
split.
{ destruct Hid as (Hidb & Hidz & Hids). change (SFa g pos) with SF in Hidb, Hidz, Hids. split; [|split].
  - apply GF; [unfold V_id; clear; lia | | exact Hidb].
    rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE. clear; lia.
  - apply SHF; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidz].
  - apply SHB; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hids]. }
split.
{ destruct Hhw as ((Hhb & Hhz & Hhs) & Hh0 & Hh24). change (SFa g pos) with SF in Hhb, Hhz, Hhs, Hh0.
  split; [split; [|split]|].
  - replace (SF + V_hw + 4) with (SF + 436) in * by (unfold V_hw; clear; lia).
    apply GF; [clear; lia | | exact Hhb]. rewrite length_map. unfold m_hwb. rewrite d6_hwb_length. clear; lia.
  - apply SHF; [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhz].
  - apply SHB; [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhs].
  - split; [apply VMF; [unfold V_hw; clear; lia | unfold V_hw; clear; lia | exact Hh0]|].
    apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hh24]. }
split; [|constructor]. rewrite Ebl2. cbn [app]. destruct Hbl as [Hperm _]. rewrite Ebl in Hperm.
cbn [app] in Hperm. apply (Permutation_cons_inv (a := (pl, k))).
eapply Permutation_trans; [apply Permutation_middle | exact Hperm].
Qed.

(* D6 +0xe24..+0xe78, 21 slots: the statement of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v. *)
Theorem seg_D6 : seg_D6_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof. unfold seg_D6_stmt. intros g pos mf i pl W2 c2 H. exact (d6_run g pos mf i pl W2 c2 H). Qed.
Print Assumptions seg_D6.

Check (seg_D6 : seg_D6_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
End c.
End b.
End a.
