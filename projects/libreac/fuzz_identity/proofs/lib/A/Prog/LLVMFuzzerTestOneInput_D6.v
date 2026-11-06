(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-118, for libreac/fuzz_identity's ASan build (lib/A). The same text
   also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:141-143. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_A.v; 398 of its 470 lines of code are new or changed and 508 lines of the source are left out. *)
(* Segment D6 of LLVMFuzzerTestOneInput's ASan walk: the record's tail, 0x813b4..0x81400 (19 slots).
   seg_D6 of lib/A/Prog/LLVMFuzzerTestOneInput_inv.v: from the join inv_tail to inv_D6_end, the slot of the loop test.

   The code (BASE + 0xca8 .. BASE + 0xcf4):
     0x813b4 add s10,s10,s6       the cursor moves past the payload: x26 = p + rec_body i + rec_k i
     0x813b8 ld a0,144(s1)        the length left after the header, n - rec_body i
     0x813bc sub s2,a0,s6         x18 = n - rec_c (S i)
     0x813c0 li a0,-8
     0x813c4 .. 0x813e8           ten shadow stores of 0xf8 at s3 + 8, 14..18, 4..7 (`before` and `again` poisoned)
     0x813ec mv a0,s9
     0x813f0 jal free             the payload copy is freed (afree04_rule, through YC85.afree04_sub)
     0x813f4 addiw s4,s5,1        x20 = i + 1
     0x813f8 ld a0,112(s1)        x10 = nrec
     0x813fc li s5,6              x21 = 6
   Both runs are plain runs (no checked access). The first writes only the frame's shadow window [s3 + 4, s3 + 19),
   which the journal's own frame (4, pos) covers; the second writes nothing. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
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
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
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

(* The symbolic state at 0x813b4. Region 0: the two machine-frame words the segment loads, base s1 (atom 9):
   mf+112 = nrec (atom 33) and mf+144 = n - rec_body i (atom 32); read-only. Region 1: the frame's shadow, base s3
   (atom 19), writable on the cells the ten stores hit. *)
Definition d6_mf : YP09.region := YP09.mkRegion (Some 9%nat) 112 152 112 112
  [YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
Definition d6_sh : YP09.region := YP09.mkRegion (Some 19%nat) 0 128 4 19 [].
Definition ss_d6 : sstate := mkSS 0xca8 sr_atoms [d6_mf; d6_sh] None (mkFacts [] [] []).

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
intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
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
Lemma d6_md_neg : forall x : Z, mul_div M_MUL (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (- x).
Proof.
intros x. apply bv_eq. cbn [mul_div]. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.mul_mod by lia. f_equal. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
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
(* What this segment needs, each as the contract's Section states it (LLVMFuzzerTestOneInput.v, _inv.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
(* The free's call trace, as the contract states it (LLVMFuzzerTestOneInput.v HUMF); this segment's free returns
   to BASE + 0xce8, an element of LLVMF_FREE_RAS. *)
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

Theorem seg_D6_holds :
  seg_D6 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none ameta_inv
    arodata_okS.
Proof.
intros g pos mf i pl W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & Rs3 & V80 & V192 & V176 & Vra & Vs0 &
  V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80b & V88 & V96 & V104 & Vmf24 & Vflag & HPRE & Hfds & Hfs & Hinb).
destruct HP as ((Hi & Hbl & Hpl & Hid & V112 & Hfix & Hmid & Hmag & V136 & V144 & V152 & V160 & Rk & Hcur) &
  Hhw & R26 & R24 & R25 & R21).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
(* the entry state *)
pose proof HPRE as (HFN & Hraz & _ & _ & Hinp & Hlen & _ & _ & Hnev0 & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
(* the journal at the start *)
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _ & _ & ETop & _).
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
set (bod := SlotModel.rec_body inp i) in *.
set (nrec := SlotModel.nrec inp) in *.
pose proof (SlotModel.rec_bounds inp i) as (_ & Hbod0 & Hbodk & _ & _ & Hcs).
pose proof (SlotModel.rec_k_range inp i) as Hkr. fold k in Hkr.
pose proof (SlotModel.nrec_range inp) as Hnr. fold nrec in Hnr.
fold k bod in Hbodk, Hcs.
assert (Hnlen : SlotModel.nlen inp = e_n g) by (unfold SlotModel.nlen; rewrite Hlen; reflexivity).
assert (Hi64 : (Z.of_nat i < 64)%Z).
{ unfold m_nrec, SlotModel.nrecn in Hi. fold inp nrec in Hi. clear - Hi Hnr. lia. }
assert (Hmc : m_cur g (S i) = bod + k) by (unfold m_cur; fold inp; exact Hcs).
(* the environment: atom 32 = n - rec_body i (mf+144), atom 33 = nrec (mf+112) *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (e_n g - bod); Z_to_bv 64 nrec])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (e_n g - bod))
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 nrec)
  by (rewrite HE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (ER : regs_ok E sr_atoms regs2) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (AGE : env_agree 32 (Ereg regs2 [Z_to_bv 64 (e_n g - bod); Z_to_bv 64 nrec]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U9 : bv_unsigned (ew E 9) = mf).
{ rewrite (EE 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U19 : bv_unsigned (ew E 19) = sh).
{ rewrite (EE 19%nat 19%bv eq_refl), Rs3. apply unsigned_lit_small. clear - Hsh1 C1. lia. }
(* the symbolic state at 0x813b4 *)
assert (HS : st_ok_pi SEGS VAL E ss_d6
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0xca8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_d6. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold d6_mf, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi; unfold sp0 in *; lia|].
      split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ mf 112 8 (SOff 33 0) nrec);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hnr; lia | lia | exact V112].
      * apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 32 0) (e_n g - bod));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - Hbodk Hbod0 Hkr Hnlen Hinp; rewrite Hnlen in Hbodk; destruct Hinp as [[H0 _] | [[_ Hn] _]]; lia
        | lia | exact V144].
    + unfold d6_sh, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly2 S2 W2 mem2 md2 (4 * Z.of_nat i + 3) (sh + o) HJ ltac:(
        right; right; right; exists 4, pos; split; [left; reflexivity|]; right;
        unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; fold sh; clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, d6_mf, d6_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    right. clear - Hsh1 Hmf0. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0xca8)) with (Z_to_bv 64 (BASE + 0xca8)).
(* ---- run 1: 0x813b4 .. the free call at 0x813f0 ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold ss_d6 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; unfold d6_mf, d6_sh in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  [lia|].
  rewrite U19 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. fold sh. clear - Ha. lia. }
(* what run 1 kept: every byte outside the shadow window *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 4 <= a < sh + 19) ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => sh + 4 <= x < sh + 19) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold ss_d6, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U9 in Hr; clear - Hr; lia | rewrite U19 in Hr; clear - Hr; lia]. }
clear HF HFr HG.
(* the registers at the call *)
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (8%bv : bv 5) R8.
rewrite (EE 25%nat 25%bv eq_refl), R25 in R10. rewrite (EE 2%nat 2%bv eq_refl), Rsp in R2.
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
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hn2 & _).
  unfold EV_LLVMF in HEV. clear - Hn2 Hnev0 HEV Hi64. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
assert (MOKf : mo_ok MT S2 (mo_free MT)).
{ apply (mo_ok_le MT MTL S2 (mo_free MT) ((EV_LLVMF - (4 * Z.of_nat i + 3)) * (mo_malloc MT 256 + mo_free MT)) MOK).
  unfold EV_LLVMF. clear - HM0 HF0 Hi64. nia. }
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite R2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Us0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Ura : raZ (ms_regs ms) = BASE + 0xce8).
{ unfold raZ. rewrite R1. apply unsigned_lit_small. clear - HBASE. lia. }
(* the call chain: the entry's frame record at sp0 on top of the entry's own chain *)
assert (HCH : exists ch, chain_pre ly2 (aview SEGS (w_H W2) (ms_mem ms)) (ms_regs ms) ch /\
  (ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)])).
{ assert (Ura4 : 4096 <= raZ (ms_regs ms)) by (rewrite Ura; clear - HBLO; lia).
  change (spZ (e_regs g)) with sp0 in Hch0.
  assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
  { apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
  destruct (Z_lt_le_dec sp0 (ly_top ly2 - 16)) as [Hlt | Hge].
  - exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; exists sp0, (s0Z (e_regs g)); reflexivity].
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
(* ---- the free of the payload copy, 0x813f0 ---- *)
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W2 (ms_regs ms) (ms_mem ms) LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 _ (4 * Z.of_nat i + 3) pl k (mf - sp0)
    (Z_to_bv 64 (BASE + 0xce8)) ch HJ Hinpl).
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
  - destruct Hchs as [Ech | (fp & v & Ech)]; rewrite Ech.
    + eapply llvmf_univ_call0; [exact HUMF|]. rewrite Ura. unfold LLVMF_FREE_CTX, LLVMF_FREE_RAS.
      apply in_or_app. right. apply in_map_iff. exists 0xce8. split; [reflexivity|].
      cbn [In]. right. left. reflexivity.
    + eapply llvmf_univ_call; [exact HUMF|]. rewrite Ura. unfold LLVMF_FREE_CTX, LLVMF_FREE_RAS.
      apply in_or_app. left. apply in_map_iff. exists 0xce8. split; [reflexivity|].
      cbn [In]. right. left. reflexivity.
  - intros Hin. exfalso. exact (HnotE Hin).
  - exact MOKf. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & Ebl & Ebl2) & Hfrs3 & HK3 & MLE3 & HJf).
clear HJf.
(* back at 0x813f4: only the machine-frame region survives the call *)
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0%nat] HS3.
match type of HS3 with ?Q -> _ => assert (HQ : Q); [|specialize (HS3 HQ); clear HQ] end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  eapply (region_kept_stack_aj SEGS B); [exact HK3 | exact HJ3 | exact U9 | clear - Hmfb; lia
  | clear - Hmfb HSTK' Has; lia | clear - Hmfb; lia | clear - Hmfb; lia | clear - Hmfb; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs3) CLOB) HEI ltac:(cbv; lia)) as HEI3.
(* ---- run 2: 0x813f4 .. 0x81400 ---- *)
paj_run_to_sh RUNTOP HS HJ3 0xcf4.
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
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct Hbl as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). right. exact Hine. }
  assert (Hne : (e_p g, e_n g) <> (pl, k)) by (intros Heq; rewrite Heq in Hine; exact (HnotE Hine)).
  pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) pl k HAR2 Hine2 Hinpl Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (_ & Hp4096 & Hpce & Hpapp & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  rewrite KEEP3 by (clear - Hj Hpce Hp4096 Hrq C1; lia).
  rewrite (K2 (e_p g) (e_n g) j Hine2); [| clear - Hj Hrq; lia | cbn beta; clear - Hj Hrq Hd; lia].
  apply KEEP1; [clear - Hj Hpce Hp4096 Hrq C1; lia|].
  intros Hw. apply (fshadow_not_app SF 128 (e_p g) (req_size (e_n g)) (e_p g + j));
  [exact HSF0 | clear - HSF1 C1; lia | exact Hpapp | | clear - Hj Hrq; lia].
  rewrite Esh in Hw. unfold SHADOW_OFF in Hw. clear - Hw. lia. }
(* the registers at 0x81400 *)
prreg HS (20%bv : bv 5) Q20. prreg HS (10%bv : bv 5) Q10. prreg HS (21%bv : bv 5) Q21. prreg HS (24%bv : bv 5) Q24.
prreg HS (26%bv : bv 5) Q26. prreg HS (18%bv : bv 5) Q18. prreg HS (2%bv : bv 5) Q2. prreg HS (9%bv : bv 5) Q9.
prreg HS (8%bv : bv 5) Q8. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (19%bv : bv 5) Q19.
rewrite (EE 21%nat 21%bv eq_refl), R21 in Q20. unfold w64 in Q20. rewrite d6_aluw_inc in Q20 by (clear - Hi64; lia).
rewrite (EE 22%nat 22%bv eq_refl), (EE 26%nat 26%bv eq_refl), Rk, R26 in Q26. unfold w64 in Q26.
rewrite alu64_add_lit in Q26.
rewrite (EE 22%nat 22%bv eq_refl), Rk, E32 in Q18. unfold w64 in Q18. rewrite d6_md_neg, alu64_add_lit in Q18.
rewrite E33 in Q10. rewrite (EE 24%nat 24%bv eq_refl), R24 in Q24.
rewrite (EE 2%nat 2%bv eq_refl), Rsp in Q2. rewrite (EE 9%nat 9%bv eq_refl), Rs1 in Q9.
rewrite (EE 8%nat 8%bv eq_refl), Rs0 in Q8. rewrite (EE 3%nat 3%bv eq_refl), Rgp in Q3.
rewrite (EE 4%nat 4%bv eq_refl), Rtp in Q4. rewrite (EE 19%nat 19%bv eq_refl), Rs3 in Q19.
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Efd Efs].
(* ---- the boundary inv_D6_end at 0x81400 ---- *)
apply SRr_ret.
unfold inv_D6_end, acut. pmkst HS.
exists ly3, S3, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy md3) mat0 md3).
split; [reflexivity|].
split; [replace (4 * Z.of_nat i + 4) with (4 * Z.of_nat i + 3 + 1) by (clear; lia); exact HJ3|].
split; [rewrite Hfrs3; exact Hfrs|].
split; [unfold EV_LLVMF; clear - Hi64; lia|].
split.
{ eapply (mo_le_mono MT MTL); [exact (mo_le_trans MT MTL _ _ _ _ _ MLE MLE3)|]. clear - HM0 HF0. nia. }
split.
{ apply (mo_ok_step MT MTL S2 S3 (mo_free MT)); [|exact MLE3].
  apply (mo_ok_le MT MTL _ _ _ MOK). unfold EV_LLVMF. clear - HM0 HF0 Hi64. nia. }
split.
{ unfold ecommon. change (e_sp0 g) with sp0. change (SFa g pos) with SF.
  split; [exact Q2|]. split; [exact Q9|]. split; [exact Q8|].
  split; [exact Hmfb|]. split; [exact Hmf32|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Q19|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V80]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V176]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vra]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vs0]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V24]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V32]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V40]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V48]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V56]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V72]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V80b]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V88]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V96]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V104]|].
  split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Vmf24]|].
  split; [apply VMF; [clear; lia | clear; lia | exact Vflag]|].
  split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  exact HINB. }
unfold rec_live, mf_fixed, mf_id, mf_again, cur_at, id_at, hw_at, hblocks.
change (e_sp0 g) with sp0. change (SFa g pos) with SF.
split; [exact Hi|].
split; [rewrite Q20; unfold w64; f_equal; clear - Hi64; lia|].
split; [rewrite Q10; reflexivity|].
split; [rewrite Q21; reflexivity|].
split; [rewrite Q24; reflexivity|].
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V112]|].
split.
{ destruct Hfix as (F32 & F40 & F48 & F72 & F88 & F96 & F104 & F120 & F128).
  repeat split; apply VMS; first [assumption | clear - Hmfb; lia]. }
split.
{ split; [rewrite Q26, Hmc; unfold w64; f_equal; ring|].
  split; [rewrite Q18, Hmc; unfold w64; f_equal; ring|].
  exact Hcur. }
split.
{ destruct Hid as (Hidb & Hidz & Hidk). change (SFa g pos) with SF in Hidb, Hidz, Hidk. split; [|split].
  - apply GF; [unfold V_id; clear; lia | | exact Hidb].
    rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE. clear; lia.
  - apply SHF; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidz].
  - apply SHB; [unfold V_id; clear; lia | unfold V_id, N_id; clear; lia | unfold N_id; clear; lia | exact Hidk]. }
split.
{ destruct Hhw as (Hhw1 & Hhw2 & Hhw3 & Hhw4). change (SFa g pos) with SF in Hhw1, Hhw2, Hhw3, Hhw4.
  split; [|split; [|split]].
  - apply VMF; [unfold V_hw; clear; lia | unfold V_hw; clear; lia | exact Hhw1].
  - replace (SF + V_hw + 4) with (SF + 436) in * by (unfold V_hw; clear; lia).
    apply GF; [clear; lia | | exact Hhw2]. rewrite length_map. unfold m_hwb. rewrite d6_hwb_length. clear; lia.
  - apply SHF; [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhw3].
  - apply SHB; [unfold V_hw; clear; lia | unfold V_hw, N_hw; clear; lia | unfold N_hw; clear; lia | exact Hhw4]. }
split.
{ split; [|constructor]. rewrite Ebl2. cbn [app]. destruct Hbl as [Hperm _]. rewrite Ebl in Hperm.
  cbn [app] in Hperm. apply (Permutation_cons_inv (a := (pl, k))).
  eapply Permutation_trans; [apply Permutation_middle | exact Hperm]. }
split; [apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmid]|].
apply VMS; [clear - Hmfb; lia | clear - Hmfb; lia | exact Hmag].
Qed.

End c.
End b.
End a.
