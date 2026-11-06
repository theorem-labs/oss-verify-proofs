(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1527-1530,
   1556-1561, for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_D4.v, with its module paths, module names, addresses and numbers changed; 1171 of its 1273 lines of code are new or changed and 836 lines of the source are left out. *)
(* Segment B of LLVMFuzzerTestOneInput's ASan+UBSan walk (fuzz_identity.asan-ubsan, BASE + 0x280 .. BASE + 0x370,
   0x809f4 .. 0x80ae4): the eight start-up checks of the harness, each a call on a NULL or empty argument.
     0x809f4..0x80a10  s3 = &id (SF+352); id's shadow unpoisoned (0x809f8..0x80a0c: 0, 0, 0, 0, 6)
     0x80a14           reac_identity_init(NULL): the callee's NULL path (0x83a84..0x83aa4) is walked in line; its
                       contract asks the 38 bytes to lie in a block or a frame, which address 0 does not
     0x80a18..0x80a20  mf+184 = &id; reac_identity_init(&id)                          (HINIT)
     0x80a34, 0x80a54  reac_identity_ingest(NULL, 0, 0, 0), (&id, 0, NULL, 4): both refused, -1 (HING)
     0x80a6c           reac_identity_fw_str(0, NULL, 8): -1                              (HFWS)
     0x80a8c           reac_identity_reac_ver_str(0, 0, 0, NULL, 20): -1                (HVS)
     0x80aac           reac_box_catalogue_defect(NULL, 8, 8, "x"): 0                     (HCATD)
     0x80ab8           reac_box_family_of(NULL): 0                                       (HFAM, famof_tbl from HIMG)
     0x80ac4..0x80ae0  s3 = &hw (SF+432), hw's two shadow bytes (0, 4), the memset's arguments.
   Every abort branch (to 0x82614) is decided by the callee's post: the walk pins a0 to the value the post gives.
   The walk is split at the return of each call (b_st, a boundary of this file only): one lemma per call. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
reac_box_catalogue_defect reac_box_family_of reac_identity_fw_str reac_identity_init reac_identity_ingest
reac_identity_reac_ver_str.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel reac_identity_ingest_c
reac_box_catalogue_defect_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The keep set of a step: the machine-frame slots and saved words ecommon states, the frame's flag word, id and
   its shadow's five cells, and mf+184 (&id). *)
Definition b_ec_at (sp0 SF mf a : Z) : Prop :=
(mf + 16 <= a < mf + 24) \/ (mf + 64 <= a < mf + 72) \/ (mf + 168 <= a < mf + 176) \/ (mf + 192 <= a < mf + 200) \/
(sp0 - 104 <= a < sp0) \/ (SF + 1016 <= a < SF + 1024).
Definition b_kz (sp0 SF mf a : Z) : Prop :=
b_ec_at sp0 SF mf a \/ (mf + 184 <= a < mf + 192) \/ (SF + 352 <= a < SF + 390) \/
(SHADOW_OFF + SF / 8 + 44 <= a < SHADOW_OFF + SF / 8 + 49).

(* Atom 32 of every start state is the frame's address SF. *)
Definition b_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).
Lemma b_sh_off : forall SF c, SF mod 8 = 0 -> shadow_of_addr SHADOW_OFF (SF + c) = SHADOW_OFF + SF / 8 + c / 8.
Proof.
intros SF c H. unfold shadow_of_addr. rewrite <- Z.add_assoc. f_equal.
rewrite (Z.div_mod SF 8) at 1 by lia. rewrite H, Z.add_0_r.
replace (8 * (SF / 8) + c) with (c + (SF / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition b_E (regs : bvmap 5 word) (SF : Z) : env := Eimg (Ereg regs [Z_to_bv 64 SF]).

Lemma b_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem pc SF (rs : smem),
  regions_wf rs = true ->
  Forall (region_ok SEGS (b_E regs SF) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (b_E regs SF) rs ->
  st_ok_pi SEGS VAL (b_E regs SF) (b_ss pc rs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc SF rs Hwf Hrs Hpd. rewrite restrict_mkst_fx. unfold b_ss.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hrs | exact Hpd |].
unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact Logic.I.
Qed.
Lemma b_E_reg : forall regs SF n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (b_E regs SF) n = getr regs r.
Proof. intros regs SF n r Hn. unfold b_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma b_E_32 : forall regs SF, ew (b_E regs SF) 32 = Z_to_bv 64 SF.
Proof. intros regs SF. unfold b_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma b_E_img : forall regs SF, img_env VAL A_LIM (b_E regs SF).
Proof. intros regs SF. unfold b_E. apply Eimg_env. Qed.

(* What a preserved register set keeps. *)
Lemma b_pres : forall r r', aregs_preserved r r' ->
  getr r' 2 = getr r 2 /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 8 = getr r 8 /\
  getr r' 9 = getr r 9 /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 23 = getr r 23 /\
  getr r' 25 = getr r 25.
Proof.
intros r r' H.
repeat split; [apply (H 2) | apply (H 3) | apply (H 4) | apply (H 8) | apply (H 9) | apply (H 18) | apply (H 19)
  | apply (H 23) | apply (H 25)]; unfold acallee_saved; lia.
Qed.

Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section the contract and the boundary layer are stated in (LLVMFuzzerTestOneInput.v, _inv.v). *)
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)]).

(* ---- what the segment takes: LLVMFuzzerTestOneInput.v's Section hypotheses, with the contract's text ---------- *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PSIG : identb_prog_sig_ok (PI := PI).
Hypothesis MTL : ameter_laws MT.
Hypothesis HMT0 : forall s s' : astate, mo_le MT s s' 0.
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Variable G : list (Z * Z).
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Hypothesis HCATD : reac_box_catalogue_defect.treac_box_catalogue_defect_spec B G.
Hypothesis HFWS : reac_identity_fw_str.treac_identity_fw_str_spec B.
Hypothesis HINIT : reac_identity_init.treac_identity_init_spec B (BASE + AF_reac_identity_init).
Hypothesis HING : reac_identity_ingest.treac_identity_ingest_spec B.
Hypothesis HFAM : reac_box_family_of.treac_box_family_of_spec B.
Hypothesis HVS : reac_identity_reac_ver_str.treac_identity_reac_ver_str_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- the predicate between the calls: acut at k = 0 with what this segment carries ---------------------- *)
Definition b_car (g : ectx) (pos mf : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) : Prop :=
  id_at g pos 0 W2 mem2 /\ hblocks B g ly2 S2 [] /\ mf_id g pos mf W2 mem2 /\ sh_reg g pos regs2 /\
  getr regs2 18 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g).
Definition b_st (g : ectx) (pos mf pc : Z) (R : bvmap 5 word -> Prop) : world SEGS -> config -> Prop :=
  ACUT g pos mf 0 (BASE + pc) (fun ly2 S2 W2 regs2 mem2 md2 => b_car g pos mf ly2 S2 W2 regs2 mem2 /\ R regs2).

(* ---- the facts of a boundary a step uses ---------------------------------------------------------------- *)
Lemma b_prep : forall g pos mf ly2 S2 W2 regs2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> frames S2 = [(4, pos)] -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  (alloc_ceiling + 16400 <= mf /\ e_sp0 g <= 2 ^ 47 /\ mf mod 32 = 0 /\ e_sp0 g - 336 <= mf <= e_sp0 g - 320 /\
   e_sp0 g mod 16 = 0 /\ e_sp0 g - LLVMF_STK <= mf - 16400 /\ (mf - e_sp0 g) mod 16 = 0) /\
  (4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 32 = 0 /\
   frame_addr ly2 4 pos = SFa g pos /\ fs_frame_bytes 4 = 1024 /\ In (4, pos) (frames S2)).
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 k HJ HFR HEC.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstat & _).
pose proof Hstat as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HEC as (_ & _ & _ & Hmf & Hmf32 & _).
pose proof (asan_consts) as (C1 & _).
assert (ES : ASTACK = 16384) by reflexivity. assert (ESK : STK_LLVMF = 336 + 16 + ASTACK) by reflexivity.
assert (Efa : frame_addr ly2 4 pos = SFa g pos).
{ unfold SFa, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (F1 & F2 & F3).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (F32 & _).
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
rewrite Hfb, Efa in *.
split.
- assert (Hm16 : (mf - e_sp0 g) mod 16 = 0).
  { rewrite Zminus_mod, Hal16. pose proof (Z.div_mod mf 32 ltac:(lia)) as D. rewrite Hmf32, Z.add_0_r in D.
    replace (mf mod 16) with 0; [reflexivity|]. rewrite D. replace (32 * (mf / 32)) with ((2 * (mf / 32)) * 16) by lia.
    symmetry. apply Z_mod_mult. }
  unfold e_sp0 in *. clear - Hal16 Hstk0 Hceil Hslo Hshi H47 Hmf Hmf32 Hm16 HSTK ES ESK C1. repeat split; lia.
- exact (conj F1 (conj F2 (conj F3 (conj F32 (conj eq_refl (conj eq_refl Hin4)))))).
Qed.

(* The input block: kept by the journal from the entry (no heap block of the entry is gone, hblocks). *)
Lemma b_inp : forall g pos ly3 S3 W3 mem3 md3 k,
  EPRE g -> AJ g pos ly3 S3 W3 mem3 md3 k -> hblocks B g ly3 S3 [] -> bytes_at8 W3 mem3 (e_p g) (e_pl g).
Proof.
intros g pos ly3 S3 W3 mem3 md3 k HPRE HJ (Hperm & _).
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & Hinp & Hlen & Hgar & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
destruct Hinp as [[Hn0 _] | [Hn Hpin]].
- unfold bytes_at8. destruct (e_pl g) as [|x l]; [intros j Hj; cbn in Hj; lia | cbn in Hlen; lia].
- unfold bytes_at8. apply (garr8_frame SEGS _ _ (e_p g) _ Hgar). intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview SEGS).
  assert (Hin3 : In (e_p g, e_n g) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hpin).
  replace a with (e_p g + (a - e_p g)) by lia.
  apply (F2 (e_p g) (e_n g) (a - e_p g) Hpin Hin3).
  + unfold req_size. destruct (Z.eqb_spec (e_n g) 0); lia.
  + intros (r & Hr & _). destruct Hr.
Qed.

(* ecommon at a later state of the same journal, from the registers and the bytes it states. *)
Lemma b_ec_keep : forall g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3,
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  AJ g pos ly3 S3 W3 mem3 md3 k3 -> hblocks B g ly3 S3 [] ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  (forall a, b_ec_at (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  ECOMMON g pos mf ly3 S3 W3 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 k3 HEC HJ3 HB3 R2 R9 R8 R3 R4 KEEP.
assert (VK : forall a n v, (forall x, a <= x < a + Z.of_nat n -> b_ec_at (e_sp0 g) (SFa g pos) mf x) ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W3 mem3) a n v).
{ intros a n v Hx Hv. eapply (val_mem_kept SEGS); [|exact Hv]. intros kk Hk. apply KEEP. apply Hx. lia. }
destruct HEC as (Hsp & Hs1 & Hs0 & Hmf & Hmf32 & Hgp & Htp & V16 & V64 & V192 & V168 & Vra & Vs0 & W9 & W18 & W19 &
  W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vfl & HPRE & Hfds & Hfs & Hinp).
destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as [Ifd Ifs].
refine (conj _ (conj _ (conj _ (conj Hmf (conj Hmf32 (conj _ (conj _ _))))))).
- rewrite R2. exact Hsp.
- rewrite R9. exact Hs1.
- rewrite R8. exact Hs0.
- rewrite R3. exact Hgp.
- rewrite R4. exact Htp.
- unfold b_ec_at in VK.
  repeat match goal with
  | |- _ /\ _ => split
  | |- e_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HPRE
  | |- forall fd, _ => intros fd; rewrite Ifd; reflexivity
  | |- m_fs _ = _ => exact Ifs
  | |- bytes_at8 _ _ (e_p g) _ => exact (b_inp g pos ly3 S3 W3 mem3 md3 k3 HPRE HJ3 HB3)
  | |- val_mem _ _ ?a _ _ => apply VK; [intros x Hx; cbn in Hx; clear - Hx; lia | assumption]
  end.
Qed.

(* What the segment carries, kept. *)
Lemma b_car_keep : forall g pos mf ly2 S2 W2 regs2 mem2 ly3 S3 W3 regs3 mem3,
  SFa g pos mod 32 = 0 -> 0 <= SFa g pos ->
  b_car g pos mf ly2 S2 W2 regs2 mem2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  getr regs3 18 = getr regs2 18 -> getr regs3 23 = getr regs2 23 -> getr regs3 25 = getr regs2 25 ->
  (forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  b_car g pos mf ly3 S3 W3 regs3 mem3.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 ly3 S3 W3 regs3 mem3 H32 H0
  ((Hidb & Hidz & Hidk) & (Hp & Hf) & Hmid & Hsh & H18 & H25) Hperm R18 R23 R25 KEEP.
unfold b_kz in KEEP.
assert (Hsf8 : SFa g pos mod 8 = 0) by (apply mod32_mod8; exact H32).
refine (conj (conj _ (conj _ _)) (conj (conj _ Hf) (conj _ (conj _ (conj _ _))))).
- unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hidb). intros a Ha. apply (mbyte_of_aview SEGS). apply KEEP.
  unfold m_id in Ha. cbn [SlotModel.rec_id] in Ha. rewrite length_map in Ha. unfold V_id in Ha.
  change (length RcIdentModel.ID0) with 38%nat in Ha. clear - Ha. lia.
- unfold sh_zero, zero_shadow in *. intros i Hi. rewrite KEEP; [exact (Hidz i Hi)|].
  unfold V_id, N_id in *. change (38 / 8) with 4 in Hi. rewrite (b_sh_off (SFa g pos) 352 Hsf8).
  change (352 / 8) with 44. clear - Hi. lia.
- unfold sh_blk in *. apply (block_shadow_agree (aview SEGS (w_H W2) mem2)); [|exact Hidk].
  intros i Hi. apply KEEP. unfold V_id, N_id in *. change ((38 + 7) / 8) with 5 in Hi.
  rewrite (b_sh_off (SFa g pos) 352 Hsf8). change (352 / 8) with 44. clear - Hi. lia.
- eapply Permutation_trans; [exact Hperm | exact Hp].
- unfold mf_id in *. eapply (val_mem_kept SEGS); [|exact Hmid]. intros kk Hk. apply KEEP. clear - Hk. lia.
- unfold sh_reg in *. rewrite R23. exact Hsh.
- rewrite R18. exact H18.
- rewrite R25. exact H25.
Qed.

(* The boundary of a step from the facts at its end. *)
Lemma b_mk : forall g pos mf pc (R : bvmap 5 word -> Prop) S2 ly3 S3 W3 regs3 mem3 md3,
  mo_ok MT S2 ((EV_LLVMF - 0) * MEV MT) ->
  AJ g pos ly3 S3 W3 mem3 md3 0 -> frames S3 = [(4, pos)] ->
  ECOMMON g pos mf ly3 S3 W3 regs3 mem3 md3 -> b_car g pos mf ly3 S3 W3 regs3 mem3 -> R regs3 ->
  b_st g pos mf pc R W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3).
Proof.
intros g pos mf pc R S2 ly3 S3 W3 regs3 mem3 md3 HMOK HJ3 HFR3 HEC3 HCAR3 HR3.
unfold b_st, acut. exists ly3, S3, regs3, mem3, md3.
split; [reflexivity|]. split; [exact HJ3|]. split; [exact HFR3|].
split; [unfold EV_LLVMF; lia|].
split; [rewrite Z.mul_0_l; apply HMT0|].
split; [exact (mo_ok_step MT MTL S2 S3 0 _ ltac:(rewrite Z.add_0_l; exact HMOK) (HMT0 S2 S3))|].
split; [exact HEC3 | exact (conj HCAR3 HR3)].
Qed.

(* A step's end from its start, the end's journal and the bytes and registers the step kept. *)
Lemma b_close : forall g pos mf pc (R : bvmap 5 word -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
  AJ g pos ly2 S2 W2 mem2 md2 0 -> frames S2 = [(4, pos)] -> mo_ok MT S2 ((EV_LLVMF - 0) * MEV MT) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> b_car g pos mf ly2 S2 W2 regs2 mem2 ->
  AJ g pos ly3 S3 W3 mem3 md3 0 -> frames S3 = [(4, pos)] ->
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
  getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 -> getr regs3 8 = getr regs2 8 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 ->
  getr regs3 18 = getr regs2 18 -> getr regs3 23 = getr regs2 23 -> getr regs3 25 = getr regs2 25 ->
  (forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  R regs3 ->
  b_st g pos mf pc R W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3).
Proof.
intros g pos mf pc R ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HJ2 HFR2 HMOK HEC2 HCAR2 HJ3 HFR3 Hperm
  R2 R9 R8 R3 R4 R18 R23 R25 KEEP HR.
destruct (b_prep g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ2 HFR2 HEC2) as (_ & (SF0 & _ & _ & SF32 & _)).
assert (HCAR3 : b_car g pos mf ly3 S3 W3 regs3 mem3)
  by exact (b_car_keep g pos mf ly2 S2 W2 regs2 mem2 ly3 S3 W3 regs3 mem3 SF32 ltac:(lia) HCAR2 Hperm R18 R23 R25 KEEP).
apply (b_mk g pos mf pc R S2 ly3 S3 W3 regs3 mem3 md3 HMOK HJ3 HFR3); [|exact HCAR3 | exact HR].
apply (b_ec_keep g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 0 HEC2 HJ3 (proj1 (proj2 HCAR3))
  R2 R9 R8 R3 R4).
intros a Ha. apply KEEP. left. exact Ha.
Qed.

(* What a caller-journal call kept: tcj_kept outside its window and its E, on (a part Pk of) the keep set. *)
Lemma b_keep_tcj_on : forall g pos mf STK1 lyc Sc W memc W2 mem2 (E Pk : Z -> Prop),
  tcj_kept B STK1 lyc Sc W memc W2 mem2 mf E ->
  alloc_ceiling <= mf -> mf <= e_sp0 g - 320 -> e_sp0 g <= 2 ^ 47 ->
  In (4, pos) (frames Sc) -> frame_addr lyc 4 pos = SFa g pos -> SFa g pos mod 32 = 0 -> 0 <= SFa g pos ->
  (forall a, Pk a -> b_kz (e_sp0 g) (SFa g pos) mf a) -> (forall a, Pk a -> ~ E a) ->
  forall a, Pk a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros g pos mf STK1 lyc Sc W memc W2 mem2 E Pk (T1 & _ & _ & T4 & _) Hac Hmf Hsp0 Hin Efa H32 H0 HPk HE a HPa.
pose proof (HE a HPa) as HnE. pose proof (HPk a HPa) as Ha.
assert (Hsf8 : SFa g pos mod 8 = 0) by (apply mod32_mod8; exact H32).
pose proof (asan_consts) as (C1 & _).
unfold b_kz, b_ec_at in Ha.
assert (TM : mf <= a < e_sp0 g -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros Hr. apply T1; [clear - Hr Hac Hsp0; lia | clear - Hr; lia | exact HnE]. }
assert (TF : SFa g pos <= a < SFa g pos + 1024 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros Hr. apply (T4 4 pos a Hin); [|exact HnE]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes 4) with 1024. exact Hr. }
assert (TS : SHADOW_OFF + SFa g pos / 8 <= a < SHADOW_OFF + SFa g pos / 8 + 128 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros Hr. apply (T4 4 pos a Hin); [|exact HnE]. right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes 4 / 8) with 128. exact Hr. }
destruct Ha as [[Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]] | [Ha | [Ha | Ha]]].
1, 2, 3, 4, 5, 7: apply TM; clear - Ha Hmf; lia.
1, 2: apply TF; clear - Ha; lia.
apply TS; clear - Ha; lia.
Qed.

(* The allocator room a call asks for. *)
Lemma b_room : forall g pos ly2 S2 W2 mem2 md2,
  EPRE g -> AJ g pos ly2 S2 W2 mem2 md2 0 -> st_nev S2 + EV_LLVMF <= EV_MAX /\ blocks_bytes S2 <= LIVE_MAX.
Proof.
intros g pos ly2 S2 W2 mem2 md2 HPRE HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
split; [clear - Hnev Hev HEV; lia | exact (wf_live _ _ _ _ _ (am_wf _ _ _ _ (proj1 HAR)))].
Qed.
(* A run whose regions have no write window changes no byte. *)
Lemma b_frame_ro : forall E (rs : smem) (m m' : word -> option byte) H a,
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a Hro HF. apply (aview_eq_of SEGS). unfold mrestrict. rewrite HF; [reflexivity|].
intros (r & Hin & Ha). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Lemma b_m16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* ---- +0x2b0 (0x80a24) .. +0x2c4: reac_identity_ingest(NULL, 0, NULL, 0) at 0x80a34, refused ------------------- *)
Lemma b_T1 : forall g pos mf W2 c2,
  b_st g pos mf 0x2b0 (fun _ => True) W2 c2 ->
  SRr SEGS W2 c2 (b_st g pos mf 0x2c4 (fun r => getr r 10 = w64 (-1))).
Proof.
intros g pos mf W2 c2 HC.
destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HK & HMLE & HMOK & HEC & HCAR & _).
destruct (b_prep g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ HFR HEC) as
  ((Hac & Hsp47 & Hmf32 & Hmf & Hsp16 & Hstk & Hm16) & (SF0 & SF1 & SFapp & SF32 & Efa & Hfb & Hin4)).
pose proof HEC as (Hsp & Hs1 & Hs0 & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
destruct (b_room g pos ly2 S2 W2 mem2 md2 HPRE HJ) as [Hnev Hlive].
pose proof HJ as HJ0.
pose proof (b_entry W2 regs2 mem2 0x2b0 (SFa g pos) [] eq_refl (Forall_nil _) Logic.I) as HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x2b0)) with (Z_to_bv 64 (BASE + 0x2b0)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
pmkst HS.
rewrite (PSIG IB_reac_identity_ingest AF_reac_identity_ingest eq_refl).
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (23%bv : bv 5) R23.
prreg HS (25%bv : bv 5) R25.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
rewrite (b_E_reg regs2 (SFa g pos) 2 2%bv eq_refl) in Rsp. rewrite (b_E_reg regs2 (SFa g pos) 3 3%bv eq_refl) in Rgp.
rewrite (b_E_reg regs2 (SFa g pos) 4 4%bv eq_refl) in Rtp. rewrite (b_E_reg regs2 (SFa g pos) 8 8%bv eq_refl) in R8.
rewrite (b_E_reg regs2 (SFa g pos) 9 9%bv eq_refl) in R9. rewrite (b_E_reg regs2 (SFa g pos) 18 18%bv eq_refl) in R18.
rewrite (b_E_reg regs2 (SFa g pos) 23 23%bv eq_refl) in R23. rewrite (b_E_reg regs2 (SFa g pos) 25 25%bv eq_refl) in R25.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS reac_identity_ingest.A_reac_identity_ingest rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HING LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 _ _ 0 _
    0 0 0 0 RcIdentModel.ID0 [] HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Ra3.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Qsp. apply b_m16. exact Hmf32.
  - rewrite Qsp. unfold reac_identity_ingest.INGEST_STK, ESTACK. lia.
  - rewrite Qsp. lia.
  - reflexivity.
  - intros Hr. vm_compute in Hr. discriminate Hr.
  - unfold reac_identity_ingest.EV_INGEST, EV_LLVMF in *. lia.
  - unfold reac_identity_ingest.LIVE_INGEST. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & HT3 & _).
rewrite Rra. apply SRr_ret.
replace (0 + reac_identity_ingest.EV_INGEST) with 0 in HJ3 by reflexivity.
destruct (b_pres _ _ HP3) as (P2 & P3 & P4 & P8 & P9 & P18 & _ & P23 & P25).
apply (b_close g pos mf 0x2c4 _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 regs3 mem3 md3 HJ0 HFR HMOK HEC HCAR HJ3 HFR
  (Permutation_refl _)).
- rewrite P2. exact Rsp.
- rewrite P9. exact R9.
- rewrite P8. exact R8.
- rewrite P3. exact Rgp.
- rewrite P4. exact Rtp.
- rewrite P18. exact R18.
- rewrite P23. exact R23.
- rewrite P25. exact R25.
- intros a Ha. rewrite Qsp in HT3.
  rewrite (b_keep_tcj_on g pos mf _ ly2 S2 W2 _ W2 mem3 _ _ HT3 ltac:(lia) ltac:(lia) ltac:(lia) Hin4 Efa SF32 ltac:(lia)
    (fun x Hx => Hx) ltac:(intros x _ (Hx & _); vm_compute in Hx; discriminate Hx) a Ha).
  eapply b_frame_ro; [|exact HF]. vm_compute. reflexivity.
- rewrite Ha03. reflexivity.
Qed.

(* ---- the closing of a step after a call ------------------------------------------------------------------ *)
(* A caller-journal call (tcj_kept). *)
Lemma b_close_tcj : forall g pos mf pc (R : bvmap 5 word -> Prop) ly2 S2 W2 regs2 mem2 md2 regsc memc STK1
  (E : Z -> Prop) ly3 S3 W3 regs3 mem3 md3,
  AJ g pos ly2 S2 W2 mem2 md2 0 -> frames S2 = [(4, pos)] -> mo_ok MT S2 ((EV_LLVMF - 0) * MEV MT) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> b_car g pos mf ly2 S2 W2 regs2 mem2 ->
  (forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W2) memc a = aview SEGS (w_H W2) mem2 a) ->
  getr regsc 2 = getr regs2 2 -> getr regsc 9 = getr regs2 9 -> getr regsc 8 = getr regs2 8 ->
  getr regsc 3 = getr regs2 3 -> getr regsc 4 = getr regs2 4 ->
  getr regsc 18 = getr regs2 18 -> getr regsc 23 = getr regs2 23 -> getr regsc 25 = getr regs2 25 ->
  AJ g pos ly3 S3 W3 mem3 md3 0 -> frames S3 = frames S2 ->
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> aregs_preserved regsc regs3 ->
  tcj_kept B STK1 ly2 S2 W2 memc W3 mem3 mf E ->
  (forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> ~ E a) ->
  R regs3 ->
  b_st g pos mf pc R W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3).
Proof.
intros g pos mf pc R ly2 S2 W2 regs2 mem2 md2 regsc memc STK1 E ly3 S3 W3 regs3 mem3 md3
  HJ2 HFR2 HMOK HEC2 HCAR2 KRUN C2 C9 C8 C3 C4 C18 C23 C25 HJ3 HFR3 Hperm HP HT HE HR.
destruct (b_prep g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ2 HFR2 HEC2) as
  ((Hac & Hsp47 & _ & Hmf & _) & (SF0 & _ & _ & SF32 & Efa & _ & Hin4)).
destruct (b_pres _ _ HP) as (P2 & P3 & P4 & P8 & P9 & P18 & _ & P23 & P25).
apply (b_close g pos mf pc R ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HJ2 HFR2 HMOK HEC2 HCAR2 HJ3
  ltac:(rewrite HFR3; exact HFR2) Hperm).
- rewrite P2. exact C2.
- rewrite P9. exact C9.
- rewrite P8. exact C8.
- rewrite P3. exact C3.
- rewrite P4. exact C4.
- rewrite P18. exact C18.
- rewrite P23. exact C23.
- rewrite P25. exact C25.
- intros a Ha.
  rewrite (b_keep_tcj_on g pos mf STK1 ly2 S2 W2 memc W3 mem3 E _ HT ltac:(lia) ltac:(lia) Hsp47 Hin4 Efa SF32 ltac:(lia)
    (fun x Hx => Hx) HE a Ha).
  exact (KRUN a Ha).
- exact HR.
Qed.

(* What a call in the afn_pre form kept: its own journal from the call state at sp = mf. *)
Lemma b_keep_sub : forall g pos mf STK1 ly2 S2 W2 memc mdc ly3 S3 W3 mem3 md3 k1,
  ajournal SEGS B STK1 mf [] ly2 S2 W2 memc mdc [] ly3 S3 W3 mem3 md3 k1 ->
  alloc_ceiling <= mf -> mf <= e_sp0 g - 320 -> e_sp0 g <= 2 ^ 47 ->
  In (4, pos) (frames S2) -> frame_addr ly2 4 pos = SFa g pos ->
  forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) memc a.
Proof.
intros g pos mf STK1 ly2 S2 W2 memc mdc ly3 S3 W3 mem3 md3 k1 HJ Hac Hmf Hsp0 Hin Efa a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & F4 & _).
assert (HnF : ~ inFP [] a) by (intros (r & Hr & _); destruct Hr).
unfold b_kz, b_ec_at in Ha.
assert (TM : mf <= a < e_sp0 g -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) memc a).
{ intros Hr. apply F1; [clear - Hr Hac Hsp0; lia | clear - Hr; lia]. }
assert (TF : SFa g pos <= a < SFa g pos + 1024 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) memc a).
{ intros Hr. apply (F4 4 pos a Hin); [|exact HnF]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes 4) with 1024. exact Hr. }
assert (TS : SHADOW_OFF + SFa g pos / 8 <= a < SHADOW_OFF + SFa g pos / 8 + 128 ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) memc a).
{ intros Hr. apply (F4 4 pos a Hin); [|exact HnF]. right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes 4 / 8) with 128. exact Hr. }
destruct Ha as [[Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]] | [Ha | [Ha | Ha]]].
1, 2, 3, 4, 5, 7: apply TM; clear - Ha Hmf; lia.
1, 2: apply TF; clear - Ha; lia.
apply TS; clear - Ha; lia.
Qed.

(* A call in the afn_pre form: its journal composed into the entry's. *)
Lemma b_close_sub : forall g pos mf pc (R : bvmap 5 word -> Prop) ly2 S2 W2 regs2 mem2 md2 regsc memc mdc STK1
  ly3 S3 W3 regs3 mem3 md3,
  AJ g pos ly2 S2 W2 mem2 md2 0 -> frames S2 = [(4, pos)] -> mo_ok MT S2 ((EV_LLVMF - 0) * MEV MT) ->
  ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 -> b_car g pos mf ly2 S2 W2 regs2 mem2 ->
  AJ g pos ly2 S2 W2 memc mdc 0 ->
  (forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W2) memc a = aview SEGS (w_H W2) mem2 a) ->
  getr regsc 2 = getr regs2 2 -> getr regsc 9 = getr regs2 9 -> getr regsc 8 = getr regs2 8 ->
  getr regsc 3 = getr regs2 3 -> getr regsc 4 = getr regs2 4 ->
  getr regsc 18 = getr regs2 18 -> getr regsc 23 = getr regs2 23 -> getr regsc 25 = getr regs2 25 ->
  0 <= STK1 -> e_sp0 g - LLVMF_STK <= mf - STK1 ->
  ajournal SEGS B STK1 mf [] ly2 S2 W2 memc mdc [] ly3 S3 W3 mem3 md3 0 ->
  Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> aregs_preserved regsc regs3 ->
  R regs3 ->
  b_st g pos mf pc R W3 (cfg_at SEGS (BASE + pc) regs3 mem3 md3).
Proof.
intros g pos mf pc R ly2 S2 W2 regs2 mem2 md2 regsc memc mdc STK1 ly3 S3 W3 regs3 mem3 md3
  HJ2 HFR2 HMOK HEC2 HCAR2 HJc KRUN C2 C9 C8 C3 C4 C18 C23 C25 HS0 HSb HJ1 Hperm HP HR.
destruct (b_prep g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ2 HFR2 HEC2) as
  ((Hac & Hsp47 & _ & Hmf & _) & (SF0 & _ & _ & SF32 & Efa & _ & Hin4)).
destruct (b_pres _ _ HP) as (P2 & P3 & P4 & P8 & P9 & P18 & _ & P23 & P25).
pose proof (ajournal_sub SEGS B LAWS pa_segs_low LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)] ly2 S2 W2 memc mdc 0 STK1 mf [] [] ly3 S3 W3 mem3 md3 0 HJc HJ1 ltac:(lia) ltac:(lia)
  ltac:(intros a (r & Hr & _); destruct Hr)) as HJ3.
change ([] ++ [(4, pos)]) with [(4, pos)] in HJ3. change (0 + 0) with 0 in HJ3.
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs & _).
apply (b_close g pos mf pc R ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HJ2 HFR2 HMOK HEC2 HCAR2 HJ3
  ltac:(rewrite Hfrs; exact HFR2) Hperm).
- rewrite P2. exact C2.
- rewrite P9. exact C9.
- rewrite P8. exact C8.
- rewrite P3. exact C3.
- rewrite P4. exact C4.
- rewrite P18. exact C18.
- rewrite P23. exact C23.
- rewrite P25. exact C25.
- intros a Ha.
  rewrite (b_keep_sub g pos mf STK1 ly2 S2 W2 memc mdc ly3 S3 W3 mem3 md3 0 HJ1 ltac:(lia) ltac:(lia) Hsp47 Hin4 Efa
    a Ha).
  exact (KRUN a Ha).
- exact HR.
Qed.

(* The frame-pointer chain an afn_pre call asks for: the entry's chain, with the entry's own record pushed when the
   layout's top leaves room for it. *)
Lemma b_chain : forall g pos mf ly2 S2 W2 regs2 mem2 md2 k,
  AJ g pos ly2 S2 W2 mem2 md2 k -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  exists ch, achain ly2 (aview SEGS (w_H W2) mem2) mf (e_sp0 g) ch.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 k HJ HEC.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstat & _).
pose proof Hstat as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct HEC as (_ & _ & _ & Hmf & _ & _ & _ & _ & _ & _ & _ & Vra & Vs0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HPRE & _).
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as ((_ & _ & Hra4 & _ & _ & _ & _ & Hch0 & _) & Hra & _).
pose proof (asan_consts) as (C1 & _).
unfold e_sp0 in *.
destruct (Z_lt_le_dec (spZ (e_regs g)) (ly_top (e_ly g) - 16)) as [Hlt | Hge].
- exists [(spZ (e_regs g), RA_LLVMF, s0Z (e_regs g))].
  apply (achain_ly_top (e_ly g) ly2); [exact Etop|].
  apply (achain_push (e_ly g) (aview SEGS (w_H (e_W g)) (e_mem g)) (aview SEGS (w_H W2) mem2) (spZ (e_regs g))
    (s0Z (e_regs g)) RA_LLVMF [] mf Hch0).
  + clear - Htop H47. lia.
  + intros a Ha. exact (aview_above_of_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a Ha).
  + apply (rdword_of_val_mem SEGS). exact Vra. rewrite <- Hra. unfold raZ. apply bv_unsigned_in_range.
  + apply (rdword_of_val_mem SEGS). exact Vs0. unfold s0Z. apply bv_unsigned_in_range.
  + rewrite <- Hra. exact Hra4.
  + clear - Hceil Hslo Hstk0 C1. lia.
  + clear - Hal16. pose proof (Z.div_mod (spZ (e_regs g)) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D.
    rewrite D. replace (16 * (spZ (e_regs g) / 16)) with ((2 * (spZ (e_regs g) / 16)) * 8) by lia.
    apply Z.mod_mul. lia.
  + exact Hlt.
  + clear - Hmf. lia.
- exists []. left. split; [right; left; rewrite Etop; exact Hge | reflexivity].
Qed.

(* HW_FAMILY's three family fields, from the image fact. *)
Lemma b_famof_tbl : forall (W : world SEGS) mem,
  garr8 SEGS (rd W mem) (VAL (A_OBJ 17)) HW_ROWS -> reac_box_family_of.famof_tbl W mem 1 2 3.
Proof.
intros W mem HG. unfold reac_box_family_of.famof_tbl, reac_box_family_of.FAMOF_HWF.
assert (GB : forall j, (j < 36)%nat ->
  mbyte SEGS (rd W mem) (VAL (A_OBJ 17) + Z.of_nat j) = Some (Z_to_bv 8 (le_byte (nth j HW_ROWS 0) 1 0))).
{ intros j Hj. destruct (HG j ltac:(unfold HW_ROWS; cbn [length]; lia)) as [Hv _]. specialize (Hv 0%nat ltac:(lia)).
  rewrite Z.add_0_r in Hv. exact Hv. }
assert (G4 : forall o v, (o + 4 <= 36)%nat ->
  (forall k, (k < 4)%nat -> Z_to_bv 8 (le_byte v 4 k) = Z_to_bv 8 (le_byte (nth (o + k) HW_ROWS 0) 1 0)) ->
  val_mem SEGS (rd W mem) (VAL (A_OBJ 17) + Z.of_nat o) 4 v).
{ intros o v Ho Hk k Hk4. replace (VAL (A_OBJ 17) + Z.of_nat o + Z.of_nat k) with (VAL (A_OBJ 17) + Z.of_nat (o + k)) by lia.
  rewrite GB by lia. rewrite Hk by exact Hk4. reflexivity. }
split.
{ intros a Ha. replace a with (VAL (A_OBJ 17) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 17)))) by lia.
  unfold aview. rewrite GB by lia. discriminate. }
split; [lia|]. split.
{ rewrite <- (Z.add_0_r (VAL (A_OBJ 17))) at 1. apply (G4 0%nat 1); [lia|].
  intros k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
split; [lia|]. split.
{ apply (G4 12%nat 2); [lia|].
  intros k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
split; [lia|].
{ apply (G4 24%nat 3); [lia|].
  intros k Hk. destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
Qed.

(* The read-only image at a state of the journal. *)
Lemma b_aro : forall g pos ly2 S2 W2 mem2 md2 k,
  EPRE g -> AJ g pos ly2 S2 W2 mem2 md2 k -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros g pos ly2 S2 W2 mem2 md2 k HPRE HJ.
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ (HRO _ HAROS)).
Qed.

(* ---- the start of a step ------------------------------------------------------------------------------- *)
Ltac b_open HC :=
  destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HK & HMLE & HMOK & HEC & HCAR & HR);
  destruct (b_prep _ _ _ ly2 S2 _ regs2 mem2 md2 0 HJ HFR HEC) as
    ((Hac & Hsp47 & Hmf32 & Hmf & Hsp16 & Hstk & Hm16) & (SF0 & SF1 & SFapp & SF32 & Efa & Hfb & Hin4));
  pose proof HEC as (Hsp & Hs1 & Hs0 & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & HPRE & _);
  destruct (b_room _ _ ly2 S2 _ mem2 md2 HPRE HJ) as [Hnev Hlive];
  pose proof HJ as HJ0.
Ltac b_regs HS regs2 SF Rra Rsp Rgp Rtp R8 R9 R18 R23 R25 :=
  prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
  prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (18%bv : bv 5) R18; prreg HS (23%bv : bv 5) R23;
  prreg HS (25%bv : bv 5) R25;
  rewrite (b_E_reg regs2 SF 2 2%bv eq_refl) in Rsp; rewrite (b_E_reg regs2 SF 3 3%bv eq_refl) in Rgp;
  rewrite (b_E_reg regs2 SF 4 4%bv eq_refl) in Rtp; rewrite (b_E_reg regs2 SF 8 8%bv eq_refl) in R8;
  rewrite (b_E_reg regs2 SF 9 9%bv eq_refl) in R9; rewrite (b_E_reg regs2 SF 18 18%bv eq_refl) in R18;
  rewrite (b_E_reg regs2 SF 23 23%bv eq_refl) in R23; rewrite (b_E_reg regs2 SF 25 25%bv eq_refl) in R25.
Ltac b_norm_ss HS :=
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* mf+184, read at 0x80a48. *)
Definition b_rmid : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 0 0 [YP09.mkChunk 184 (CVal 8 (SOff 32 352))].

(* ---- +0x2c4 (0x80a38) .. +0x2e4: s3 = -1, the abort test of call 3, reac_identity_ingest(&id, 0, NULL, 4) ------ *)
Lemma b_T2 : forall g pos mf W2 c2,
  b_st g pos mf 0x2c4 (fun r => getr r 10 = w64 (-1)) W2 c2 ->
  SRr SEGS W2 c2 (b_st g pos mf 0x2e4 (fun r => getr r 10 = w64 (-1) /\ getr r 19 = w64 (-1))).
Proof.
intros g pos mf W2 c2 HC. b_open HC.
pose proof HCAR as (_ & _ & Hmid & _).
assert (HRG : region_ok SEGS (b_E regs2 (SFa g pos)) (rd W2 mem2) b_rmid).
{ unfold region_ok, b_rmid. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (b_E_reg regs2 (SFa g pos) 9 9%bv eq_refl), Hs1. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ mf 184 8 (SOff 32 352) (SFa g pos + 352)).
  - cbn [sv_denot]. rewrite b_E_32, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - exact Hmid. }
pose proof (b_entry W2 regs2 mem2 0x2c4 (SFa g pos) [b_rmid] eq_refl ltac:(apply Forall_cons; [exact HRG | apply Forall_nil])
  ltac:(cbn [pairwise_disjoint all_disjoint]; split; exact Logic.I)) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) (-1) HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite HR; reflexivity)
  eq_refl) as HS.
clear HS0. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x2c4)) with (Z_to_bv 64 (BASE + 0x2c4)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
rewrite (PSIG IB_reac_identity_ingest AF_reac_identity_ingest eq_refl).
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (19%bv : bv 5) R19.
rewrite b_E_32, unsigned_lit_small in Ra0 by lia.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
assert (Href : reac_identity_ingest_c.ingest_refused (SFa g pos + 352) 0 4 = true).
{ unfold reac_identity_ingest_c.ingest_refused. rewrite Bool.orb_true_r. reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS reac_identity_ingest.A_reac_identity_ingest rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HING LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 _ _ 0 _
    (SFa g pos + 352) 0 0 4 RcIdentModel.ID0 (repeat (Z_to_bv 8 0) 4) HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Ra3.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite Qsp. apply b_m16. exact Hmf32.
  - rewrite Qsp. unfold reac_identity_ingest.INGEST_STK, ESTACK. lia.
  - rewrite Qsp. lia.
  - reflexivity.
  - intros Hr. rewrite Href in Hr. discriminate Hr.
  - unfold reac_identity_ingest.EV_INGEST, EV_LLVMF in *. lia.
  - unfold reac_identity_ingest.LIVE_INGEST. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & HT3 & _).
rewrite Rra. apply SRr_ret.
replace (0 + reac_identity_ingest.EV_INGEST) with 0 in HJ3 by reflexivity.
rewrite Qsp in HT3.
eapply (b_close_tcj g pos mf 0x2e4 _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ _ ly2 S2 W2 regs3 mem3 md3
  HJ0 HFR HMOK HEC HCAR).
- intros a Ha. eapply b_frame_ro; [|exact HF]. vm_compute. reflexivity.
- exact Rsp.
- exact R9.
- exact R8.
- exact Rgp.
- exact Rtp.
- exact R18.
- exact R23.
- exact R25.
- exact HJ3.
- reflexivity.
- apply Permutation_refl.
- exact HP3.
- exact HT3.
- intros x _ (Hx & _). rewrite Href in Hx. discriminate Hx.
- split.
  + rewrite Ha03. unfold reac_identity_ingest_c.ingest_ret. rewrite Href. reflexivity.
  + destruct (b_pres _ _ HP3) as (_ & _ & _ & _ & _ & _ & P19 & _). rewrite P19, R19. apply bv_eq. reflexivity.
Qed.

(* ---- +0x2e4 (0x80a58) .. +0x2fc: the abort test of call 4, reac_identity_fw_str(0, NULL, 8) -------------------- *)
Lemma b_T3 : forall g pos mf W2 c2,
  b_st g pos mf 0x2e4 (fun r => getr r 10 = w64 (-1) /\ getr r 19 = w64 (-1)) W2 c2 ->
  SRr SEGS W2 c2 (b_st g pos mf 0x2fc (fun r => getr r 10 = w64 (-1))).
Proof.
intros g pos mf W2 c2 HC. b_open HC. destruct HR as [HR10 HR19].
pose proof (b_entry W2 regs2 mem2 0x2e4 (SFa g pos) [] eq_refl (Forall_nil _) Logic.I) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) (-1) HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite HR10; reflexivity)
  eq_refl) as HS1.
pose proof (st_ok_pi_pin_reg' _ _ _ (19%bv : bv 5) (-1) HS1 ltac:(cbn [ms_regs restrict mkst]; rewrite HR19; reflexivity)
  eq_refl) as HS.
clear HS0 HS1. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x2e4)) with (Z_to_bv 64 (BASE + 0x2e4)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
pmkst HS.
rewrite (PSIG IB_reac_identity_fw_str AF_reac_identity_fw_str eq_refl).
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS (BASE + AF_reac_identity_fw_str) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HFWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 _ _ 0 _
    0 0 8 HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia.
  - lia.
  - lia.
  - rewrite Qsp. apply b_m16. exact Hmf32.
  - rewrite Qsp. unfold reac_identity_fw_str.REAC_IDENTITY_FW_STR_STK, reac_identity_fw_str.FW_FRAME, ESTACK. lia.
  - rewrite Qsp. lia.
  - intros Hw. vm_compute in Hw. discriminate Hw. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HFR3 & HPm3 & HIF).
destruct HIF as [Ha03 HT3].
rewrite Rra. apply SRr_ret.
rewrite Qsp in HT3.
eapply (b_close_tcj g pos mf 0x2fc _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ _ ly3 S3 W3 regs3 mem3 md3
  HJ0 HFR HMOK HEC HCAR).
- intros a Ha. eapply b_frame_ro; [|exact HF]. vm_compute. reflexivity.
- exact Rsp.
- exact R9.
- exact R8.
- exact Rgp.
- exact Rtp.
- exact R18.
- exact R23.
- exact R25.
- exact HJ3.
- exact HFR3.
- exact HPm3.
- exact HP3.
- exact HT3.
- intros x _ [].
- exact Ha03.
Qed.

(* ---- +0x2fc (0x80a70) .. +0x31c: the abort test of call 5, reac_identity_reac_ver_str(0, 0, 0, NULL, 20) ------- *)
Lemma b_T4 : forall g pos mf W2 c2,
  b_st g pos mf 0x2fc (fun r => getr r 10 = w64 (-1)) W2 c2 ->
  SRr SEGS W2 c2 (b_st g pos mf 0x31c (fun r => getr r 10 = w64 (-1))).
Proof.
intros g pos mf W2 c2 HC. b_open HC.
pose proof (b_entry W2 regs2 mem2 0x2fc (SFa g pos) [] eq_refl (Forall_nil _) Logic.I) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) (-1) HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite HR; reflexivity)
  eq_refl) as HS.
clear HS0. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x2fc)) with (Z_to_bv 64 (BASE + 0x2fc)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
pmkst HS.
rewrite (PSIG IB_reac_identity_reac_ver_str AF_reac_identity_reac_ver_str eq_refl).
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (14%bv : bv 5) Ra4.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS reac_identity_reac_ver_str.A_reac_identity_reac_ver_str rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HVS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 _ _ 0 _
    0 0 0 0 20 HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
  - rewrite Rgp. exact Hgp.
  - rewrite Rtp. exact Htp.
  - rewrite Qsp. apply b_m16. exact Hmf32.
  - rewrite Qsp. unfold reac_identity_reac_ver_str.REAC_VER_STR_STK, write_uint.WRITE_UINT_STK, ESTACK. lia.
  - rewrite Qsp. lia.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - exact Ra3.
  - exact Ra4.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - intros Hf. vm_compute in Hf. discriminate Hf.
  - rewrite HFR. cbn. lia. }
cbv beta. intros W3 c3 _ (-> & ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPm3 & HFR3 & HIF).
destruct HIF as [Ha03 HT3].
rewrite Rra. apply SRr_ret.
replace (0 + reac_identity_reac_ver_str.EV_REAC_VER_STR) with 0 in HJ3 by reflexivity.
rewrite Qsp in HT3.
eapply (b_close_tcj g pos mf 0x31c _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ _ ly3 S3 W2 regs3 mem3 md3
  HJ0 HFR HMOK HEC HCAR).
- intros a Ha. eapply b_frame_ro; [|exact HF]. vm_compute. reflexivity.
- exact Rsp.
- exact R9.
- exact R8.
- exact Rgp.
- exact Rtp.
- exact R18.
- exact R23.
- exact R25.
- exact HJ3.
- exact HFR3.
- exact HPm3.
- exact HP3.
- exact HT3.
- intros x _ [].
- exact Ha03.
Qed.

(* An afn_pre call's pre-condition at a step's call state (sp = mf). *)
Lemma b_afn : forall g pos mf ly2 S2 W2 regs2 mem2 md2 memc mdc regsc STK1 ch,
  AJ g pos ly2 S2 W2 mem2 md2 0 -> frames S2 = [(4, pos)] -> ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
  AJ g pos ly2 S2 W2 memc mdc 0 ->
  (forall a, mf <= a < 2 ^ 64 -> aview SEGS (w_H W2) memc a = aview SEGS (w_H W2) mem2 a) ->
  achain ly2 (aview SEGS (w_H W2) mem2) mf (e_sp0 g) ch ->
  getr regsc 2 = w64 mf -> getr regsc 8 = w64 (e_sp0 g) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  0 <= STK1 -> e_sp0 g - LLVMF_STK <= mf - STK1 ->
  afn_pre SEGS B STK1 ly2 S2 W2 regsc memc mdc ch.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 memc mdc regsc STK1 ch HJ2 HFR HEC HJc KRUN Hch Rsp R8 Rgp Rtp Hra Hra4 H0 Hb.
destruct (b_prep g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ2 HFR HEC) as ((Hac & Hsp47 & Hmf32 & Hmf & Hsp16 & Hstk & Hm16) & _).
pose proof (asan_consts) as (C1 & _).
assert (Qsp : spZ regsc = mf)
  by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; clear - Hac Hmf Hsp47 C1; lia).
assert (Qs0 : s0Z regsc = e_sp0 g)
  by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; clear - Hac Hmf Hsp47 C1; lia).
apply (afn_pre_at SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  ly2 S2 W2 memc mdc 0 regsc STK1 (mf - e_sp0 g) ch HJc); try assumption.
- rewrite Qsp. lia.
- lia.
- lia.
- rewrite Qsp, Qs0. apply (achain_kept ly2 (aview SEGS (w_H W2) mem2) _ mf (e_sp0 g) ch mf Hch); [lia | |].
  + pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & Hshi & H47 & _ & _ & Htop) & _).
    pose proof HJc as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). rewrite Etop. lia.
  + intros a Ha. exact (KRUN a Ha).
Qed.

(* ---- +0x31c (0x80a90) .. +0x33c: the abort test of call 5, reac_box_catalogue_defect(NULL, 8, 8, "x") ---------- *)
Lemma b_T5 : forall g pos mf W2 c2,
  b_st g pos mf 0x31c (fun r => getr r 10 = w64 (-1)) W2 c2 ->
  SRr SEGS W2 c2 (b_st g pos mf 0x33c (fun r => getr r 10 = w64 0)).
Proof.
intros g pos mf W2 c2 HC. b_open HC.
destruct (b_chain g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ HEC) as [ch Hch].
pose proof (b_entry W2 regs2 mem2 0x31c (SFa g pos) [] eq_refl (Forall_nil _) Logic.I) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) (-1) HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite HR; reflexivity)
  eq_refl) as HS.
clear HS0. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x31c)) with (Z_to_bv 64 (BASE + 0x31c)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
pmkst HS.
rewrite (PSIG IB_reac_box_catalogue_defect AF_reac_box_catalogue_defect eq_refl).
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
rewrite (img_env_atomP _ 245 HEI ltac:(unfold A_TEXT, A_LIM; lia)) in Ra3.
change (Z_to_bv 64 (VAL 245)) with (w64 (VAL (A_OBJ 4))) in Ra3.
assert (KRUN : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
  by (intros a; eapply b_frame_ro; [|exact HF]; vm_compute; reflexivity).
pose proof (b_afn g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_mem ms) _ (ms_regs ms)
  reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK ch HJ0 HFR HEC HJ (fun a _ => KRUN a) Hch
  ltac:(rewrite Rsp; exact Hsp) ltac:(rewrite R8; exact Hs0) ltac:(rewrite Rgp; exact Hgp) ltac:(rewrite Rtp; exact Htp)
  ltac:(rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity])
  ltac:(unfold raZ; rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia); pose proof pa_base_lo; lia)
  ltac:(unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK; lia)
  ltac:(unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK; lia)) as HPRE'.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS reac_box_catalogue_defect.A_reac_box_catalogue_defectP rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HCATD ly2 S2 W2 _ _ _ ch 0 8 8 (VAL (A_OBJ 4)) 0 0 0 [] [] HPRE' Ra0 Ra1 Ra2 Ra3).
  - lia.
  - lia.
  - lia.
  - pose proof (pa_val_range (A_OBJ 4)). lia.
  - lia.
  - lia.
  - lia.
  - intros H. exfalso. apply H. reflexivity.
  - intros H. exfalso. apply H. reflexivity. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP3 & Ha03 & -> & -> & -> & HPm3).
rewrite Rra. apply SRr_ret.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
rewrite Qsp in HJ1.
eapply (b_close_sub g pos mf 0x33c _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _
  reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK ly2 S2 W2 regs3 mem3 md3
  HJ0 HFR HMOK HEC HCAR HJ (fun a _ => KRUN a)).
- exact Rsp.
- exact R9.
- exact R8.
- exact Rgp.
- exact Rtp.
- exact R18.
- exact R23.
- exact R25.
- unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. lia.
- unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. lia.
- exact HJ1.
- apply Permutation_refl.
- exact HP3.
- exact Ha03.
Qed.

(* ---- +0x33c (0x80ab0) .. +0x348: the abort test of call 6, reac_box_family_of(NULL) ---------------------------- *)
Lemma b_T6 : forall g pos mf W2 c2,
  b_st g pos mf 0x33c (fun r => getr r 10 = w64 0) W2 c2 ->
  SRr SEGS W2 c2 (b_st g pos mf 0x348 (fun r => getr r 10 = w64 0)).
Proof.
intros g pos mf W2 c2 HC. b_open HC.
destruct (b_chain g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ HEC) as [ch Hch].
pose proof (b_entry W2 regs2 mem2 0x33c (SFa g pos) [] eq_refl (Forall_nil _) Logic.I) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite HR; reflexivity)
  eq_refl) as HS.
clear HS0. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x33c)) with (Z_to_bv 64 (BASE + 0x33c)).
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_nil. }
pmkst HS.
rewrite (PSIG IB_reac_box_family_of AF_reac_box_family_of eq_refl).
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0.
assert (KRUN : forall a, aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a)
  by (intros a; eapply b_frame_ro; [|exact HF]; vm_compute; reflexivity).
pose proof (b_afn g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_mem ms) _ (ms_regs ms)
  reac_box_family_of.REAC_BOX_FAMILY_OF_STK ch HJ0 HFR HEC HJ (fun a _ => KRUN a) Hch
  ltac:(rewrite Rsp; exact Hsp) ltac:(rewrite R8; exact Hs0) ltac:(rewrite Rgp; exact Hgp) ltac:(rewrite Rtp; exact Htp)
  ltac:(rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity])
  ltac:(unfold raZ; rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia); pose proof pa_base_lo; lia)
  ltac:(unfold reac_box_family_of.REAC_BOX_FAMILY_OF_STK, reac_box_family_of.FAMOF_FRAME, ESTACK; lia)
  ltac:(unfold reac_box_family_of.REAC_BOX_FAMILY_OF_STK, reac_box_family_of.FAMOF_FRAME, ESTACK; lia)) as HPRE'.
pose proof (HIMG W2 (ms_mem ms) (b_aro g pos ly2 S2 W2 (ms_mem ms) _ 0 HPRE HJ)) as (_ & _ & _ & _ & HW17 & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS reac_box_family_of.A_reac_box_family_ofP rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (HFAM ly2 S2 W2 _ _ _ ch 0 1 2 3 HPRE' Ra0).
  - lia.
  - intros H. exfalso. apply H. reflexivity.
  - exact (b_famof_tbl W2 (ms_mem ms) HW17). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP3 & -> & -> & -> & _ & r & Hres & Ha03).
rewrite Rra. apply SRr_ret.
assert (Qsp : spZ (ms_regs ms) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
rewrite Qsp in HJ1.
assert (Hr0 : r = 0).
{ unfold reac_box_family_of.famof_res in Hres.
  destruct Hres as [(_ & Hr) | [(H0 & _) | [(H0 & _) | [(H0 & _) | [(H0 & _) | (H0 & _)]]]]];
    [exact Hr | exfalso; apply H0; reflexivity ..]. }
subst r.
eapply (b_close_sub g pos mf 0x348 _ ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _
  reac_box_family_of.REAC_BOX_FAMILY_OF_STK ly2 S2 W2 regs3 mem3 md3
  HJ0 HFR HMOK HEC HCAR HJ (fun a _ => KRUN a)).
- exact Rsp.
- exact R9.
- exact R8.
- exact Rgp.
- exact Rtp.
- exact R18.
- exact R23.
- exact R25.
- unfold reac_box_family_of.REAC_BOX_FAMILY_OF_STK, reac_box_family_of.FAMOF_FRAME, ESTACK. lia.
- unfold reac_box_family_of.REAC_BOX_FAMILY_OF_STK, reac_box_family_of.FAMOF_FRAME, ESTACK. lia.
- exact HJ1.
- apply Permutation_refl.
- exact HP3.
- exact Ha03.
Qed.

(* ---- the frame's shadow and the frame, apart --------------------------------------------------------------- *)
(* The frame's shadow cells lie below the machine frame and apart from the frame's own bytes. *)
Lemma b_sh_apart : forall SF mf,
  4096 <= SF -> SF + 1024 <= alloc_ceiling -> in_app SF 1024 -> SF mod 8 = 0 -> alloc_ceiling + 16400 <= mf ->
  0 <= SF / 8 /\ 8 * (SF / 8) = SF /\ SHADOW_OFF + SF / 8 + 128 <= mf - 16 /\
  (SHADOW_OFF + SF / 8 + 128 <= SF \/ SF + 1024 <= SHADOW_OFF + SF / 8).
Proof.
intros SF mf H0 H1 Happ H8 Hmf. pose proof (asan_consts) as (C1 & _).
pose proof (Z.div_mod SF 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
split; [apply Z.div_pos; lia|]. split; [lia|]. lia.
Qed.
(* A run changed no byte outside its write windows. *)
Lemma b_frame_w : forall E (rs : smem) (m m' : word -> option byte) H a WS,
  frame_of E rs m m' -> windows rs = WS -> 0 <= a < 2 ^ 64 ->
  (forall b wlo whi, In (b, wlo, whi) WS -> ~ (base_val E b + wlo <= a < base_val E b + whi)) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' H a WS HF HW Ha HN. apply (aview_eq_of SEGS). unfold mrestrict. rewrite HF; [reflexivity|].
rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hb & Hr). rewrite HW in Hb.
exact (HN b wlo whi Hb Hr).
Qed.
(* One byte from a view. *)
Lemma b_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_wrap.
change (bv_modulus 8) with 256 in *. change (2 ^ 8) with 256.
repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
(* id after reac_identity_init: 38 zero bytes, i.e. RcIdentModel.ID0. *)
Lemma b_id0 : forall (W : world SEGS) mem a,
  (forall i, 0 <= i < 38 -> aview SEGS (w_H W) mem (a + i) = Some 0) -> bytes_at8 W mem a RcIdentModel.ID0.
Proof.
intros W mem a H j Hj. change (length (map (fun b : byte => bv_unsigned b) RcIdentModel.ID0)) with 38%nat in Hj.
assert (Hn : nth j (map (fun b : byte => bv_unsigned b) RcIdentModel.ID0) 0 = 0).
{ clear H. do 38 (destruct j as [|j]; [reflexivity|]). lia. }
rewrite Hn. split; [|lia]. apply b_vm1. apply H. lia.
Qed.

(* ---- +0x348 (0x80abc) .. +0x370: the abort test of call 7, &hw, hw's shadow, the memset's arguments --------- *)
(* mf+64 (the frame address), read at 0x80ac4; hw's two shadow cells, written at 0x80ad0 / 0x80ad4. *)
Definition b_rmf64 : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
Definition b_rhw : YP09.region := YP09.mkRegion (Some 23%nat) 54 56 54 56 [].
Definition b_W7 : list (option nat * Z * Z) := [(Some 9%nat, 0, 0); (Some 23%nat, 54, 56)].
#[local] Notation INVB := (inv_B_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Lemma b_T7 : forall g pos mf W2 c2,
  b_st g pos mf 0x348 (fun r => getr r 10 = w64 0) W2 c2 -> SRr SEGS W2 c2 (INVB g pos mf).
Proof.
intros g pos mf W2 c2 HC. b_open HC.
pose proof HEC as (_ & _ & _ & _ & _ & _ & _ & _ & V64 & _).
pose proof HCAR as (_ & _ & _ & Hsh & _).
pose proof HJ as (HAR & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (_ & _ & _ & Hfsh).
rewrite Efa, Hfb in Hfsh.
pose proof (asan_consts) as (C1 & _).
assert (Hsf8 : SFa g pos mod 8 = 0) by (apply mod32_mod8; exact SF32).
destruct (b_sh_apart (SFa g pos) mf SF0 SF1 SFapp Hsf8 Hac) as (Hd0 & Hd8 & Hsmf & Hsfr).
assert (B23 : bv_unsigned (ew (b_E regs2 (SFa g pos)) 23) = SHADOW_OFF + SFa g pos / 8).
{ rewrite (b_E_reg regs2 (SFa g pos) 23 23%bv eq_refl), Hsh. unfold w64, shadow_addr. apply unsigned_lit_small.
  clear - Hd0 Hsmf Hac Hmf Hsp47. unfold SHADOW_OFF in *. lia. }
assert (B9 : bv_unsigned (ew (b_E regs2 (SFa g pos)) 9) = mf).
{ rewrite (b_E_reg regs2 (SFa g pos) 9 9%bv eq_refl), Hs1. unfold w64. apply unsigned_lit_small. lia. }
assert (HR1 : region_ok SEGS (b_E regs2 (SFa g pos)) (rd W2 mem2) b_rmf64).
{ unfold region_ok, b_rmf64. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite B9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ mf 64 8 (SOff 32 0) (SFa g pos)).
  - cbn [sv_denot]. rewrite b_E_32, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia.
  - exact V64. }
assert (HR2 : region_ok SEGS (b_E regs2 (SFa g pos)) (rd W2 mem2) b_rhw).
{ unfold region_ok, b_rhw. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite B23. split; [unfold SHADOW_OFF; lia|]. split; [clear - Hd0 Hsmf Hac Hmf Hsp47; unfold SHADOW_OFF in *; lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS).
  replace (SHADOW_OFF + SFa g pos / 8 + o) with (shadow_addr (SFa g pos) + o) by (unfold shadow_addr; lia).
  exact (proj1 (Hfsh o ltac:(change (1024 / 8) with 128; lia))). }
assert (HPD : pairwise_disjoint (b_E regs2 (SFa g pos)) [b_rmf64; b_rhw]).
{ cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact Logic.I] | split; exact Logic.I].
  unfold extent_disjoint, b_rmf64, b_rhw. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B9, B23.
  right. clear - Hsmf. lia. }
pose proof (b_entry W2 regs2 mem2 0x348 (SFa g pos) [b_rmf64; b_rhw] eq_refl
  ltac:(apply Forall_cons; [exact HR1 | apply Forall_cons; [exact HR2 | apply Forall_nil]]) HPD) as HS0.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite HR; reflexivity)
  eq_refl) as HS.
clear HS0. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x348)) with (Z_to_bv 64 (BASE + 0x348)).
paj_run_to_sh RUNTOP HS HJ 880.
{ apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHADOW_OFF + SFa g pos / 8)); [reflexivity | exact B23 | |
    apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. right. right. exists 4, pos. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa, Hfb. change (1024 / 8) with 128. lia. }
pmkst HS.
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (19%bv : bv 5) R19.
rewrite b_E_32, unsigned_lit_small in Ra0 by lia. rewrite b_E_32, unsigned_lit_small in R19 by lia.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HRW.
unfold region_ok in HRW.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HRW.
destruct HRW as (_ & _ & _ & HCH). rewrite B23 in HCH.
pose proof (val_of_chunk_ok SEGS _ _ _ 55 1 (SLit 4) 4 (Forall_inv HCH) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V55.
pose proof (val_of_chunk_ok SEGS _ _ _ 54 1 (SLit 0) 0 (Forall_inv (Forall_inv_tail HCH)) eq_refl ltac:(cbn; lia)
  ltac:(cbn; lia)) as V54.
apply SRr_ret.
assert (KRUN : forall a, b_kz (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. unfold b_kz, b_ec_at in Ha.
  apply (b_frame_w _ _ _ _ _ a b_W7 HF); [vm_compute; reflexivity | clear - Ha Hd0 Hsmf Hac Hmf Hsp47 SF0 SF1 C1; unfold SHADOW_OFF in *; lia|].
  intros b wlo whi Hin. destruct Hin as [E1 | [E1 | []]]; injection E1 as <- <- <-; cbn [base_val]; [lia|].
  rewrite B23. clear - Ha Hsmf Hsfr Hmf. lia. }
pose proof (b_car_keep g pos mf ly2 S2 W2 regs2 mem2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) SF32 ltac:(lia) HCAR
  (Permutation_refl _) R18 R23 R25 KRUN) as Hcar.
pose proof (b_ec_keep g pos mf ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ 0 HEC HJ
  (proj1 (proj2 Hcar)) Rsp R9 R8 Rgp Rtp (fun a Ha => KRUN a (or_introl Ha))) as Hec.
destruct Hcar as (Hid & Hhb & Hmid' & Hsh' & H18' & H25').
unfold inv_B_end, acut. exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
split; [reflexivity|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact HK|]. split; [exact HMLE|].
split; [exact HMOK|]. split; [exact Hec|].
refine (conj Hid (conj Hhb (conj Hmid' (conj Hsh' _)))).
split; [rewrite R19; reflexivity|]. split; [rewrite Ra0; reflexivity|]. split; [exact Ra1|]. split; [exact Ra2|].
split; [exact H18'|]. split; [exact H25'|].
change (shadow_addr (SFa g pos + V_hw)) with (shadow_of_addr SHADOW_OFF (SFa g pos + 432)).
change (shadow_addr (SFa g pos + V_hw + 8)) with (shadow_of_addr SHADOW_OFF (SFa g pos + 432 + 8)).
replace (SFa g pos + 432 + 8) with (SFa g pos + 440) by lia.
rewrite !b_sh_off by exact Hsf8. change (432 / 8) with 54. change (440 / 8) with 55.
split; [exact (aview_of_val_mem1 SEGS _ _ _ _ V54 ltac:(lia)) | exact (aview_of_val_mem1 SEGS _ _ _ _ V55 ltac:(lia))].
Qed.

(* ---- +0x280 (0x809f4) .. +0x2b0: id's shadow, reac_identity_init(NULL) in line, mf+184, reac_identity_init(&id) - *)
(* The facts of inv_A_end the segment uses. *)
Definition b_st0 (g : ectx) (pos mf : Z) : world SEGS -> config -> Prop :=
  ACUT g pos mf 0 (BASE + 0x280) (fun ly2 S2 W2 regs2 mem2 md2 =>
    hblocks B g ly2 S2 [] /\ sh_reg g pos regs2 /\ getr regs2 16 = w64 (SFa g pos) /\
    getr regs2 18 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g)).
(* id's shadow cells (0x809f8..0x80a0c), reac_identity_init's 16-byte frame below sp (0x83a84..0x83aa0), mf+184
   (0x80a18). *)
Definition b_rsh : YP09.region := YP09.mkRegion (Some 23%nat) 44 49 44 49 [].
Definition b_rcf : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [].
Definition b_rmw : YP09.region := YP09.mkRegion (Some 9%nat) 184 192 184 192 [].
Definition b_W0 : list (option nat * Z * Z) := [(Some 23%nat, 44, 49); (Some 2%nat, -16, 0); (Some 9%nat, 184, 192)].
Lemma b_S0 : forall g pos mf W2 c2,
  b_st0 g pos mf W2 c2 -> SRr SEGS W2 c2 (b_st g pos mf 0x2b0 (fun _ => True)).
Proof.
intros g pos mf W2 c2 HC.
destruct HC as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & HFR & HK & HMLE & HMOK & HEC & (HB & Hsh & H16 & H18 & H25)).
destruct (b_prep g pos mf ly2 S2 W2 regs2 mem2 md2 0 HJ HFR HEC) as
  ((Hac & Hsp47 & Hmf32 & Hmf & Hsp16 & Hstk & Hm16) & (SF0 & SF1 & SFapp & SF32 & Efa & Hfb & Hin4)).
pose proof HEC as (Hsp & Hs1 & Hs0 & _ & _ & Hgp & Htp & _).
pose proof HJ as HJ0.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 4 pos HAR Hin4) as (_ & _ & _ & Hfsh).
rewrite Efa, Hfb in Hfsh.
pose proof (asan_consts) as (C1 & _).
assert (Hsf8 : SFa g pos mod 8 = 0) by (apply mod32_mod8; exact SF32).
destruct (b_sh_apart (SFa g pos) mf SF0 SF1 SFapp Hsf8 Hac) as (Hd0 & Hd8 & Hsmf & Hsfr).
assert (B23 : bv_unsigned (ew (b_E regs2 (SFa g pos)) 23) = SHADOW_OFF + SFa g pos / 8).
{ rewrite (b_E_reg regs2 (SFa g pos) 23 23%bv eq_refl), Hsh. unfold w64, shadow_addr. apply unsigned_lit_small.
  clear - Hd0 Hsmf Hac Hmf Hsp47. unfold SHADOW_OFF in *. lia. }
assert (B9 : bv_unsigned (ew (b_E regs2 (SFa g pos)) 9) = mf).
{ rewrite (b_E_reg regs2 (SFa g pos) 9 9%bv eq_refl), Hs1. unfold w64. apply unsigned_lit_small. lia. }
assert (B2 : bv_unsigned (ew (b_E regs2 (SFa g pos)) 2) = mf).
{ rewrite (b_E_reg regs2 (SFa g pos) 2 2%bv eq_refl), Hsp. unfold w64. apply unsigned_lit_small. lia. }
assert (HPS : forall a, mf - 16 <= a < mf + 192 -> apresent (w_H W2) mem2 a) by (intros a Ha; apply Hpres; lia).
assert (HRS : Forall (region_ok SEGS (b_E regs2 (SFa g pos)) (rd W2 mem2)) [b_rsh; b_rcf; b_rmw]).
{ repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val b_rsh b_rcf b_rmw].
  - rewrite B23. split; [unfold SHADOW_OFF; lia|]. split; [clear - Hd0 Hsmf Hac Hmf Hsp47; unfold SHADOW_OFF in *; lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS).
    replace (SHADOW_OFF + SFa g pos / 8 + o) with (shadow_addr (SFa g pos) + o) by (unfold shadow_addr; lia).
    exact (proj1 (Hfsh o ltac:(change (1024 / 8) with 128; lia))).
  - rewrite B2. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HPS. lia.
  - rewrite B9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HPS. lia. }
assert (HPD : pairwise_disjoint (b_E regs2 (SFa g pos)) [b_rsh; b_rcf; b_rmw]).
{ cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, b_rsh, b_rcf, b_rmw.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite B2, B9, B23.
  repeat split; try exact Logic.I; clear - Hsmf; lia. }
pose proof (b_entry W2 regs2 mem2 0x280 (SFa g pos) [b_rsh; b_rcf; b_rmw] eq_refl HRS HPD) as HS. b_norm_ss HS.
pose proof (b_E_img regs2 (SFa g pos)) as HEI.
unfold cfg_at. change (w64 (BASE + 0x280)) with (Z_to_bv 64 (BASE + 0x280)).
(* run 1: 0x809f4 .. the call at 0x80a14 (a0 = 0) *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHADOW_OFF + SFa g pos / 8)); [reflexivity | exact B23 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. right. right. exists 4, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa, Hfb. change (1024 / 8) with 128. lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (mf - e_sp0 g));
    [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo b_rcf]; lia | cbn [YP09.r_whi b_rcf]; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - e_sp0 g));
    [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo b_rmw]; lia | cbn [YP09.r_whi b_rmw]; lia |].
  apply awr_ok_nil. }
rename ms into ms1. rename HJ into HJ1. rename HF into HF1. clear HFr HG.
(* reac_identity_init(NULL): its own code, in line (0x83a84 addi sp; sd ra; beqz a0 taken; ld ra; addi sp; ret) *)
rewrite (PSIG IB_reac_identity_init AF_reac_identity_init eq_refl) in HS.
lazymatch type of HS with st_ok _ ?Ex (?sp ?X _) ?M =>
  assert (HS' : st_ok_pi SEGS VAL Ex (sp X AF_reac_identity_init) M) by exact HS end.
clear HS. rename HS' into HS. b_norm_ss HS.
(* run 2: the callee's NULL path and back, 0x80a18 .. the call at 0x80a20 (a0 = &id) *)
paj_run_shc RUNP RUNC HS HJ1.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat (SHADOW_OFF + SFa g pos / 8)); [reflexivity | exact B23 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right. right. right. exists 4, pos. split; [left; reflexivity|].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa, Hfb. change (1024 / 8) with 128. lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (mf - e_sp0 g));
    [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - e_sp0 g));
    [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  apply awr_ok_nil. }
rename ms into ms2. rename HJ1 into HJ2. rename HF into HF2. clear HFr HG.
pmkst HS.
rewrite (PSIG IB_reac_identity_init AF_reac_identity_init eq_refl).
b_regs HS regs2 (SFa g pos) Rra Rsp Rgp Rtp R8 R9 R18 R23 R25.
prreg HS (10%bv : bv 5) Ra0.
rewrite (b_E_reg regs2 (SFa g pos) 16 16%bv eq_refl), H16 in Ra0. unfold w64 in Ra0.
rewrite unsigned_lit_small in Ra0 by lia.
assert (Qsp : spZ (ms_regs ms2) = mf) by (unfold spZ; rewrite Rsp, Hsp; unfold w64; apply unsigned_lit_small; lia).
(* what run 1 and run 2 wrote: id's five shadow cells and mf+184 *)
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as HRG0.
pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as HRG2.
unfold region_ok in HRG0, HRG2.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict] in HRG0, HRG2.
destruct HRG0 as (_ & _ & _ & HCH0). destruct HRG2 as (_ & _ & _ & HCH2). rewrite B23 in HCH0. rewrite B9 in HCH2.
pose proof (Forall_inv HCH0) as C48. pose proof (Forall_inv (Forall_inv_tail HCH0)) as C47.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCH0))) as C46.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HCH0)))) as C45.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HCH0))))) as C44.
pose proof (Forall_inv HCH2) as C184.
clear HCH0 HCH2.
assert (SB : forall o v, (o = 44 /\ v = 0) \/ (o = 45 /\ v = 0) \/ (o = 46 /\ v = 0) \/ (o = 47 /\ v = 0) \/ (o = 48 /\ v = 6) ->
  aview SEGS (w_H W2) (ms_mem ms2) (SHADOW_OFF + SFa g pos / 8 + o) = Some v).
{ intros o v Hov. apply (aview_of_val_mem1 SEGS); [|lia].
  destruct Hov as [(-> & ->) | [(-> & ->) | [(-> & ->) | [(-> & ->) | (-> & ->)]]]];
  [ exact (val_of_chunk_ok SEGS _ _ _ 44 1 (SLit 0) 0 C44 eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
  | exact (val_of_chunk_ok SEGS _ _ _ 45 1 (SLit 0) 0 C45 eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
  | exact (val_of_chunk_ok SEGS _ _ _ 46 1 (SLit 0) 0 C46 eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
  | exact (val_of_chunk_ok SEGS _ _ _ 47 1 (SLit 0) 0 C47 eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
  | exact (val_of_chunk_ok SEGS _ _ _ 48 1 (SLit 6) 6 C48 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) ]. }
assert (VMID : val_mem SEGS (rd W2 (ms_mem ms2)) (mf + 184) 8 (SFa g pos + 352)).
{ apply (val_of_chunk_ok SEGS _ _ _ 184 8 (SOff 16 352) (SFa g pos + 352) C184).
  - cbn [sv_denot]. rewrite (b_E_reg regs2 (SFa g pos) 16 16%bv eq_refl), H16. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
clear C44 C45 C46 C47 C48 C184.
assert (BS : block_shadow (aview SEGS (w_H W2) (ms_mem ms2)) SHADOW_OFF (SFa g pos + 352) 38).
{ split; [rewrite Zplus_mod, Hsf8; reflexivity|]. split; [lia|]. intros i Hi. change ((38 + 7) / 8) with 5 in Hi.
  rewrite (b_sh_off (SFa g pos) 352 Hsf8). change (352 / 8) with 44. change (38 / 8) with 4. change (38 mod 8) with 6.
  replace (SHADOW_OFF + SFa g pos / 8 + 44 + i) with (SHADOW_OFF + SFa g pos / 8 + (44 + i)) by lia.
  assert (Hi5 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  destruct Hi5 as [-> | [-> | [-> | [-> | ->]]]];
    [ apply (SB 44 0) | apply (SB 45 0) | apply (SB 46 0) | apply (SB 47 0) | apply (SB 48 6) ]; lia. }
(* reac_identity_init(&id) at 0x80a20 *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?Q =>
  change (SRr SEGS W2 (cfg_at SEGS (BASE + AF_reac_identity_init) rg mm mdx) Q) end.
pose proof HJ2 as (HAR2 & _).
eapply SRr_bind.
{ apply (HINIT LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly2 S2 W2 _ _ 0 _
    (SFa g pos + 352) HJ2).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Rgp. exact Hgp.
  - rewrite Rtp. exact Htp.
  - exact Ra0.
  - rewrite Qsp. apply b_m16. exact Hmf32.
  - rewrite Qsp. unfold reac_identity_init.REAC_IDENTITY_INIT_STK, ESTACK. lia.
  - rewrite Qsp. lia.
  - intros a Ha. right. exists 4, pos. split; [exact Hin4|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa, Hfb.
    unfold reac_identity_init.IDENT_SIZE in Ha. lia.
  - intros a Ha. unfold reac_identity_init.IDENT_SIZE in Ha.
    assert (Hw : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly2 S2) ly2 [(4, pos)] a).
    { right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite Efa, Hfb. lia. }
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2 Hw) as [Hp Ho].
    split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|]. rewrite Qsp. unfold ESTACK. lia.
  - eapply block_shadow_range; [exact BS | lia | unfold reac_identity_init.IDENT_SIZE; lia].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS ly2 S2 W2 _ _ 4 pos (SFa g pos + 352) 38 HAR2 Hin4);
      rewrite ?Efa, ?Hfb; unfold reac_identity_init.IDENT_SIZE; lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HFR3 & HPm3 & Hz3 & HT3).
rewrite Rra. apply SRr_ret.
rewrite Qsp in HT3.
destruct (b_pres _ _ HP3) as (P2 & P3 & P4 & P8 & P9 & P18 & _ & P23 & P25).
assert (HB3 : hblocks B g ly3 S3 []) by (destruct HB as [HBp HBf]; split; [exact (Permutation_trans HPm3 HBp) | exact HBf]).
(* what the call kept: the machine frame, the frame's flag word, id's shadow and mf+184 *)
assert (KC : forall a, (b_ec_at (e_sp0 g) (SFa g pos) mf a \/ (mf + 184 <= a < mf + 192) \/
    (SHADOW_OFF + SFa g pos / 8 + 44 <= a < SHADOW_OFF + SFa g pos / 8 + 49)) ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms2) a).
{ apply (b_keep_tcj_on g pos mf _ ly2 S2 W2 (ms_mem ms2) W3 mem3 _ _ HT3 ltac:(lia) ltac:(lia) Hsp47 Hin4 Efa SF32
    ltac:(lia)).
  - intros a Ha. unfold b_kz. destruct Ha as [Ha | [Ha | Ha]]; [left; exact Ha | right; left; exact Ha |
      right; right; right; exact Ha].
  - intros a Ha Hid. unfold reac_identity_init.IDENT_SIZE in Hid. unfold b_ec_at in Ha.
    clear - Ha Hid Hsfr Hsmf Hmf Hac SF1. lia. }
assert (KR : forall a, b_ec_at (e_sp0 g) (SFa g pos) mf a -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. unfold b_ec_at in Ha.
  assert (Hr : 0 <= a < 2 ^ 64) by (clear - Ha Hac Hmf Hsp47 SF0 SF1 C1; lia).
  assert (HN : forall b wlo whi, In (b, wlo, whi) b_W0 ->
    ~ (base_val (b_E regs2 (SFa g pos)) b + wlo <= a < base_val (b_E regs2 (SFa g pos)) b + whi)).
  { intros b wlo whi Hin. destruct Hin as [E1 | [E1 | [E1 | []]]]; injection E1 as <- <- <-; cbn [base_val];
      [rewrite B23 | rewrite B2 | rewrite B9]; clear - Ha Hsmf Hsfr Hmf Hac SF1; lia. }
  rewrite (b_frame_w _ _ _ _ _ a b_W0 HF2 ltac:(vm_compute; reflexivity) Hr HN).
  exact (b_frame_w _ _ _ _ _ a b_W0 HF1 ltac:(vm_compute; reflexivity) Hr HN). }
assert (HEC3 : ECOMMON g pos mf ly3 S3 W3 regs3 mem3 md3).
{ apply (b_ec_keep g pos mf ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 0 HEC HJ3 HB3).
  - rewrite P2. exact Rsp.
  - rewrite P9. exact R9.
  - rewrite P8. exact R8.
  - rewrite P3. exact Rgp.
  - rewrite P4. exact Rtp.
  - intros a Ha. rewrite (KC a (or_introl Ha)). exact (KR a Ha). }
apply (b_mk g pos mf 0x2b0 (fun _ => True) S2 ly3 S3 W3 regs3 mem3 md3 HMOK HJ3 ltac:(rewrite HFR3; exact HFR) HEC3);
  [|exact Logic.I].
refine (conj (conj _ (conj _ _)) (conj HB3 (conj _ (conj _ (conj _ _))))).
- unfold m_id, V_id. cbn [SlotModel.rec_id]. apply b_id0. intros i Hi.
  unfold reac_identity_init.IDENT_SIZE in Hz3. exact (Hz3 i Hi).
- unfold sh_zero, zero_shadow, V_id, N_id. change (38 / 8) with 4. intros i Hi.
  rewrite (b_sh_off (SFa g pos) 352 Hsf8). change (352 / 8) with 44.
  rewrite KC by (right; right; lia).
  replace (SHADOW_OFF + SFa g pos / 8 + 44 + i) with (SHADOW_OFF + SFa g pos / 8 + (44 + i)) by lia. apply SB.
  assert (Hi4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct Hi4 as [-> | [-> | [-> | ->]]]; [left | right; left | right; right; left | right; right; right; left];
    split; reflexivity.
- unfold sh_blk, V_id, N_id. apply (block_shadow_agree (aview SEGS (w_H W2) (ms_mem ms2))); [|exact BS].
  intros i Hi. change ((38 + 7) / 8) with 5 in Hi. rewrite (b_sh_off (SFa g pos) 352 Hsf8). change (352 / 8) with 44.
  apply KC. right; right. lia.
- unfold mf_id, V_id. eapply (val_mem_kept SEGS); [|exact VMID]. intros kk Hk. apply KC. right; left. cbn in Hk. lia.
- unfold sh_reg. rewrite P23, R23. exact Hsh.
- rewrite P18, R18. exact H18.
- rewrite P25, R25. exact H25.
Qed.

(* ---- the segment -------------------------------------------------------------------------------------------- *)
Lemma seg_B : seg_B_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS.
Proof.
unfold seg_B_stmt. intros g pos mf W2 c2 HA.
assert (H0 : b_st0 g pos mf W2 c2).
{ unfold inv_A_end, acut in HA. unfold b_st0, acut.
  destruct HA as (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & HFR & HK & HMLE & HMOK & HEC &
    (_ & _ & _ & HB & Hsh & H16 & H18 & H25)).
  exists ly2, S2, regs2, mem2, md2.
  exact (conj Hc (conj HJ (conj HFR (conj HK (conj HMLE (conj HMOK (conj HEC
    (conj HB (conj Hsh (conj H16 (conj H18 H25))))))))))). }
eapply SRr_bind; [exact (b_S0 g pos mf W2 c2 H0)|]. intros W3 c3 _ H3.
eapply SRr_bind; [exact (b_T1 g pos mf W3 c3 H3)|]. intros W4 c4 _ H4.
eapply SRr_bind; [exact (b_T2 g pos mf W4 c4 H4)|]. intros W5 c5 _ H5.
eapply SRr_bind; [exact (b_T3 g pos mf W5 c5 H5)|]. intros W6 c6 _ H6.
eapply SRr_bind; [exact (b_T4 g pos mf W6 c6 H6)|]. intros W7 c7 _ H7.
eapply SRr_bind; [exact (b_T5 g pos mf W7 c7 H7)|]. intros W8 c8 _ H8.
eapply SRr_bind; [exact (b_T6 g pos mf W8 c8 H8)|]. intros W9 c9 _ H9.
exact (b_T7 g pos mf W9 c9 H9).
Qed.
Check (seg_B : seg_B_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
  ameta_inv arodata_okS).

End c.
End b.
End a.
Print Assumptions seg_B.
