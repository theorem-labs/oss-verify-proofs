(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102, pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994): SEGMENT S1 of the walk of parse_noting (the B'
   twin of row N10-PNA; cut table lib/B/Prog/PN102BCuts.v): the entry (the batch kit's tparse_noting_specX pre, pn_pre) to cut_S2
   at +0x28: +0x00 addi sp,sp,-48; +0x04 .. +0x14 sd ra / s0 / s1 / s2 / s3 at 40 / 32 / 24 / 16 / 8 (sp); +0x18 mv
   s0,a2; +0x1c mv s2,a1; +0x20 mv s3,a0 (one run of the symbolic engine, YC1fPx.v's paj_run_x_inv with the memnorm
   carrier, as lib/B/Prog/FuzzStrdupB.v); +0x24 jal fuzz_alloc_live through its batch-kit text tfuzz_alloc_live_specX (owner
   a Theorem Labs lane) by YCbqGcall.v aj_call_x; the five saved words read off the run's stack region (YI04.v
   val_of_chunk_ok) and kept across the callee by its journal; pj_parse's slot word (the entry sp - 96, cut_S2's last
   conjunct, the word of pn_cw's arm 2) kept by the run (it writes only [sp0 - 48, sp0)) and by the callee (its
   journal at sp0 - 48 with STK_fuzz_alloc_live = 0 keeps every byte above the ceiling). The journal at cut_S2 is at
   the empty budget (pn_frame .. []: no wild site before pj_parse).
   rule 24: proves function parse_noting (fuzz_preset, image B') (preparation; proof-index 03:20Z: 0 named / 0 by
   address / 0 released; the rule-24 parse_noting check CONFIRM 03:25Z; PORT of a Theorem Labs lane's image-A' file of the same role,
   a working branch lib/A/Prog/PN102S1.v 13970867e0c, at PI_prog_B / prh_img_B). This file:
   segment S1 of that walk.
   CHANGED from the A' file: the fpre has five conjuncts (frm_zero at entry, FRM0-ENTRY), passed to the callee's
   fpre; cut_S2's slot equation; lib/A/Prog/S1ImgA.v not required (it Requires lib/A/PRH_Img.v and nothing of it is
   used).
   SHAPES TAKEN: the entry state, the write and keep tactics and the call idiom are lib/A/Prog/FuzzStrdup.v's (sd_entry,
   sd_awr, sd_keep; its fuzz_malloc call), at this frame of 48 bytes.
   NUMERALS: 48 (the frame, LENGTH), 8 .. 40 (the save slots, LENGTH), 96 (the frames of parse_noting and pj_parse,
   LENGTH), 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (the engine's shadow and stack bounds), atom indices of the engine. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PN102BCuts PN102BHelp PN102BKeep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at parse_noting's entry: its frame of 48 bytes below the entry sp (atom 2), sp in the stack band
   astk_ok gives; no shadow entry (the body makes no instrumented access) *)
Definition PN_Bx : sv := SOff 32 0.
Definition PN_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pn_regions : smem := [ stack_region PN_FRAME ].
Definition pn_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition ss_pn : sstate := mkSS PN_SLOT0 sr_atoms pn_regions None pn_facts.
Definition pn_SH : list shent := [].

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation PL := PL_prog_B.
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val rc B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val rc B_prog_listing PA A_TEXT).
#[local] Abbreviation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Abbreviation PST := (@prh_pst prh_img_B).
#[local] Abbreviation RL := (prh_room_live_a8 (cp := CP)).
Definition PN_EI (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).

Lemma pn_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* a word the run stored, read back as a reader's eight bytes *)
Lemma pn_chunk_rd64 : forall E (H : word -> bool) (m : word -> option byte) base off e v,
  YP09.chunk_ok SEGS E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rd64 (aview SEGS H m) (base + off) v.
Proof.
intros E H m base off e v Hc He Hv.
pose proof (val_of_chunk_ok SEGS E (mrestrict H m) base off 8 e v Hc He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)) as HV.
intros k Hk. unfold aview. specialize (HV k ltac:(cbn in Hk |- *; lia)). rewrite HV. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte.
apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

Ltac pn_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; unfold PN_FRAME; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].

Ltac pn_keep K H rg Wx HU :=
lazymatch type of K with
| frame_of ?Ex ?rsx (mrestrict _ ?mA) (mrestrict _ ?mB) =>
assert (H : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg - 48 <= a < spZ rg) ->
aview SEGS (w_H Wx) mB a = aview SEGS (w_H Wx) mA a)
by (intros a Ha Hn; apply (pn_aview_of_frame Wx Ex rsx mA mB a K); [|exact Ha];
intros (r & Hin & Hr); vm_compute in Hin;
destruct Hin as [Hin | Hin]; [subst r | destruct Hin];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?ew_havoc_old in Hr by (cbv; lia);
rewrite HU in Hr; lia)
end.

(* registers by their unsigned index *)
Lemma pn1_getr_eq : forall regs (r r' : bv 5), bv_unsigned r = bv_unsigned r' -> getr regs r = getr regs r'.
Proof. intros regs r r' H. apply bv_eq in H. subst r'. reflexivity. Qed.

Lemma pn1_val_mem_move : forall (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> mbyte SEGS m' (a + Z.of_nat k) = mbyte SEGS m (a + Z.of_nat k)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v HK H k Hk. rewrite (HK k Hk). exact (H k Hk). Qed.

Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B (AR_laws_ok_cf (cp := CP) SEGS B).
#[local] Abbreviation Hsegs := (@pa_segs_low rc B_prog_listing PA).

(* the read-only view moves with the image bytes *)
Lemma pn1_rod_move : forall (W : world SEGS) m m',
  (forall a, in_img SEGS a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W) m) ->
  arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B (aview SEGS (w_H W) m').
Proof.
intros W m m' HK HRO a Hro Hn1 Hn2.
assert (Hi : in_img SEGS a).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr];
    [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
rewrite (HK a Hi). exact (HRO a Hro Hn1 Hn2).
Qed.

(* the ledger moves with the bytes below the ceiling (its statics and its blocks' heads are there) *)
Lemma pn1_ledger_move : forall ly S Hp (W W' : world SEGS) mem mem' md Lam peak cnt fail ran most own,
  ARc ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling ->
     mbyte SEGS (mrestrict (w_H W') mem') a = mbyte SEGS (mrestrict (w_H W) mem) a) ->
  prh_ledger B ly S Hp W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W W' mem mem' md Lam peak cnt fail ran most own HAR (HG & HND & HB & HP) HK.
pose proof (@ASAN_CEIL_range rc) as [[HC0 HC1] _]. unfold ASAN_CEIL in HC0, HC1.
assert (KS : forall a n v, 0 <= a -> a + Z.of_nat n <= YM05.alloc_ceiling ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W') mem') a n v).
{ intros a n v H0 H1 H. apply (pn1_val_mem_move (mrestrict (w_H W) mem) (mrestrict (w_H W') mem') a n v); [|exact H]. intros k Hk. apply HK. lia. }
destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6b) & (G7 & G7b) & GB).
split; [|split; [exact HND|split; [|exact HP]]].
- split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_live + _)%Z; lia | exact G1]|].
  split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_peak + _)%Z; lia | exact G2]|].
  split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_count + _)%Z; lia | exact G3]|].
  split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_fail + _)%Z; lia | exact G4]|].
  split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_ran_out + _)%Z; lia | exact G5]|].
  split; [split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_most + _)%Z; lia | exact G6] | exact G6b]|].
  split; [split; [apply KS; [vm_compute; congruence | vm_compute (pi_g_own_ran_out + _)%Z; lia | exact G7] | exact G7b]|].
  exact GB.
- apply Forall_forall. intros [a k] Hin. pose proof (proj1 (Forall_forall _ _) HB (a, k) Hin) as (Hk & Hab & Hhp & Hal & Hv).
  cbn [fst snd] in *.
  destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
  assert (Hcf : @cf_head CP = 16) by reflexivity. rewrite Hcf in *.
  unfold req_size in Hc. destruct (Z.eqb_spec (k + 16) 0); [lia|].
  split; [exact Hk|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Hal|].
  apply KS; [lia | cbn; lia | exact Hv].
Qed.

Lemma pn_entry : forall STK ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARc STK ly S Hp W regs mem md ch -> PN_FRAME <= STK ->
  st_ok_pi SEGS VAL (PN_EI regs) ss_pn (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PN_SLOT0)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS PN_Bx pn_SH (PN_EI regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H48.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := PN_EI regs) in *.
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold PN_EI; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold ss_pn. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold pn_regions, stack_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Usp. unfold PN_FRAME in *. split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [pn_regions pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact I]].
    cbn [pn_facts f_atoms atoms_ok].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia].
- unfold sh_ok, pn_SH. apply Forall_nil.
Qed.

Theorem pn_seg_S1 : forall CTX0,
  pn_seg_S1_stmt (fx := fx) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PA) B ARc SK CTX0.
Proof.
intros CTX0 HT X HPRE.
pose proof (pp_fpre _ _ _ _ HPRE) as (HPREx & HROD & HSHI & HRAM & HFRM).
pose proof HPREx as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
let v := eval vm_compute in (@STK_parse_noting prh_img_B) in
assert (EST : @STK_parse_noting prh_img_B = v) by (vm_compute; reflexivity).
let v := eval vm_compute in (@STK_fuzz_alloc_live prh_img_B) in
assert (ESL : @STK_fuzz_alloc_live prh_img_B = v) by (vm_compute; reflexivity).
set (regs := px_regs X) in *. set (W := px_W X) in *. set (mem := px_mem X) in *. set (md := px_md X) in *.
set (ly := px_ly X) in *. set (S := px_S X) in *. set (Hp := px_Hp X) in *.
destruct (pn_entry STK_parse_noting ly S Hp W regs mem md (px_ch X) HPREx ltac:(rewrite EST; unfold PN_FRAME; lia))
  as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARc STK_parse_noting [(px_doc X, px_doc X + 56)]
  ly S Hp W regs mem md (px_ch X) HPREx) as HJ.
remember (PN_EI regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold PN_EI; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n) by (intros n Hn; subst E; unfold PN_EI; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
pose (RUNM := paj_run_x_inv (SK := SK) (PL := PL) (PI := PA) B PST ARc LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (YSRrMemnorm.srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS))).
unfold cfg_at. change (w64 (SIGMA AS_parse_noting)) with (Z_to_bv 64 (BASE + PN_SLOT0)).
pose proof (fun H : YAkMemnorm.memnorm SEGS mem => H) as HPM.
paj_run_tok_x_inv RUNM HS HJ SHOK HPM PN_Bspan; [pn_awr regs Usp|].
clear HF HG.
pn_keep HFr KA regs W Usp. clear HFr.
prreg HS (2%bv : bv 5) P2. prreg HS (1%bv : bv 5) P1. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
pose proof (@ASAN_CEIL_range rc) as [[HC0 HC1] _]. unfold ASAN_CEIL in HC0, HC1.
assert (ER : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] n r Hr). }
pose proof (pp_out _ _ _ _ HPRE) as (_ & (Hd0 & Hdc & _)).
pose proof (pp_a0 _ _ _ _ HPRE) as A10. pose proof (pp_a1 _ _ _ _ HPRE) as A11.
pose proof (pp_a2 _ _ _ _ HPRE) as A12.
fold regs in A10, A11, A12.
(* the bytes below the stack frame are the entry's *)
assert (KB : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply KA; [lia|]. rewrite EST in Hslo. lia. }
assert (ROD1 : arodata_okP SEGS (@pa_relro_lo rc B_prog_listing PA) (@pa_relro_hi rc B_prog_listing PA) B
                 (aview SEGS (w_H W) (ms_mem ms))).
{ apply (pn1_rod_move W mem (ms_mem ms)); [|exact HROD]. intros a Hi. pose proof (Hsegs a Hi) as Ha.
  apply KB. unfold kLowMemEnd in Ha. lia. }
assert (LED1 : prh_ledger B ly S Hp W (ms_mem ms) (px_Lam X) (px_peak X) (px_cnt X) (px_fail X) (px_ran X)
                 (px_most X) (px_own X)).
{ apply (pn1_ledger_move ly S Hp W W mem (ms_mem ms) md); [exact HAR | exact (pp_ledger _ _ _ _ HPRE) |].
  intros a Ha. unfold mbyte. specialize (KB a Ha). unfold aview, mbyte in KB.
  lazymatch goal with |- ?l = ?r => destruct l as [b1|] eqn:Eb1; destruct r as [b2|] eqn:Eb2 end;
    cbn [option_map] in KB; try discriminate KB; [|reflexivity].
  injection KB as KB. f_equal. apply bv_eq. exact KB. }
assert (HSP1 : spZ (ms_regs ms) = spZ regs + -48).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HSH1 : spZ (ms_regs ms) + 64 <= ly_stk_hi ly) by (rewrite HSP1; lia).
assert (HRAM1 : raZ (ms_regs ms) < YM05.alloc_ceiling).
{ unfold raZ. rewrite P1.
  lazymatch goal with |- bv_unsigned (Z_to_bv 64 ?e) < _ => let v := eval vm_compute in e in change e with v end;
  rewrite unsigned_lit_small by lia; lia. }
(* ---- +0x24 jal fuzz_alloc_live, through its text ---- *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
  eapply (aj_call_x (SK := SK) SEGS B PST ARc LAWS Hsegs W E _ msq STK_parse_noting (spZ regs)
    [(px_doc X, px_doc X + 56)] ly S Hp W mem md [] ly S Hp mdq 0
    (@STK_fuzz_alloc_live prh_img_B) [] (-48) (ew E 2) _ [] _ HS eq_refl HJ) end.
  - exact (st_ok_restrict_reg SEGS (w_H W) E _ _ 2%bv HS).
  - reflexivity.
  - exact Usp.
  - reflexivity.
  - lia.
  - rewrite ESL. lia.
  - rewrite ESL, EST. lia.
  - rewrite P3, (ER 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  - rewrite P4, (ER 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  - exact P1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - lazymatch goal with |- _ <= bv_unsigned (Z_to_bv 64 ?e) => let v := eval vm_compute in e in change e with v end;
    rewrite unsigned_lit_small by lia; lia.
  - apply achain_low. unfold s0Z. rewrite P8, (ER 12%nat 12%bv ltac:(lia) eq_refl), A12. unfold w64.
    rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1.
    exact (HT ly S Hp W _ _ _ [] (px_Lam X) (px_peak X) (px_cnt X) (px_fail X) (px_ran X) (px_most X) (px_own X)
      (conj HPRE1 (conj ROD1 (conj HSH1 (conj HRAM1 HFRM)))) LED1).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJc & HP3 &
  ((Hrl & R10' & EHp & ES & Eab & HL2) & Hmn3)).
apply SRr_ret.
(* the saved words, from the run's region, kept by the callee (its sp is 48 below the entry sp) *)
pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _). cbn [ss_mem setpc ms_mem restrict] in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs). cbn [YP09.r_chunks YP09.r_base base_val] in Hcs.
rewrite Usp in Hcs.
pose proof (Forall_inv Hcs) as C40. pose proof (Forall_inv (Forall_inv_tail Hcs)) as C32.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hcs))) as C24.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hcs)))) as C16.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hcs))))) as C8.
assert (HJc' : ajournal_x (SK := SK) SEGS B PST ARc (@STK_fuzz_alloc_live prh_img_B) (spZ regs + -48) []
    ly S Hp W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) [] ly2 S2 Hp2 W2 mem3 md3 k1) by exact HJc.
assert (SW : forall off (rr : bv 5) (n : nat), 8 <= off <= 40 -> Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) (spZ regs) (YP09.mkChunk (- off) (CVal 8 (SOff n 0))) ->
  rd64 (aview SEGS (w_H W2) mem3) (spZ regs - off) (bv_unsigned (getr regs rr))).
{ intros off rr n Hoff Hn Hn32 Hc.
  apply (pn_rd64_kept (aview SEGS (w_H W) (ms_mem ms))).
  - intros i Hi. apply (pn_above_kept (SK := SK) SEGS B PST ARc _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJc'); [|lia].
    rewrite EST in Hslo. lia.
  - replace (spZ regs - off) with (spZ regs + - off) by lia.
    apply (pn_chunk_rd64 E (w_H W) (ms_mem ms) (spZ regs) (- off) (SOff n 0)); [exact Hc | | apply u64_range].
    cbn [sv_denot]. rewrite (ER n rr Hn32 Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CS : forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr H2 H8 H9 H18 H19. unfold acallee_saved in Hr.
  assert (Hc : r = 3 \/ r = 4 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat destruct Hc as [Hc|Hc]; subst r;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?n) = _ =>
    let Hx := fresh "Hx" in prreg HS (Z_to_bv 5 n) Hx; rewrite Hx;
    let nn := eval vm_compute in (Z.to_nat n) in
    exact (ER nn (Z_to_bv 5 n) ltac:(lia) eq_refl) end. }
assert (G3 : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
  by (intros r Hr; exact (HP3 r Hr)).
let v := eval vm_compute in (PN_SLOT0 + PN_S2) in
assert (ES2 : PN_SLOT0 + PN_S2 = v) by (vm_compute; reflexivity).
exists regs3, mem3, md3, ly2, S2, Hp2, (0 + k1).
split; [rewrite pn_cfg_eq, ES2; reflexivity|].
split.
{ split; [exact HJ3|].
  split.
  { assert (E2r : spZ regs3 = spZ (ms_regs ms)).
    { unfold spZ. f_equal. rewrite (pn1_getr_eq regs3 _ (Z_to_bv 5 2)) by reflexivity.
      rewrite (G3 2 ltac:(unfold acallee_saved; lia)). apply pn1_getr_eq. reflexivity. }
    rewrite E2r, HSP1. unfold PN_FRAME. change (px_regs X) with regs. lia. }
  split; [exact (SW 8 1%bv 1%nat ltac:(lia) eq_refl ltac:(lia) C8)|].
  split; [exact (SW 16 8%bv 8%nat ltac:(lia) eq_refl ltac:(lia) C16)|].
  split; [exact (SW 24 9%bv 9%nat ltac:(lia) eq_refl ltac:(lia) C24)|].
  split; [exact (SW 32 18%bv 18%nat ltac:(lia) eq_refl ltac:(lia) C32)|].
  split; [exact (SW 40 19%bv 19%nat ltac:(lia) eq_refl ltac:(lia) C40)|].
  split; [intros r Hr H2 H8 H9 H18 H19; rewrite (G3 r Hr); exact (CS r Hr H2 H8 H9 H18 H19)|].
  split; [exact (pp_frm _ _ _ _ HPRE)|].
  split; [exact (pn_fregs_refl fx)|].
  split; [intros H0; exact (Hmn3 (HPM H0))|].
  exact (pn_img_keep B _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJc' pn_sink_nil ROD1). }
assert (R8 : getr regs3 8 = getr (ms_regs ms) 8).
{ rewrite (pn1_getr_eq regs3 _ (Z_to_bv 5 8)) by reflexivity. rewrite (G3 8 ltac:(unfold acallee_saved; lia)).
  apply pn1_getr_eq. reflexivity. }
assert (R18 : getr regs3 18 = getr (ms_regs ms) 18).
{ rewrite (pn1_getr_eq regs3 _ (Z_to_bv 5 18)) by reflexivity. rewrite (G3 18 ltac:(unfold acallee_saved; lia)).
  apply pn1_getr_eq. reflexivity. }
assert (R19 : getr regs3 19 = getr (ms_regs ms) 19).
{ rewrite (pn1_getr_eq regs3 _ (Z_to_bv 5 19)) by reflexivity. rewrite (G3 19 ltac:(unfold acallee_saved; lia)).
  apply pn1_getr_eq. reflexivity. }
split; [rewrite R8, P8, (ER 12%nat 12%bv ltac:(lia) eq_refl); exact A12|].
split; [rewrite R18, P18, (ER 11%nat 11%bv ltac:(lia) eq_refl); exact A11|].
split; [rewrite R19, P19, (ER 10%nat 10%bv ltac:(lia) eq_refl); exact A10|].
split; [exact R10'|].
split; [exact ES|]. split; [exact EHp|]. split; [exact Eab|].
split; [exact HL2|].
(* pj_parse's slot word, the entry sp - 96: below the run's writes [sp0 - 48, sp0) and above the ceiling, where the
   callee's journal (at sp0 - 48, STK_fuzz_alloc_live = 0) keeps every byte *)
rewrite pn_frame_B, pn_frame_pj_B. unfold PN_FRAME.
change (px_regs X) with regs. change (px_W X) with W. change (px_mem X) with mem.
pose proof (ajx_hi HJc') as G9. rewrite ESL in G9.
rewrite EST in Hslo.
apply rdword_ext. intros i Hi.
assert (Ha : YM05.alloc_ceiling <= spZ regs - 48 - 48 + i < 2 ^ 64) by (clear - Hi Hceil Hslo Hshi H47; lia).
rewrite (G9 _ Ha) by (clear - Hi; lia).
apply KA; clear - Hi Ha HC0; lia.
Qed.

End I.
