(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module paths, module names and addresses changed; 670 of its 799 lines of code are new or changed and 5936 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame IdentCJ IdentRo
IdentProgSig YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YK1g YK0w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv reac_identity_ingest.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import LLVMFuzzerTestOneInput_D1cut.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition p9_ss : sstate := mkSS 0x5c0 sr_atoms [] None (mkFacts [] [] []).
Definition p7_mf : YP09.region := YP09.mkRegion (Some 9%nat) 136 184 136 168
  [YP09.mkChunk 144 (CVal 8 (SOff 35 0)); YP09.mkChunk 168 (CVal 8 (SOff 33 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition p7_g : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 1 [].
Definition p7_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF d1_SB d1_SB 0);
           (34%nat, mkAF 4096 (2 ^ 47 - 256) 0)] [] [(SAlu ALU_ADD (SOff 18 0) (SOff 22 0), SOff 34 0)].
Definition p7_SH : list shent := [mkSHE 34 0 1].
Definition p7_ssA : sstate := mkSS 0x558 sr_atoms [p7_mf; p7_g] None p7_facts.
Definition p7_sh : YP09.region := YP09.mkRegion (Some 19%nat) 14 19 14 19 [].
Definition p7_extra (SF gb k nb : Z) : list word := map (Z_to_bv 64) [d1_SB; SF + V_again; gb + k; nb].

Lemma d79_garr8_mv : forall segs H H' (m m' : word -> option byte) a b l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') b l.
Proof.
intros segs H H' m m' a b l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (a + Z.of_nat j) (b + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros kk Hkk. replace (b + Z.of_nat j + kk) with (b + (Z.of_nat j + kk)) by lia.
replace (a + Z.of_nat j + kk) with (a + (Z.of_nat j + kk)) by lia. apply Hk. lia.
Qed.
Lemma d79_block_shadow_mv : forall (rd rd' : reader) Bs a n,
  (forall i, 0 <= i < (n + 7) / 8 -> rd' (shadow_of_addr Bs a + i) = rd (shadow_of_addr Bs a + i)) ->
  block_shadow rd Bs a n -> block_shadow rd' Bs a n.
Proof.
intros rd rd' Bs a n Hk (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
intros i Hi. rewrite (Hk i Hi). exact (H3 i Hi).
Qed.
Lemma d79_mod16 : forall mf sp0, mf mod 32 = 0 -> sp0 mod 16 = 0 -> (mf - sp0) mod 16 = 0.
Proof.
intros mf sp0 H1 H2. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia].
apply Z.mod_divide; [lia|]. destruct H1 as [q1 E1]. destruct H2 as [q2 E2]. exists (2 * q1 - q2). lia.
Qed.

Ltac d79_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac d79_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia.

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
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
Hypothesis HUMF : forall c, In c (LLVMF_FREE_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := paj_run_to B LAWS.
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).

Lemma d79_chain : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 mem3 md3 kk (regsT : bvmap 5 word),
  CTX g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 mem3 md3 kk ->
  (forall a, e_sp0 g - 16 <= a < e_sp0 g -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  spZ regsT = mf -> s0Z regsT = e_sp0 g -> 4096 <= raZ regsT ->
  exists ch, chain_pre ly3 (aview SEGS (w_H W3) mem3) regsT ch /\
    (ch = [] \/ ch = [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))]).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 mem3 md3 kk regsT HC HJ3 KEEP Usp Us0 Ura4.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & _ & Hsp0al & H47 & _).
destruct HC as (HJ & _ & _ & _ & _ & HEC & _).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vra & Vs0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HPRE as (HFN & Hraz & _).
pose proof HFN as (_ & _ & Hra4 & _ & _ & _ & _ & Hch0 & _).
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (_ & Hstk0 & Hceil & Hslo & Hshi & H47s & _ & Htop0 & Htop1).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof asan_consts as (C1 & _).
set (sp0 := e_sp0 g) in *.
change (spZ (e_regs g)) with sp0 in Hch0.
assert (Hach : achain ly3 (aview SEGS (w_H (e_W g)) (e_mem g)) sp0 (s0Z (e_regs g)) []).
{ apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
destruct (Z_lt_le_dec sp0 (ly_top ly3 - 16)) as [Hlt | Hge].
- exists [(sp0, RA_LLVMF, s0Z (e_regs g))]. split; [|right; reflexivity].
  eapply (achain_chain_pre ly3 _ mf sp0); [| rewrite Usp; clear - Hmf0; unfold ASTACK in *; lia | exact Us0 | exact Ura4].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  apply (achain_push ly3 _ _ sp0 (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
  + rewrite ETop. clear - Htop1 Hshi H47s. lia.
  + intros a Ha. apply F1; clear - Ha Hceil Hslo Hstk0; lia.
  + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - Hraz Rra; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (sp0 - 8) (sp0 - 8) 8 RA_LLVMF); [|exact Vra].
    intros kk' Hkk. apply KEEP; clear - Hkk; lia.
  + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (sp0 - 16) (sp0 - 16) 8 (s0Z (e_regs g))); [|exact Vs0].
    intros kk' Hkk. apply KEEP; clear - Hkk; lia.
  + rewrite <- Hraz. exact Hra4.
  + clear - Hceil Hslo Hstk0. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmfb. lia.
- exists []. split; [|left; reflexivity].
  eapply (achain_chain_pre ly3 _ mf sp0 []); [| rewrite Usp; clear - Hmf0; unfold ASTACK in *; lia | exact Us0 | exact Ura4].
  left. split; [right; left; exact Hge | reflexivity].
Qed.

Theorem d1_ph9 : d1_ph9_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3 HC HR.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ2 & Hfrs2 & Hk2 & MLE2 & MOK2 & HEC & Hi & _ & _ & _ & HRL).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & _).
destruct HRL as (_ & _ & _ & _ & _ & Hbl2 & _ & _).
destruct HR as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP).
destruct HP as ((R2 & R9 & R8 & R3 & R4 & R19 & R24) & R20 & R18 & R10 & R23 & R25 & R22 & R27 &
  V136 & V144 & V152 & V160 & Bpl & Bgb & SHbe & Bbe & SHag & Bag & Bid).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
set (k := D1k g i) in *.
assert (Hkr : 0 <= k <= 255) by (apply SlotModel.rec_k_range).
set (sp0 := e_sp0 g) in *.
set (SF := SFa g pos) in *.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn'; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn').
assert (HAE : env_agree 32 (Ereg regs3 []) E)
  by (rewrite HE; split; [intros n Hn'; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E p9_ss
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x5c0)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold p9_ss. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [exact I | split; exact I]. }
clear HE.
unfold cfg_at. change (w64 (BASE + 0x5c0)) with (Z_to_bv 64 (BASE + 0x5c0)).
paj_run_shc RUNP RUNC HS HJ3.
{ apply awr_ok_nil. }
assert (KEEPR : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a. apply aview_eq_of. apply HFr. intros (rr & Hin & _). destruct Hin. }
clear HF HFr HG.
pose proof (regs_kept_of_st_ok SEGS E _ _ regs3 [] [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS HAE
  ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
prreg HS (10%bv : bv 5) Q10. prreg HS (21%bv : bv 5) Q21. prreg HS (1%bv : bv 5) Q1.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Q10. rewrite (EE 10%nat 10%bv eq_refl), R10 in Q21.
assert (Q2 : getr (ms_regs ms) 2 = w64 mf) by (rewrite HKR by (cbn; tauto); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite HKR by (cbn; tauto); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite HKR by (cbn; tauto); exact R4).
assert (Q8 : getr (ms_regs ms) 8 = w64 sp0) by (rewrite HKR by (cbn; tauto); exact R8).
pmkst HS. rewrite (pal_free B TL).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SF) by (unfold SF, SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hingb : In (gb, k + 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). left. reflexivity. }
assert (Hinpl : In (pl, k) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). right. left. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ (gb, k + 1) (pl, k) _ HAR3 Hperm3) as Hdgp.
unfold zdisjoint, block_rng in Hdgp. cbn [fst snd] in Hdgp.
assert (HnotE : ~ In (gb, k + 1) (ablocks B (e_ly g) (e_S g))).
{ intros Hin. destruct Hbl2 as [Hperm2 _]. cbn [app] in Hperm2.
  apply (Permutation_in _ (Permutation_sym Hperm2)) in Hin. apply in_split in Hin as (l1 & l2 & El).
  assert (Hp2 : Permutation (ablocks B ly3 S3) ((gb, k + 1) :: (gb, k + 1) :: (pl, k) :: l1 ++ l2)).
  { eapply Permutation_trans; [exact Hperm3|]. cbn [app]. apply perm_skip. rewrite El.
    eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_middle|]. apply perm_swap. }
  pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 (ms_mem ms) _ (gb, k + 1) (gb, k + 1) _ HAR3 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (k + 1) ltac:(lia)).
  clear - Hd H. lia. }
assert (Hnev : st_nev S3 < EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hn3 & _).
  unfold EV_LLVMF in HEV. clear - Hn3 Hnev0 HEV Hi64. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_mono MT MTL k 256 ltac:(lia)) as HMk.
pose proof (mo_malloc_mono MT MTL (k + 1) 256 ltac:(lia)) as HMk1.
pose proof (mo_malloc_nonneg MT MTL k ltac:(lia)) as HMk0.
pose proof (mo_malloc_nonneg MT MTL (k + 1) ltac:(lia)) as HMk10.
assert (MOKf : mo_ok MT S3 (mo_free MT)).
{ apply (mo_ok_step MT MTL S2 S3 (mo_malloc MT k + mo_malloc MT (k + 1)) (mo_free MT)); [|exact MLE3].
  apply (mo_ok_le MT MTL _ _ _ MOK2). unfold EV_LLVMF.
  assert (Hq : 2 <= 4 * 64 + 10 - 4 * Z.of_nat i) by (clear - Hi64; lia).
  clear - HM0 HF0 HMk HMk1 HMk0 HMk10 Hq. nia. }
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite Q2. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb C1 Has. lia. }
assert (Us0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite Q8. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb C1 Has. lia. }
assert (Ura : raZ (ms_regs ms) = BASE + 0x5cc).
{ unfold raZ. rewrite Q1. apply unsigned_lit_small. clear - HBASE. lia. }
assert (KS0 : forall a, sp0 - 16 <= a < sp0 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite KEEPR. apply KEEP3.
  - clear - Ha Hmf0 Hmfb H47 C1 Has. lia.
  - left. clear - Ha Hmf0 Hmfb Has. lia.
  - unfold WR1, WR0. change (SFa g pos) with SF. change (shadow_addr SF) with sh.
    unfold V_before, N_before, V_again, N_again, V_id, N_id.
    clear - Ha Hmf0 Hmfb HSF1 Hsh1 Has. lia. }
destruct (d79_chain g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 (ms_mem ms) _ _ (ms_regs ms) HC HJ3 KS0
  Usp Us0 ltac:(rewrite Ura; clear - HBLO; lia)) as (ch & HCH & Hchs).
eapply SRr_mono.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W3 (ms_regs ms) (ms_mem ms) LLVMF_STK sp0 []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 _ (4 * Z.of_nat i + 2) gb (k + 1) (mf - sp0)
    (Z_to_bv 64 (BASE + 0x5cc)) ch HJ3 Hingb).
  - exact Q10.
  - rewrite Usp. clear. lia.
  - exact (d79_mod16 mf sp0 Hmf32 Hsp0al).
  - clear - Hmfb. lia.
  - clear - HSTKm Hmfb Has. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hnev.
  - exact HCH.
  - exact (d1_univ_free B RA_LLVMF HUMF (ms_regs ms) 0x5cc ch _ _ Ura ltac:(cbn; tauto) Hchs).
  - intros Hin. exfalso. exact (HnotE Hin).
  - exact MOKf. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (l1 & l2 & Ebl & Ebl4) & Hfrs4 & HK4 &
  MLE4 & _).
pose proof HK4 as (K1 & K2 & _ & K4 & _).
assert (STK4 : forall a, mf <= a < 2 ^ 64 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite K1 by (clear - Ha Hmf0 Has; lia). apply KEEPR. }
assert (FR4 : forall a, SF <= a < SF + 1024 \/ sh <= a < sh + 128 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. rewrite (K4 4 pos a Hin4).
  - apply KEEPR.
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa3. change (fs_frame_bytes 4) with 1024.
    change (1024 / 8) with 128. fold sh. exact Ha.
  - cbv beta. intros Hg. apply (d1_fz_not_block B LAWS g pos ly3 S3 W3 (ms_mem ms) _ gb (k + 1) a HAR3 Hin4 EFa3 Hingb Hg).
    fold SF sh. exact Ha. }
assert (PL4 : forall j, 0 <= j < req_size k -> aview SEGS (w_H W4) mem4 (pl + j) = aview SEGS (w_H W3) mem3 (pl + j)).
{ intros j Hj. rewrite (K2 pl k j Hinpl Hj); [apply KEEPR|]. cbv beta. clear - Hdgp Hj. lia. }
assert (VMS : forall off v, 136 <= off <= 160 -> val_mem SEGS (rd W3 mem3) (mf + off) 8 v ->
  val_mem SEGS (rd W4 mem4) (mf + off) 8 v).
{ intros off v Ho Hv. apply (val_mem_moved SEGS (w_H W3) (w_H W4) mem3 mem4 (mf + off) (mf + off) 8 v); [|exact Hv].
  intros kk Hkk. apply STK4. clear - Ho Hkk Hmfb H47. lia. }
assert (GF : forall a l, SF <= a -> a + Z.of_nat (length l) <= SF + 1024 ->
  garr8 SEGS (rd W3 mem3) a l -> garr8 SEGS (rd W4 mem4) a l).
{ intros a l H0 H1 Hg. apply (d79_garr8_mv SEGS (w_H W3) (w_H W4) mem3 mem4 a a l); [|exact Hg].
  intros kk Hkk. apply FR4. left. clear - H0 H1 Hkk. lia. }
assert (SHB : forall off n, 0 <= off -> off + n <= 1024 -> 0 <= n -> off mod 8 = 0 ->
  sh_blk W3 mem3 (SF + off) n -> sh_blk W4 mem4 (SF + off) n).
{ intros off n H0 H1 Hn' H8 Hz. unfold sh_blk in *.
  apply (d79_block_shadow_mv (aview SEGS (w_H W3) mem3) (aview SEGS (w_H W4) mem4) SHADOW_OFF (SF + off) n); [|exact Hz].
  intros ii Hii. apply FR4. right. unfold shadow_of_addr. rewrite Esh.
  clear - H0 H1 Hn' H8 Hii HSF64. lia. }
unfold D1S. exists ly4, S4, regs4, mem4, md4.
split; [reflexivity|].
split; [replace (4 * Z.of_nat i + 3) with (4 * Z.of_nat i + 2 + 1) by (clear; lia); exact HJ4|].
split; [rewrite Hfrs4; exact Hfrs3|].
split.
{ rewrite Ebl4. rewrite Ebl in Hperm3. cbn [app] in Hperm3 |- *.
  apply (Permutation_cons_inv (a := (gb, k + 1))).
  eapply Permutation_trans; [apply Permutation_middle | exact Hperm3]. }
split; [exact (Forall_inv_tail Hhs3)|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ MLE3 MLE4)|].
split.
{ apply (d1_keep_alloc B g pos mf (WR1 g pos mf) ly3 S3 W3 (ms_mem ms) W4 mem4
    (fun a => gb <= a < gb + req_size (k + 1)) W2 mem2 sp0 (mf - sp0) Hin4 EFa3 HK4 ltac:(clear; lia)).
  - intros a Ha. left. left. exact Ha.
  - intros a Ha. exact (d1_fz_not_block B LAWS g pos ly3 S3 W3 (ms_mem ms) _ gb (k + 1) a HAR3 Hin4 EFa3 Hingb Ha).
  - intros a Ha Hz Hn'. rewrite KEEPR. exact (KEEP3 a Ha Hz Hn'). }
unfold P9, RCb.
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr (ms_regs ms) r)
  by (intros r Hr; exact (d1_presv (ms_regs ms) regs4 r HP4 Hr)).
split.
{ split; [rewrite PR by d79_cs; exact Q2|].
  split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R9|].
  split; [rewrite PR by d79_cs; exact Q8|].
  split; [rewrite PR by d79_cs; exact Q3|].
  split; [rewrite PR by d79_cs; exact Q4|].
  split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R19|].
  rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R24. }
split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R20|].
split; [rewrite PR by d79_cs; exact Q21|].
split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R23|].
split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R25|].
split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R22|].
split; [rewrite PR by d79_cs; rewrite HKR by (cbn; tauto); exact R27|].
split; [apply VMS; [clear; lia | exact V136]|].
split; [apply VMS; [clear; lia | exact V144]|].
split; [apply VMS; [clear; lia | exact V152]|].
split; [apply VMS; [clear; lia | exact V160]|].
split.
{ unfold bytes_at8 in *. apply (d79_garr8_mv SEGS (w_H W3) (w_H W4) mem3 mem4 pl pl _); [|exact Bpl].
  intros kk Hkk. rewrite length_map, SlotModel.rec_pl_length in Hkk. apply PL4.
  pose proof (req_size_pos0 k ltac:(lia)). change (SlotModel.rec_k (e_pl g) i) with k in Hkk. clear - Hkk H. lia. }
split; [apply SHB; [unfold V_before; clear; lia | unfold V_before, N_before; clear; lia | unfold N_before; clear; lia
  | unfold V_before; clear; lia | exact SHbe]|].
split.
{ unfold bytes_at8 in *. apply GF; [unfold V_before; clear; lia | | exact Bbe].
  rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_before, RcIdentModel.ID_SIZE. clear; lia. }
split; [apply SHB; [unfold V_again; clear; lia | unfold V_again, N_again; clear; lia | unfold N_again; clear; lia
  | unfold V_again; clear; lia | exact SHag]|].
split.
{ unfold bytes_at8 in *. apply GF; [unfold V_again; clear; lia | | exact Bag].
  rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_again, RcIdentModel.ID_SIZE. clear; lia. }
unfold bytes_at8 in *. apply GF; [unfold V_id; clear; lia | | exact Bid].
rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length. unfold V_id, RcIdentModel.ID_SIZE. clear; lia.
Qed.

Theorem d1_ph7 : d1_ph7_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3 HC HR.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ2 & Hfrs2 & Hk2 & MLE2 & MOK2 & HEC & Hi & _ & _ & _ & HRL).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V176 & _).
destruct HRL as (_ & _ & _ & _ & _ & Hbl2 & _ & Hmag). unfold mf_again in Hmag.
destruct HR as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP).
destruct HP as ((R2 & R9 & R8 & R3 & R4 & R19 & R20 & R21 & R24) & R18 & R23 & R25 & R22 & R27 & R26 &
  V144 & Bpl & Bgb & SHbe & Bbe & Bid).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
set (k := D1k g i) in *.
set (bod := D1body g i) in *.
assert (Hkr : 0 <= k <= 255) by (apply SlotModel.rec_k_range).
pose proof (SlotModel.rec_bounds (e_pl g) i) as (_ & Hbod0 & Hbodk & _).
change (SlotModel.rec_body (e_pl g) i) with bod in Hbod0, Hbodk.
change (SlotModel.rec_k (e_pl g) i) with k in Hbodk. rewrite Hnlen in Hbodk.
pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrqn.
set (sp0 := e_sp0 g) in *.
set (SF := SFa g pos) in *.
set (sh := shadow_addr SF) in *.
assert (Esh : sh = SHADOW_OFF + SF / 8) by reflexivity.
assert (Hsh1 : 0 <= sh /\ sh + 128 <= alloc_ceiling).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF in Esh. lia. }
assert (Hsh2 : SHADOW_OFF <= sh /\ sh + 128 <= kHighMemBeg).
{ clear - Esh HSF0 HSF1 C1. clearbody sh SF. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (Hmfr : 2 ^ 46 <= mf /\ mf + 320 <= 2 ^ 47) by (clear - Hmf0 Hmfb H47 C1 Has; lia).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SF) by (unfold SF, SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hingb : In (gb, k + 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). left. reflexivity. }
assert (Hinpl : In (pl, k) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). right. left. reflexivity. }
pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 mem3 _ (gb, k + 1) (pl, k) _ HAR3 Hperm3) as Hdgp.
unfold zdisjoint, block_rng in Hdgp. cbn [fst snd] in Hdgp.
assert (HnotE : ~ In (gb, k + 1) (ablocks B (e_ly g) (e_S g))).
{ intros Hin. destruct Hbl2 as [Hperm2 _]. cbn [app] in Hperm2.
  apply (Permutation_in _ (Permutation_sym Hperm2)) in Hin. apply in_split in Hin as (l1 & l2 & El).
  assert (Hp2 : Permutation (ablocks B ly3 S3) ((gb, k + 1) :: (gb, k + 1) :: (pl, k) :: l1 ++ l2)).
  { eapply Permutation_trans; [exact Hperm3|]. cbn [app]. apply perm_skip. rewrite El.
    eapply Permutation_trans; [apply perm_skip; apply Permutation_sym, Permutation_middle|]. apply perm_swap. }
  pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 mem3 _ (gb, k + 1) (gb, k + 1) _ HAR3 Hp2) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (k + 1) ltac:(lia)).
  clear - Hd H. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ gb (k + 1) HAR3 Hingb) as (_ & Hg4096 & Hgce & Hgapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pl k HAR3 Hinpl) as (_ & Hpl4096 & Hplce & Hplapp & _).
pose proof (req_size_pos (k + 1) ltac:(lia)) as Hrq1.
pose proof (req_size_pos k ltac:(lia)) as Hrq0.
assert (Hgk : 4096 <= gb + k /\ gb + k + 1 <= alloc_ceiling) by (clear - Hg4096 Hgce Hrq1 Hkr; lia).
assert (NB : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + req_size m ->
  0 <= a < 2 ^ 64 /\ ~ (sh + 14 <= a < sh + 19) /\ ~ (mf + 136 <= a < mf + 168) /\ ~ (SF + 112 <= a < SF + 150) /\
  ~ (mf - 4096 <= a < mf)).
{ intros b m a Hb Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3 Hb) as (_ & Hb4096 & Hbce & Hbapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b m 4 pos HAR3 Hb Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa3, HFB in Hdf.
  split; [clear - Ha Hb4096 Hbce C1; lia|].
  split; [intros Hs; apply (fshadow_not_app SF 128 b (req_size m) a); [exact HSF0 | clear - HSF1 C1; lia | exact Hbapp
    | rewrite Esh in Hs; unfold SHADOW_OFF in Hs; clear - Hs; lia | exact Ha]|].
  split; [clear - Ha Hbce Hmf0 Has; lia|]. split; [clear - Ha Hdf; lia|]. clear - Ha Hbce Hmf0 Has; lia. }
assert (NF : forall a, SF <= a < SF + 1024 ->
  0 <= a < 2 ^ 64 /\ ~ (sh + 14 <= a < sh + 19) /\ ~ (mf + 136 <= a < mf + 168) /\ a <> gb + k /\
  ~ (mf - 4096 <= a < mf)).
{ intros a Ha. pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 gb (k + 1) 4 pos HAR3 Hingb Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa3, HFB in Hdf.
  split; [clear - Ha HSF0 HSF1 C1; lia|].
  split; [intros Hs; apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | rewrite Esh in Hs; unfold SHADOW_OFF in Hs; clear - Hs; lia | exact Ha]|].
  split; [clear - Ha HSF1 Hmf0 Has; lia|]. split; [clear - Ha Hdf Hrq1 Hkr; lia|]. clear - Ha HSF1 Hmf0 Has; lia. }
assert (NS : forall a, sh <= a < sh + 128 ->
  0 <= a < 2 ^ 64 /\ ~ (mf + 136 <= a < mf + 168) /\ a <> gb + k /\ ~ (SF + 112 <= a < SF + 150) /\
  ~ (mf - 4096 <= a < mf)).
{ intros a Ha. split; [clear - Ha Hsh1 C1; lia|]. split; [clear - Ha Hsh1 Hmf0 Has; lia|].
  split; [intros ->; apply (fshadow_not_app SF 128 gb (req_size (k + 1)) (gb + k)); [exact HSF0 | clear - HSF1 C1; lia
    | exact Hgapp | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | clear - Hrq1 Hkr; lia]|].
  split; [intros Hf; apply (fshadow_not_app SF 128 SF 1024 a); [exact HSF0 | clear - HSF1 C1; lia | exact HSFapp
    | rewrite Esh in Ha; unfold SHADOW_OFF in Ha; clear - Ha; lia | clear - Hf; lia]|].
  clear - Ha Hsh1 Hmf0 Has; lia. }
assert (KST : forall a, mf + 168 <= a < sp0 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply KEEP3.
  - clear - Ha Hmf0 Hmfb H47 C1 Has. lia.
  - left. clear - Ha Hmf0 Hmfb Has. lia.
  - apply (d1_nwr_stack g pos mf a Hmf0 HSF0 HSF1); clear - Ha; lia. }
assert (V168 : val_mem SEGS (rd W3 mem3) (mf + 168) 8 (SF + V_again)).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 168) (mf + 168) 8 _); [|exact Hmag].
  intros kk Hkk. apply KST. clear - Hkk Hmfb. lia. }
assert (V176' : val_mem SEGS (rd W3 mem3) (mf + 176) 8 SHADOW_OFF).
{ apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (mf + 176) (mf + 176) 8 _); [|exact V176].
  intros kk Hkk. apply KST. clear - Hkk Hmfb. lia. }
remember (Eimg (Ereg regs3 (p7_extra SF gb k (e_n g - bod)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (ER : regs_ok E sr_atoms regs3) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn'; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn').
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (p7_extra SF gb k (e_n g - bod)) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clear HE.
assert (E32 : ew E 32 = Z_to_bv 64 d1_SB) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = Z_to_bv 64 (SF + V_again)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (gb + k)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = Z_to_bv 64 (e_n g - bod)) by exact (EX 3%nat ltac:(lia)).
clear EX.
assert (UA : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v)
  by (intros n v Hn' Hv; rewrite Hn'; apply unsigned_lit_small; exact Hv).
assert (U9 : bv_unsigned (ew E 9) = mf)
  by (apply UA; [rewrite (EE 9%nat 9%bv eq_refl); exact R9 | clear - Hmfr; lia]).
assert (U2 : bv_unsigned (ew E 2) = mf)
  by (apply UA; [rewrite (EE 2%nat 2%bv eq_refl); exact R2 | clear - Hmfr; lia]).
assert (U19 : bv_unsigned (ew E 19) = sh)
  by (apply UA; [rewrite (EE 19%nat 19%bv eq_refl); exact R19 | clear - Hsh1 C1; lia]).
assert (U32 : bv_unsigned (ew E 32) = d1_SB) by (apply UA; [exact E32 | unfold d1_SB; lia]).
assert (U34 : bv_unsigned (ew E 34) = gb + k) by (apply UA; [exact E34 | clear - Hgk C1; lia]).
assert (HS0 : st_ok_pi SEGS VAL E p7_ssA
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x558)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold p7_ssA. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, p7_mf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [clear - Hmfr; lia|]. split; [clear - Hmfr; lia|].
      split.
      { intros o Ho. apply (apresent_writable SEGS).
        apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
          [(4, pos)] ly3 S3 W3 mem3 md3 (4 * Z.of_nat i + 2) (mf + o) HJ3 ltac:(left; clear - Ho Hmfb HSTK' Has; lia))). }
      constructor; [|constructor; [|constructor; [|constructor]]].
      * apply (chunk_ok_val SEGS E _ mf 144 8 (SOff 35 0) (e_n g - bod));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hbodk Hbod0 Hn Hkr; lia
        | lia | exact V144].
      * apply (chunk_ok_val SEGS E _ mf 168 8 (SOff 33 0) (SF + V_again));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold V_again; clear - HSF0 HSF1 C1; lia | lia | exact V168].
      * apply (chunk_ok_val SEGS E _ mf 176 8 (SOff 32 0) d1_SB);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold d1_SB; cbn; lia | lia
        | exact V176'].
    + unfold region_ok, p7_g. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U34. split; [clear - Hgk; lia|]. split; [clear - Hgk C1; lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      refine (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
        [(4, pos)] ly3 S3 W3 mem3 md3 (4 * Z.of_nat i + 2) (gb + k + o) HJ3 _)).
      right; right; left. exists gb, (k + 1). split; [exact Hingb|]. split; [exact HnotE|]. clear - Ho Hrq1 Hkr; lia.
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, p7_mf, p7_g. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U34. right. clear - Hgk Hmf0 Has. lia.
  - unfold facts_ok, p7_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok; cbn [af_lo af_hi af_al2]. rewrite U2, U9, U32, U34.
      change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold d1_SB. clear - Hmfr Hmf32 Hgk C1. repeat match goal with |- _ /\ _ => split end; try lia; try exact I.
    + split; [|exact I]. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned.
      rewrite (EE 18%nat 18%bv eq_refl), (EE 22%nat 22%bv eq_refl), R18, R22, E34. unfold w64. apply alu64_add_lit. }
assert (SHOK : sh_ok SEGS d1_Bx p7_SH E (mrestrict (w_H W3) mem3)).
{ unfold p7_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 E d1_Bx 34 (gb + k) 1 (gb + k) 0 1).
  - apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 mem3 md3 gb (k + 1) (gb + k) 1 HAR3 Hingb);
    clear - Hrq1 Hkr; lia.
  - unfold d1_Bx. rewrite (U_atom E 32 d1_SB E32) by (unfold d1_SB; lia). reflexivity.
  - apply (U_atom E 34 (gb + k) E34). clear - Hgk C1. lia.
  - lia.
  - lia.
  - intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp. unfold SHADOW_OFF.
    clear - Hx Hgapp Hrq1 Hkr. lia. }
unfold cfg_at. change (w64 (BASE + 0x558)) with (Z_to_bv 64 (BASE + 0x558)).
paj_run_to_tok RUNTO HS0 HJ3 SHOK d1_Bspan 0x584.
{ change (ss_mem p7_ssA) with [p7_mf; p7_g].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
    [reflexivity | rewrite U9; ring | cbn [YP09.r_wlo p7_mf]; clear - Hmfb HSTK' Has; lia
    | cbn [YP09.r_whi p7_mf]; clear - Hmfb; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gb + k)); [reflexivity | exact U34 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi p7_g] in Ha. right; right; left. exists gb, (k + 1).
    split; [exact Hingb|]. split; [exact HnotE|]. clear - Ha Hrq1 Hkr; lia.
  - apply awr_ok_nil. }
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 136 <= a < mf + 168) -> a <> gb + k ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H1 H2.
  apply (kept_of_frame E (ss_mem p7_ssA) (w_H W3) mem3 (ms_mem ms)
    (fun x => mf + 136 <= x < mf + 168 \/ x = gb + k) HFr); [| exact Ha | intros [H|H]; [exact (H1 H) | exact (H2 H)]].
  intros bb wlo whi aa Hin Hr. unfold p7_ssA, p7_mf, p7_g, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | []]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite U9 in Hr; left; clear - Hr; lia | rewrite U34 in Hr; right; clear - Hr; lia]. }
clear HF HFr HG SHOK.
lazymatch type of HS0 with st_ok_pi _ _ ?Ex _ _ => set (EA := Ex) in * end.
assert (EAlo : forall n, (n < 512)%nat -> ew EA n = ew E n).
{ intros n Hn'. unfold EA. rewrite !ew_ewset_other by lia. reflexivity. }
assert (UA9 : bv_unsigned (ew EA 9) = mf) by (rewrite EAlo by lia; exact U9).
assert (UA19 : bv_unsigned (ew EA 19) = sh) by (rewrite EAlo by lia; exact U19).
assert (UA34 : bv_unsigned (ew EA 34) = gb + k) by (rewrite EAlo by lia; exact U34).
pose proof (st_ok_pi_add_region EA _ _ p7_sh HS0 eq_refl) as HSB.
assert (RSH : region_ok SEGS EA (ms_mem (restrict (w_H W3) ms)) p7_sh).
{ unfold region_ok, p7_sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
  rewrite UA19. split; [clear - Hsh1; lia|]. split; [clear - Hsh1 C1; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  refine (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly3 S3 W3 (ms_mem ms) _ (4 * Z.of_nat i + 2) (sh + o) HJ3 _)).
  right; right; right. exists 4, pos. split; [left; reflexivity|]. right.
  unfold in_zr; cbn [fst snd]. rewrite EFa3, HFB. fold sh. clear - Ho; lia. }
specialize (HSB RSH). clear RSH.
lazymatch type of HSB with all_disjoint _ _ ?rs -> _ => assert (DSH : all_disjoint EA p7_sh rs) end.
{ cbn [all_disjoint ss_mem]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val p7_sh].
  rewrite UA9, UA19, UA34.
  split; [left; clear - Hsh1 Hmf0 Has; lia|]. split; [|exact I].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hgapp. unfold SHADOW_OFF, kHighMemBeg in Hsh2.
  clear - Hgapp Hsh2 Hrq1 Hkr. lia. }
specialize (HSB DSH). clear DSH.
paj_run_shc RUNP RUNC HSB HJ3.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat sh); [reflexivity | exact UA19 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi p7_sh] in Ha. right; right; right. exists 4, pos.
    split; [left; reflexivity|]. right. unfold in_zr; cbn [fst snd]. rewrite EFa3, HFB. fold sh. clear - Ha; lia. }
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (mf - sp0));
    [reflexivity | rewrite UA9; ring | cbn [YP09.r_wlo]; clear - Hmfb HSTK' Has; lia | cbn [YP09.r_whi]; clear - Hmfb; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 34%nat (gb + k)); [reflexivity | exact UA34 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left. exists gb, (k + 1).
    split; [exact Hingb|]. split; [exact HnotE|]. clear - Ha Hrq1 Hkr; lia.
  - apply awr_ok_nil. }
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 14 <= a < sh + 19) -> ~ (mf + 136 <= a < mf + 168) -> a <> gb + k ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms) a).
{ intros a Ha H0 H1 H2.
  apply (kept_of_frame EA _ (w_H W3) (ms_mem ms) (ms_mem ms0)
    (fun x => sh + 14 <= x < sh + 19 \/ mf + 136 <= x < mf + 168 \/ x = gb + k) HFr);
    [| exact Ha | intros [H|[H|H]]; [exact (H0 H) | exact (H1 H) | exact (H2 H)]].
  intros bb wlo whi aa Hin Hr. unfold p7_sh, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
  [rewrite UA19 in Hr; left | rewrite UA9 in Hr; right; left | rewrite UA34 in Hr; right; right]; clear - Hr; lia. }
clear HF HFr HG.
assert (KAB : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 14 <= a < sh + 19) -> ~ (mf + 136 <= a < mf + 168) -> a <> gb + k ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H0 H1 H2. rewrite (KB a Ha H0 H1 H2). exact (KA a Ha H1 H2). }
prreg HSB (10%bv : bv 5) Q10. prreg HSB (11%bv : bv 5) Q11. prreg HSB (12%bv : bv 5) Q12. prreg HSB (1%bv : bv 5) Q1.
prreg HSB (2%bv : bv 5) Q2. prreg HSB (3%bv : bv 5) Q3. prreg HSB (4%bv : bv 5) Q4. prreg HSB (8%bv : bv 5) Q8.
prreg HSB (9%bv : bv 5) Q9. prreg HSB (18%bv : bv 5) Q18. prreg HSB (19%bv : bv 5) Q19. prreg HSB (20%bv : bv 5) Q20.
prreg HSB (22%bv : bv 5) Q22. prreg HSB (23%bv : bv 5) Q23. prreg HSB (24%bv : bv 5) Q24. prreg HSB (25%bv : bv 5) Q25.
prreg HSB (27%bv : bv 5) Q27.
rewrite ?EAlo in Q10, Q11, Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q20, Q22, Q23, Q24, Q25, Q27 by lia.
rewrite E33 in Q10, Q20. rewrite (EE 24%nat 24%bv eq_refl), R24 in Q11, Q24.
rewrite (EE 2%nat 2%bv eq_refl), R2 in Q2. rewrite (EE 3%nat 3%bv eq_refl), R3 in Q3.
rewrite (EE 4%nat 4%bv eq_refl), R4 in Q4. rewrite (EE 8%nat 8%bv eq_refl), R8 in Q8.
rewrite (EE 9%nat 9%bv eq_refl), R9 in Q9. rewrite (EE 18%nat 18%bv eq_refl), R18 in Q18.
rewrite (EE 19%nat 19%bv eq_refl), R19 in Q19. rewrite (EE 22%nat 22%bv eq_refl), R22 in Q22.
rewrite (EE 23%nat 23%bv eq_refl), R23 in Q23. rewrite (EE 25%nat 25%bv eq_refl), R25 in Q25.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Q27.
pose proof (st_ok_region_nth (segs := SEGS) EA _ _ 0 _ HSB eq_refl) as RG0.
pose proof (st_ok_region_nth (segs := SEGS) EA _ _ 1 _ HSB eq_refl) as RG1.
destruct RG0 as (_ & _ & _ & CH0). destruct RG1 as (_ & _ & _ & CH1).
cbn [ms_mem restrict YP09.r_base YP09.r_chunks base_val] in CH0, CH1.
rewrite UA19 in CH0. rewrite UA9 in CH1. rewrite Forall_forall in CH0, CH1.
assert (A0 : forall j, 14 <= j < 18 -> aview SEGS (w_H W3) (ms_mem ms0) (sh + j) = Some 0).
{ intros j Hj. apply (aview_of_val_mem1 SEGS); [|lia].
  assert (Hc : j = 14 \/ j = 15 \/ j = 16 \/ j = 17) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]];
  match goal with |- val_mem _ _ (sh + ?o) _ _ =>
    exact (val_of_chunk_ok SEGS EA _ sh o 1 (SLit 0) 0 (CH0 (YP09.mkChunk o (CVal 1 (SLit 0))) ltac:(d79_in))
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) end. }
assert (A18 : aview SEGS (w_H W3) (ms_mem ms0) (sh + 18) = Some 6).
{ apply (aview_of_val_mem1 SEGS); [|lia].
  apply (val_of_chunk_ok SEGS EA _ sh 18 1 (SOff 21 0) 6 (CH0 (YP09.mkChunk 18 (CVal 1 (SOff 21 0))) ltac:(d79_in))); [|cbn; lia | cbn; lia].
  cbn [sv_denot]. rewrite EAlo by lia. rewrite (EE 21%nat 21%bv eq_refl), R21. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (DEN : forall n v (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> getr regs3 r = w64 v ->
  0 <= v < 2 ^ 64 -> sv_denot EA (SOff n 0) = Z_to_bv 64 v).
{ intros n v r Hn' Hr Hg Hv. cbn [sv_denot]. rewrite EAlo by lia. rewrite (EE n r Hr), Hg. unfold w64.
  rewrite unsigned_lit_small by exact Hv. rewrite Z.add_0_r. reflexivity. }
assert (C136 : val_mem SEGS (rd W3 (ms_mem ms0)) (mf + 136) 8 (e_p g + bod)).
{ apply (val_of_chunk_ok SEGS EA _ mf 136 8 (SOff 26 0) (e_p g + bod) (CH1 (YP09.mkChunk 136 (CVal 8 (SOff 26 0))) ltac:(d79_in)));
  [apply (DEN 26%nat _ 26%bv); [lia | reflexivity | exact R26 | clear - Hp4096 Hpce Hrqn Hbodk Hbod0 Hkr C1; lia]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hp4096 Hpce Hrqn Hbodk Hbod0 Hkr C1; lia | lia]. }
assert (C144 : val_mem SEGS (rd W3 (ms_mem ms0)) (mf + 144) 8 (e_n g - bod)).
{ apply (val_of_chunk_ok SEGS EA _ mf 144 8 (SOff 35 0) (e_n g - bod) (CH1 (YP09.mkChunk 144 (CVal 8 (SOff 35 0))) ltac:(d79_in)));
  [cbn [sv_denot]; rewrite EAlo by lia; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hbodk Hbod0 Hn Hkr; lia | lia]. }
assert (C152 : val_mem SEGS (rd W3 (ms_mem ms0)) (mf + 152) 8 pl).
{ apply (val_of_chunk_ok SEGS EA _ mf 152 8 (SOff 25 0) pl (CH1 (YP09.mkChunk 152 (CVal 8 (SOff 25 0))) ltac:(d79_in)));
  [apply (DEN 25%nat _ 25%bv); [lia | reflexivity | exact R25 | clear - Hpl4096 Hplce Hrq0 C1; lia]
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hpl4096 Hplce Hrq0 C1; lia | lia]. }
assert (C160 : val_mem SEGS (rd W3 (ms_mem ms0)) (mf + 160) 8 (Z.of_nat i)).
{ apply (val_of_chunk_ok SEGS EA _ mf 160 8 (SOff 20 0) (Z.of_nat i) (CH1 (YP09.mkChunk 160 (CVal 8 (SOff 20 0))) ltac:(d79_in)));
  [apply (DEN 20%nat _ 20%bv); [lia | reflexivity | exact R20 | clear - Hi64; lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hi64; lia | lia]. }
clear CH0 CH1 DEN.
assert (SHAGB : sh_blk W3 (ms_mem ms0) (SF + V_again) N_again).
{ unfold sh_blk, block_shadow, V_again, N_again. split; [clear - HSF64; lia|]. split; [lia|].
  intros ii Hii. unfold shadow_of_addr.
  replace (SHADOW_OFF + (SF + 112) / 8 + ii) with (sh + (14 + ii)) by (rewrite Esh; clear - Hii; lia).
  assert (Hc : ii = 0 \/ ii = 1 \/ ii = 2 \/ ii = 3 \/ ii = 4) by (clear - Hii; lia).
  destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
  [ rewrite (A0 (14 + 0)) by lia | rewrite (A0 (14 + 1)) by lia | rewrite (A0 (14 + 2)) by lia
  | rewrite (A0 (14 + 3)) by lia | replace (14 + 4) with 18 by lia; rewrite A18 ]; reflexivity. }
assert (SHbeB : sh_blk W3 (ms_mem ms0) (SF + V_before) N_before).
{ apply (d1_shblk_moved W3 W3 mem3 (ms_mem ms0) _ _); [|exact SHbe].
  intros kk Hkk. unfold N_before in Hkk.
  replace (shadow_addr (SF + V_before) + kk) with (sh + (4 + kk)) by (unfold shadow_addr, V_before; rewrite Esh;
    clear - Hkk; lia).
  destruct (NS (sh + (4 + kk)) ltac:(clear - Hkk; lia)) as (H0 & H1 & H2 & _).
  apply KAB; [exact H0 | clear - Hkk; lia | exact H1 | exact H2]. }
assert (BbeB : bytes_at8 W3 (ms_mem ms0) (SF + V_before) (m_id g i)).
{ apply (d1_bytes_moved W3 W3 mem3 (ms_mem ms0) _ _); [|exact Bbe].
  intros kk Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  unfold RcIdentModel.ID_SIZE, V_before in *.
  destruct (NF (SF + 32 + kk) ltac:(clear - Hkk; lia)) as (H0 & H1 & H2 & H3 & _).
  apply KAB; [exact H0 | exact H1 | exact H2 | exact H3]. }
assert (Usp : spZ (ms_regs ms0) = mf) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; clear - Hmfr; lia).
pmkst HSB.
pose proof HJ3 as (HAR4 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 pos HAR4 Hin4) as (_ & _ & HFpres & _).
rewrite EFa3, HFB in HFpres.
eapply SRr_mono.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA IS___asan_memcpy) AMEMCPY W3 (ms_regs ms0) (ms_mem ms0)
    LLVMF_STK sp0 [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 _ (4 * Z.of_nat i + 2)
    (SF + V_again) (SF + V_before) 38 (mf - sp0) (Z_to_bv 64 (BASE + 1452)) HJ3 Q10 Q11 Q12).
  - lia.
  - unfold V_again. clear - HSF0. lia.
  - unfold V_again. clear - HSF1 C1. lia.
  - rewrite Usp. clear. lia.
  - exact (d79_mod16 mf sp0 Hmf32 Hsp0al).
  - clear - Hmfb. lia.
  - rewrite Hes. clear - HSTKm Hmfb Has. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. unfold V_again in Ha. split.
    + right; right; right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite EFa3, HFB. clear - Ha. lia.
    + rewrite Hes. clear - Ha HSF1 Hmf0 Has. lia.
  - apply (amem_range_sub_app SF 1024 (SF + V_again) 38); [exact HSFapp | exact HSF1 | unfold V_again; lia
    | unfold V_again; lia | lia].
  - apply (block_shadow_range _ SHADOW_OFF (SF + V_again) N_again (SF + V_again) 38 SHAGB); unfold N_again; lia.
  - intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ 4 pos); [exact HAR4 | exact Hin4
    | rewrite EFa3; unfold V_again; lia | rewrite EFa3, HFB; unfold V_again; lia | lia].
  - split; [unfold V_before; clear - HSF0; lia|]. split; [unfold V_before; clear - HSF1 C1; lia|].
    split.
    { intros a Ha. unfold V_before in Ha. split.
      - apply (aview_some_of_apresent SEGS). apply (proj1 (HFpres a ltac:(clear - Ha; lia))).
      - rewrite Usp, Hes. clear - Ha HSF1 Hmf0 Has. lia. }
    split; [unfold V_again, V_before; lia|].
    split; [apply (amem_range_sub_app SF 1024 (SF + V_before) 38); [exact HSFapp | exact HSF1 | unfold V_before; lia
      | unfold V_before; lia | lia]|].
    split; [apply (block_shadow_range _ SHADOW_OFF (SF + V_before) N_before (SF + V_before) 38 SHbeB);
      unfold N_before; lia|].
    intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ 4 pos); [exact HAR4 | exact Hin4
      | rewrite EFa3; unfold V_before; lia | rewrite EFa3, HFB; unfold V_before; lia | lia]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & _ & Heff & Hfr4 & _ & _).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (SF + 112 <= a < SF + 150) -> ~ (mf - 4096 <= a < mf) ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms0) a).
{ intros a Ha H1 H2. apply Hfr4; [exact Ha | unfold V_again; clear - H1; lia | rewrite Hes; clear - H2; lia]. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (sh + 14 <= a < sh + 19) -> ~ (mf + 136 <= a < mf + 168) -> a <> gb + k ->
  ~ (SF + 112 <= a < SF + 150) -> ~ (mf - 4096 <= a < mf) -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha H0 H1 H2 H3 H4. rewrite (KC a Ha H3 H4). exact (KAB a Ha H0 H1 H2). }
assert (VM : forall off v, 136 <= off <= 160 -> val_mem SEGS (rd W3 (ms_mem ms0)) (mf + off) 8 v ->
  val_mem SEGS (rd W3 mem4) (mf + off) 8 v).
{ intros off v Ho Hv. apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms0) mem4 (mf + off) (mf + off) 8 v); [|exact Hv].
  intros kk Hkk. apply KC; clear - Ho Hkk Hmfr HSF1 Hmf0 Has; lia. }
assert (BK : forall b m bs, In (b, m) (ablocks B ly3 S3) -> Z.of_nat (length bs) <= req_size m ->
  (forall kk, 0 <= kk < Z.of_nat (length bs) -> b + kk <> gb + k) ->
  bytes_at8 W3 mem3 b bs -> bytes_at8 W3 mem4 b bs).
{ intros b m bs Hb Hl Hne Hbs. apply (d1_bytes_moved W3 W3 mem3 mem4 _ _); [|exact Hbs].
  intros kk Hkk.
  destruct (NB b m (b + kk) Hb ltac:(clear - Hkk Hl; lia)) as (H0 & H1 & H2 & H3 & H4).
  apply KM; [exact H0 | exact H1 | exact H2 | exact (Hne kk Hkk) | exact H3 | exact H4]. }
assert (FK : forall a, SF <= a < SF + 1024 -> ~ (SF + 112 <= a < SF + 150) ->
  aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hg. destruct (NF a Ha) as (H0 & H1 & H2 & H3 & H4). apply KM; assumption. }
unfold D1S. exists ly3, S3, regs4, mem4, md4.
split; [reflexivity|].
split; [exact HJ4|].
split; [exact Hfrs3|].
split; [exact Hperm3|].
split; [exact Hhs3|].
split; [exact MLE3|].
split.
{ intros a Ha Hz Hw. rewrite KM; [exact (KEEP3 a Ha Hz Hw) | exact Ha | | | | |];
  unfold WR1, WR0 in Hw; change (SFa g pos) with SF in Hw; change (shadow_addr SF) with sh in Hw;
  unfold V_before, N_before, V_again, N_again, V_id, N_id in Hw.
  - intros H. apply Hw. left. right. right. right. right. right. exact H.
  - intros H. apply Hw. left. right. left. exact H.
  - intros ->. destruct Hz as [Hz | [Hz | Hz]]; [clear - Hz Hgk; lia | |].
    + destruct (NF _ Hz) as (_ & _ & _ & H & _). exact (H eq_refl).
    + destruct (NS _ Hz) as (_ & _ & H & _). exact (H eq_refl).
  - intros H. apply Hw. left. right. right. right. left. clear - H. lia.
  - intros H. apply Hw. left. left. rewrite Has. clear - H. lia. }
unfold P7, RCb. change (SFa g pos) with SF. change (shadow_addr SF) with sh.
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr (ms_regs ms0) r)
  by (intros r Hr; exact (d1_presv (ms_regs ms0) regs4 r HP4 Hr)).
split.
{ split; [rewrite PR by d79_cs; exact Q2|]. split; [rewrite PR by d79_cs; exact Q9|].
  split; [rewrite PR by d79_cs; exact Q8|]. split; [rewrite PR by d79_cs; exact Q3|].
  split; [rewrite PR by d79_cs; exact Q4|]. split; [rewrite PR by d79_cs; exact Q19|].
  rewrite PR by d79_cs; exact Q24. }
split; [rewrite PR by d79_cs; exact Q20|].
split; [rewrite PR by d79_cs; exact Q18|].
split; [rewrite PR by d79_cs; exact Q23|].
split; [rewrite PR by d79_cs; exact Q25|].
split; [rewrite PR by d79_cs; exact Q22|].
split; [rewrite PR by d79_cs; exact Q27|].
split; [apply VM; [lia | exact C136]|].
split; [apply VM; [lia | exact C144]|].
split; [apply VM; [lia | exact C152]|].
split; [apply VM; [lia | exact C160]|].
split.
{ apply (BK pl k _ Hinpl); [| |exact Bpl].
  - rewrite SlotModel.rec_pl_length. change (SlotModel.rec_k (e_pl g) i) with k. clear - Hrq0 Hkr. lia.
  - intros kk Hkk Heq. rewrite SlotModel.rec_pl_length in Hkk. change (SlotModel.rec_k (e_pl g) i) with k in Hkk.
    clear - Hkk Heq Hdgp Hrq0 Hrq1 Hkr. lia. }
split.
{ apply (BK gb (k + 1) _ Hingb); [| |exact Bgb].
  - rewrite SlotModel.rec_pl_length. change (SlotModel.rec_k (e_pl g) i) with k. clear - Hrq1 Hkr. lia.
  - intros kk Hkk Heq. rewrite SlotModel.rec_pl_length in Hkk. change (SlotModel.rec_k (e_pl g) i) with k in Hkk.
    clear - Hkk Heq Hkr. lia. }
split.
{ apply (d1_shblk_moved W3 W3 mem3 mem4 _ _); [|exact SHbe].
  intros kk Hkk. unfold N_before in Hkk.
  replace (shadow_addr (SF + V_before) + kk) with (sh + (4 + kk)) by (unfold shadow_addr, V_before; rewrite Esh;
    clear - Hkk; lia).
  destruct (NS (sh + (4 + kk)) ltac:(clear - Hkk; lia)) as (H0 & H1 & H2 & H3 & H4).
  apply KM; [exact H0 | clear - Hkk; lia | exact H1 | exact H2 | exact H3 | exact H4]. }
split.
{ apply (d1_bytes_moved W3 W3 mem3 mem4 _ _); [|exact Bbe].
  intros kk Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  unfold RcIdentModel.ID_SIZE, V_before in *. apply FK; clear - Hkk; lia. }
split.
{ apply (d1_shblk_moved W3 W3 (ms_mem ms0) mem4 _ _); [|exact SHAGB].
  intros kk Hkk. unfold N_again in Hkk.
  replace (shadow_addr (SF + V_again) + kk) with (sh + (14 + kk)) by (unfold shadow_addr, V_again; rewrite Esh;
    clear - Hkk; lia).
  destruct (NS (sh + (14 + kk)) ltac:(clear - Hkk; lia)) as (H0 & _ & _ & H3 & H4).
  apply KC; [exact H0 | exact H3 | exact H4]. }
split.
{ unfold bytes_at8 in *.
  apply (d79_garr8_mv SEGS (w_H W3) (w_H W3) (ms_mem ms0) mem4 (SF + V_before) (SF + V_again) _); [|exact BbeB].
  intros kk Hkk. rewrite length_map in Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
  unfold RcIdentModel.ID_SIZE in Hkk. exact (Heff kk ltac:(clear - Hkk; lia)). }
apply (d1_bytes_moved W3 W3 mem3 mem4 _ _); [|exact Bid].
intros kk Hkk. unfold m_id in Hkk. rewrite SlotModel.rec_id_length in Hkk.
unfold RcIdentModel.ID_SIZE, V_id in *. apply FK; clear - Hkk; lia.
Qed.

End c.
End b.
End a.
