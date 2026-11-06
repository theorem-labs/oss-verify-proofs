(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Segment D1 of LLVMFuzzerTestOneInput's ASan walk, phases 5 and 6 (the statements, the shared predicates and the
   facts every phase uses are LLVMFuzzerTestOneInput_D1cut.v):
     Ph5 0x80c30..0x80c44  the ingest result is >= 0 (the plain model decides it), then malloc(k + 1) for the
                           guard copy g (0x80c40)
     Ph6 0x80c44..0x80c64  the NULL check of g, and memcpy(g, pl, k) when k > 0 (0x80c60)
   Each abort branch is refuted by the model (SlotModel.rec_r is 0 or 1) or by the malloc result (>= 4096), so no
   path reaches a report call. *)
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
(* YC4b turns lia's division and modulo handling off; the shadow arithmetic here needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut file's d1_cs, which its Section does not export *)
Ltac d1_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia.

(* the cut file's d1_prraw, also for a state the plain run left (st_ok_pi) *)
Ltac d1p56_prraw HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

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
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
(* What this segment takes, each with the name and type the contract's Section gives it (LLVMFuzzerTestOneInput.v). *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis HLIVE : LIVE_LLVMF <= LIVE_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IS___asan_memcpy).
(* The allocator call traces (LLVMFuzzerTestOneInput.v, the contract's text). *)
Hypothesis HUMM : forall c, In c (LLVMF_MALLOC_CTX RA_LLVMF) ->
In (firstn kUnwindMax (pc_malloc_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
(* the cut file's predicates and facts, with this Section's parameters *)
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation RUNS := (D1S B MT LLVMF_STK).
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).

(* ---- moving a memory fact to a state whose view did not change on its range ---------------------------------- *)
Lemma d1p56_vm : forall (Wa Wb : world SEGS) ma mb a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H Wb) mb x = aview SEGS (w_H Wa) ma x) ->
  val_mem SEGS (rd Wa ma) a n v -> val_mem SEGS (rd Wb mb) a n v.
Proof.
intros Wa Wb ma mb a n v HK HV.
apply (val_mem_moved SEGS (w_H Wa) (w_H Wb) ma mb a a n v); [|exact HV].
intros j Hj. apply HK. lia.
Qed.
Lemma d1p56_b8 : forall (Wa Wb : world SEGS) ma mb a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> aview SEGS (w_H Wb) mb x = aview SEGS (w_H Wa) ma x) ->
  bytes_at8 Wa ma a bs -> bytes_at8 Wb mb a bs.
Proof.
intros Wa Wb ma mb a bs HK HB j Hj. rewrite length_map in Hj.
destruct (HB j ltac:(rewrite length_map; exact Hj)) as [Hv Hr]. split; [|exact Hr].
apply (d1p56_vm Wa Wb ma mb (a + Z.of_nat j) 1 (nth j (map (fun b : byte => bv_unsigned b) bs) 0)); [|exact Hv].
intros x Hx. apply HK. cbn [Z.of_nat] in Hx. lia.
Qed.
(* the destination of a copy: its bytes are the source's *)
Lemma d1p56_b8_copy : forall (W : world SEGS) ma mb d s bs,
  (forall j, 0 <= j < Z.of_nat (length bs) ->
     aview SEGS (w_H W) mb (d + j) = aview SEGS (w_H W) ma (s + j)) ->
  bytes_at8 W ma s bs -> bytes_at8 W mb d bs.
Proof.
intros W ma mb d s bs HK HB j Hj. rewrite length_map in Hj.
destruct (HB j ltac:(rewrite length_map; exact Hj)) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS (w_H W) (w_H W) ma mb (s + Z.of_nat j) (d + Z.of_nat j) 1
  (nth j (map (fun b : byte => bv_unsigned b) bs) 0)); [|exact Hv].
intros x Hx. cbn [Z.of_nat] in Hx.
replace (d + Z.of_nat j + x) with (d + (Z.of_nat j + x)) by lia.
replace (s + Z.of_nat j + x) with (s + (Z.of_nat j + x)) by lia.
apply HK. lia.
Qed.
Lemma d1p56_sh : forall (Wa Wb : world SEGS) ma mb a n,
  (forall x, shadow_addr a <= x < shadow_addr a + (n + 7) / 8 ->
     aview SEGS (w_H Wb) mb x = aview SEGS (w_H Wa) ma x) ->
  sh_blk Wa ma a n -> sh_blk Wb mb a n.
Proof.
intros Wa Wb ma mb a n HK HS. unfold sh_blk in *.
apply (block_shadow_agree (aview SEGS (w_H Wa) ma) (aview SEGS (w_H Wb) mb) SHADOW_OFF a n); [|exact HS].
intros j Hj. apply HK. unfold shadow_of_addr, shadow_addr in *. lia.
Qed.
Lemma d1p56_vis : forall (W : world SEGS) mem a bs j,
  bytes_at8 W mem a bs -> (j < length bs)%nat -> aview SEGS (w_H W) mem (a + Z.of_nat j) <> None.
Proof.
intros W mem a bs j HB Hj.
destruct (HB j ltac:(rewrite length_map; exact Hj)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. discriminate.
Qed.
(* A block of the running state is not one of the entry's. *)
Lemma d1p56_notin : forall ly S (W : world SEGS) mem md b n l,
  AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) ((b, n) :: l) -> 0 <= n -> ~ In (b, n) l.
Proof.
intros ly S W mem md b n l HAR HP Hn Hin.
apply in_split in Hin as (l1 & l2 & ->).
assert (HP2 : Permutation (ablocks B ly S) ((b, n) :: (b, n) :: l1 ++ l2)).
{ etransitivity; [exact HP|]. apply perm_skip. symmetry. apply Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md (b, n) (b, n) (l1 ++ l2) HAR HP2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos n Hn). lia.
Qed.
(* The frame's shadow lies far below the machine stack's window. *)
Lemma d1p56_shlo : forall x, 0 <= x -> x + 1024 <= alloc_ceiling -> shadow_addr x + 128 < alloc_ceiling.
Proof.
intros x Hx Hc. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
assert (Hq : 8 * (x / 8) <= x).
{ pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
lia.
Qed.
Lemma d1p56_notWR : forall g pos mf a, 4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
  alloc_ceiling + ASTACK <= mf -> mf + 168 <= a -> ~ WR1 g pos mf a.
Proof.
intros g pos mf a H0 H1 H2 Ha.
pose proof (d1p56_shlo (SFa g pos) ltac:(lia) H1) as HSH.
assert (Has : ASTACK = 16384) by reflexivity.
unfold WR1, WR0, V_before, N_before, V_again, N_again, V_id, N_id.
clear - H0 H1 H2 Ha HSH Has. lia.
Qed.

(* ---- the call chain at a call made after the record's own stores ---------------------------------------------- *)
(* d1_chain of the cut file asks that the whole machine stack above mf is as it was at the segment's start; from
   Ph2 on mf+144 is not, so this is that lemma with only the two words the chain reads. *)
Lemma d1p56_chain : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 mem3 md3 kk (regsT : bvmap 5 word),
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
    intros kk' Hkk. apply KEEP; clear - Hkk; cbn [Z.of_nat] in Hkk; lia.
  + apply rdword_of_val_mem; [|unfold s0Z; clear - Rs0r; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W3) mem2 mem3 (sp0 - 16) (sp0 - 16) 8 (s0Z (e_regs g))); [|exact Vs0].
    intros kk' Hkk. apply KEEP; clear - Hkk; cbn [Z.of_nat] in Hkk; lia.
  + rewrite <- Hraz. exact Hra4.
  + clear - Hceil Hslo Hstk0. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmfb. lia.
- exists []. split; [|left; reflexivity].
  eapply (achain_chain_pre ly3 _ mf sp0 []); [| rewrite Usp; clear - Hmf0; unfold ASTACK in *; lia | exact Us0 | exact Ura4].
  left. split; [right; left; exact Hge | reflexivity].
Qed.

(* ---- Ph5's malloc: 0x80c40 malloc(k + 1) ---------------------------------------------------------------------- *)
Lemma d1p56_malloc2 : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 pl ly3 S3 (W3 : world SEGS) mem3
  (regsT : bvmap 5 word) memT mdT,
  CTX g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 memT mdT (4 * Z.of_nat i + 1) ->
  frames S3 = [(4, pos)] ->
  Permutation (ablocks B ly3 S3) ([(pl, D1k g i)] ++ ablocks B ly2 S2) ->
  mo_le MT S2 S3 (mo_malloc MT (D1k g i)) ->
  (forall a, aview SEGS (w_H W3) memT a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, 0 <= a < 2 ^ 64 ->
     (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
      shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
     ~ WR1 g pos mf a -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
  RC B g pos mf i regsT ->
  getr regsT 10 = w64 (D1k g i + 1) ->
  getr regsT 23 = w64 (SlotModel.rec_r (e_pl g) i) ->
  getr regsT 25 = w64 pl ->
  getr regsT 22 = w64 (D1k g i) ->
  getr regsT 27 = w64 (D1addr g i) ->
  getr regsT 26 = w64 (e_p g + D1body g i) ->
  getr regsT 1 = Z_to_bv 64 (BASE + 0x538) ->
  val_mem SEGS (rd W3 mem3) (mf + 144) 8 (e_n g - D1body g i) ->
  bytes_at8 W3 mem3 pl (SlotModel.rec_pl (e_pl g) i) ->
  sh_blk W3 mem3 (SFa g pos + V_before) N_before ->
  bytes_at8 W3 mem3 (SFa g pos + V_before) (m_id g i) ->
  bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g (S i)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) mdT)
    (fun W4 c4 => exists gb, RUNS g pos mf i ly2 S2 W2 mem2 2 (BASE + 0x538)
       (mo_malloc MT (D1k g i) + mo_malloc MT (D1k g i + 1)) [(gb, D1k g i + 1); (pl, D1k g i)] (WR1 g pos mf)
       (P5 B g pos mf i pl gb) W4 c4).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl ly3 S3 W3 mem3 regsT memT mdT
  HC HJ3 Hfrs3 Hperm3 MLE3 KEEPT KEEP3 HRC R10 R23 R25 R22 R27 R26 R1 V144 B8pl SHb B8b B8id.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJ & Hfrs & Hk & MLE & MOK & HEC & Hi & _ & _ & _ & HRL).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & Hnev0 & Hlive0 & _).
destruct HRL as (_ & _ & _ & _ & _ & Hbl & _ & _).
pose proof HRC as (Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs3 & R20 & R21 & R24).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof (d1p56_shlo (SFa g pos) ltac:(lia) HSF1) as HSH.
set (k := D1k g i) in *.
assert (Hkr : 0 <= k <= 255) by (apply SlotModel.rec_k_range).
assert (Usp : spZ regsT = mf).
{ unfold spZ. rewrite Rsp. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1 Has. lia. }
assert (Us0 : s0Z regsT = e_sp0 g).
{ unfold s0Z. rewrite Rs0. apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1 Has. lia. }
assert (Ura : raZ regsT = BASE + 0x538).
{ unfold raZ. rewrite R1. apply unsigned_lit_small. clear - HBASE. lia. }
assert (KEEPhi : forall a, e_sp0 g - 16 <= a < e_sp0 g -> aview SEGS (w_H W3) memT a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. rewrite (KEEPT a). apply KEEP3.
  - clear - Ha Hmf0 Hmfb H47 C1 Has. lia.
  - left. clear - Ha Hmf0 Hmfb Has. lia.
  - apply (d1p56_notWR g pos mf a HSF0 HSF1 ltac:(clear - Hmf0; lia)). clear - Ha Hmfb. lia. }
destruct (d1p56_chain g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 memT mdT (4 * Z.of_nat i + 1) regsT HC HJ3
  KEEPhi Usp Us0 ltac:(rewrite Ura; clear - HBLO; lia)) as (ch & HCH & Hchs).
assert (Hlive : blocks_bytes S3 + (k + 1) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ Hperm3), bsum_app,
    (bsum_perm _ _ (proj1 Hbl)), app_nil_l, <- (blocks_bytes_bsum B (e_ly g) (e_S g)).
  cbn [bsum fold_right fst snd].
  unfold LIVE_LLVMF in HLIVE. clear - Hlive0 HLIVE Hkr. lia. }
assert (Hnev : st_nev S3 < EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hn2 & _). unfold EV_LLVMF in HEV. clear - Hn2 Hnev0 HEV Hi64. lia. }
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0. pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_mono MT MTL (k + 1) 256 ltac:(lia)) as HMk1.
pose proof (mo_malloc_mono MT MTL k 256 ltac:(lia)) as HMk.
pose proof (mo_malloc_nonneg MT MTL k ltac:(lia)) as HMk0.
pose proof (mo_malloc_nonneg MT MTL (k + 1) ltac:(lia)) as HMk10.
assert (MOKm : mo_ok MT S3 (mo_malloc MT (k + 1))).
{ apply (mo_ok_step MT MTL S2 S3 (mo_malloc MT k) (mo_malloc MT (k + 1))); [|exact MLE3].
  apply (mo_ok_le MT MTL S2 (mo_malloc MT k + mo_malloc MT (k + 1))
    ((EV_LLVMF - 4 * Z.of_nat i) * (mo_malloc MT 256 + mo_free MT)) MOK).
  unfold EV_LLVMF. clear - HM0 HF0 HMk HMk1 Hi64. nia. }
eapply SRr_mono.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC4 W3 regsT memT LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 mdT (4 * Z.of_nat i + 1) (k + 1)
    (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0x538)) ch HJ3 R10).
  - unfold MALLOC_MAX. clear - Hkr. lia.
  - exact Hlive.
  - rewrite Usp. clear. lia.
  - clear - Hmf32 Hsp0al. apply Z.mod_divide in Hmf32; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
    apply Z.mod_divide; [lia|]. destruct Hmf32 as [q1 E1]. destruct Hsp0al as [q2 E2]. exists (2 * q1 - q2). lia.
  - clear - Hmfb. lia.
  - clear - HSTKm. lia.
  - exact Rgp.
  - exact Rtp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact Hnev.
  - exact HCH.
  - exact (d1_univ_malloc B RA_LLVMF HUMM regsT 0x538 ch _ _ Ura ltac:(cbn; tauto) Hchs).
  - exact MOKm. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & res & -> & HJ4 & HP4 & Hres & Hfr4 & Hr4 & Hbl4 & HK4 &
  MLE4 & _).
pose proof HJ4 as (HAR4 & Hly4 & _). pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
assert (EFa4 : frame_addr ly4 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF4; reflexivity).
pose proof HJ3 as (HAR3 & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (Hplin : In (pl, k) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); cbn [app In]; left; reflexivity).
assert (Hresb : In (res, k + 1) (ablocks B ly4 S4)) by (rewrite Hbl4; apply in_or_app; right; left; reflexivity).
assert (HEnot : forall a, res <= a < res + req_size (k + 1) ->
  ~ (SFa g pos <= a < SFa g pos + 1024 \/ shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128)).
{ intros a Ha. apply (d1_fz_not_block B LAWS g pos ly4 S4 W4 mem4 md4 res (k + 1) a HAR4).
  - rewrite Hfr4, Hfrs3. left. reflexivity.
  - exact EFa4.
  - exact Hresb.
  - exact Ha. }
assert (KEEPZ : forall a, 0 <= a < 2 ^ 64 ->
  (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
   shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
  ~ (mf - ASTACK <= a < mf) -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hz Hnw. rewrite <- (KEEPT a).
  apply (d1_keep_alloc B g pos mf (fun a' => mf - ASTACK <= a' < mf) ly3 S3 W3 memT W4 mem4
    (fun a' => res <= a' < res + req_size (k + 1)) W3 memT (e_sp0 g) (mf - e_sp0 g) Hin4 EFa3 HK4
    ltac:(clear; lia) ltac:(intros a' Ha'; exact Ha') HEnot ltac:(intros a' Ha' Hz' Hn'; reflexivity) a Ha Hz Hnw). }
replace (4 * Z.of_nat i + 1 + 1) with (4 * Z.of_nat i + 2) in HJ4 by lia.
exists res. unfold D1S. exists ly4, S4, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [rewrite Hfr4; exact Hfrs3|].
split.
{ rewrite Hbl4. etransitivity; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact Hperm3. }
split.
{ constructor; [cbn [fst]; exact Hr4|]. constructor; [|constructor]. cbn [fst].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hplin) as (_ & Hpl4096 & _). exact Hpl4096. }
split; [exact (mo_le_trans MT MTL S2 S3 S4 _ _ MLE3 MLE4)|].
split.
{ intros a Ha Hz Hnw. rewrite (KEEPZ a Ha Hz ltac:(intros Hc; apply Hnw; left; left; exact Hc)).
  exact (KEEP3 a Ha Hz Hnw). }
assert (Hbnd : forall a, mf + 144 <= a < mf + 152 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply KEEPZ; [clear - Ha Hmf0 Hmfb H47 C1 Has; lia | left; clear - Ha Hmf0 Has; lia
  | clear - Ha Hmf0 Has; lia]. }
assert (Hfb : forall a, SFa g pos <= a < SFa g pos + 1024 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply KEEPZ; [clear - Ha HSF0 HSF1 C1; lia | right; left; exact Ha
  | clear - Ha HSF1 Hmf0 Has; lia]. }
assert (Hfs : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply KEEPZ; [clear - Ha HSH C1 HSF0; unfold shadow_addr, SHADOW_OFF in *; lia
  | right; right; exact Ha | clear - Ha HSH Hmf0 Has; lia]. }
unfold P5. split; [exact (d1_RC_pres B g pos mf i regsT regs4 HP4 HRC)|].
split; [exact Hres|].
split; [rewrite (d1_presv regsT regs4 23%bv HP4) by d1_cs; exact R23|].
split; [rewrite (d1_presv regsT regs4 25%bv HP4) by d1_cs; exact R25|].
split; [rewrite (d1_presv regsT regs4 22%bv HP4) by d1_cs; exact R22|].
split; [rewrite (d1_presv regsT regs4 27%bv HP4) by d1_cs; exact R27|].
split; [rewrite (d1_presv regsT regs4 26%bv HP4) by d1_cs; exact R26|].
split.
{ apply (d1p56_vm W3 W4 mem3 mem4 (mf + 144) 8 (e_n g - D1body g i)); [|exact V144].
  intros x Hx. apply Hbnd. cbn [Z.of_nat] in Hx. lia. }
split.
{ pose proof HK4 as (_ & K2 & _).
  apply (d1p56_b8 W3 W4 mem3 mem4 pl (SlotModel.rec_pl (e_pl g) i)); [|exact B8pl].
  intros x Hx. rewrite SlotModel.rec_pl_length in Hx.
  change (SlotModel.rec_k (e_pl g) i) with k in Hx. rewrite Z2Nat.id in Hx by (clear - Hkr; lia).
  rewrite <- (KEEPT x). replace x with (pl + (x - pl)) by lia.
  apply (K2 pl k (x - pl) Hplin).
  - pose proof (req_size_pos k ltac:(lia)) as Hrq. clear - Hx Hkr Hrq. lia.
  - intros Hc. apply in_split in Hplin as (l1 & l2 & E1).
    pose proof (sep_blocks_pos SEGS B LAWS ly4 S4 W4 mem4 md4 (pl, k) (res, k + 1) l1 l2 [] HAR4
      ltac:(rewrite Hbl4, E1, <- app_assoc; reflexivity)) as Hd.
    unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos k ltac:(lia)) as Hq1. pose proof (req_size_pos (k + 1) ltac:(lia)) as Hq2.
    clear - Hd Hc Hx Hkr Hq1 Hq2. lia. }
split.
{ apply (d1p56_sh W3 W4 mem3 mem4 (SFa g pos + V_before) N_before); [|exact SHb].
  intros x Hx. apply Hfs. unfold V_before, N_before, shadow_addr, SHADOW_OFF in *.
  assert (Hq : 8 * (SFa g pos / 8) <= SFa g pos < 8 * (SFa g pos / 8) + 8).
  { pose proof (Z.div_mod (SFa g pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SFa g pos) 8 ltac:(lia)). lia. }
  assert (Hq2 : 8 * ((SFa g pos + 32) / 8) <= SFa g pos + 32 < 8 * ((SFa g pos + 32) / 8) + 8).
  { pose proof (Z.div_mod (SFa g pos + 32) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SFa g pos + 32) 8 ltac:(lia)). lia. }
  clear - Hx Hq Hq2. lia. }
split.
{ apply (d1p56_b8 W3 W4 mem3 mem4 (SFa g pos + V_before) (m_id g i)); [|exact B8b].
  intros x Hx. apply Hfb. unfold m_id in Hx. rewrite SlotModel.rec_id_length in Hx.
  unfold V_before, RcIdentModel.ID_SIZE in *. clear - Hx. lia. }
{ apply (d1p56_b8 W3 W4 mem3 mem4 (SFa g pos + V_id) (m_id g (S i))); [|exact B8id].
  intros x Hx. apply Hfb. unfold m_id in Hx. rewrite SlotModel.rec_id_length in Hx.
  unfold V_id, RcIdentModel.ID_SIZE in *. clear - Hx. lia. }
Qed.

(* ---- Ph5: 0x80c30..0x80c44 ------------------------------------------------------------------------------------ *)
Theorem d1_ph5 : d1_ph5_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold d1_ph5_stmt. intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3 HC HD.
destruct HD as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP).
destruct HP as (HRC & R10 & R25 & R22 & R27 & R26 & V144 & B8pl & SHb & B8b & B8id).
pose proof HRC as (Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs3 & R20 & R21 & R24).
pose proof (SlotModel.rec_r_range (e_pl g) i) as Hrr.
assert (Hkr : 0 <= D1k g i <= 255) by (apply SlotModel.rec_k_range).
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs3 []) kk)
  by (intros kk Hkk; rewrite HE; apply Eimg_low; exact Hkk).
assert (E10 : ew E 10 = Z_to_bv 64 (SlotModel.rec_r (e_pl g) i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E22 : ew E 22 = Z_to_bv 64 (D1k g i))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact R22).
assert (HAE : env_agree 32 (Ereg regs3 []) E)
  by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x524 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x524)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x524)) with (Z_to_bv 64 (BASE + 0x524)).
psrr_branch_pi RUNP BR HS.
- (* the ingest result is >= 0: on to the guard copy's malloc *)
  paj_run_shc RUNP RUNC HS HJ3.
  { awr_ok_tac. }
  assert (KEEPT : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
  { intros a. apply aview_eq_of. apply HFr. intros (r & Hr & _). destruct Hr. }
  pmkst HS. rewrite (pal_malloc B TL).
  prreg HS (1%bv : bv 5) Q1.
  d1p56_prraw HS (10%bv : bv 5) Q10. d1p56_prraw HS (23%bv : bv 5) Q23.
  pose proof (regs_kept_of_st_ok SEGS E _ _ _ _ [2; 3; 4; 8; 9; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  eapply (d1p56_malloc2 g pos mf i ly2 S2 W2 regs2 mem2 md2 pl ly3 S3 W3 mem3 _ _ _ HC HJ3 Hfrs3 Hperm3 MLE3
    KEEPT KEEP3).
  + unfold RC. repeat split; (rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right]))); assumption.
  + eapply d1_reg_val; [exact Q10 | | clear - Hkr; lia].
    first [ apply (d1_U_off E 22 1 (D1k g i) ltac:(d1_ew)); clear - Hkr; lia
          | rewrite U_SAlu, (U_atom E 22 (D1k g i) ltac:(d1_ew)) by (clear - Hkr; lia);
            rewrite U_lit by lia; cbn [zalu_raw]; apply d1_zcanon_small; clear - Hkr; lia ].
  + eapply d1_reg_val; [exact Q23 | apply (U_atom E 10 _ ltac:(d1_ew)); clear - Hrr; lia | clear - Hrr; lia].
  + rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). exact R25.
  + rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). exact R22.
  + rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). exact R27.
  + rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). exact R26.
  + exact Q1.
  + exact V144.
  + exact B8pl.
  + exact SHb.
  + exact B8b.
  + exact B8id.
- (* the result is < 0: the plain model refutes it *)
  exfalso.
  rewrite (d1_branch_ge E (SOff 10 0) (SLit 0)) in Hc.
  + apply negb_false_iff, Z.ltb_lt in Hc.
    rewrite (U_atom E 10 _ E10) in Hc by (clear - Hrr; lia). rewrite U_lit in Hc by lia. clear - Hc Hrr. lia.
  + rewrite (U_atom E 10 _ E10) by (clear - Hrr; lia). clear - Hrr. lia.
  + rewrite U_lit by lia. lia.
Qed.

(* ---- Ph6: 0x80c44..0x80c64 ------------------------------------------------------------------------------------ *)
Theorem d1_ph6 : d1_ph6_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold d1_ph6_stmt. intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3 HC HD.
destruct HD as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfrs3 & Hperm3 & Hhs3 & MLE3 & KEEP3 & HP).
destruct HP as (HRC & R10 & R23 & R25 & R22 & R27 & R26 & V144 & B8pl & SHb & B8b & B8id).
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & (Hn & Hinp2 & Hine & Hp4096 & Hpce & Hpapp & Hnlen) & Hi64 & Hcur).
pose proof HC as (HJent & Hfrs & Hkent & MLE & MOK & HEC & Hi & _ & _ & _ & HRL).
destruct HRL as (_ & _ & _ & _ & _ & Hbl & _ & _).
pose proof (proj1 Hbl) as Hbl2. rewrite app_nil_l in Hbl2.
pose proof HRC as (Rsp & Rs1 & Rs0 & Rgp & Rtp & Rs3 & R20 & R21 & R24).
assert (Hkr : 0 <= D1k g i <= 255) by (apply SlotModel.rec_k_range).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (d1p56_shlo (SFa g pos) ltac:(lia) HSF1) as HSH.
set (k := D1k g i) in *.
assert (Hgb4096 : 4096 <= gb) by (pose proof (Forall_inv Hhs3) as Hf; cbn [fst] in Hf; exact Hf).
assert (Hgbin : In (gb, k + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); cbn [app In]; left; reflexivity).
assert (Hplin : In (pl, k) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); cbn [app In]; right; left; reflexivity).
pose proof HJ3 as (HAR3 & Hly3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hgbin) as (_ & _ & Hgbce & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hplin) as (_ & Hpl4096 & Hplce & _).
pose proof (req_size_pos k ltac:(lia)) as Hrq1. pose proof (req_size_pos (k + 1) ltac:(lia)) as Hrq2.
assert (Hgbnew : ~ In (gb, k + 1) (ablocks B (e_ly g) (e_S g))).
{ intros Hcc.
  apply (d1p56_notin ly3 S3 W3 mem3 md3 gb (k + 1) ((pl, k) :: ablocks B ly2 S2) HAR3
    ltac:(cbn [app] in Hperm3; exact Hperm3) ltac:(clear - Hkr; lia)).
  right. apply (Permutation_in _ (Permutation_sym Hbl2)). exact Hcc. }
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EL : forall kk, (kk < A_TEXT)%nat -> ew E kk = ew (Ereg regs3 []) kk)
  by (intros kk Hkk; rewrite HE; apply Eimg_low; exact Hkk).
assert (E10 : ew E 10 = Z_to_bv 64 gb)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact R10).
assert (E22 : ew E 22 = Z_to_bv 64 k)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 22 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 pl)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs3 _ 25 25%bv eq_refl); exact R25).
assert (HAE : env_agree 32 (Ereg regs3 []) E)
  by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x538 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x538)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x538)) with (Z_to_bv 64 (BASE + 0x538)).
psrr_branch_pi RUNP BR HS.
- (* the malloc did not return NULL *)
  paj_run_shc RUNP RUNC HS HJ3.
  { awr_ok_tac. }
  psrr_branch_pi RUNP BR HS.
  + (* k = 0: no copy *)
    assert (Hk0 : k = 0).
    { rewrite (branch_eq_U E (SOff 22 0) (SLit 0)) in Hc0.
      apply Z.eqb_eq in Hc0. rewrite (U_atom E 22 k E22) in Hc0 by (clear - Hkr; lia).
      rewrite U_lit in Hc0 by lia. exact Hc0. }
    paj_run_to_shc RUNTOP HS HJ3 (0x558).
    { awr_ok_tac. }
    assert (KEEPT : forall a, aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms) a).
    { intros a. apply aview_eq_of. apply HFr0. intros (r & Hr & _). destruct Hr. }
    assert (KEEPT1 : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
    { intros a. apply aview_eq_of. apply HFr. intros (r & Hr & _). destruct Hr. }
    assert (KEEPB : forall a, aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a)
      by (intros a; rewrite (KEEPT a); apply KEEPT1).
    d1p56_prraw HS (18%bv : bv 5) Q18.
    pose proof (regs_kept_of_st_ok_pi E _ _ _ _ [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict] in HKR.
    pmkst HS. apply SRr_ret.
    unfold D1S. exists ly3, S3, (ms_regs ms0), (ms_mem ms0), (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat md3)) mat0 (with_vm_backing (m_vm_lazy md3) mat md3)).
    split; [reflexivity|]. split; [exact HJ3|]. split; [exact Hfrs3|]. split; [exact Hperm3|]. split; [exact Hhs3|].
    split; [exact MLE3|].
    split; [intros a Ha Hz Hnw; rewrite (KEEPB a); exact (KEEP3 a Ha Hz Hnw)|].
    unfold P6. split.
    { unfold RC. repeat split; (rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right]))); assumption. }
    split; [eapply d1_reg_val; [exact Q18 | apply (U_atom E 10 _ ltac:(d1_ew)); clear - Hgb4096 Hgbce Hrq2 C1; lia
                                | clear - Hgb4096 Hgbce Hrq2 C1; lia]|].
    split; [rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R23|].
    split; [rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R25|].
    split; [rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R22|].
    split; [rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R27|].
    split; [rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R26|].
    split; [exact (d1p56_vm W3 W3 mem3 (ms_mem ms0) (mf + 144) 8 _ ltac:(intros x _; apply KEEPB) V144)|].
    split; [exact (d1p56_b8 W3 W3 mem3 (ms_mem ms0) pl _ ltac:(intros x _; apply KEEPB) B8pl)|].
    split.
    { assert (Hnil : SlotModel.rec_pl (e_pl g) i = []).
      { apply length_zero_iff_nil. rewrite SlotModel.rec_pl_length.
        change (SlotModel.rec_k (e_pl g) i) with k. rewrite Hk0. reflexivity. }
      unfold bytes_at8. rewrite Hnil. cbn [map]. apply garr8_nil. }
    split; [exact (d1p56_sh W3 W3 mem3 (ms_mem ms0) _ _ ltac:(intros x _; apply KEEPB) SHb)|].
    split; [exact (d1p56_b8 W3 W3 mem3 (ms_mem ms0) _ _ ltac:(intros x _; apply KEEPB) B8b)|].
    exact (d1p56_b8 W3 W3 mem3 (ms_mem ms0) _ _ ltac:(intros x _; apply KEEPB) B8id).
  + (* k > 0: the copy *)
    assert (Hk0 : k <> 0).
    { rewrite (branch_eq_U E (SOff 22 0) (SLit 0)) in Hc0.
      apply Z.eqb_neq in Hc0. rewrite (U_atom E 22 k E22) in Hc0 by (clear - Hkr; lia).
      rewrite U_lit in Hc0 by lia. exact Hc0. }
    paj_run_shc RUNP RUNC HS HJ3.
    { awr_ok_tac. }
    assert (KEEPT : forall a, aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) (ms_mem ms) a).
    { intros a. apply aview_eq_of. apply HFr0. intros (r & Hr & _). destruct Hr. }
    assert (KEEPT1 : forall a, aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
    { intros a. apply aview_eq_of. apply HFr. intros (r & Hr & _). destruct Hr. }
    assert (KEEPB : forall a, aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a)
      by (intros a; rewrite (KEEPT a); apply KEEPT1).
    pose proof HJ3 as (HAR3' & _).
    assert (B8plT : bytes_at8 W3 (ms_mem ms0) pl (SlotModel.rec_pl (e_pl g) i))
      by (exact (d1p56_b8 W3 W3 mem3 (ms_mem ms0) pl _ ltac:(intros x _; apply KEEPB) B8pl)).
    pmkst HS.
    prreg HS (1%bv : bv 5) Rra.
    d1p56_prraw HS (10%bv : bv 5) Qa0. d1p56_prraw HS (11%bv : bv 5) Qa1. d1p56_prraw HS (12%bv : bv 5) Qa2.
    d1p56_prraw HS (18%bv : bv 5) Q18.
    pose proof (regs_kept_of_st_ok SEGS E _ _ _ _ [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict] in HKR.
    assert (Ma0 : getr (ms_regs ms0) 10 = w64 gb)
      by (eapply d1_reg_val; [exact Qa0 | apply (U_atom E 10 _ ltac:(d1_ew)); clear - Hgb4096 Hgbce Hrq2 C1; lia
                              | clear - Hgb4096 Hgbce Hrq2 C1; lia]).
    assert (Ma1 : getr (ms_regs ms0) 11 = w64 pl)
      by (eapply d1_reg_val; [exact Qa1 | apply (U_atom E 25 _ ltac:(d1_ew)); clear - Hpl4096 Hplce Hrq1 C1; lia
                              | clear - Hpl4096 Hplce Hrq1 C1; lia]).
    assert (Ma2 : getr (ms_regs ms0) 12 = w64 k)
      by (eapply d1_reg_val; [exact Qa2 | apply (U_atom E 22 _ ltac:(d1_ew)); clear - Hkr; lia | clear - Hkr; lia]).
    assert (M18 : getr (ms_regs ms0) 18 = w64 gb)
      by (eapply d1_reg_val; [exact Q18 | apply (U_atom E 10 _ ltac:(d1_ew)); clear - Hgb4096 Hgbce Hrq2 C1; lia
                              | clear - Hgb4096 Hgbce Hrq2 C1; lia]).
    assert (Msp : spZ (ms_regs ms0) = e_sp0 g + (mf - e_sp0 g)).
    { unfold spZ. rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). rewrite Rsp.
      rewrite unsigned_lit_small by (clear - Hmf0 Hmfb H47 C1 Has; lia). lia. }
    eapply SRr_bind.
    { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      eapply (aj_intrin_at SEGS B LAWS pa_segs_low OCpy (SIGMA IS___asan_memcpy) AMEMCPY W3 rT mT
        LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 dT
        (4 * Z.of_nat i + 2) gb pl k (mf - e_sp0 g) (Z_to_bv 64 (BASE + 0x558)) HJ3) end.
      - exact Ma0.
      - exact Ma1.
      - exact Ma2.
      - clear - Hkr. lia.
      - clear - Hgb4096. lia.
      - clear - Hgb4096 Hgbce Hkr Hrq2 C1. lia.
      - exact Msp.
      - clear - Hmf32 Hsp0al. apply Z.mod_divide in Hmf32; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
        apply Z.mod_divide; [lia|]. destruct Hmf32 as [q1 E1]. destruct Hsp0al as [q2 E2]. exists (2 * q1 - q2). lia.
      - clear - Hmfb. lia.
      - clear - HSTKm Hmfb Hes Has. lia.
      - rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). exact Rgp.
      - rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])). exact Rtp.
      - exact Rra.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. split.
        + right. right. left. exists gb, (k + 1).
          split; [exact Hgbin|]. split; [exact Hgbnew|]. clear - Ha Hkr Hrq2. lia.
        + clear - Ha Hgb4096 Hgbce Hkr Hrq2 Hmf0 Has Hes Hmfb. lia.
      - exact (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ gb (k + 1) gb k HAR3' Hgbin
          ltac:(lia) ltac:(clear - Hkr Hrq2; lia)).
      - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ gb (k + 1) gb k HAR3' Hgbin
          ltac:(lia) ltac:(clear - Hkr Hrq2; lia)).
      - intros Hkpos.
        exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ gb (k + 1) gb k HAR3' Hgbin
          ltac:(lia) ltac:(clear - Hkr Hrq2; lia) Hkpos).
      - split; [clear - Hpl4096; lia|].
        split; [clear - Hpl4096 Hplce Hkr Hrq1 C1; lia|].
        split.
        { intros a Ha. split.
          - replace a with (pl + Z.of_nat (Z.to_nat (a - pl))) by lia.
            apply (d1p56_vis W3 (ms_mem ms0) pl (SlotModel.rec_pl (e_pl g) i) (Z.to_nat (a - pl)) B8plT).
            rewrite SlotModel.rec_pl_length. change (SlotModel.rec_k (e_pl g) i) with k.
            clear - Ha Hkr. lia.
          - rewrite Msp. clear - Ha Hpl4096 Hplce Hkr Hrq1 Hmf0 Has Hes. lia. }
        split.
        { pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ gb (k + 1) pl k HAR3' Hgbin Hplin
            ltac:(intros Hcc; injection Hcc as _ Hcc2; clear - Hcc2; lia)) as Hd.
          unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hkr Hrq1 Hrq2. lia. }
        split.
        { exact (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ pl k pl k HAR3' Hplin
            ltac:(lia) ltac:(clear - Hkr Hrq1; lia)). }
        split.
        { exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ pl k pl k HAR3' Hplin
            ltac:(lia) ltac:(clear - Hkr Hrq1; lia)). }
        { intros Hkpos.
          exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ pl k pl k HAR3' Hplin
            ltac:(lia) ltac:(clear - Hkr Hrq1; lia) Hkpos). } }
    cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha0 & Heff & Hfrc & Hpres4).
    apply SRr_ret.
    assert (HKEEPm : forall a, 0 <= a < 2 ^ 64 ->
      (alloc_ceiling <= a \/ SFa g pos <= a < SFa g pos + 1024 \/
       shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
      ~ (mf - ASTACK <= a < mf) -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) (ms_mem ms0) a).
    { intros a Ha Hz Hnw. apply (Hfrc a Ha).
      - intros Hc1. destruct Hz as [Hz | Hz].
        + clear - Hz Hc1 Hgbce Hkr Hrq2 C1. lia.
        + apply (d1_fz_not_block B LAWS g pos ly3 S3 W3 (ms_mem ms0) _ gb (k + 1) a HAR3'
            ltac:(rewrite Hfrs3; left; reflexivity) ltac:(unfold SFa, frame_addr;
              pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _); rewrite EF3; reflexivity) Hgbin
            ltac:(clear - Hc1 Hkr Hrq2; lia)).
          exact Hz.
      - intros Hc1. apply Hnw. clear - Hc1 Hes Has. lia. }
    unfold D1S. exists ly3, S3, regs4, mem4, md4.
    split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfrs3|]. split; [exact Hperm3|]. split; [exact Hhs3|].
    split; [exact MLE3|].
    split.
    { intros a Ha Hz Hnw.
      rewrite (HKEEPm a Ha Hz ltac:(intros Hc1; apply Hnw; left; left; exact Hc1)), (KEEPB a).
      exact (KEEP3 a Ha Hz Hnw). }
    unfold P6. split.
    { apply (d1_RC_pres B g pos mf i (ms_regs ms0) regs4 HP4). unfold RC.
      repeat split; (rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right]))); assumption. }
    split; [rewrite (d1_presv (ms_regs ms0) regs4 18%bv HP4) by d1_cs; exact M18|].
    split; [rewrite (d1_presv (ms_regs ms0) regs4 23%bv HP4) by d1_cs;
            rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R23|].
    split; [rewrite (d1_presv (ms_regs ms0) regs4 25%bv HP4) by d1_cs;
            rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R25|].
    split; [rewrite (d1_presv (ms_regs ms0) regs4 22%bv HP4) by d1_cs;
            rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R22|].
    split; [rewrite (d1_presv (ms_regs ms0) regs4 27%bv HP4) by d1_cs;
            rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R27|].
    split; [rewrite (d1_presv (ms_regs ms0) regs4 26%bv HP4) by d1_cs;
            rewrite HKR by (cbn [In]; repeat (first [left; reflexivity | right])); exact R26|].
    assert (Hbnd : forall a, mf + 144 <= a < mf + 152 -> aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha. rewrite (HKEEPm a ltac:(clear - Ha Hmf0 Hmfb H47 C1 Has; lia)
        ltac:(left; clear - Ha Hmf0 Has; lia) ltac:(clear - Ha Hmf0 Has; lia)).
      apply KEEPB. }
    assert (Hfb : forall a, SFa g pos <= a < SFa g pos + 1024 ->
      aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha. rewrite (HKEEPm a ltac:(clear - Ha HSF0 HSF1 C1; lia) ltac:(right; left; exact Ha)
        ltac:(clear - Ha HSF1 Hmf0 Has; lia)).
      apply KEEPB. }
    assert (Hfs : forall a, shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 ->
      aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
    { intros a Ha. rewrite (HKEEPm a ltac:(clear - Ha HSH C1 HSF0; unfold shadow_addr, SHADOW_OFF in *; lia)
        ltac:(right; right; exact Ha) ltac:(clear - Ha HSH Hmf0 Has; lia)).
      apply KEEPB. }
    split.
    { apply (d1p56_vm W3 W3 mem3 mem4 (mf + 144) 8 (e_n g - D1body g i)); [|exact V144].
      intros x Hx. apply Hbnd. cbn [Z.of_nat] in Hx. lia. }
    split.
    { apply (d1p56_b8 W3 W3 (ms_mem ms0) mem4 pl (SlotModel.rec_pl (e_pl g) i)); [|exact B8plT].
      intros x Hx. rewrite SlotModel.rec_pl_length in Hx.
      change (SlotModel.rec_k (e_pl g) i) with k in Hx. rewrite Z2Nat.id in Hx by (clear - Hkr; lia).
      apply (Hfrc x ltac:(clear - Hx Hpl4096 Hplce Hkr Hrq1 C1; lia)).
      - pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 (ms_mem ms0) _ gb (k + 1) pl k HAR3' Hgbin Hplin
          ltac:(intros Hcc; injection Hcc as _ Hcc2; clear - Hcc2; lia)) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hx Hkr Hrq1 Hrq2. lia.
      - clear - Hx Hpl4096 Hplce Hkr Hrq1 Hmf0 Has Hes. lia. }
    split.
    { apply (d1p56_b8_copy W3 (ms_mem ms0) mem4 gb pl (SlotModel.rec_pl (e_pl g) i)); [|exact B8plT].
      intros j Hj. rewrite SlotModel.rec_pl_length in Hj.
      change (SlotModel.rec_k (e_pl g) i) with k in Hj. rewrite Z2Nat.id in Hj by (clear - Hkr; lia).
      apply Heff. clear - Hj Hkr. lia. }
    split.
    { apply (d1p56_sh W3 W3 mem3 mem4 (SFa g pos + V_before) N_before); [|exact SHb].
      intros x Hx. apply Hfs. unfold V_before, N_before, shadow_addr, SHADOW_OFF in *.
      assert (Hq : 8 * (SFa g pos / 8) <= SFa g pos < 8 * (SFa g pos / 8) + 8).
      { pose proof (Z.div_mod (SFa g pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SFa g pos) 8 ltac:(lia)). lia. }
      assert (Hq2 : 8 * ((SFa g pos + 32) / 8) <= SFa g pos + 32 < 8 * ((SFa g pos + 32) / 8) + 8).
      { pose proof (Z.div_mod (SFa g pos + 32) 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (SFa g pos + 32) 8 ltac:(lia)). lia. }
      clear - Hx Hq Hq2. lia. }
    split.
    { apply (d1p56_b8 W3 W3 mem3 mem4 (SFa g pos + V_before) (m_id g i)); [|exact B8b].
      intros x Hx. apply Hfb. unfold m_id in Hx. rewrite SlotModel.rec_id_length in Hx.
      unfold V_before, RcIdentModel.ID_SIZE in *. clear - Hx. lia. }
    { apply (d1p56_b8 W3 W3 mem3 mem4 (SFa g pos + V_id) (m_id g (S i))); [|exact B8id].
      intros x Hx. apply Hfb. unfold m_id in Hx. rewrite SlotModel.rec_id_length in Hx.
      unfold V_id, RcIdentModel.ID_SIZE in *. clear - Hx. lia. }
- (* the malloc returned NULL: the result is at or above 4096 *)
  exfalso.
  rewrite (branch_ne_U E (SOff 10 0) (SLit 0)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  rewrite (U_atom E 10 _ E10) in Hc by (clear - Hgb4096 Hgbce Hrq2 C1; lia). rewrite U_lit in Hc by lia.
  clear - Hc Hgb4096. lia.
Qed.

End c.
End b.
End a.
