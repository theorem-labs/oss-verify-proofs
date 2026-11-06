(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its addresses changed; 466 of its 542 lines of code are new or changed and 1067 lines of the source are left out. *)
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

Lemma d48_sh_apart {rc : YM05.RunCeil} : forall F, in_app F 1024 -> F + 1024 <= alloc_ceiling ->
  (shadow_addr F + 128 <= F \/ F + 1024 <= shadow_addr F) /\ 0 <= shadow_addr F /\
  shadow_addr F + 128 <= alloc_ceiling.
Proof.
intros F Happ Hc. pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF.
clear - Happ Hc C1. lia.
Qed.
Lemma d48_sh_off : forall F c, F mod 64 = 0 -> 0 <= c -> c mod 8 = 0 -> shadow_addr (F + c) = shadow_addr F + c / 8.
Proof. intros F c HF Hc Hc8. unfold shadow_addr. lia. Qed.
Ltac d48_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma d48_mb_of : forall (W : world SEGS) mem a bs, bytes_at8 W mem a bs -> mbytes_at SEGS (rd W mem) a bs.
Proof.
intros W mem a bs Hb j Hj. unfold bytes_at8 in Hb.
rewrite (garr8_mbyte SEGS _ _ _ j Hb) by (rewrite length_map; exact Hj).
assert (E2 : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
{ rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). apply map_nth. }
rewrite E2, Z_to_bv_bv_unsigned. symmetry. apply nth_error_nth'. exact Hj.
Qed.
Lemma d48_of_mb : forall (W : world SEGS) mem a bs, mbytes_at SEGS (rd W mem) a bs -> bytes_at8 W mem a bs.
Proof.
intros W mem a bs Hb j Hj. rewrite length_map in Hj.
assert (E2 : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned (nth j bs (Z_to_bv 8 0))).
{ rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). apply map_nth. }
rewrite E2. pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. split; [|lia].
intros k Hk. assert (Hk0 : k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (Hb j Hj). assert (E : nth_error bs j = Some (nth j bs (Z_to_bv 8 0))) by (apply nth_error_nth'; exact Hj).
rewrite E. f_equal. cbv delta [YO0f.le_byte YG0f.le_byte] beta.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small _ 256) by lia. rewrite Z.mod_small by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma d48_bytes_kept : forall (W W' : world SEGS) mem mem' a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  bytes_at8 W mem a bs -> bytes_at8 W' mem' a bs.
Proof.
intros W W' mem mem' a bs K Hb. unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hb).
intros x Hx. rewrite length_map in Hx. apply (mbyte_of_aview SEGS). apply K. exact Hx.
Qed.
Lemma d48_sh_kept : forall (W W' : world SEGS) mem mem' a n,
  (forall x, shadow_addr a <= x < shadow_addr a + (n + 7) / 8 ->
     aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
  sh_blk W mem a n -> sh_blk W' mem' a n.
Proof.
intros W W' mem mem' a n K Hs. unfold sh_blk in *.
apply (block_shadow_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W') mem') SHADOW_OFF a n); [|exact Hs].
intros j Hj. unfold shadow_of_addr. apply K. unfold shadow_addr. lia.
Qed.

Section c.
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
Hypothesis PSIG : ident_prog_sig_ok (PI := PI).
Hypothesis HING : treac_identity_ingest_spec B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
#[local] Notation CTX := (D1ctx B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation RUNS := (D1S B MT LLVMF_STK).
#[local] Notation NUMS := (d1_nums B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS HSTK LAWS).

Lemma d48_RCb_pres : forall g pos mf (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  RCb B g pos mf regs -> RCb B g pos mf regs'.
Proof.
intros g pos mf regs regs' HP (R2 & R9 & R8 & R3 & R4 & R19 & R24).
unfold RCb. repeat split; (rewrite d1_presv with (regs := regs); [assumption | exact HP | d48_cs]).
Qed.

Lemma d48_call : forall g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 (W3 : world SEGS) memT mdT kk hs
  (regsT : bvmap 5 word) vid p Lp ret,
  CTX g pos mf i ly2 S2 W2 regs2 mem2 md2 ->
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly3 S3 W3 memT mdT (4 * Z.of_nat i + kk) ->
  frames S3 = [(4, pos)] -> Permutation (ablocks B ly3 S3) (hs ++ ablocks B ly2 S2) ->
  0 <= kk <= 2 -> bsum hs <= LIVE_LLVMF ->
  In (p, Lp) (ablocks B ly3 S3) -> D1k g i <= Lp ->
  (vid = V_id \/ vid = V_again) ->
  bytes_at8 W3 memT (SFa g pos + vid) (m_id g i) -> sh_blk W3 memT (SFa g pos + vid) 38 ->
  bytes_at8 W3 memT p (SlotModel.rec_pl (e_pl g) i) ->
  spZ regsT = mf -> getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regsT 10 = w64 (SFa g pos + vid) -> getr regsT 11 = w64 (D1addr g i) ->
  getr regsT 12 = w64 p -> getr regsT 13 = w64 (D1k g i) ->
  SRr SEGS W3 (cfg_at SEGS A_reac_identity_ingest regsT memT mdT)
    (fun W4 c4 => W4 = W3 /\ exists regs4 mem4 md4, c4 = cfg_at SEGS (BASE + ret) regs4 mem4 md4 /\
       ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
         ly3 S3 W3 mem4 md4 (4 * Z.of_nat i + kk) /\
       aregs_preserved regsT regs4 /\
       getr regs4 10 = w64 (SlotModel.rec_r (e_pl g) i) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ((alloc_ceiling <= a /\ ~ (mf - ASTACK <= a < mf)) \/
           SFa g pos <= a < SFa g pos + 1024 \/
           shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 \/
           (exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m)) ->
          ~ (SFa g pos + vid <= a < SFa g pos + vid + 38) ->
          aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) memT a) /\
       bytes_at8 W3 mem4 (SFa g pos + vid) (m_id g (S i))).
Proof.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 memT mdT kk hs regsT vid p Lp ret
  HC HJ Hfr3 Hperm3 Hkk Hbs Hpin HLp Hvid Bid Sid Bp Usp Rra Hret Hret2 R10 R11 R12 R13.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & _ & Hi64 & _).
pose proof HC as (_ & _ & _ & _ & _ & HEC & _ & _ & _ & _ & HRL).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hnev0 & Hlive0 & _).
destruct HRL as (_ & _ & _ & _ & _ & Hbl & _ & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin3 : In (4, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin) as (_ & Hp4 & Hpc & _ & _ & _ & HLp0).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (Has : ASTACK = 16384) by reflexivity.
assert (His : INGEST_STK = 4128) by reflexivity.
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr. change (SlotModel.rec_k (e_pl g) i) with (D1k g i) in Hkr.
pose proof (D1Model.d1_addr_range (e_pl g) i) as Har. change (SlotModel.rec_addr (e_pl g) i) with (D1addr g i) in Har.
pose proof (req_size_pos Lp ltac:(lia)) as (Hrq1 & Hrq2).
assert (Hvr : 0 <= vid /\ vid + 38 <= 1024 /\ vid mod 8 = 0) by (destruct Hvid as [-> | ->]; unfold V_id, V_again; lia).
remember (SFa g pos + vid) as id eqn:Eid.
assert (Hid0 : id <> 0) by (clear - HSF0 Hvr Eid; lia).
assert (Hp0 : D1k g i <> 0 -> p <> 0) by (intros _; clear - Hp4; lia).
assert (HNR : reac_identity_ingest_c.ingest_refused id p (D1k g i) = false)
  by (exact (D1Model.d1_ingest_ok (e_pl g) i id p Hid0 Hp0)).
eapply SRr_mono.
{ apply (HING LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 W3 memT mdT
    (4 * Z.of_nat i + kk) regsT id (D1addr g i) p (D1k g i) (m_id g i) (SlotModel.rec_pl (e_pl g) i) HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; assumption.
  - unfold raZ. rewrite Rra. rewrite unsigned_lit_small by (clear - HBASE Hret; lia). clear - HBLO Hret; lia.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R13.
  - clear - HSF0 HSF1 C1 Hvr Eid. lia.
  - exact Har.
  - clear - Hp4 Hpc Hrq1 C1. lia.
  - clear - Hkr. lia.
  - rewrite Usp. clear - Hmf32. lia.
  - rewrite Usp. clear - HSTKm Has His. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - rewrite SlotModel.rec_pl_length. reflexivity.
  - intros _. split.
    + unfold ting_rec_ok.
      split; [clear - HSF64 Hvr Eid; lia|].
      split.
      { left. exists 4, pos. split; [exact Hin3|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa3.
        change (fs_frame_bytes 4) with 1024. clear - Ha Hvr Eid. lia. }
      split; [right; rewrite Usp; clear - Hvr HSF1 Hmf0 Has His Eid; lia|].
      split.
      { intros a Ha.
        assert (Hw : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B ly3 S3) ly3 [(4, pos)] a).
        { right. right. right. exists 4, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EFa3.
          change (fs_frame_bytes 4) with 1024. clear - Ha Hvr Eid. lia. }
        split; [exact Hw | exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw))]. }
      split; [apply (block_shadow_range _ _ id 38); [exact Sid | lia | lia]|].
      split; [exact (SlotModel.rec_id_length (e_pl g) i)|].
      exact (d48_mb_of W3 memT id (m_id g i) Bid).
    + unfold ting_pay_ok. split.
      * intros _. exists p, Lp. split; [exact Hpin | clear - HLp; lia].
      * exact (d48_mb_of W3 memT p _ Bp).
  - unfold EV_INGEST. unfold EV_LLVMF in HEV. clear - Hnev3 Hnev0 HEV Hi64 Hkk. lia.
  - unfold LIVE_INGEST.
    rewrite (blocks_bytes_bsum B ly3 S3), (bsum_perm _ _ Hperm3), bsum_app, (bsum_perm _ _ (proj1 Hbl)), app_nil_l,
      <- (blocks_bytes_bsum B (e_ly g) (e_S g)).
    unfold LIVE_LLVMF in HLIVE, Hbs. clear - Hlive0 HLIVE Hbs. lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HPR4 & R104 & HK4 & HREC4).
split; [reflexivity|]. exists regs4, mem4, md4.
split; [rewrite Rra; reflexivity|].
split; [unfold EV_INGEST in HJ4; rewrite Z.add_0_r in HJ4; exact HJ4|].
split; [exact HPR4|].
split; [rewrite R104; f_equal; exact (D1Model.d1_ingest_ret (e_pl g) i id p Hid0 Hp0)|].
split.
{ intros a Ha Hz Hn. destruct HK4 as (K1 & K2 & _ & K4 & _).
  destruct Hz as [(Hz & Hw) | [Hz | [Hz | (b & m & Hb & Hr)]]].
  - apply K1; [clear - Ha Hz; lia | rewrite Usp; clear - Hw Has His; lia | intros (_ & HE); exact (Hn HE)].
  - apply (K4 4 pos a Hin3); [|intros (_ & HE); exact (Hn HE)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa3. change (fs_frame_bytes 4) with 1024. exact Hz.
  - apply (K4 4 pos a Hin3); [|intros (_ & HE); exact (Hn HE)].
    right. unfold in_zr. cbn [fst snd]. rewrite EFa3. change (fs_frame_bytes 4 / 8) with 128. exact Hz.
  - replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hb); [clear - Hr; lia|].
    replace (b + (a - b)) with a by lia. intros (_ & HE). exact (Hn HE). }
change (m_id g (S i)) with (snd (RcIdentModel.ING (m_id g i) (D1addr g i) (SlotModel.rec_pl (e_pl g) i))).
exact (d48_of_mb W3 mem4 id _ (HREC4 HNR)).
Qed.

Theorem d1_ph4 : d1_ph4_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold d1_ph4_stmt.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl W3 c3 HC HD.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & _ & Hi64 & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRL).
destruct HRL as (_ & _ & _ & (Bid2 & _ & Sid2) & _).
destruct HD as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfr3 & Hperm3 & Hhs & MLE3 & KEEP3 & HP3).
destruct HP3 as (HRC & R25 & R22 & R27 & R26 & R18 & V144 & Bpl & SHb & Bb).
pose proof HRC as (Rsp & _).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin3 : In (4, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (Hpin : In (pl, D1k g i) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin) as (_ & Hp4 & Hpc & _).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr. change (SlotModel.rec_k (e_pl g) i) with (D1k g i) in Hkr.
pose proof (req_size_pos (D1k g i) ltac:(lia)) as (Hrq1 & Hrq2).
assert (Lid : forall j, Z.of_nat (length (m_id g j)) = 38).
{ intros j. unfold m_id. rewrite SlotModel.rec_id_length. reflexivity. }
assert (Lpl : Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) = D1k g i).
{ rewrite SlotModel.rec_pl_length, Z2Nat.id; [reflexivity | exact (proj1 Hkr)]. }
destruct (d48_sh_apart (SFa g pos) HSFapp HSF1) as (HSA & HS0 & HSc).
assert (Hsid : shadow_addr (SFa g pos + V_id) = shadow_addr (SFa g pos) + 44)
  by (rewrite d48_sh_off by (unfold V_id; lia); reflexivity).
assert (Hsbef : shadow_addr (SFa g pos + V_before) = shadow_addr (SFa g pos) + 4)
  by (rewrite d48_sh_off by (unfold V_before; lia); reflexivity).
assert (HidW : forall a, SFa g pos + V_id <= a < SFa g pos + V_id + 38 \/
                         shadow_addr (SFa g pos) + 44 <= a < shadow_addr (SFa g pos) + 49 -> ~ WR0 g pos mf a).
{ intros a Ha. unfold WR0, V_id, V_before, V_again, N_before, N_again in *.
  set (S0 := shadow_addr (SFa g pos)) in *. set (F := SFa g pos) in *.
  clear - Ha HSA HS0 HSc Hmf0 HSF0 HSF1 Has. lia. }
assert (Bid3 : bytes_at8 W3 mem3 (SFa g pos + V_id) (m_id g i)).
{ apply (d48_bytes_kept W2 W3 mem2 mem3 _ _); [|exact Bid2].
  intros a Ha. rewrite Lid in Ha.
  apply KEEP3; [clear - Ha HSF0 HSF1 C1; unfold V_id in *; lia | right; left; clear - Ha; unfold V_id in *; lia |].
  apply HidW. left. exact Ha. }
assert (Sid3 : sh_blk W3 mem3 (SFa g pos + V_id) 38).
{ apply (d48_sh_kept W2 W3 mem2 mem3 _ _); [|exact Sid2].
  intros a Ha. rewrite Hsid in Ha. change ((38 + 7) / 8) with 5 in Ha.
  apply KEEP3; [clear - Ha HS0 HSc C1; lia | right; right; clear - Ha; lia |].
  apply HidW. right. clear - Ha. lia. }
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HAG : env_agree 32 (Ereg regs3 []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x510 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x510)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split. }
clear HE.
unfold cfg_at. change (w64 (BASE + 0x510)) with (Z_to_bv 64 (BASE + 0x510)).
paj_run_shc RUNP RUNC HS HJ3.
{ apply awr_ok_nil. }
assert (TK : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ apply (aview_kept_frame (segs := SEGS) E _ (w_H W3) mem3 (ms_mem ms) 0 HFr ltac:(lia)).
  intros a _ (rr & Hr & _). cbn [ss_mem In] in Hr. exact Hr. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (13%bv : bv 5) Ra3. prreg HS (1%bv : bv 5) Rra.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra0. rewrite (EE 27%nat 27%bv eq_refl), R27 in Ra1.
rewrite (EE 25%nat 25%bv eq_refl), R25 in Ra2. rewrite (EE 22%nat 22%bv eq_refl), R22 in Ra3.
assert (HPRT : aregs_preserved regs3 (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok SEGS (w_H W3) E _ _ regs3 [] HS HAG); vm_compute; reflexivity).
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (d1_presv regs3 (ms_regs ms) 2%bv HPRT) by d48_cs. rewrite Rsp. unfold w64.
  apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1 Has. lia. }
pmkst HS.
rewrite (PSIG IS_reac_identity_ingest AF_reac_identity_ingest eq_refl).
assert (Bid4 : bytes_at8 W3 (ms_mem ms) (SFa g pos + V_id) (m_id g i)).
{ apply (d48_bytes_kept W3 W3 mem3 (ms_mem ms) _ _); [|exact Bid3].
  intros a Ha. apply TK. rewrite Lid in Ha. clear - Ha HSF0 HSF1 C1. unfold V_id in *. lia. }
assert (Sid4 : sh_blk W3 (ms_mem ms) (SFa g pos + V_id) 38).
{ apply (d48_sh_kept W3 W3 mem3 (ms_mem ms) _ _); [|exact Sid3].
  intros a Ha. apply TK. rewrite Hsid in Ha. change ((38 + 7) / 8) with 5 in Ha. clear - Ha HS0 HSc C1. lia. }
assert (Bpl4 : bytes_at8 W3 (ms_mem ms) pl (SlotModel.rec_pl (e_pl g) i)).
{ apply (d48_bytes_kept W3 W3 mem3 (ms_mem ms) _ _); [|exact Bpl].
  intros a Ha. apply TK. rewrite Lpl in Ha.
  clear - Ha Hp4 Hpc Hrq2 C1. lia. }
eapply SRr_mono.
{ apply (d48_call g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 (ms_mem ms) _ 1 [(pl, D1k g i)] (ms_regs ms)
    V_id pl (D1k g i) 0x524 HC HJ3 Hfr3 Hperm3 ltac:(lia)
    ltac:(unfold bsum, LIVE_LLVMF; cbn [fold_right snd]; clear - Hkr; lia) Hpin ltac:(lia) ltac:(left; reflexivity)
    Bid4 Sid4 Bpl4 Usp Rra ltac:(lia) ltac:(reflexivity) Ra0 Ra1 Ra2 Ra3). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HPR4 & R104 & K4T & Bid5).
assert (HPRT4 : aregs_preserved regs3 regs4) by exact (aregs_preserved_trans _ _ _ HPRT HPR4).
assert (K34 : forall a, 0 <= a < 2 ^ 64 ->
          ((alloc_ceiling <= a /\ ~ (mf - ASTACK <= a < mf)) \/
           SFa g pos <= a < SFa g pos + 1024 \/
           shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 \/
           (exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m)) ->
          ~ (SFa g pos + V_id <= a < SFa g pos + V_id + 38) ->
          aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hz Hn. rewrite (K4T a Ha Hz Hn). exact (TK a Ha). }
clear K4T TK.
unfold D1S. exists ly3, S3, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfr3|]. split; [exact Hperm3|]. split; [exact Hhs|].
split; [exact MLE3|].
split.
{ intros a Ha Hz Hn. rewrite (K34 a Ha).
  - apply KEEP3; [exact Ha | exact Hz | intros Hw; apply Hn; left; exact Hw].
  - destruct Hz as [Hz | [Hz | Hz]];
      [left; split; [exact Hz | intros Hs; apply Hn; left; left; exact Hs] | right; left; exact Hz | right; right; left; exact Hz].
  - intros Hi. apply Hn. right. unfold N_id. exact Hi. }
unfold P4.
split; [exact (d1_RC_pres B g pos mf i regs3 regs4 HPRT4 HRC)|].
split; [exact R104|].
split; [rewrite (d1_presv regs3 regs4 25%bv HPRT4) by d48_cs; exact R25|].
split; [rewrite (d1_presv regs3 regs4 22%bv HPRT4) by d48_cs; exact R22|].
split; [rewrite (d1_presv regs3 regs4 27%bv HPRT4) by d48_cs; exact R27|].
split; [rewrite (d1_presv regs3 regs4 26%bv HPRT4) by d48_cs; exact R26|].
split.
{ apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 mem4); [|exact V144].
  intros k Hk. apply K34; [clear - Hk Hmf0 Hmfb H47 C1 Has; lia | left; split; [clear - Hk Hmf0 Has C1; lia | clear - Hk; lia] |].
  clear - Hk Hmf0 HSF1 Has. unfold V_id. lia. }
split.
{ apply (d48_bytes_kept W3 W3 mem3 mem4 _ _); [|exact Bpl].
  intros a Ha. rewrite Lpl in Ha.
  assert (Hab : pl <= a < pl + req_size (D1k g i)) by (clear - Ha Hrq2; lia).
  apply K34; [clear - Hab Hp4 Hpc C1; lia | right; right; right; exists pl, (D1k g i); split; [exact Hpin | exact Hab] |].
  intros Hi. apply (d1_fz_not_block B LAWS g pos ly3 S3 W3 mem3 md3 pl (D1k g i) a HAR3 Hin3 EFa3 Hpin Hab).
  left. clear - Hi. unfold V_id in Hi. lia. }
split.
{ apply (d48_sh_kept W3 W3 mem3 mem4 _ _); [|exact SHb].
  intros a Ha. rewrite Hsbef in Ha. unfold N_before in Ha. change ((38 + 7) / 8) with 5 in Ha.
  apply K34; [clear - Ha HS0 HSc C1; lia | right; right; left; clear - Ha; lia |].
  clear - Ha HSA HS0 HSF0. unfold V_id. lia. }
split.
{ apply (d48_bytes_kept W3 W3 mem3 mem4 _ _); [|exact Bb].
  intros a Ha. rewrite Lid in Ha.
  apply K34; [clear - Ha HSF0 HSF1 C1; unfold V_before in *; lia | right; left; clear - Ha; unfold V_before in *; lia |].
  clear - Ha. unfold V_before, V_id in *. lia. }
exact Bid5.
Qed.

Theorem d1_ph8 : d1_ph8_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
unfold d1_ph8_stmt.
intros g pos mf i ly2 S2 W2 regs2 mem2 md2 pl gb W3 c3 HC HD.
pose proof (NUMS g pos mf i ly2 S2 W2 regs2 mem2 md2 HC) as (Hmf0 & Hmfb & Hmf32 & Hsp0al & H47 & HSTKm &
  (HSF0 & HSF1 & HSF64 & HSFapp & EFa) & _ & Hi64 & _).
destruct HD as (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hfr3 & Hperm3 & Hhs & MLE3 & KEEP3 & HP3).
destruct HP3 as (HRC & R20 & R18 & R23 & R25 & R22 & R27 & V136 & V144 & V152 & V160 & Bpl & Bgb & SHb & Bb &
  SHa & Ba & Bid).
pose proof HRC as (Rsp & _).
pose proof HJ3 as (HAR3 & Hly3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF3; reflexivity).
assert (Hin3 : In (4, pos) (frames S3)) by (rewrite Hfr3; left; reflexivity).
assert (Hpin : In (pl, D1k g i) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); right; left; reflexivity).
assert (Hgin : In (gb, D1k g i + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm3)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin) as (_ & Hp4 & Hpc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hgin) as (_ & Hg4 & Hgc & _).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
pose proof (SlotModel.rec_k_range (e_pl g) i) as Hkr. change (SlotModel.rec_k (e_pl g) i) with (D1k g i) in Hkr.
pose proof (req_size_pos (D1k g i) ltac:(lia)) as (Hrq1 & Hrq2).
pose proof (req_size_pos (D1k g i + 1) ltac:(lia)) as (Hrg1 & Hrg2).
assert (Lid : forall j, Z.of_nat (length (m_id g j)) = 38).
{ intros j. unfold m_id. rewrite SlotModel.rec_id_length. reflexivity. }
assert (Lpl : Z.of_nat (length (SlotModel.rec_pl (e_pl g) i)) = D1k g i).
{ rewrite SlotModel.rec_pl_length, Z2Nat.id; [reflexivity | exact (proj1 Hkr)]. }
destruct (d48_sh_apart (SFa g pos) HSFapp HSF1) as (HSA & HS0 & HSc).
assert (Hsag : shadow_addr (SFa g pos + V_again) = shadow_addr (SFa g pos) + 14)
  by (rewrite d48_sh_off by (unfold V_again; lia); reflexivity).
assert (Hsbef : shadow_addr (SFa g pos + V_before) = shadow_addr (SFa g pos) + 4)
  by (rewrite d48_sh_off by (unfold V_before; lia); reflexivity).
remember (Eimg (Ereg regs3 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs3 r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (HAG : env_agree 32 (Ereg regs3 []) E)
  by (subst E; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x5ac sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x5ac)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split. }
clear HE.
unfold cfg_at. change (w64 (BASE + 0x5ac)) with (Z_to_bv 64 (BASE + 0x5ac)).
paj_run_shc RUNP RUNC HS HJ3.
{ apply awr_ok_nil. }
assert (TK : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) mem3 a).
{ apply (aview_kept_frame (segs := SEGS) E _ (w_H W3) mem3 (ms_mem ms) 0 HFr ltac:(lia)).
  intros a _ (rr & Hr & _). cbn [ss_mem In] in Hr. exact Hr. }
clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (13%bv : bv 5) Ra3. prreg HS (1%bv : bv 5) Rra.
rewrite (EE 20%nat 20%bv eq_refl), R20 in Ra0. rewrite (EE 27%nat 27%bv eq_refl), R27 in Ra1.
rewrite (EE 18%nat 18%bv eq_refl), R18 in Ra2. rewrite (EE 22%nat 22%bv eq_refl), R22 in Ra3.
assert (HPRT : aregs_preserved regs3 (ms_regs ms))
  by (apply (aregs_preserved_of_st_ok SEGS (w_H W3) E _ _ regs3 [] HS HAG); vm_compute; reflexivity).
assert (Usp : spZ (ms_regs ms) = mf).
{ unfold spZ. rewrite (d1_presv regs3 (ms_regs ms) 2%bv HPRT) by d48_cs. rewrite Rsp. unfold w64.
  apply unsigned_lit_small. clear - Hmf0 Hmfb H47 C1 Has. lia. }
pmkst HS.
rewrite (PSIG IS_reac_identity_ingest AF_reac_identity_ingest eq_refl).
assert (Ba4 : bytes_at8 W3 (ms_mem ms) (SFa g pos + V_again) (m_id g i)).
{ apply (d48_bytes_kept W3 W3 mem3 (ms_mem ms) _ _); [|exact Ba].
  intros a Ha. apply TK. rewrite Lid in Ha. clear - Ha HSF0 HSF1 C1. unfold V_again in *. lia. }
assert (Sa4 : sh_blk W3 (ms_mem ms) (SFa g pos + V_again) 38).
{ apply (d48_sh_kept W3 W3 mem3 (ms_mem ms) _ _); [|exact SHa].
  intros a Ha. apply TK. rewrite Hsag in Ha. unfold N_again in Ha. change ((38 + 7) / 8) with 5 in Ha.
  clear - Ha HS0 HSc C1. lia. }
assert (Bgb4 : bytes_at8 W3 (ms_mem ms) gb (SlotModel.rec_pl (e_pl g) i)).
{ apply (d48_bytes_kept W3 W3 mem3 (ms_mem ms) _ _); [|exact Bgb].
  intros a Ha. apply TK. rewrite Lpl in Ha.
  clear - Ha Hg4 Hgc Hrg2 C1. lia. }
unfold N_again in SHa.
eapply SRr_mono.
{ apply (d48_call g pos mf i ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 (ms_mem ms) _ 2 [(gb, D1k g i + 1); (pl, D1k g i)]
    (ms_regs ms) V_again gb (D1k g i + 1) 0x5c0 HC HJ3 Hfr3 Hperm3 ltac:(lia)
    ltac:(unfold bsum, LIVE_LLVMF; cbn [fold_right snd]; clear - Hkr; lia) Hgin ltac:(lia) ltac:(right; reflexivity)
    Ba4 Sa4 Bgb4 Usp Rra ltac:(lia) ltac:(reflexivity) Ra0 Ra1 Ra2 Ra3). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HPR4 & R104 & K4T & Ba5).
assert (HPRT4 : aregs_preserved regs3 regs4) by exact (aregs_preserved_trans _ _ _ HPRT HPR4).
assert (K34 : forall a, 0 <= a < 2 ^ 64 ->
          ((alloc_ceiling <= a /\ ~ (mf - ASTACK <= a < mf)) \/
           SFa g pos <= a < SFa g pos + 1024 \/
           shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128 \/
           (exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m)) ->
          ~ (SFa g pos + V_again <= a < SFa g pos + V_again + 38) ->
          aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hz Hn. rewrite (K4T a Ha Hz Hn). exact (TK a Ha). }
clear K4T TK.
assert (Kst : forall a w, mf + 136 <= a -> a + Z.of_nat w <= mf + 168 -> forall v,
          val_mem SEGS (rd W3 mem3) a w v -> val_mem SEGS (rd W3 mem4) a w v).
{ intros a w Ha1 Ha2 v Hv. apply (val_mem_kept SEGS (w_H W3) (w_H W3) mem3 mem4); [|exact Hv].
  intros k Hk. apply K34; [clear - Hk Ha1 Ha2 Hmf0 Hmfb H47 C1 Has; lia
    | left; split; [clear - Hk Ha1 Hmf0 Has C1; lia | clear - Hk Ha1; lia] |].
  clear - Hk Ha1 Hmf0 HSF1 Has. unfold V_again. lia. }
assert (Kblk : forall b m bs, In (b, m) (ablocks B ly3 S3) -> Z.of_nat (length bs) <= req_size m ->
          bytes_at8 W3 mem3 b bs -> bytes_at8 W3 mem4 b bs).
{ intros b m bs Hb Hl Hbs. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & Hb4 & Hbc & _).
  apply (d48_bytes_kept W3 W3 mem3 mem4 _ _); [|exact Hbs].
  intros a Ha. assert (Hab : b <= a < b + req_size m) by (clear - Ha Hl; lia).
  apply K34; [clear - Hab Hb4 Hbc C1; lia | right; right; right; exists b, m; split; [exact Hb | exact Hab] |].
  intros Hi. apply (d1_fz_not_block B LAWS g pos ly3 S3 W3 mem3 md3 b m a HAR3 Hin3 EFa3 Hb Hab).
  left. clear - Hi. unfold V_again in Hi. lia. }
assert (Kfr : forall a bs, SFa g pos <= a -> a + Z.of_nat (length bs) <= SFa g pos + 1024 ->
          (a + Z.of_nat (length bs) <= SFa g pos + V_again \/ SFa g pos + V_again + 38 <= a) ->
          bytes_at8 W3 mem3 a bs -> bytes_at8 W3 mem4 a bs).
{ intros a bs H1 H2 H3 Hbs. apply (d48_bytes_kept W3 W3 mem3 mem4 _ _); [|exact Hbs].
  intros x Hx. apply K34; [clear - Hx H1 H2 HSF0 HSF1 C1; lia | right; left; clear - Hx H1 H2; lia |].
  clear - Hx H3. lia. }
assert (Ksh : forall a, a mod 8 = 0 -> SFa g pos <= a -> a + 38 <= SFa g pos + 1024 ->
          sh_blk W3 mem3 a 38 -> sh_blk W3 mem4 a 38).
{ intros a Ha8 H1 H2 Hs. apply (d48_sh_kept W3 W3 mem3 mem4 _ _); [|exact Hs].
  intros x Hx. change ((38 + 7) / 8) with 5 in Hx.
  assert (Hsx : shadow_addr (SFa g pos) <= shadow_addr a /\ shadow_addr a + 5 <= shadow_addr (SFa g pos) + 128)
    by (clear - H1 H2 Ha8 HSF64; unfold shadow_addr; lia).
  apply K34; [clear - Hx Hsx HS0 HSc C1; lia | right; right; left; clear - Hx Hsx; lia |].
  clear - Hx Hsx HSA HSF0. unfold V_again. lia. }
unfold D1S. exists ly3, S3, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfr3|]. split; [exact Hperm3|]. split; [exact Hhs|].
split; [exact MLE3|].
split.
{ intros a Ha Hz Hn. rewrite (K34 a Ha).
  - apply KEEP3; [exact Ha | exact Hz | exact Hn].
  - destruct Hz as [Hz | [Hz | Hz]];
      [left; split; [exact Hz | intros Hs; apply Hn; left; left; exact Hs] | right; left; exact Hz | right; right; left; exact Hz].
  - intros Hi. apply Hn. left. right. right. right. left. unfold N_again. exact Hi. }
unfold P8.
split; [exact (d48_RCb_pres g pos mf regs3 regs4 HPRT4 HRC)|].
split; [rewrite (d1_presv regs3 regs4 20%bv HPRT4) by d48_cs; exact R20|].
split; [rewrite (d1_presv regs3 regs4 18%bv HPRT4) by d48_cs; exact R18|].
split; [exact R104|].
split; [rewrite (d1_presv regs3 regs4 23%bv HPRT4) by d48_cs; exact R23|].
split; [rewrite (d1_presv regs3 regs4 25%bv HPRT4) by d48_cs; exact R25|].
split; [rewrite (d1_presv regs3 regs4 22%bv HPRT4) by d48_cs; exact R22|].
split; [rewrite (d1_presv regs3 regs4 27%bv HPRT4) by d48_cs; exact R27|].
split; [exact (Kst (mf + 136) 8%nat ltac:(lia) ltac:(lia) _ V136)|].
split; [exact (Kst (mf + 144) 8%nat ltac:(lia) ltac:(lia) _ V144)|].
split; [exact (Kst (mf + 152) 8%nat ltac:(lia) ltac:(lia) _ V152)|].
split; [exact (Kst (mf + 160) 8%nat ltac:(lia) ltac:(lia) _ V160)|].
split; [exact (Kblk pl (D1k g i) (SlotModel.rec_pl (e_pl g) i) Hpin ltac:(rewrite Lpl; clear - Hrq2; lia) Bpl)|].
split; [exact (Kblk gb (D1k g i + 1) (SlotModel.rec_pl (e_pl g) i) Hgin ltac:(rewrite Lpl; clear - Hrg2; lia) Bgb)|].
split; [exact (Ksh (SFa g pos + V_before) ltac:(clear - HSF64; unfold V_before; lia) ltac:(unfold V_before; lia)
           ltac:(unfold V_before; lia) SHb)|].
split; [exact (Kfr (SFa g pos + V_before) (m_id g i) ltac:(unfold V_before; lia) ltac:(rewrite Lid; unfold V_before; lia)
           ltac:(rewrite Lid; unfold V_before, V_again; lia) Bb)|].
split; [unfold N_again; exact (Ksh (SFa g pos + V_again) ltac:(clear - HSF64; unfold V_again; lia)
           ltac:(unfold V_again; lia) ltac:(unfold V_again; lia) SHa)|].
split; [exact Ba5|].
exact (Kfr (SFa g pos + V_id) (m_id g (S i)) ltac:(unfold V_id; lia) ltac:(rewrite Lid; unfold V_id; lia)
         ltac:(rewrite Lid; unfold V_id, V_again; lia) Bid).
Qed.

End c.
End b.
End a.
