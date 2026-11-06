(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 269 of its 319 lines of code are new or changed and 464 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins, asan-ubsan d663f82d): segment H3_B of the walk of check_reject_clean_starved
   (row CRB-H3, a Theorem Labs lane's subagent CrsX3H3). Closing lemma crs_seg_H3_B : the B' kit's crs_from_H3_B (B' +1052 =
   0x824fc .. +1072 = 0x82510 = X3_B), from fuzz_alloc_count's and fuzz_pick's texts at prh_img_B (HT_fuzz_alloc_count,
   HT_fuzz_pick: the kit's tfuzz_pick_specX, lib/A/PRH_FnCheck.v), the kit's transport record (HK : CrsKeep_B) and the
   continuation crs_from_X3_B. THE SEGMENT (the B' listing lib/B/Listing_prog.v slots 908 .. 912):
     +1052 jal fuzz_alloc_count (a0 = the count, crs_cnt2_B + N0); +1056 sub a2, a0, s7 (= N0); +1060 mv a0, s5
     (data); +1064 mv a1, s4 (size); +1068 jal fuzz_pick (its return site +1072 = X3_B, a0 = ck_pick tb N0 = cPick0_B).
   On B' the compact pick is this CALL (A' inlines it as its third djb2 loop L3), so H3_B has no loop: both calls go
   through CrsSeg_X3_B.x3_acc_call, the three instructions between them through the listing runner. fuzz_pick's input
   window at the state of its call (src_rd) is the kit's crs_src_rd_at_B over crs_dat_B there: the bytes kept by the
   count's ledger (x3_st), the reader's home moved by kpb_home_move, its shadow by kpb_home_sh (the home is below
   alloc_ceiling: h3_home_ceil).
   DONOR (rule 24, reuse): lane CrsX3H3's own A' file lib/A/Prog/CrsSeg_H3.v blob b0a8064c165c
   (a working branch 0a0dced97c5): the count call, the home / shadow transport and h3_home_ceil, at the kit's
   _B names; every B' number recomputed on the B' listing / PAImg (STK_fuzz_pick = 16, x3_stk / h3_stk).
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index check_reject_clean_starved 0x82160`, the internal file
   index-crcs-Aprime.out, and an internal record of that lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for check_reject_clean_starved).
   INPUTS: pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
   listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702; image record
   lib/B/PRH_ImgB.v (prh_img_B); the kit texts of record walkkit-next f97c8b2f046b by path (PRH_FnAlloc.v
   tfuzz_alloc_count_specX, PRH_FnCheck.v tfuzz_pick_specX); kit lib/B/Prog/CrsKitBp.v at a working branch
   fb124cd27931. Numerals: offsets +1052 .. +1072 (LENGTH: 4 * slot). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterApp WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Supply CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp CrsWexBp CrsSeg_X3_B.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PRW_WalkEnvB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the import closure leaves lia's division / modulo conversion off; this file's arithmetic needs it *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma h3_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* `sub a2, a0, s7` with a0 = s7 + N0 (the runner's form of sub: a0 + s7 * -1) *)
Lemma h3_sub : forall E a n, U E (SOff 42 0) = a + n -> U E (SOff 55 0) = a -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 42 0) (SMd M_MUL (SOff 55 0) (SLit (-1)))) = w64 n.
Proof.
intros E a n H42 H55 Ha Hn Han.
change (w64 n) with (sv_denot E (SLit n)). apply U_inj.
rewrite U_SAlu, U_SMd, !U_SLit, H42, H55. unfold zcanon, zmd_raw, zalu_raw, M64.
assert (E1 : (a * ((-1) mod 2 ^ 64)) mod 2 ^ 64 = (2 ^ 64 - a) mod 2 ^ 64).
{ replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  replace (a * (2 ^ 64 - 1)) with ((2 ^ 64 - a) + (a - 1) * 2 ^ 64) by ring. rewrite Z.mod_add by lia. reflexivity. }
rewrite E1.
assert (E2 : (a + n + (2 ^ 64 - a) mod 2 ^ 64) mod 2 ^ 64 = n).
{ rewrite Z.add_mod_idemp_r by lia. replace (a + n + (2 ^ 64 - a)) with (n + 1 * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite E2. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma h3_sub_ew : forall E a n, U E (SOff 42 0) = a + n -> U E (SOff 55 0) = a -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  alu64 ALU_ADD (ew E 42) (mul_div M_MUL (ew E 55) (Z_to_bv 64 (-1))) = w64 n.
Proof.
intros E a n H42 H55 Ha Hn Han. rewrite <- (h3_soff0 E 42), <- (h3_soff0 E 55).
exact (h3_sub E a n H42 H55 Ha Hn Han).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
(* S1ImgB loads lib/A's image (S1ImgA): the B' listing and image instances are preferred here *)
#[local] Existing Instance PI_prog_B | 0.
#[local] Existing Instance PL_prog_B | 0.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

Lemma h3_stk : STK_fuzz_pick (PI := prh_img_B) = 16.
Proof. vm_compute. reflexivity. Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_B)).

(* the input window's three state-free facts of crs_pre_B *)
Lemma h3_pre_facts : forall CTX0 C, crs_pre_B (fx := fx) B ARx CTX0 C ->
  cSize_B C <= 3 * 2 ^ 20 /\ 0 < cb_data C /\ cb_data C + cSize_B C < 2 ^ 62.
Proof.
intros CTX0 C H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
exact (conj H1 (conj H2 H3)).
Qed.

(* the reader's home is below alloc_ceiling: a ledger block, a read-only image range, or an allocator block *)
Lemma h3_home_ceil : forall ly S Hp W mem md Lam peak cnt fail ran most own p n,
  ARx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_FnReader.prhReader_home (PA := PA) B ly S Hp Lam p n -> 0 <= n -> p + n <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own p n HAR HL Hh Hn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof cf_head_nonneg as Ch.
destruct Hh as [[(b & m & Hin & Hb & Hm) | [(_ & _ & Htop & _) | (_ & Htop & _)]] | (b & m & Hin & _ & Hb & Hm)].
- pose proof (prh_ledger_blocks B ly S Hp W mem Lam peak cnt fail ran most own HL) as HF. rewrite Forall_forall in HF.
  destruct (HF (b, m) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & _ & Hc & _).
  unfold req_size in Hc. destruct (Z.eqb_spec (m + cf_head) 0); lia.
- lazymatch type of Htop with _ <= ?h => assert (h < 2 ^ 40) by (vm_compute; reflexivity) end. lia.
- lazymatch type of Htop with _ <= ?h => assert (h < 2 ^ 40) by (vm_compute; reflexivity) end. lia.
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hc & _).
  unfold req_size in Hc. destruct (Z.eqb_spec m 0); lia.
Qed.

(* ---- the registers: at H3_B (the kit's list) ---- *)
Definition h3_regs (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B ++ [(23%bv, crs_cnt2_B C)].

Local Ltac h3_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  lia.
Local Ltac h3_te_close :=
  lazymatch goal with |- ew (TE ?r0 ?rc ?mo) ?n = _ =>
    let nn := eval vm_compute in n in
    lazymatch eval vm_compute in (Nat.ltb nn 32) with
    | true => apply (te_entry r0 rc mo _ nn); reflexivity
    | false => lazymatch eval vm_compute in (Nat.ltb nn 64) with
      | true => let kk := eval vm_compute in (Nat.sub nn 32) in apply (te_cur r0 rc mo _ kk); reflexivity
      | false => let j := eval vm_compute in (Nat.sub nn 64) in rewrite (te_more_lt r0 rc mo j) by lia; reflexivity
      end
    end
  end.
Local Ltac h3_keepr HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; h3_te_close end.
Local Ltac h3_in := cbv [h3_regs x3_regs crs_rbase_B crs_rsh_B crs_rargs_B crs_rlive_B crs_rro_B app In]; tauto.

(* the registers of h3_regs are callee-saved: a call keeps them *)
Lemma h3_regs_pres : forall (regs regs2 : bvmap 5 word) C sp2,
  crs_regsat_B regs (h3_regs C sp2) -> aregs_preserved regs regs2 -> crs_regsat_B regs2 (h3_regs C sp2).
Proof.
intros regs regs2 C sp2 H HP. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros p Hp.
rewrite <- (H p Hp). cbv [h3_regs crs_rbase_B crs_rsh_B crs_rargs_B crs_rlive_B crs_rro_B app In] in Hp.
repeat (destruct Hp as [<- | Hp]; [cbn [fst]; apply (x3_ap regs regs2 _ HP); h3_cs |]). destruct Hp.
Qed.

(* ==== CRB-H3: the closing lemma ==== *)
Lemma crs_seg_H3_B : forall CTX0 C
  (HT_fuzz_alloc_count : forall fxq, tfuzz_alloc_count_specX (fx := fxq) (rc := rc) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK)
  (HT_fuzz_pick : forall fxq, tfuzz_pick_specX (fx := fxq) (rc := rc) (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK)
  (HK : CrsKeep_B B ARx),
  crs_from_X3_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  crs_from_H3_B (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HTC HTP HK HX3. unfold crs_from_H3_B.
intros fxk ly S Hp W regs mem md k sp2 Lam peak Hdoc HB HRG (HCO & HPM) HDAT HT.
(* THE WORLD RELATION: every boundary of H3 is after a free (pj_parse's, then the writers'), so the kit's crs_from_H3_B
   / crs_from_X3_B take crs_baseR_B at R := wle' SEGS RZ_cf and conclude SRr' (SRrG at R); both calls of H3
   (fuzz_alloc_count, fuzz_pick) run at R by CrsSeg_X3_B.x3_acc_call, and the run between them by paj_run_xR *)
unfold SRr' in HX3 |- *.
set (R := wle' SEGS YGcfRehidePost.RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS YGcfRehidePost.RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS YGcfRehidePost.RZ_cf).
assert (Rw : forall W W', wle W W' -> R W W') by exact (wle_wle' SEGS YGcfRehidePost.RZ_cf).
destruct HCO as (HL & Hpk & Hran0 & Hcn & Hc62 & HRL & HPOS).
pose proof HB as (Hpre & HFZ & HFK & HJ & HFR & HSV & HSL & HROD & HMN & HR3 & HR4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof x3_stk as (ESTK & EF0 & EL0 & ER0 & EC0 & EW0).
pose proof h3_stk as EP0.
pose proof crs_frame_is_pi_B as EFR. unfold CRS_FRAME_B in EFR, Hs1.
pose proof (h3_pre_facts CTX0 C Hpre) as (Hsz & Hd0 & Hd62).
pose proof (x3_pre_more (fx := fx) B ARx CTX0 C Hpre) as (HCL & HL0 & Hc0 & Hr0 & Htk0 & Hdocs & Hlive & Hrq & Hfr0).
destruct Hdocs as [Hdz | (Hread & Htree0 & Hw0 & Hw1 & Hdep)]; [exact (False_ind _ (Hdoc Hdz))|].
pose proof (crs_wN_pos (cb_t C) false) as N0p.
pose proof (crs_wN_le (cb_t C) false ltac:(lia)) as N0l.
assert (EN0 : cN0_B C = Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (cb_t C) false)))))
  by reflexivity.
pose proof HDAT as (HBY & HHOME & HRA0 & HHULL).
assert (HST : x3_st B C (crs_evs_at_H3_B C) ly S Hp W mem Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0).
{ split; [exact HL|]. split; [exact Hpk|]. split; [reflexivity|]. split; [exact Hcn|]. split; [exact HRL|].
  split; [exact HPOS|]. split; [exact HPM | split; [exact HBY | exact HT]]. }
assert (E2 : getr regs 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG); h3_in).
assert (E8 : getr regs 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG); h3_in).
unfold crs_cfg_B, CRS_PC_H3_B.
assert (HS : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs []) (ss_x3 1052)
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CRS_PC0_B + 1052))) mem (YK11.seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (cb_regs C) regs [])) by apply te_env.
unfold crs_JR_B in HJ.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
(* +1052 jal fuzz_alloc_count *)
paj_run_tok_x RUN HS HJ SHOK (0, 0).
{ cbv [ss_x3 ss_mem]. apply awr_ok_nil. }
rename HF into HFm. apply frame_of_read_only in HFm; [|vm_compute; reflexivity]. clear HFr HG.
rewrite HFm in HJ.
assert (KR : forall p, In p (h3_regs C sp2) -> getr (ms_regs ms) (fst p) = getr regs (fst p)).
{ intros p Hpp. cbv [h3_regs crs_rbase_B crs_rsh_B crs_rargs_B crs_rlive_B crs_rro_B app In] in Hpp.
  repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; h3_keepr HS |]). destruct Hpp. }
assert (KR3 : getr (ms_regs ms) 3 = getr regs 3) by h3_keepr HS.
assert (KR4 : getr (ms_regs ms) 4 = getr regs 4) by h3_keepr HS.
prreg HS (1%bv : bv 5) Z1.
assert (A1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1056))).
{ rewrite Z1. f_equal; try (vm_compute; reflexivity). }
assert (HRGm : crs_regsat_B (ms_regs ms) (h3_regs C sp2)) by exact (x3_regsat_sub regs (ms_regs ms) _ _ HRG (fun p Hp => Hp) KR).
assert (HBm : crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md) mat md) k sp2).
{ rewrite HFm. exact (x3_base_md (fx := fx) B ARx R CTX0 C fxk ly S Hp W regs mem md k sp2 (ms_regs ms) _ HB HJ KR3 KR4). }
assert (HSTm : x3_st B C (crs_evs_at_H3_B C) ly S Hp W (ms_mem ms) Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0)
  by (rewrite HFm; exact HST).
apply (x3_acc_call (fx := fx) B ARx LAWS HK R Rr Rt Rw CTX0 C (crs_evs_at_H3_B C) fxk (STK_fuzz_alloc_count (PI := prh_img_B)) 1056
  W _ _ ms _ ly S Hp k sp2 Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 SIZE_MAXZ
  (fun ly' S' Hp' W' regs' mem' md' =>
     (room_live_cf S -> room_live_cf S') /\
     getr regs' 10 = w64 (crs_cnt2_B C + cN0_B C) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
     LEDGER ly' S' Hp' W' mem' Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0)
  _ HS eq_refl HBm).
- rewrite (KR (2%bv, sp2)) by h3_in. exact E2.
- rewrite (KR (8%bv, spZ (cb_regs C))) by h3_in. exact E8.
- exact A1.
- lia.
- reflexivity.
- rewrite EC0. lia.
- rewrite EC0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
- exact HSTm.
- intros ch1 HFPRE.
  exact (HTC fxk ly S Hp W (ms_regs ms) (ms_mem ms) _ ch1 Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0 HFPRE
    ltac:(rewrite HFm; exact HL)).
- intros ly2 S2 Hp2 W2 regs2 mem2 md2 (_ & _ & EHp & ES & EAB & HL2). exact (conj EHp (conj ES (conj EAB HL2))).
- (* after the count (+1056): a0 = the count *)
  intros ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB2 HP (_ & R10 & _ & _ & EAB & _) HST2.
  pose proof HB2 as (_ & HFZ2 & HFK2 & HJ2 & _). unfold crs_JR_B in HJ2.
  pose proof HST2 as (HL2 & Hpk2 & _ & Hcn2 & HRL2 & HPOS2 & HPM2 & HBY2 & HT2).
  assert (Hn0 : 0 <= cSize_B C) by (unfold cSize_B; lia).
  assert (HHOME2 : PRH_FnReader.prhReader_home (PA := PA) B ly2 S2 Hp2 Lam (cb_data C) (cSize_B C)).
  { refine (kpb_home_move B ARx HK ly S Hp W mem Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0
      ly2 S2 Hp2 W2 mem2 Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0 (cb_data C) (cSize_B C) HL HL2
      (Permutation_refl _) _ HHOME).
    rewrite EAB. apply Permutation_refl. }
  assert (HDAT2 : crs_dat_B B C ly2 S2 Hp2 W2 mem2 Lam).
  { split; [exact HBY2|]. split; [exact HHOME2|].
    destruct (Z.eq_dec (cSize_B C) 0) as [E0 | Ene].
    - split; [rewrite E0; intros ii Hii; lia | intros Hlt; lia].
    - assert (Hceil : cb_data C + cSize_B C <= YM05.alloc_ceiling)
        by exact (h3_home_ceil ly S Hp W mem _ Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0 (cb_data C)
                    (cSize_B C) (ajxR_ar HJ) HL HHOME Hn0).
      destruct (kpb_home_sh B ARx HK ly2 S2 Hp2 W2 mem2 md2 Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0
        (cb_data C) (cSize_B C) (ajxR_ar HJ2) HL2 HHOME2 ltac:(lia) ltac:(lia) Hceil) as (HRA2 & HHV2).
      split; [exact HRA2 | intros _; exact HHV2]. }
  assert (HSRC : src_rd (PA := PA) W2 mem2 (cb_data C) (cb_tb C))
    by exact (crs_src_rd_at_B (fx := fx) B ARx CTX0 C _ _ _ _ _ _ Hpre HDAT2).
  assert (HRG2 : crs_regsat_B regs2 (h3_regs C sp2)) by exact (h3_regs_pres _ _ C sp2 HRGm HP).
  assert (G20 : getr regs2 20 = w64 (cSize_B C)) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  assert (G21 : getr regs2 21 = w64 (cb_data C)) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  assert (G23 : getr regs2 23 = w64 (crs_cnt2_B C)) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  assert (G2 : getr regs2 2 = w64 sp2) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  assert (G8 : getr regs2 8 = w64 (spZ (cb_regs C))) by (apply (x3_rget _ _ _ _ HRG2); h3_in).
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL2) as (_ & _ & Hcb2 & _).
  assert (Hcn2b : cb_cnt C <= crs_cnt2_B C).
  { unfold crs_cnt2_B, crs_cnt1_B, crs_first_B. pose proof (crs_wN_pos (cb_t C) true).
    assert (cN1_B C >= 1) by (unfold cN1_B, PjWriteHyp.wcalls; lia).
    pose proof (crs_pick_lt (cb_tb C) (cN1_B C) ltac:(lia)).
    destruct (Z.eqb_spec (cb_took C) 0); [lia|]. pose proof (crs_pick_lt (cb_tb C) (cb_took C) ltac:(lia)). lia. }
  pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as (_ & _ & Hc0b & _).
  (* +1056 .. +1068: sub a2, a0, s7; mv a0, s5; mv a1, s4; jal fuzz_pick *)
  assert (HS2 : @st_ok_pi SEGS VAL fxk (TE (cb_regs C) regs2 []) (ss_x3 1056)
    (restrict (w_H W2) (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CRS_PC0_B + 1056))) mem2 (YK11.seg_rom SEGS)))).
  { apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
  assert (SHOK2 : sh_ok SEGS (SLit 0) [] (TE (cb_regs C) regs2 []) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
  assert (HEI2 : img_env VAL A_LIM (TE (cb_regs C) regs2 [])) by apply te_env.
  assert (U42 : U (TE (cb_regs C) regs2 []) (SOff 42 0) = crs_cnt2_B C + cN0_B C).
  { apply U_atom; [rewrite (te_cur (cb_regs C) regs2 [] 10%bv 10) by reflexivity; exact R10 | lia]. }
  assert (U55 : U (TE (cb_regs C) regs2 []) (SOff 55 0) = crs_cnt2_B C).
  { apply U_atom; [rewrite (te_cur (cb_regs C) regs2 [] 23%bv 23) by reflexivity; exact G23 | lia]. }
  clear HS SHOK HEI KR KR3 KR4 Z1 A1 HBm HSTm.
  pose (RUN2 := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
  paj_run_tok_x RUN2 HS2 HJ2 SHOK2 (0, 0).
  { cbv [ss_x3 ss_mem]. apply awr_ok_nil. }
  rename HF into HFm2. apply frame_of_read_only in HFm2; [|vm_compute; reflexivity]. clear HFr HG.
  rewrite HFm2 in HJ2.
  assert (KR : forall p, In p (h3_regs C sp2) -> getr (ms_regs ms0) (fst p) = getr regs2 (fst p)).
  { intros p Hpp. cbv [h3_regs crs_rbase_B crs_rsh_B crs_rargs_B crs_rlive_B crs_rro_B app In] in Hpp.
    repeat (destruct Hpp as [<- | Hpp]; [cbn [fst]; h3_keepr HS2 |]). destruct Hpp. }
  assert (KR3 : getr (ms_regs ms0) 3 = getr regs2 3) by h3_keepr HS2.
  assert (KR4 : getr (ms_regs ms0) 4 = getr regs2 4) by h3_keepr HS2.
  prreg HS2 (1%bv : bv 5) Z1. prreg HS2 (10%bv : bv 5) Z10. prreg HS2 (11%bv : bv 5) Z11. prreg HS2 (12%bv : bv 5) Z12.
  assert (A1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + (CRS_PC0_B + 1072))).
  { rewrite Z1. f_equal; try (vm_compute; reflexivity). }
  assert (A10 : getr (ms_regs ms0) 10 = w64 (cb_data C)) by (rewrite Z10, <- G21; h3_te_close).
  assert (A11 : getr (ms_regs ms0) 11 = w64 (Z.of_nat (length (cb_tb C)))).
  { rewrite Z11. change (Z.of_nat (length (cb_tb C))) with (cSize_B C). rewrite <- G20. h3_te_close. }
  assert (A12 : getr (ms_regs ms0) 12 = w64 (cN0_B C)).
  { rewrite Z12. apply (h3_sub_ew _ (crs_cnt2_B C) (cN0_B C) U42 U55); lia. }
  assert (HRGm2 : crs_regsat_B (ms_regs ms0) (h3_regs C sp2)) by exact (x3_regsat_sub regs2 (ms_regs ms0) _ _ HRG2 (fun p Hp => Hp) KR).
  assert (HBm2 : crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly2 S2 Hp2 W2 (ms_regs ms0) (ms_mem ms0)
    (with_vm_backing (m_vm_lazy md2) mat0 md2) (k + k1) sp2).
  { rewrite HFm2. exact (x3_base_md (fx := fx) B ARx R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 (ms_regs ms0) _
      HB2 HJ2 KR3 KR4). }
  assert (HSTm2 : x3_st B C (crs_evs_at_H3_B C) ly2 S2 Hp2 W2 (ms_mem ms0) Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0)
    by (rewrite HFm2; exact HST2).
  apply (x3_acc_call (fx := fx) B ARx LAWS HK R Rr Rt Rw CTX0 C (crs_evs_at_H3_B C) fxk (STK_fuzz_pick (PI := prh_img_B)) 1072
    W2 _ _ ms0 _ ly2 S2 Hp2 (k + k1) sp2 Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 SIZE_MAXZ
    (fun ly' S' Hp' W' regs' mem' md' =>
       getr regs' 10 = w64 (ck_pick (cb_tb C) (cN0_B C)) /\ Hp' = Hp2 /\ S' = S2 /\ ablocks B ly' S' = ablocks B ly2 S2 /\
       (room_live_cf S2 -> room_live_cf S') /\
       LEDGER ly' S' Hp' W' mem' Lam peak (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0 /\
       PRH_Base.bytes_at (PA := PA) W' mem' (cb_data C) (cb_tb C))
    _ HS2 eq_refl HBm2).
  + rewrite (KR (2%bv, sp2)) by h3_in. exact G2.
  + rewrite (KR (8%bv, spZ (cb_regs C))) by h3_in. exact G8.
  + exact A1.
  + lia.
  + reflexivity.
  + rewrite EP0. lia.
  + rewrite EP0, ESTK. unfold CRS_FRAME_B. rewrite EFR. lia.
  + exact HSTm2.
  + intros ch1 HFPRE.
    unfold cSize_B in Hsz, Hd62.
    exact (HTP fxk ly2 S2 Hp2 W2 (ms_regs ms0) (ms_mem ms0) _ ch1 (cb_data C) (cb_tb C) (cN0_B C) Lam peak
      (crs_cnt2_B C + cN0_B C) SIZE_MAXZ 0 (cb_most C) 0 HFPRE A10 A11 A12 ltac:(lia) Hsz Hd0 Hd62
      ltac:(rewrite HFm2; exact HSRC) ltac:(rewrite HFm2; exact HL2)).
  + intros ly3 S3 Hp3 W3 regs3 mem3 md3 (_ & EHp & ES & EAB3 & _ & HL3 & _). exact (conj EHp (conj ES (conj EAB3 HL3))).
  + (* at the return (+1072 = X3_B): a0 = the pick *)
    intros ly3 S3 Hp3 W3 regs3 mem3 md3 k2 HB3 HP3 (R10' & _) HST3.
    pose proof HST3 as (HL3 & _ & _ & _ & _ & _ & HPM3 & HBY3 & HT3).
    change (BASE + (CRS_PC0_B + 1072)) with (BASE + CRS_PC_X3_B).
    refine (HX3 fxk ly3 S3 Hp3 W3 regs3 mem3 md3 (k + k1 + k2) sp2 Lam peak Hdoc HB3 _ _ HBY3 HT3).
    * pose proof (h3_regs_pres _ _ C sp2 HRGm2 HP3) as HR3'.
      unfold crs_regsat_B in *. rewrite Forall_forall in *. intros pp Hpp.
      cbv [crs_rbase_B crs_rsh_B crs_rlive_B crs_rro_B app In] in Hpp.
      repeat (destruct Hpp as [<- | Hpp];
        [first [exact R10' | apply HR3'; cbv [h3_regs crs_rbase_B crs_rsh_B crs_rargs_B crs_rlive_B crs_rro_B app In]; tauto] |]).
      destruct Hpp.
    * exact (x3_core_of_st (fx := fx) B ARx CTX0 C (crs_evs_at_H3_B C) ly3 S3 Hp3 W3 mem3 Lam peak (crs_cnt2_B C + cN0_B C) 0
        Hpre HST3 Hc62).
Qed.

End f.
End d.

Print Assumptions crs_seg_H3_B.
