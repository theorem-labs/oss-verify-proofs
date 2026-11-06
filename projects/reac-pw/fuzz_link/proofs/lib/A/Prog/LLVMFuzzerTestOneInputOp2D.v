(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 365 of its 418 lines of code are new or changed and 1279 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...), the op_mark arm:
   from model_read's return (+0xc04, Op2Cut.v o2_r_inv) through the test of its answer and the call of
   model_decide (0x838fc, model_decide_c.v `model_decide_acontract`, the Section hypothesis MDC) to its return o2_d_inv
   (+0x112c); the listing (internal path) (internal record, sha256 e84d6f0c6974):

     +0xc04  beqz a0 -> +0x1120        model_read answered 0
     +0xc08  mv s7, a0                 its code is the answer, -> +0xc0c (o2_u_inv)
     +0x1120 a0 := s2 (F + 0x160), a1 := s5 (F + 0x1a0), jal model_decide

   model_decide reads the kind and the alias model_read left in the two frame objects (its read set, `akb` by the
   frame clause) and the two literals (Dec.v dec_lit_rt).

   o2_dc : forall POST i, FROM POST (o2_u_inv i) -> FROM POST (o2_d_inv i) -> FROM POST (o2_r_inv i).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C LLVMFuzzerTestOneInputOp2R LLVMFuzzerTestOneInputDec
  LLVMFuzzerTestOneInputOp3Lib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition LO2_d : Z := AF_LLVMFuzzerTestOneInput + 0x112c.   (* 0x83900, model_decide's return *)
Definition o2d_r_ss : sstate := mkSS LO2_r sr_atoms [] None (mkFacts [] [] []).

(* the model's answer when model_read fails, and after model_decide *)
Lemma o2_MM_rfail : forall t kbs gbs, (0 < length t)%nat -> r_rc (o2_RR t kbs) <> 0 ->
  o2_MM (Some t) kbs gbs = Mres (r_rc (o2_RR t kbs)) (mk_names gbs) (r_reqs (o2_RR t kbs)) (r_state (o2_RR t kbs)).
Proof.
  intros t kbs gbs Hl Hr. unfold o2_MM, o2_mm. destruct (Nat.eqb_spec (length t) 0) as [E|_]; [lia|].
  fold (o2_RR t kbs). destruct (Z.eqb_spec (r_rc (o2_RR t kbs)) 0) as [E|_]; [contradiction | reflexivity].
Qed.

(* the texts a reader leaves fit in the cap (lib/Prog/Slot/LC0Lib.v c0_rkind_len, c0_ralias_len) *)
Lemma o2_rkind_len : forall tab nm kc ac reqs K, 0 <= kc ->
  Z.of_nat (length (r_kind (read_core tab nm kc ac reqs K))) <= Z.max 0 (kc - 1).
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core.
  destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|].
  destruct (index_of tab s =? 0); [cbn; lia|]. cbn [r_kind].
  destruct (Z.ltb_spec kc 1); [cbn; lia|]. unfold text_of_attr.
  destruct (a_kind (talk_attrs K)) as [pay|]; [pose proof (cut_text_len pay kc ltac:(lia)); lia | cbn; lia].
Qed.

Lemma o2_ralias_len : forall tab nm kc ac reqs K, 0 <= ac ->
  Z.of_nat (length (r_alias (read_core tab nm kc ac reqs K))) <= Z.max 0 (ac - 1).
Proof.
  intros tab nm kc ac reqs K Hk. unfold read_core.
  destruct nm as [s|]; [|cbn; lia].
  destruct (Nat.eqb (length s) 0); [cbn; lia|].
  destruct (index_of tab s =? 0); [cbn; lia|]. cbn [r_alias].
  destruct (Z.ltb_spec ac 1); [cbn; lia|]. unfold text_of_attr.
  destruct (a_alias (talk_attrs K)) as [pay|]; [pose proof (cut_text_len pay ac ltac:(lia)); lia | cbn; lia].
Qed.

Lemma o2_RR_lens : forall t kbs,
  Z.of_nat (length (r_kind (o2_RR t kbs))) < 32 /\ Z.of_nat (length (r_alias (o2_RR t kbs))) < 256.
Proof.
  intros t kbs. unfold o2_RR, read_model. cbv zeta. cbn [r_kind r_alias].
  pose proof (o2_rkind_len lf_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs) ltac:(cbv; discriminate)) as H1.
  pose proof (o2_ralias_len lf_tab (Some t) KIND_CAP ALIAS_MAX [] (nk_kstate kbs) ltac:(cbv; discriminate)) as H2.
  unfold KIND_CAP, ALIAS_MAX in *. cbn [Z.max Z.sub] in H1, H2. split; lia.
Qed.

(* a beqz on a register holding a small signed value *)
Lemma o2_beqz_s : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
  intros E n v H Hv. rewrite branch_eq_U, U_SOff, H, U_lit by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia.
  destruct (Z.eqb_spec v 0) as [-> | Hn]; [reflexivity|].
  apply Z.eqb_neq. destruct (Z_lt_le_dec v 0).
  - rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) by lia. lia.
  - rewrite Z.mod_small by lia. exact Hn.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MDC : forall fy : YK11.FPState, model_decide_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* +0x112c: model_decide has answered (a0) on model_read's kind and alias *)
Definition o2_d_inv (i : Z) (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists (md mk P N s : Z) (t kbs mbs gbs : list byte) (T3 : list (Z * Z)),
  lf_shape fy LO2_d ms3 /\ getr (ms_regs ms3) 20 = w64 s /\ w_name s (Some t) /\ (0 < length t)%nat /\
  getr (ms_regs ms3) 18 = w64 (lf_F cx fp + LO_B160) /\ getr (ms_regs ms3) 21 = w64 (lf_F cx fp + LO_B1A0) /\
  getr (ms_regs ms3) 22 = w64 md /\ getr (ms_regs ms3) 26 = w64 (lf_F cx fp + LO_WA) /\
  o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 /\
  marks_are gbs mbs /\ r_rc (o2_RR t kbs) = 0 /\
  md_reqs mbs = r_reqs (o2_RR t kbs) /\ md_kstate mbs kbs = r_state (o2_RR t kbs) /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B160) (r_kind (o2_RR t kbs)) /\
  acstr_at SEGS (rdW W3 (ms_mem ms3)) (lf_F cx fp + LO_B1A0) (r_alias (o2_RR t kbs)) /\
  getr (ms_regs ms3) 10 = w64 (decide (Some (r_kind (o2_RR t kbs))) (Some (r_alias (o2_RR t kbs)))).

(* the cut's pieces across a stretch whose changed bytes X miss every footprint (Op3C.v u_mem_carry) *)
Lemma o2_mem2_carry : forall (X : Z -> Prop) i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 (W3 : world SEGS) ms3 md3
    ms' md',
  o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 W3 ms3 md3 ->
  length sh = 112%nat ->
  kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) ->
  (forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> ~ X a) ->
  mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms')) -> m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  getr (ms_regs ms') 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms') 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms3) 4 -> getr (ms_regs ms') 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms') 19 = getr (ms_regs ms3) 19 ->
  getr (ms_regs ms') 24 = getr (ms_regs ms3) 24 -> getr (ms_regs ms') 25 = getr (ms_regs ms3) 25 ->
  getr (ms_regs ms') 27 = getr (ms_regs ms3) 27 ->
  o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 W3 ms' md'.
Proof.
  intros X i md mk P N kbs mbs gbs T3 sh cx fp k2 ly3 S3 W3 ms3 md3 ms' md' HU Hl KB NX GB Fd Fs
    Q2 Q3 Q4 Q8 Q9 Q19 Q24 Q25 Q27.
  destruct HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop & Hns).
  split; [exact Hi|]. split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
  split; [unfold o2_kregs in *; rewrite Q19, Q24, Q25, Q27; exact Hreg|].
  split; [exact (lf_saved_keep X cx W3 ms3 W3 ms' KB (fun a Ha => NX a ltac:(tauto)) Hsv)|].
  split; [exact (lf_header_keep X cx fp W3 ms3 W3 ms' KB (fun a Ha => NX a ltac:(tauto)) Hhd)|].
  split; [apply (lf_fshadow_keep X cx fp W3 ms3 W3 ms' sh KB); [|exact Hfs]; rewrite Hl;
    intros a Ha; exact (NX a ltac:(tauto))|].
  split; [exact (lf_slots_keep X cx md mk fp W3 ms3 W3 ms' KB (fun a Ha => NX a ltac:(tauto)) Hsl)|].
  split; [exact (lf_cur_keep X cx W3 ms3 W3 ms' P N KB (fun a Ha => NX a ltac:(tauto)) Hcur)|].
  split; [exact (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 ms' md' KB Fd Fs
    (fun a Ha => NX a ltac:(tauto)) Hjbk)|].
  split; [exact (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KB (fun a Ha => NX a ltac:(tauto)) Hblk)|].
  split; [exact (lf_data_nm_keep X _ _ cx md mk kbs mbs gbs KB (wcarry_on_grows _ _ _ GB)
    (fun a Ha => NX a ltac:(tauto)) Hdat)|].
  split; [exact Hop | exact Hns].
Qed.

(* a string in one of the two frame objects, as the string wrappers ask of it inside a callee of window K *)
Lemma o2d_buf_rt : forall cx fp (W : world SEGS) ms (regs : bvmap 5 word) K o n s,
  lf_fshadow cx fp W ms SH_M -> lf_F cx fp mod 32 = 0 -> 4096 <= lf_F cx fp ->
  lf_F cx fp + 1024 <= alloc_ceiling ->
  (forall a, lf_F cx fp <= a < lf_F cx fp + 1024 -> apresent (w_H W) (ms_mem ms) a) ->
  in_app (lf_F cx fp) 1024 ->
  ((o = LO_B160 /\ n = 32) \/ (o = LO_B1A0 /\ n = 256)) ->
  acstr_at SEGS (rdW W (ms_mem ms)) (lf_F cx fp + o) s -> Z.of_nat (length s) < n ->
  lf_F cx fp + o + n <= spZ regs - K ->
  astr_rt_ok SEGS regs K (rdW W (ms_mem ms)) (lf_F cx fp + o) s.
Proof.
  intros cx fp W ms regs K o n s Hfs F32 F4 Fc Fpres Fapp Ho Hac Hl Hsp.
  destruct (o2r_buf_shadow cx fp W ms o n Hfs F32 F4 Fc Ho) as (BRA & BHV).
  assert (Hon : 352 <= o /\ o + n <= 672) by (destruct Ho as [(-> & ->) | (-> & ->)]; unfold LO_B160, LO_B1A0; lia).
  pose proof alloc_ceiling_lt as CL.
  split; [lia|]. split; [lia|].
  split; [unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
  split; [apply (md_ra_sub _ (lf_F cx fp + o) n); [exact BRA | lia | lia]|].
  split; [apply (md_hull_sub _ (lf_F cx fp + o) n); [exact BHV | lia | lia | lia]|].
  split.
  - intros b Hb. rewrite ard_aview. apply dec_aview_present. apply Fpres.
    pose proof (Z.mod_pos_bound (lf_F cx fp + o + Z.of_nat (length s)) 8 ltac:(lia)). lia.
  - unfold apart_frame. left. lia.
Qed.

(* model_decide's read set: bytes of the two frame objects, frame bytes of the call *)
Lemma o2d_ard : forall cx fp ly S (W : world SEGS) mem (regs : bvmap 5 word) slo shi a,
  In (LF_CID, fp) (frames S) -> frame_addr ly LF_CID fp = lf_F cx fp ->
  aarg regs 0 = lf_F cx fp + LO_B160 -> aarg regs 1 = lf_F cx fp + LO_B1A0 ->
  (forall s, acstr_at SEGS (rdW W mem) (lf_F cx fp + LO_B160) s -> Z.of_nat (length s) < 32) ->
  (forall s, acstr_at SEGS (rdW W mem) (lf_F cx fp + LO_B1A0) s -> Z.of_nat (length s) < 256) ->
  decide_ard SEGS regs (rdW W mem) a -> akb SEGS B ly S slo shi a.
Proof.
  intros cx fp ly S W mem regs slo shi a Hin Hfa R0 R1 L0 L1 Ha.
  right; right; right. exists LF_CID, fp. split; [exact Hin|]. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite Hfa. change (fs_frame_bytes LF_CID) with 1024.
  destruct Ha as [(Hnz & s & Hs & Ha) | (Hnz & s & Hs & Ha)].
  - rewrite R0 in Hs, Ha. pose proof (L0 s Hs). unfold LO_B160 in *. lia.
  - rewrite R1 in Hs, Ha. pose proof (L1 s Hs). unfold LO_B1A0 in *. lia.
Qed.

Lemma o2_dc : forall POST i,
  FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) -> FROM POST (o2_d_inv i) ->
  FROM POST (o2_r_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HU HD cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HR.
  destruct HR as (md & mk & P & N & s & t & kbs & mbs & gbs & T3 & Hsh & R20 & Hw & Hlt & R18 & R21 & R22 & R26 & HM
    & Hare & R10 & Hrq & Hks & Hkd & Hal & Hkb & Hab).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HM as (Hi & Hcore & Hkr & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdatn & Hop & Hns).
  pose proof Hkr as (R19 & R24 & R25 & R27).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  set (RR := o2_RR t kbs) in *.
  assert (RRr : - 2 ^ 32 < r_rc RR < 2 ^ 32).
  { pose proof Hdatn as (_ & Hnwf & _). unfold RR, o2_RR, read_model. cbn [r_rc]. apply u_norm_rc_range.
    apply u_read_rc_range; unfold nk_kstate; cbn [k_sock k_send k_end]; unfold nlk_wf in Hnwf; lia. }
  set (E := Eimg (Ereg (ms_regs ms3) [])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E10 : ew E 10 = Z_to_bv 64 (r_rc RR)) by (rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl); exact R10).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E o2d_r_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_r)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold o2d_r_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  rewrite (lf_shape_eta fy LO2_r ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LO2_r)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  assert (HA : env_agree 32 (Ereg (ms_regs ms3) []) E) by exact (lf_env_agree0 (ms_regs ms3)).
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0xc04 taken: model_read answered 0; model_decide *)
    rewrite (o2_beqz_s E 10 _ E10 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    paj_run_tok RUN HS HJ SHOK (0, 0); [apply awr_ok_x_nil|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    pose proof (kagree_frame_nil _ _ _ HFrA) as KA.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
    assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok _ ?Ex ?ssx _ => set (ssA := ssx) in HS end.
    pmkst HS.
    assert (Hpc : ss_pc ssA = pa_sigma LS_model_decide) by reflexivity.
    rewrite Hpc. replace (pa_sigma LS_model_decide) with MODEL_DECIDE_A by (rewrite (lv_sigma LV); reflexivity).
    prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
    prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    try rewrite (img_env_codeptr E HEI) in Q1.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q10.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q11.
    rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl) in Q18. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl) in Q20. rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21.
    rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22. rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24.
    rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25. rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26.
    rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (HMA : o2_mem2 B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 msA md4)
      by exact (o2_mem2_carry (fun _ => False) i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msA md4 HM
        SH_M_len KA (fun a _ H => H) HGA Fd Fs Q2 Q3 Q4 Q8 Q9 Q19 Q24 Q25 Q27).
    pose proof HMA as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatnA & _).
    pose proof (lf_data_of_nm _ _ _ _ _ _ _ HdatnA Hare) as HdatA.
    pose proof HjbkA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROA & _).
    destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
      cx fp ly3 S3 W3 (ms_mem msA) md4 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
    destruct (o5_geo SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB)
      as (Hal0 & Hceil0 & H470 & Hsp1r & Hsp132 & Hsp146).
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    pose proof alloc_ceiling_lt as CL.
    assert (Rsp : spZ (ms_regs msA) = lf_sp1 cx).
    { unfold spZ. rewrite Q2, R2. unfold w64. apply unsigned_lit_small. clear - Hsp146 Hsp1r H470. lia. }
    set (F := lf_F cx fp) in *.
    assert (Ra0 : aarg (ms_regs msA) 0 = F + LO_B160)
      by (rewrite ar_aarg0, Q10, R18; unfold w64; apply unsigned_lit_small; unfold LO_B160; clear - F4 Fc CL; lia).
    assert (Ra1 : aarg (ms_regs msA) 1 = F + LO_B1A0)
      by (rewrite ar_aarg1, Q11, R21; unfold w64; apply unsigned_lit_small; unfold LO_B1A0; clear - F4 Fc CL; lia).
    pose proof HJ as (_ & _ & (memSA & HJiA & _) & _). pose proof HJiA as (HARA & _).
    assert (HKd : alloc_ceiling <= spZ (ms_regs msA) - DECIDE_AK)
      by (rewrite Rsp, DECIDE_AK_val; clear - Hsp1r Hceil0; unfold LLVMF_STK in *; lia).
    destruct (o2_RR_lens t kbs) as (Lkd & Lal). fold RR in Lkd, Lal.
    assert (HkdA : acstr_at SEGS (rdW W3 (ms_mem msA)) (F + LO_B160) (r_kind RR))
      by exact (acstr_keep SEGS (fun _ => False) _ _ _ _ KA (fun _ _ H => H) Hkd).
    assert (HalA : acstr_at SEGS (rdW W3 (ms_mem msA)) (F + LO_B1A0) (r_alias RR))
      by exact (acstr_keep SEGS (fun _ => False) _ _ _ _ KA (fun _ _ H => H) Hal).
    assert (Hspd : F + LO_B1A0 + 256 <= spZ (ms_regs msA) - DECIDE_AK)
      by (rewrite Rsp, DECIDE_AK_val; unfold LO_B1A0, LLVMF_STK in *; clia).
    assert (RTk : astr_rt_ok SEGS (ms_regs msA) DECIDE_AK (rdW W3 (ms_mem msA)) (F + LO_B160) (r_kind RR))
      by (apply (o2d_buf_rt cx fp W3 msA (ms_regs msA) DECIDE_AK LO_B160 32 (r_kind RR) HfsA F32 F4 Fc
            (fun a Ha => proj1 (Fpres a Ha)) Fapp ltac:(left; split; reflexivity) HkdA Lkd);
          unfold LO_B160, LO_B1A0 in *; clia).
    assert (RTa : astr_rt_ok SEGS (ms_regs msA) DECIDE_AK (rdW W3 (ms_mem msA)) (F + LO_B1A0) (r_alias RR))
      by (apply (o2d_buf_rt cx fp W3 msA (ms_regs msA) DECIDE_AK LO_B1A0 256 (r_alias RR) HfsA F32 F4 Fc
            (fun a Ha => proj1 (Fpres a Ha)) Fapp ltac:(right; split; reflexivity) HalA Lal); clia).
    pose proof (lv_text LV) as HBASE.
    change (mkCfg (mkst (ms_regs msA) (Z_to_bv 64 MODEL_DECIDE_A) (ms_mem msA) (seg_rom SEGS)) md4)
      with (cfg_at (fx := fy) SEGS MODEL_DECIDE_A (ms_regs msA) (ms_mem msA) md4).
    assert (Hnz0 : F + LO_B160 <> 0) by (unfold LO_B160; clear - F4; lia).
    assert (Hnz1 : F + LO_B1A0 <> 0) by (unfold LO_B1A0; clear - F4; lia).
    apply (ar_leaf_call SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END fy MODEL_DECIDE_A
      DECIDE_AK 0 [] (decide_apre SEGS LA_MD_PREFIX LA_MD_VLAN) (decide_ard SEGS) decide_awr (decide_apost SEGS)
      (MDC fy) cx fp ly3 S3 W3 (ms_mem msA) md4 _ (ms_regs msA) (POST cx) HB HJ HROA);
      [ rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]
      | unfold raZ; rewrite Q1, HBASE; rewrite unsigned_lit_small by (unfold link_text; lia); unfold link_text; lia
      | rewrite Q3, R3; exact (proj1 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB))
      | rewrite Q4, R4; exact (proj2 (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB))
      | exact Rsp
      | pose proof DECIDE_AK_val; unfold LLVMF_STK; lia
      | lia
      | pose proof HjbkA as (Jk & _); pose proof lf_ev_bound as EB; clear - Jk EB Hi;
        unfold lf_ev, LF_EV_SET, LF_EV_OP, EV_LIB in *; lia
      | apply Forall_nil
      | intros a (r & [] & _)
      | intros a (r & [] & _)
      | intros a Ha; exact (o2d_ard cx fp ly3 S3 W3 (ms_mem msA) (ms_regs msA) _ _ a
          ltac:(rewrite Hfr; left; reflexivity) HFa Ra0 Ra1
          (fun s0 Hs0 => ltac:(rewrite (kp_acstr_unique _ _ _ _ _ Hs0 HkdA); exact Lkd))
          (fun s0 Hs0 => ltac:(rewrite (kp_acstr_unique _ _ _ _ _ Hs0 HalA); exact Lal)) Ha)
      | 
      | ].
    + (* the Pre *)
      destruct (dec_lit_rt B TB HSEGS ly3 S3 W3 (ms_mem msA) md4 (ms_regs msA) HARA HROA HKd)
        as ((P1 & Q1') & (P2 & Q2') & _).
      exists (Some (r_kind RR)), (Some (r_alias RR)). rewrite Ra0, Ra1.
      split; [split; [exact Hnz0 | exact HkdA]|]. split; [split; [exact Hnz1 | exact HalA]|].
      split; [exact P1|]. split; [exact Q1'|]. split; [exact P2|]. split; [exact Q2'|].
      split; [intros t0 E0; injection E0 as <-; exact RTk | intros t0 E0; injection E0 as <-; exact RTa].
    + (* model_decide's return, +0x112c *)
      intros W2 ly2 S2 regs2 mem2 md2 Hle HJ2 Hpr Hfr2 Hfd2 Hfs2 Hkp Hsk Hs2 Hperm Hpost.
      rewrite Z.add_0_r in HJ2.
      set (ms2 := @mkst fy regs2 (getr (ms_regs msA) 1) mem2 (seg_rom SEGS)).
      change mem2 with (ms_mem ms2) in HJ2, Hkp, Hsk, Hpost.
      set (Er := fun a => inFP (decide_awr (ms_regs msA) (rdW W3 (ms_mem msA))) a) in *.
      assert (LC : lf_call B cx DECIDE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er).
      { split; [rewrite DECIDE_AK_val; lia|]. split; [rewrite <- Rsp; exact HKd|]. split; [exact Hkp | exact Hsk]. }
      assert (NEr : forall a, ~ Er a) by (intros a (r & [] & _)).
      assert (HE : forall a, Er a -> (md <= a < md + MD_SIZE) \/ (lf_F cx fp + 24 <= a < lf_F cx fp + 1016))
        by (intros a Ha; exfalso; exact (NEr a Ha)).
      pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _).
      pose proof HblkA as (Bmd & Bmk & _).
      assert (Pmd : In (md, MD_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmd).
      assert (Pmk : In (mk, MK_SIZE) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Bmk).
      pose proof (ak_wcarry_callee B LAWS HSEGS ly2 S2 W2 (ms_mem ms2) md2 (rdW W3 (ms_mem msA)) md mk HAR2 Pmd Pmk)
        as WC.
      destruct (lf_img_facts B MS la_nul HSEGS TB HMS HLN) as (HIMG & _).
      pose proof (lf_call_kagree B cx DECIDE_AK ly3 S3 ly2 S2 W3 (ms_mem msA) W2 (ms_mem ms2) Er LC) as KX.
      pose proof HdatA as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & _).
      assert (Hmd2 : amodel_at SEGS (rdW W2 (ms_mem ms2)) md mbs).
      { apply (amodel_keep SEGS _ _ _ md mbs KX); [| |exact Dmd].
        - apply (wcarry_on_sub _ _ (lf_data_fp_w md mk) md MD_SIZE WC). intros i0 Hi0. unfold lf_data_fp_w.
          right; right; right; left. lia.
        - intros i0 Hi0. apply (lfx_data B MS la_nul cx DECIDE_AK ly3 S3 ly2 S2 Er md mk (md + i0) HIMG Bmd Bmk);
            [right; right; right; left; lia | apply NEr]. }
      destruct (lf_model_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
        cx fp DECIDE_AK ly3 S3 ly2 S2 W3 msA md4 W2 ms2 md2 Er k2 _ _ _ _ md mk kbs mbs gbs mbs T3 _ P N SH_M
        HB HJ Hfr LC HE Hfd2 Hfs2 Pmd Pmk WC ltac:(rewrite SH_M_len; lia) HsvA HhdA HfsA HslA HcurA HjbkA HblkA HdatA
        Hmd2 Dmwf eq_refl eq_refl) as (Hsv2 & Hhd2 & Hfs2' & Hsl2 & Hcur2 & Hjbk2 & Hblk2 & Hdat2 & HRO2).
      pose proof (ar_jbk_leaf SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp k2 _ _ _ _
        ly3 S3 ly2 S2 W2 ms2 md2 T3 _ k2 HB HJ2 Hs2 Hperm Hjbk2) as Hjbk3.
      pose proof (ar_blocks_leaf B cx md mk T3 ly3 S3 ly2 S2 _ Hperm Hblk2) as Hblk3.
      pose proof (ar_pres _ _ Hpr) as (P2 & P3 & P4 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27).
      assert (Hfa3 : forall c q, frame_addr ly3 c q = frame_addr (c_ly cx) c q)
        by (intros c q; exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ))).
      assert (Hin3 : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
      assert (Hkd2 : acstr_at SEGS (rdW W2 (ms_mem ms2)) (F + LO_B160) (r_kind RR)).
      { apply (acstr_keep SEGS _ _ _ _ _ KX); [|exact HkdA]. intros i0 Hi0.
        apply (lfx_side B cx fp DECIDE_AK ly3 S3 ly2 S2 Er _ Hin3 Hfa3); [|apply NEr].
        left. fold F. unfold LO_B160 in *. clear - Hi0 Lkd. lia. }
      assert (Hal2 : acstr_at SEGS (rdW W2 (ms_mem ms2)) (F + LO_B1A0) (r_alias RR)).
      { apply (acstr_keep SEGS _ _ _ _ _ KX); [|exact HalA]. intros i0 Hi0.
        apply (lfx_side B cx fp DECIDE_AK ly3 S3 ly2 S2 Er _ Hin3 Hfa3); [|apply NEr].
        left. fold F. unfold LO_B1A0 in *. clear - Hi0 Lal. lia. }
      pose proof (Hpost (Some (r_kind RR)) (Some (r_alias RR))
        ltac:(rewrite Ra0; split; [exact Hnz0 | exact HkdA]) ltac:(rewrite Ra1; split; [exact Hnz1 | exact HalA])) as HV.
      apply (HD cx fy fp k2 ly2 S2 W2 ms2 md2 HB Hfx HJ2 ltac:(rewrite Hfr2; exact Hfr)).
      exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
      split.
      { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        rewrite Q1. unfold LO2_d, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
      cbn [ms_regs ms2 mkst].
      split; [rewrite P20, Q20; exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
      split; [rewrite P18, Q18; exact R18|]. split; [rewrite P21, Q21; exact R21|].
      split; [rewrite P22, Q22; exact R22|]. split; [rewrite P26, Q26; exact R26|].
      split.
      { split; [exact Hi|]. split.
        { unfold lf_core in *. cbn [ms_regs ms2 mkst]. rewrite P2, P8, P9, P3, P4, Q2, Q8, Q9, Q3, Q4.
          rewrite R8, R9. repeat split; assumption. }
        split.
        { unfold o2_kregs in *. cbn [ms_regs ms2 mkst]. rewrite P19, P24, P25, P27, Q19, Q24, Q25, Q27.
          repeat split; assumption. }
        split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|]. split; [exact Hsl2|].
        split; [exact Hcur2|]. split; [exact Hjbk3|]. split; [exact Hblk3|].
        split; [exact (lf_data_nm_of _ _ _ _ _ _ _ Hdat2)|]. split; [exact Hop | exact Hns]. }
      split; [exact Hare|]. split; [exact Hc|]. split; [exact Hrq|]. split; [exact Hks|].
      split; [exact Hkd2|]. split; [exact Hal2 | exact HV].
  - (* +0xc04 not taken: model_read's code is the answer *)
    rewrite (o2_beqz_s E 10 _ E10 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LO2_u; [apply awr_ok_x_nil|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (kagree_frame_nil _ _ _ HFrB) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md3) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md3) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    assert (KR : forall r : bv 5, sr_get (ss_regs ssB) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs msB) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (lf_reg_atom fy W3 _ ssB msB _ r HS HA Hr)).
    prreg HS (23%bv : bv 5) Q23. rewrite (EL 10%nat 10%bv ltac:(lia) eq_refl) in Q23.
    apply (HU cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, s, t, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R20|]. split; [exact Hw|]. split; [exact Hlt|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R22|].
    split; [rewrite KR by (vm_compute; reflexivity); exact R26|].
    split.
    { apply (o2_mem2_carry (fun _ => False) i md mk P N kbs mbs gbs T3 SH_M cx fp k2 ly3 S3 W3 ms3 md3 msB md5 HM
        SH_M_len KB (fun a _ H => H) HGB Fd5 Fs5); rewrite KR by (vm_compute; reflexivity); reflexivity. }
    rewrite (o2_MM_rfail t kbs gbs Hlt Hc). fold RR. cbn [m_rc m_reqs m_marks].
    split; [rewrite Q23; exact R10|]. split; [exact Hrq|]. destruct Hare as (_ & Hm). symmetry; exact Hm.
Qed.

End a.
