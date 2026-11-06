(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 368 of its 420 lines of code are new or changed and 1280 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write at check_socket's return (+0x10a0):
     +0x10a0  beqz s5 -> +0x10d8 (no name)
     +0x10a4  the name's first byte, behind its instrumented check (the byte is a shadow-checked image byte);
              beqz -> +0x10d8 (the empty name)
     +0x10bc  mv a0, s6; jal wrapper_strlen (0x83894): RtString.astrlen_realizes, the Section hypothesis ASTRLEN
              (cmd_strlen_closed, lib/A/Rt/RtClosed.v), lifted by LinkWalkStrS.v aj_gx_strlen_atS
              (link_ajkit.v aj_gx_strlen_at with the model relation kept); the cut at its return (+0x10c4, w_l_inv).
   w_sl : FROM POST (w_r_inv i) -> FROM POST (w_l_inv i) -> FROM POST (w_s_inv i).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c model_write_c index_of_c reac_link_alias_write_c nl_talk_c check_socket_c check_refused_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMdl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputNm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1C.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1D.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1E.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkStrS YC88.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the name's first byte at s5 (atom 21) as atom 32 *)
Definition w_nm_rg : YP09.region := YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition w_n_facts : facts :=
  mkFacts [(21%nat, mkAF 4096 (2 ^ 47 - 2) 0); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] [].
Definition w_n_ss : sstate := mkSS LW_sret sr_atoms [w_nm_rg] None w_n_facts.
Definition w_n_SH : list shent := [mkSHE 21 0 1].

Lemma w_beq_any : forall (E : env) n,
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (bv_unsigned (ew E n) =? 0).
Proof.
  intros E n. rewrite branch_eq_U, U_SOff, U_lit by lia. unfold zcanon, M64. rewrite Z.add_0_r.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite (Z.mod_small (bv_unsigned (ew E n))) by lia. reflexivity.
Qed.

(* presence growth as a mem_grows *)
Lemma w_grows_of_present : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' Hp x Hx. unfold mrestrict in Hx |- *. destruct (H x) eqn:Eh; [exact Hx|].
  destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
  assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Eh | exists b; exact Em]).
  destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Lemma w_val_mem1 : forall segs m a b, mbyte segs m a = Some b -> val_mem segs m a 1 (bv_unsigned b).
Proof.
  intros segs m a b Hb k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the run's environment after the instrumented check: the entry's, with havoc atoms above the image's *)
Ltac w_mk_el EL EL2 :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E2 _ _ |- _ =>
      lazymatch type of EL with forall n, _ -> ew _ n = ?R =>
        assert (EL2 : forall n, (n < A_TEXT)%nat -> ew E2 n = R)
          by (intros n Hn; repeat rewrite ew_ewset_other by (unfold A_TEXT in *; lia); exact (EL n Hn)) end
  | HS : st_ok _ ?E2 _ _ |- _ =>
      lazymatch type of EL with forall n, _ -> ew _ n = ?R =>
        assert (EL2 : forall n, (n < A_TEXT)%nat -> ew E2 n = R)
          by (intros n Hn; repeat rewrite ew_ewset_other by (unfold A_TEXT in *; lia); exact (EL n Hn)) end
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
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
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
(* wrapper_strlen, as proved (lib/A/Rt/RtClosed.v cmd_strlen_closed) *)
Hypothesis ASTRLEN : forall fy : YK11.FPState,
  @RtString.astrlen_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_strlen).

#[local] Abbreviation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Abbreviation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).
Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* a string of the walk's memory, as the runtime's string *)
Lemma w_astr_of_acstr : forall (W : world SEGS) mem p s,
  acstr_at SEGS (rdW W mem) p s -> astr_at SEGS W mem p s.
Proof.
  intros W mem p s ((_ & _ & Hb) & Hnz). split; [|exact Hnz].
  intros i Hi. pose proof (Hb i Hi) as Hm. unfold aview. rewrite Hm.
  destruct (nth_error (s ++ [zb 0]) i) as [b|] eqn:En;
    [|apply nth_error_None in En; rewrite length_app in *; cbn [length] in *; lia].
  rewrite (nth_error_nth _ _ _ En). reflexivity.
Qed.

(* the strlen wrapper's premises for the text_of answer at a call with sp = lf_sp1 cx *)
Lemma w_strlen_pre : forall ly S (W : world SEGS) mem mdl (regs : bvmap 5 word) s t,
  AR SEGS B ly S W mem mdl -> arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) mem) ->
  alloc_ceiling <= spZ regs - ESTACK ->
  dec_ans B ly S (rdW W mem) s t ->
  0 < s /\ astr_at SEGS W mem s t /\ aread_ok SEGS ESTACK W regs mem s (astr_len t + 1) /\
  atail_vis SEGS W mem (s + astr_len t) /\ rt_rom_view SEGS B W mem /\ Z.of_nat (length t) < 320.
Proof.
  intros ly S W mem mdl regs s t HAR HRO HK HD.
  destruct (dec_rt_ok B LAWS TB HSEGS ly S W mem mdl regs ESTACK s t HAR HRO HK HD) as (Tcs & Trt & Tlen & Tnz).
  destruct Trt as (T0 & T31 & Tam & Tra & Thv & Ttail & Tfr).
  split; [exact T0|]. split; [exact (w_astr_of_acstr W mem s t Tcs)|].
  split.
  { unfold aread_ok, astr_len. split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemEnd in Tam; lia|].
    split; [lia|]. split.
    - intros a Ha. split.
      + destruct Tcs as ((_ & _ & Hby) & _).
        pose proof (Hby (Z.to_nat (a - s)) ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
        rewrite Z2Nat.id in Hb by lia. replace (s + (a - s)) with a in Hb by lia.
        unfold aview. rewrite Hb. destruct (nth_error (t ++ [zb 0]) (Z.to_nat (a - s))) eqn:En; [discriminate|].
        apply nth_error_None in En. rewrite length_app in En. cbn [length] in En. lia.
      + unfold ascratch_stk. unfold apart_frame in Tfr. lia.
    - split; [apply (w_amem_sub _ _ _ Tam); lia|].
      split; [rewrite <- ard_aview; exact Tra | intros _; rewrite <- ard_aview; exact Thv]. }
  split; [intros a Ha; rewrite <- ard_aview; apply Ttail; unfold astr_len in Ha; lia|].
  split; [intros a Hrom Hno Herr; exact (HRO a (or_introl Hrom) Hno Herr) | exact Tlen].
Qed.

(* the cut after the strlen wrapper: its post's facts as a callee's, then Txa.v lf_leaf_after *)
Lemma w_strlen_cut : forall cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 (W3 : world SEGS) (ms3 : machine_state)
    md3 (fy : YK11.FPState) regs2 raw mem2 md2,
  BASEF cx -> ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ->
  JRN cx fp ly3 S3 W3 mem2 md2 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_sp1 cx - ESTACK <= a < lf_sp1 cx) ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem2 a) ->
  same_but_materialized md3 md2 ->
  ak_cut SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3
    (@mkst fy regs2 raw mem2 (seg_rom SEGS)) md2 /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) mem2) /\
  lf_call B cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem ms3) W3 mem2 (fun _ => False).
Proof.
  intros cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 fy regs2 raw mem2 md2 HB HC HJ2 Hfr0 Hpres
    Hsbm.
  set (ms2 := @mkst fy regs2 raw mem2 (seg_rom SEGS)).
  pose proof HC as (HJ3 & Hfr & _ & _ & _ & _ & Hjbk & _ & _).
  pose proof alloc_ceiling_value as (CV & _).
  assert (HES : ESTACK = 4096) by reflexivity.
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ3) as (Hs1 & Hs16 & Hlo & H47).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _).
  pose proof HJi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k HB HJ3 Hfr) as (HFa2 & _ & F4 & Fc & _).
  assert (AK : akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 mem2 (lf_sp1 cx - ESTACK) (lf_sp1 cx) (fun _ => False)).
  { split; [|split; [|split; [|split; [|split]]]].
    - intros a Ha Hw _. apply Hfr0; [lia | exact Hw].
    - intros b m i Hin Hi _. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & H4 & Hc & _).
      apply Hfr0; unfold LLVMF_STK in *; lia.
    - intros a Hi _ _ _. pose proof (pa_segs_low a Hi). apply Hfr0; unfold kLowMemEnd, LLVMF_STK in *; lia.
    - intros cid pos a Hin Ha _. rewrite Hfr in Hin. destruct Hin as [Hq | []]. injection Hq as <- <-.
      unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha. rewrite HFa2 in Ha.
      change (fs_frame_bytes LF_CID) with 1024 in Ha. change (1024 / 8) with 128 in Ha.
      unfold shadow_addr, SHADOW_OFF in Ha.
      pose proof (Z.div_pos (lf_F cx fp) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (lf_F cx fp) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
      apply Hfr0; unfold LLVMF_STK in *; lia.
    - intros a Ha Hw Hp. exact (Hpres a Hp).
    - intros a Ha. apply Hstkp. unfold LLVMF_STK in *. lia. }
  assert (ASK : ashadow_kept SEGS B ly3 S3 ly3 S3 W3 (ms_mem ms3) W3 mem2).
  { intros b m a Hin _ Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & H4 & Hc & _).
    unfold shadow_addr, SHADOW_OFF.
    pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound a 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
    apply Hfr0; unfold LLVMF_STK in *; lia. }
  assert (Fd : m_fds md2 = m_fds md3) by (rewrite (same_but_materialized_wvb _ _ Hsbm); apply lf_wvb_fds).
  assert (Fs : m_fs md2 = m_fs md3) by (rewrite (same_but_materialized_wvb _ _ Hsbm); apply lf_wvb_fs).
  pose proof Hjbk as (Hkev & _).
  destruct (lf_leaf_after SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS MT_LE
    cx fp md mk kbs mbs gbs T3 own ev mo wl lv k ly3 S3 W3 ms3 md3 ESTACK (fun _ => False) ly3 S3 W3 ms2 md2 k
    HB HJ3 HC ltac:(rewrite HES; unfold LLVMF_STK; lia) ltac:(intros a []) HJ2 Hkev eq_refl Fd Fs AK ASK
    (eq_sym (set_fs_self S3)) (Permutation_refl _)) as (HC2 & HRO2 & HCALL).
  split; [exact HC2|]. split; [exact HRO2 | exact HCALL].
Qed.

Lemma w_sl : forall POST i,
  FROM POST (w_r_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (w_l_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (w_s_inv SK B MT MS la_nul LF_MO_SET LF_MO_OP i).
Proof.
  intros POST i HLR HLL cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HSI.
  destruct HSI as (md & mk & P & N & s & s6v & own1 & o0 & nm & t & K0 & kbs & mbs & gbs & T3 & nb & Hi & Hsh & Hcore &
    Hreg & Hnm & Ho0 & HC & Hcur & Hob & Href & HD & HTX & HSL & Hnb & Hown & Hfresh & Hsr & _).
  assert (REPACK : forall Q : machine_state -> option (list byte) -> list byte -> Prop, Q ms3 nm t ->
    w_c SK B MT MS la_nul LF_MO_SET LF_MO_OP LW_sret Q i cx fy fp k2 ly3 S3 W3 ms3 md3).
  { intros Q HQ. exists md, mk, P, N, s, s6v, own1, o0, nm, t, K0, kbs, mbs, gbs, T3, nb.
    repeat (split; [assumption|]). exact HQ. }
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof (lv_text LV) as HBASE.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof alloc_ceiling_value as (CV & _).
  pose proof Hcore as (R2 & R8 & R9 & R3 & R4).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27 & R20 & R18 & R23 & RRNG).
  destruct (ar_sp1_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (Hs1 & Hs16 & Hlo & H47').
  pose proof HC as (_ & _ & _ & _ & _ & _ & HjbkC & _ & HdatC).
  pose proof HjbkC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO3 & _).
  pose proof (w_name_range s nm Hnm) as Rs.
  rewrite (lf_shape_eta fy LW_sret ms3 Hsh).
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  destruct nm as [x|].
  2:{ (* no name: s5 = 0 *)
    pose proof Hnm as [(Hs0 & Hn0) | [(k & Hk & Hs1' & Hn) | (j & Hj & Hs1' & Hn)]]; [|discriminate | discriminate].
    pose proof (d4_entry fy W3 (ms_regs ms3) (ms_mem ms3) LW_sret) as HS.
    assert (SHOK : sh_ok pa_segs (SLit 0) [] (Eimg (Ereg (ms_regs ms3) []))
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_sret)) (ms_mem ms3) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
    remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
    assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
      by (intros n Hn; rewrite HEdef; apply Eimg_low; exact Hn).
    clear HEdef.
    assert (E21 : ew E 21 = Z_to_bv 64 0)
      by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 21 21%bv eq_refl), R21, Hs0; reflexivity).
    psrr_branch_tok RUN BR HS SHOK (0, 0).
    - paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LW_r; [apply awr_ok_x_nil|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
      assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
      apply (HLR cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
      apply (w_c_move SK B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP
        LW_sret LW_r (fun _ nm' _ => nm' = None) (fun _ nm t => w_refused nm t) i cx fy fp k2 ly3 S3 W3 ms3 md3 msB mdB
        (REPACK _ eq_refl) HJ (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)
        (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) [] W_R3 HS EL W_R3_low ltac:(d4chk))
        (kagree_frame_nil _ _ _ HFrB) HGB Fd Fs).
      intros nm' t' ->. left. reflexivity.
    - exfalso. rewrite w_beq_any, E21 in Hc. discriminate. }
  (* a name x at s5 *)
  destruct (lf_name_core SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END TB HSEGS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 md mk kbs mbs gbs s x HB HJ HRO3 HdatC Hnm)
    as (Ncs & Nl & Ns0 & Nam & Nra & Nhv & Ntail & Ntop & Nimg).
  pose proof Ncs as ((_ & _ & Nby) & Nnz).
  pose proof (Nby 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as Hb0. rewrite Z.add_0_r in Hb0.
  destruct (nth_error (x ++ [zb 0]) 0) as [c0|] eqn:Ec0; [|apply nth_error_None in Ec0; rewrite length_app in Ec0;
    cbn [length] in Ec0; lia].
  set (b0 := bv_unsigned c0).
  pose proof (bv_unsigned_in_range _ c0) as Rb0. change (bv_modulus 8) with 256 in Rb0. fold b0 in Rb0.
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 b0])).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) [Z_to_bv 64 b0]) n)
    by (intros n Hn; unfold E; apply Eimg_low; exact Hn).
  assert (E21 : ew E 21 = Z_to_bv 64 s)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 21 21%bv eq_refl), R21; reflexivity).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 27 27%bv eq_refl), R27; reflexivity).
  assert (E32 : ew E 32 = Z_to_bv 64 b0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E w_n_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_sret)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold w_n_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, w_nm_rg.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (u_base E 21 s E21) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ s 0 1 (SOff 32 0) b0);
        [rewrite (lf_sv_off E 32 b0 0 E32) by lia; rewrite Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (w_val_mem1 _ _ _ _ Hb0).
    - apply pairwise_disjoint_of_extents. cbn. tauto.
    - split; [|split; [exact I | exact I]].
      cbn [w_n_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E21, E27, E32. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF.
      assert (Hs4096 : 4096 <= s /\ s <= 2 ^ 47 - 2).
      { destruct Hnm as [(_ & Hn) | [(k & Hk & -> & _) | (j & Hj & -> & _)]]; [discriminate | unfold LA_G_NAMES; lia|].
        rewrite w_odd_ptrs. do 6 (destruct j as [|j]; [cbn; lia|]). lia. }
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (RA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF s 1)
    by (rewrite <- ard_aview; apply (md_ra_sub _ s (Z.of_nat (length x) + 1)); [exact Nra | lia | lia]).
  assert (SHOK : sh_ok pa_segs (SOff 27 0) w_n_SH E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LW_sret)) (ms_mem ms3) (seg_rom SEGS))))).
  { unfold sh_ok, w_n_SH. constructor; [|constructor]. unfold shent_ok, app_apart.
    cbn [she_m she_lo she_hi ms_mem mkst].
    rewrite (U_atom E 21 s E21) by lia. rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
    split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
    intros a Ha. unfold YImgTop.IMG_TOP, SHADOW_OFF in *. lia. }
  (* +0x10a0 `beqz s5`: the runner decides it (atom 21 is at least 4096) *)
    paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1);
      [apply awr_ok_x_cons; [cbn [w_n_ss w_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                            | apply awr_ok_x_nil] |].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    assert (KA : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
    { intros a _. unfold mbyte. rewrite (HFrA (Z_to_bv 64 a)); [reflexivity|].
      intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [w_nm_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
    psrr_branch_tok RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
    + (* the name's first byte is 0: the empty name, to the refused block *)
      rewrite w_beq_any in Hc. repeat rewrite ew_ewset_other in Hc by lia. rewrite E32 in Hc. rewrite unsigned_lit_small in Hc by lia. apply Z.eqb_eq in Hc.
      assert (Hx0 : x = []).
      { destruct x as [|c x']; [reflexivity|]. exfalso. cbn [app nth_error] in Ec0. injection Ec0 as <-.
        apply Nnz. left. apply bv_eq. unfold b0 in Hc. rewrite Hc. reflexivity. }
      paj_run_to_tok RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) LW_r;
        [apply awr_ok_x_cons; [cbn [w_n_ss w_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                              | apply awr_ok_x_nil] |].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      assert (KB : kagree SEGS (fun _ => False) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msB))).
      { intros a _. unfold mbyte. rewrite (HFrB (Z_to_bv 64 a)); [reflexivity|].
        intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [w_nm_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdB := mdx) in * end.
      assert (Fd : m_fds mdB = m_fds md3) by (subst mdB; rewrite !lf_wvb_fds; reflexivity).
      assert (Fs : m_fs mdB = m_fs md3) by (subst mdB; rewrite !lf_wvb_fs; reflexivity).
      w_mk_el EL EL2.
      apply (HLR cx fy fp k2 ly3 S3 W3 msB mdB HB Hfx HJ Hfr).
      apply (w_c_move SK B MT XM_LIB XN_LIB MS la_nul LF_MO_SET LF_MO_OP
        LW_sret LW_r (fun _ nm' _ => nm' = Some x) (fun _ nm t => w_refused nm t) i cx fy fp k2 ly3 S3 W3 ms3 md3 msB mdB
        (REPACK _ eq_refl) HJ (lf_shape_of_st_ok fy W3 _ _ msB HS eq_refl)
        (d4_keep_run_pi fy W3 _ _ msB (ms_regs ms3) _ W_R3 HS EL2 W_R3_low ltac:(d4chk))
        (fun a H => eq_trans (KB a H) (KA a H)) (fun a H => HGB a (HGA a H)) Fd Fs).
      intros nm' t' ->. right; left. rewrite Hx0. reflexivity.
    + (* a nonempty name: `mv a0, s6; jal wrapper_strlen` *)
      rewrite w_beq_any in Hc. repeat rewrite ew_ewset_other in Hc by lia. rewrite E32 in Hc. rewrite unsigned_lit_small in Hc by lia. apply Z.eqb_neq in Hc.
      assert (Hx0 : x <> []).
      { intros ->. cbn [app nth_error] in Ec0. injection Ec0 as <-. apply Hc. unfold b0. reflexivity. }
      paj_run_tok RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1);
        [apply awr_ok_x_cons; [cbn [w_n_ss w_nm_rg ss_mem YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
                              | apply awr_ok_x_nil] |].
      rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
      assert (KC0 : kagree SEGS (fun _ => False) (rdW W3 (ms_mem msA)) (rdW W3 (ms_mem msC))).
      { intros a _. unfold mbyte. rewrite (HFrC (Z_to_bv 64 a)); [reflexivity|].
        intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [w_nm_rg YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
      assert (KC : kagree SEGS (fun _ => False) (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)))
        by exact (fun a H => eq_trans (KC0 a H) (KA a H)).
      lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdC := mdx) in * end.
      assert (FdC : m_fds mdC = m_fds md3) by (subst mdC; rewrite !lf_wvb_fds; reflexivity).
      assert (FsC : m_fs mdC = m_fs md3) by (subst mdC; rewrite !lf_wvb_fs; reflexivity).
      w_mk_el EL EL2.
      pose proof (d4_keep_run fy W3 _ _ msC (ms_regs ms3) _ W_R3 HS EL2 W_R3_low ltac:(d4chk)) as KR.
      pose proof (ak_cut_run SK B MT MS la_nul cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 ms3 msC md3 mdC HC HJ KC
        (fun a H => HGC a (HGA a H)) FdC FsC) as HCC.
      pose proof (lf_cur_keep (fun _ => False) cx W3 ms3 W3 msC P N KC (fun a _ H => H) Hcur) as HcurC.
      pose proof (d4_dec_run B ly3 S3 _ _ s6v t KC HD) as HDC.
      pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTX (fun c H => H) KC (fun _ _ _ _ H => H)) as HTXC.
      pose proof (d4_slot_run W3 (ms_mem ms3) (ms_mem msC) _ _ KC HSL) as HSLC.
      pmkst HS.
      prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
      first [ew_reg EL 22%nat (22%bv : bv 5) Q10 | ew_reg EL2 22%nat (22%bv : bv 5) Q10]. rewrite R22 in Q10. rewrite HBASE in Q1.
      pose proof HCC as (HJC & HfrC & _ & _ & _ & _ & HjbkC2 & _ & _).
      pose proof HjbkC2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HROC & _).
      pose proof HJC as (_ & _ & (memSC & HJiC & _) & _). pose proof HJiC as (HARC & _).
      kreg KR 2 (2%bv : bv 5) K2. kreg KR 3 (3%bv : bv 5) K3. kreg KR 4 (4%bv : bv 5) K4.
      destruct (ar_gp_tp SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx HB) as (Gp & Tp).
      assert (Rsp : spZ (ms_regs msC) = lf_sp1 cx).
      { unfold spZ. rewrite K2, R2. unfold w64. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
      assert (HES : ESTACK = 4096) by reflexivity.
      destruct (w_strlen_pre ly3 S3 W3 (ms_mem msC) mdC (ms_regs msC) s6v t HARC HROC
        ltac:(rewrite Rsp, HES; unfold LLVMF_STK in *; lia) HDC) as (T0 & Tastr & Trd & Ttail & Trom & Tlen).
      eapply SRr_bind.
      { apply (@aj_gx_strlen_atS fy rc SK SEGS B LAWS pa_segs_low _ (ASTRLEN fy) G_HARNESS 0 [] W3 (ms_regs msC)
          (ms_mem msC) LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
          (c_md cx) [(LF_CID, fp)] ly3 S3 mdC k2 s6v t (getr (ms_regs msC) 1) HGX HJC);
          [ rewrite Rsp; exact Hs16 | rewrite Rsp, HES; unfold LLVMF_STK in *; lia | rewrite Rsp; lia
          | rewrite K3, R3; exact Gp | rewrite K4, R4; exact Tp | reflexivity
          | rewrite Q1, <- HBASE; apply ret_ok_codeptr_v; [lia | reflexivity]
          | rewrite Q10; reflexivity | exact T0 | exact Tastr | exact Trd | exact Ttail | exact Trom ]. }
      intros W4 c4 Hle4 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hlen2 & Hfr2 & Hpres2 & Hsbm).
      destruct (w_strlen_cut cx fp md mk kbs mbs gbs T3 _ _ _ _ _ k2 ly3 S3 W3 msC mdC fy regs2 (getr (ms_regs msC) 1)
        mem2 md2 HB HCC HJ2 ltac:(rewrite <- Rsp; exact Hfr2) Hpres2 Hsbm) as (HC2 & HRO2 & HCALL2).
      set (ms2 := @mkst fy regs2 (getr (ms_regs msC) 1) mem2 (seg_rom SEGS)) in *.
      pose proof (lf_cur_callee B cx ESTACK ly3 S3 ly3 S3 W3 msC W3 ms2 _ P N HCALL2 (fun a _ H => H) HcurC) as Hcur2.
      pose proof (tx_ans_keep B own1 nb ly3 S3 ly3 S3 _ _ _ s6v t HTXC (fun c H => H)
        (lf_call_kagree B cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem msC) W3 mem2 _ HCALL2)
        (fun k a Hb Ha => lfx_blk B ly3 S3 ly3 S3 _ _ _ own1 k a Hb Ha (fun H => H))) as HTX2.
      assert (HSL2 : rdword (aview SEGS (w_H W3) mem2) (lf_sp1 cx + LS_T130) = Some own1).
      { apply (d4_slot_callee B cx ESTACK ly3 S3 ly3 S3 W3 (ms_mem msC) W3 mem2 _ _ own1 HCALL2);
          [unfold LS_T130; lia | unfold LS_T130, LLVMF_STK in *; lia | intros j Hj H; exact H | exact HSLC]. }
      pose proof (d4_keep_pres W_R3 _ _ W_R3_saved HP2) as KT.
      pose proof (d4_keep_trans W_R3 _ _ _ KR KT) as K2T.
      destruct (w_regs3_keep XM_LIB XN_LIB la_nul cx fp i s s6v o0 (Some x) t K0 ms3 ms2
        K2T Hcore Hreg) as (Hcore2 & Hreg2).
      apply (HLL cx fy fp k2 ly3 S3 W3 ms2 md2 HB Hfx ltac:(pose proof HC2 as (HJx & _); exact HJx)
        ltac:(pose proof HC2 as (_ & Hfx2 & _); exact Hfx2)).
      exists md, mk, P, N, s, s6v, own1, o0, (Some x), t, K0, kbs, mbs, gbs, T3, nb.
      split; [exact Hi|].
      split.
      { unfold lf_shape, ms2. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
        rewrite Q1, <- HBASE. unfold LW_lret, AF_LLVMFuzzerTestOneInput. repeat split; reflexivity. }
      split; [exact Hcore2|]. split; [exact Hreg2|]. split; [exact Hnm|]. split; [exact Ho0|].
      split; [exact HC2|]. split; [exact Hcur2|]. split; [exact Hob|]. split; [exact Href|].
      split; [exact (tx_ans_dec B own1 nb ly3 S3 _ s6v t HTX2)|].
      split; [exact HTX2|]. split; [exact HSL2|]. split; [exact Hnb|]. split; [exact Hown|].
      split; [exact Hfresh|]. split; [exact Hsr|].
      split; [exists x; split; [reflexivity | exact Hx0] | exact Hlen2].
Qed.

End a.
