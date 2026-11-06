(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 458 of its 506 lines of code are new or changed and 1284 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_mark's
   name selector (operation byte mod 6 = 2, entry +0x6a8) to its call of kernel(&cursor) at 0x832a4.
   Offsets from 0x827d4; listing (internal path)
   (internal record, sha256 e84d6f0c6974). The selector is the same instruction words as op_write's (Op1S.v, the
   regions and the tactics below are its pattern):

     +0x6ac  N - 1 = 0 (no byte left)        -> +0x98c: a0 := 0, the g_names path (+0xa44): s4 := g_names
     +0x6b0  byte b := [P + 1] (an instrumented 1-byte load), cursor := (P + 2, N - 2)
     +0x6dc  b = 0xff                          -> s4 := 0
     +0xa40  b <= 0x3f                         -> +0xa44: s4 := g_names + 8 b
             b >  0x3f                         -> +0xa90: a0 := LA_ODD + 8 (b mod 6) (mulhu by 0x2aaaaaaaaaaaaaab,
                                                  the constant at .rodata + 0xa0), an instrumented 8-byte load
                                                  s4 := odd[b mod 6]
     +0xacc  a0 := &cursor; jal kernel          (all paths)

   o2_sel : forall POST i, 0 <= i <= 47 -> FROM POST (o2_k_inv .. i) -> FROM POST (lf_arm_inv .. 2 i)
   (Op2K.v's cut after kernel, with the name in s4; the kernel application is Op2K.v o2_kcall).
   The error paths of the two instrumented checks are not reached: the payload byte and the odd table are
   addressable (the SH entries).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YFen YK0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputHead.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp2K.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* atoms: 32 = P + 1 (the byte's address), 33 = N - 1, 34 = the byte, 35 = LA_ODD *)
Definition o2_odd_rg : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_ODD (LS_ODD + 8) LS_ODD LS_ODD [YP09.mkChunk LS_ODD (CVal 8 (SOff 35 0))].
Definition o2_cur_rg (vP vN : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_P (LS_N + 8) LS_P (LS_N + 8) [YP09.mkChunk LS_P (CVal 8 vP); YP09.mkChunk LS_N (CVal 8 vN)].
Definition o2_byte_rg : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition o2_facts1 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 1 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 255 0);
           (35%nat, mkAF LA_ODD LA_ODD 0)] [] [].
Definition o2_facts0 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (33%nat, mkAF 0 0 0)] [] [].
Definition o2_ss0 : sstate := mkSS LF_op2 sr_atoms [o2_cur_rg (SOff 32 0) (SOff 33 0)] None o2_facts0.
Definition o2_ss1 : sstate := mkSS LF_op2 sr_atoms [o2_odd_rg; o2_cur_rg (SOff 32 0) (SOff 33 0); o2_byte_rg] None o2_facts1.
Definition o2_SH : list shent := [mkSHE 32 0 1; mkSHE 35 0 48].

Ltac o2_awr E9 S1u :=
  try cbn [ss_mem];
  repeat (apply awr_ok_x_cons;
    [unfold o2_odd_rg, o2_cur_rg, o2_byte_rg, w_c6_rg, w_odd_tab; cbn [r_base r_wlo r_whi base_val];
     repeat rewrite ew_ewset_other by lia;
     try rewrite E9, S1u; intros ?a ?Ha;
     first [lia | left; split; [left; unfold LS_P, LS_N, LLVMF_STK, LF_MFRAME in *; lia | lia]] |]);
  apply awr_ok_x_nil.

Ltac o2_inw E9 S1u :=
  let a := fresh "a" in let r := fresh "r" in let Hi := fresh "Hi" in let Hr := fresh "Hr" in
  intros a _ (r & Hi & Hr); cbn [ss_mem o2_ss1 o2_ss0] in Hi;
  repeat (destruct Hi as [<- | Hi];
    [unfold o2_odd_rg, o2_cur_rg, o2_byte_rg, w_c6_rg, w_odd_tab in Hr; cbn [r_base r_wlo r_whi base_val] in Hr;
     repeat rewrite ew_ewset_other in Hr by lia;
     rewrite ?E9, ?S1u in Hr; cbv beta; unfold LS_P, LS_N, LS_ODD in *; lia |]);
  destruct Hi.
Ltac o2_kag cx HFr E9 S1u KN :=
  let K0 := fresh "K0" in
  pose proof (lf_frame_kagree _ _ _ _ (fun a => lf_sp1 cx + LS_P <= a < lf_sp1 cx + LS_N + 8) HFr) as K0;
  lazymatch type of K0 with _ -> kagree ?s _ ?m1 ?m2 =>
    assert (KN : kagree s (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8) m1 m2)
      by (apply K0; o2_inw E9 S1u)
  end; clear K0.

(* the end of a selector path at the kernel call: CLOSE's premises from the run's final state *)
Ltac o2_fin CLOSE LV E E9 S1u s nm P' N' ix eP eN q' R20 Hnm KX GX :=
  lazymatch goal with
  | HS : st_ok _ ?EB (setpc ?ssB ?pcB) (restrict _ ?msX) |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ =>
    refine (CLOSE EB ssB pcB msX mdx s nm P' N' ix _ eP eN q' HS _ eq_refl _ _ _ _ _ _ R20 Hnm eq_refl eq_refl
      _ _ _ _ _ _ _ _ _ KX GX _ _ _);
    [ first [reflexivity | rewrite pa_sigma_kernel, (lv_text LV); reflexivity]
    | assumption
    | split; [intros ?n ?Hn; repeat rewrite ew_ewset_other by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
              rewrite !ew_Ereg_lt by lia; reflexivity | reflexivity]
    | let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr
    | vm_compute; reflexivity
    | vm_compute; reflexivity
    | repeat rewrite ew_ewset_other by lia; rewrite E9; exact S1u
    | cbn; repeat (first [left; reflexivity | right])
    | cbn; repeat (first [left; reflexivity | right])
    | cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
      lazymatch goal with HE : ew E 32 = _ |- _ => rewrite HE end; rewrite unsigned_lit_small by lia; f_equal; lia
    | cbn [sv_denot]; repeat rewrite ew_ewset_other by lia;
      lazymatch goal with HE : ew E 33 = _ |- _ => rewrite HE end; rewrite unsigned_lit_small by lia; f_equal; lia
    | lia | lia | lia | lia | lia
    | rewrite !lf_wvb_fds; reflexivity
    | rewrite !lf_wvb_fs; reflexivity
    | assumption ]
  end.

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
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* a register a run left as the atom of its entry value holds that value, at a call stop *)
Lemma o2_reg_at : forall (fy : YK11.FPState) (W : world SEGS) E ss pc ms regs0 (r : bv 5),
  st_ok (fx := fy) SEGS E (setpc ss pc) (restrict (w_H W) ms) -> env_agree 32 (Ereg regs0 []) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fy W E ss pc ms regs0 r HS HA Hr.
  rewrite (st_ok_restrict_reg SEGS (w_H W) E _ ms r HS). cbn [setpc ss_regs]. rewrite Hr.
  pose proof (bv_unsigned_in_range 5 r) as Rr. change (bv_modulus 5) with 32 in Rr.
  cbn [sv_denot]. destruct HA as [HA _]. rewrite (HA (Z.to_nat (bv_unsigned r))) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_nat. lia.
Qed.

(* a spill slot a run left, as the frame's slot *)
Lemma o2_slot : forall (E : env) (H : word -> bool) mem r base off e v,
  region_ok SEGS E (mrestrict H mem) r -> base_val E (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mem) (base + off) = Some v.
Proof.
  intros E H mem r base off e v (_ & _ & _ & HC) Hb Hin He Hv.
  rewrite Forall_forall in HC. specialize (HC _ Hin). rewrite Hb in HC.
  apply rdword_of_val_mem; [|exact Hv].
  exact (val_of_chunk_ok SEGS E _ base off 8 e v HC He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)).
Qed.

Lemma o2_sel : forall POST i, 0 <= i <= 47 ->
  FROM POST (o2_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP 2 i).
Proof.
  intros POST i Hi HK cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr GI.
  pose proof HJ as HJ0.
  destruct GI as (md & mk & P & N & kbs & mbs & gbs & T3 & b0 & _ & _ & Hsh & Hcore & Hlr & Hsv & Hhd & Hfs &
    Hsl & HN1 & Hb0 & Hbm & Hcur & Hq & Hjbk & Hblk & Hdat & Hop).
  pose proof HB as (_ & _ & HGX & _).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof Hcur as (HcP & HcN & _).
  destruct Hq as (q & Hq & EP & EN).
  pose proof Hsl as (_ & _ & _ & _ & _ & _ & _ & SODD & _).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & _ & Hshi & Hs47 & Hpres & HAR).
  pose proof (hd_sp1 cx) as (P1 & P2 & P3).
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcP) as RP.
  pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcN) as RN.
  pose proof asan_consts as ((C1a & C1b) & _).
  assert (S1r : alloc_ceiling <= lf_sp1 cx) by (unfold LLVMF_STK, LF_MFRAME in *; lia).
  assert (S1u : bv_unsigned (getr (ms_regs ms3) 9) = lf_sp1 cx).
  { rewrite C9. unfold w64. apply unsigned_lit_small. unfold LF_MFRAME in *. lia. }
  pose proof Hlr as (L19 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
  (* the kernel call, from any state the selector's runs end in (Op2K.v) *)
  assert (CALL : forall (msX : machine_state) mdX s nm P' N',
    ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msX) mdX k2 ->
    msX = @mkst fy (ms_regs msX) (Z_to_bv 64 KERNEL_A) (ms_mem msX) (seg_rom SEGS) ->
    (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
       getr (ms_regs msX) r = getr (ms_regs ms3) r) ->
    getr (ms_regs msX) 20 = w64 s -> w_name s nm ->
    getr (ms_regs msX) 1 = Z_to_bv 64 (BASE + (AF_LLVMFuzzerTestOneInput + 0xad4)) ->
    aarg (ms_regs msX) 0 = lf_sp1 cx + LS_P ->
    kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
      (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
    m_fds mdX = m_fds md3 -> m_fs mdX = m_fs md3 ->
    lf_cur cx W3 msX P' N' ->
    SRr SEGS W3 (mkCfg msX mdX) (POST cx)).
  { intros msX mdX s nm P' N' HJX HmX KRX HsX HnmX R1X A0X KX GX FdX FsX HcX.
    exact (o2_kcall SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LV LAWS TB HSEGS KERNEL
      POST i cx fy fp k2 ly3 S3 W3 ms3 md3 md mk kbs mbs gbs T3 msX mdX P' N' s nm
      Hi HK HB Hfx HJ0 Hfr Hcore Hlr Hsv Hhd Hfs Hsl Hjbk Hblk Hdat Hop HJX HmX KRX HsX HnmX R1X A0X KX GX FdX FsX HcX). }
  (* the call stop of a run: the runner's state gives every premise of CALL but the name, the memory relations
     and the cursor's values *)
  assert (CLOSE : forall E ss pc msX mdX s nm P' N' (ix : nat) r eP eN q',
    st_ok (fx := fy) SEGS E (setpc ss pc) (restrict (w_H W3) msX) -> pc = pa_sigma LS_kernel -> ss_resv ss = None ->
    img_env pa_val A_LIM E -> env_agree 32 (Ereg (ms_regs ms3) []) E ->
    (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
       sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) ->
    sr_get (ss_regs ss) 1%bv = SOff A_TEXT (AF_LLVMFuzzerTestOneInput + 0xad4) ->
    sr_get (ss_regs ss) 10%bv = SOff 9 LS_P -> bv_unsigned (ew E 9) = lf_sp1 cx ->
    sv_denot E (sr_get (ss_regs ss) 20%bv) = w64 s -> w_name s nm ->
    nth_error (ss_mem ss) ix = Some r -> YP09.r_base r = Some 9%nat ->
    In (YP09.mkChunk LS_P (CVal 8 eP)) (YP09.r_chunks r) -> In (YP09.mkChunk LS_N (CVal 8 eN)) (YP09.r_chunks r) ->
    sv_denot E eP = Z_to_bv 64 P' -> sv_denot E eN = Z_to_bv 64 N' -> 0 <= P' < 2 ^ 64 -> 0 <= N' < 2 ^ 64 ->
    0 <= q' <= c_n cx -> P' = c_p cx + q' -> N' = c_n cx - q' ->
    kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
      (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
    mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msX)) ->
    m_fds mdX = m_fds md3 -> m_fs mdX = m_fs md3 ->
    ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly3 S3 W3 (ms_mem msX) mdX k2 ->
    SRr SEGS W3 (mkCfg msX mdX) (POST cx)).
  { intros E ss pc msX mdX s nm P' N' ix r eP eN q' HS Hpc Hrv HEI HAE KRs R1s R10s E9s R20 Hnm Hix Hrb HinP HinN
      HvP HvN RP' RN' Hq' EP' EN' KX GX FdX FsX HJX.
    pose proof (st_ok_restrict_mkst SEGS (w_H W3) _ _ msX HS Hrv) as Hms. cbn [setpc ss_pc] in Hms.
    rewrite Hpc, pa_sigma_kernel, (lv_text LV) in Hms.
    replace (link_text + AF_kernel) with KERNEL_A in Hms by reflexivity.
    apply (CALL msX mdX s nm P' N' HJX Hms).
    - intros r0 Hr0. exact (o2_reg_at fy W3 E ss pc msX (ms_regs ms3) r0 HS HAE (KRs r0 Hr0)).
    - rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ msX 20%bv HS). cbn [setpc ss_regs]. exact R20.
    - exact Hnm.
    - rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ msX 1%bv HS). cbn [setpc ss_regs]. rewrite R1s.
      exact (codeptr_val E _ HEI).
    - rewrite ar_aarg0, (st_ok_restrict_reg SEGS (w_H W3) E _ msX 10%bv HS). cbn [setpc ss_regs]. rewrite R10s.
      cbn [sv_denot]. rewrite E9s. apply unsigned_lit_small. unfold LS_P, LF_MFRAME in *. lia.
    - exact KX.
    - exact GX.
    - exact FdX.
    - exact FsX.
    - pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _). cbn [setpc ss_mem ms_mem restrict] in Hrs.
      rewrite Forall_forall in Hrs. pose proof (Hrs r (nth_error_In _ _ Hix)) as Hr.
      assert (Bs9 : base_val E (YP09.r_base r) = lf_sp1 cx) by (rewrite Hrb; exact E9s).
      unfold lf_cur, lf_slot, lf_at. split; [|split].
      + exact (o2_slot E (w_H W3) (ms_mem msX) r (lf_sp1 cx) LS_P eP P' Hr Bs9 HinP HvP RP').
      + exact (o2_slot E (w_H W3) (ms_mem msX) r (lf_sp1 cx) LS_N eN N' Hr Bs9 HinN HvN RN').
      + exists q'. lia. }
  rewrite (lf_shape_eta fy (lf_op_pc 2) ms3 Hsh).
  change (lf_op_pc 2) with LF_op2.
  destruct (Z.eq_dec (N - 1) 0) as [HN0 | HN0].
  - (* N - 1 = 0: +0x98c, a0 := 0, the g_names path with s4 := g_names *)
    set (E := Eimg (Ereg (ms_regs ms3) [w64 (P + 1); w64 (N - 1)])).
    assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
    assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
    assert (E32 : ew E 32 = Z_to_bv 64 (P + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E33 : ew E 33 = Z_to_bv 64 (N - 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E o2_ss0
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op2)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor].
        unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks o2_cur_rg base_val]. rewrite E9, S1u.
        unfold LS_N, LS_P, LF_MFRAME in *.
        split; [lia|]. split; [lia|]. split.
        * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
        * constructor; [|constructor; [|constructor]].
          -- apply (hd_chunk cx W3 ms3 E LS_P (SOff 32 0) (P + 1) HcP).
             rewrite (lf_sv_off E 32 (P + 1) 0 E32) by lia. rewrite Z.add_0_r. reflexivity.
          -- apply (hd_chunk cx W3 ms3 E LS_N (SOff 33 0) (N - 1) HcN).
             rewrite (lf_sv_off E 33 (N - 1) 0 E33) by lia. rewrite Z.add_0_r. reflexivity.
      - apply pairwise_disjoint_of_extents. cbn -[E]. tauto.
      - split; [|split; exact I]. cbn [o2_facts0 f_atoms atoms_ok].
        split.
        { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9, S1u.
          split; [unfold LF_MFRAME in *; lia|]. split; [|lia].
          unfold lf_sp1, lf_sp1_of. rewrite Z.mul_comm. change (2 ^ 5) with 32. apply Z_mod_mult. }
        unfold afact_ok; cbn [af_lo af_hi af_al2].
        pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) HcP) as RP1.
        rewrite E32, E33, !unsigned_lit_small by lia.
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
        assert (Hin0 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
          by (apply (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp
                       ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ); lia).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin0) as (_ & Pb0 & Pbc & _).
        assert (Rn0 : req_size (c_n cx) = c_n cx)
          by (unfold req_size; destruct (c_n cx =? 0) eqn:En; [apply Z.eqb_eq in En; lia | reflexivity]).
        rewrite Rn0 in Pbc. pose proof alloc_ceiling_lt as CL.
        repeat split; try lia; try exact I. }
    pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
    pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
    assert (SHOK : sh_ok pa_segs hd_Bx [] E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op2)) (ms_mem ms3) (seg_rom SEGS)))))
      by (unfold sh_ok; apply Forall_nil).
    paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    psrr_branch_tok RUN BR HS SHOK hd_span.
    + paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      o2_kag cx HFrA E9 S1u KA. o2_kag cx HFrB E9 S1u KB.
      assert (KX : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
        (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by exact (hd_kt _ _ _ _ _ KA KB).
      assert (GX : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
      assert (Hnm : w_name (LA_G_NAMES + 8 * 0) (Some (lf_gname 0)))
        by (right; left; exists 0; split; [lia|]; split; reflexivity).
      lazymatch type of HS with st_ok _ ?EB (setpc ?ssB _) _ =>
        assert (R20 : sv_denot EB (sr_get (ss_regs ssB) 20%bv) = w64 (LA_G_NAMES + 8 * 0))
          by (replace (sr_get (ss_regs ssB) 20%bv) with (SOff 246 0) by (vm_compute; reflexivity);
              rewrite (lf_sv_off EB 246 LA_G_NAMES 0 (w_atom246 LV EB ltac:(assumption))) by (unfold LA_G_NAMES; lia);
              unfold w64; f_equal; lia)
      end.
      o2_fin CLOSE LV E E9 S1u (LA_G_NAMES + 8 * 0) (Some (lf_gname 0)) (P + 1) (N - 1) 0%nat (SOff 32 0) (SOff 33 0)
        (q + 1) R20 Hnm KX GX.
    + exfalso. rewrite (lf_sv_off E 33 (N - 1) 0 E33) in Hc by lia. rewrite HN0 in Hc.
      vm_compute in Hc. discriminate Hc.
  - assert (HN2 : 1 <= N - 1) by lia.
    pose proof Hjbk as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J13 & J14 & J15).
    destruct J14 as (Pl0 & Pl1 & Pl2).
    assert (Hqn : (Z.to_nat (q + 1) < length (c_pl cx))%nat) by (unfold c_n in *; lia).
    pose proof (Pl2 (Z.to_nat (q + 1)) Hqn) as Hb. rewrite Z2Nat.id in Hb by lia.
    replace (c_p cx + (q + 1)) with (P + 1) in Hb by lia.
    destruct (nth_error (c_pl cx) (Z.to_nat (q + 1))) as [bb|] eqn:Ebb; [|apply nth_error_None in Ebb; lia].
    pose proof (bv_unsigned_in_range _ bb) as Rb. change (bv_modulus 8) with 256 in Rb.
    assert (Hin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (apply (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp
                   ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ); lia).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Pb0 & Pbc & Pbapp & _).
    assert (Rn : req_size (c_n cx) = c_n cx)
      by (unfold req_size; destruct (c_n cx =? 0) eqn:En; [apply Z.eqb_eq in En; lia | reflexivity]).
    rewrite Rn in Pbc, Pbapp.
    set (E := Eimg (Ereg (ms_regs ms3) [w64 (P + 1); w64 (N - 1); Z_to_bv 64 (bv_unsigned bb); w64 LA_ODD])).
    assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
    assert (E9 : ew E 9 = getr (ms_regs ms3) 9) by (apply ew_Eimg_Ereg_nat; reflexivity).
    assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF)
      by (transitivity (getr (ms_regs ms3) 27); [apply ew_Eimg_Ereg_nat; reflexivity | exact L27]).
    assert (E32 : ew E 32 = Z_to_bv 64 (P + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E33 : ew E 33 = Z_to_bv 64 (N - 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E34 : ew E 34 = Z_to_bv 64 (bv_unsigned bb))
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (E35 : ew E 35 = Z_to_bv 64 LA_ODD) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
    assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E o2_ss1
      (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op2)) (ms_mem ms3) (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
      - apply regs_ok_Eimg_Ereg.
      - reflexivity.
      - constructor; [|constructor; [|constructor; [|constructor]]].
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks o2_odd_rg base_val]. rewrite E9, S1u.
          unfold LS_ODD, LF_MFRAME in *.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          constructor; [|constructor].
          apply (hd_chunk cx W3 ms3 E 0x50 (SOff 35 0) LA_ODD SODD).
          rewrite (lf_sv_off E 35 LA_ODD 0 E35) by (unfold LA_ODD; lia). rewrite Z.add_0_r. reflexivity.
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks o2_cur_rg base_val]. rewrite E9, S1u.
          unfold LS_N, LS_P, LF_MFRAME in *.
          split; [lia|]. split; [lia|]. split.
          * intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold LLVMF_STK. lia.
          * constructor; [|constructor; [|constructor]].
            -- apply (hd_chunk cx W3 ms3 E LS_P (SOff 32 0) (P + 1) HcP).
               rewrite (lf_sv_off E 32 (P + 1) 0 E32) by lia. rewrite Z.add_0_r. reflexivity.
            -- apply (hd_chunk cx W3 ms3 E LS_N (SOff 33 0) (N - 1) HcN).
               rewrite (lf_sv_off E 33 (N - 1) 0 E33) by lia. rewrite Z.add_0_r. reflexivity.
        + unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks o2_byte_rg base_val].
          rewrite E32, unsigned_lit_small by lia.
          split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
          constructor; [|constructor].
          apply (chunk_ok_val SEGS E _ (P + 1) 0 1 (SOff 34 0) (bv_unsigned bb)); [| cbn; lia | cbn; lia |].
          * rewrite (lf_sv_off E 34 (bv_unsigned bb) 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
          * rewrite Z.add_0_r. exact (hd_val_mem1 _ _ _ _ Hb).
      - apply pairwise_disjoint_of_extents. cbn -[E].
        repeat match goal with |- _ /\ _ => split end; try exact I;
        unfold zdisj, extent_of_region; cbn [r_base r_lo r_hi o2_odd_rg o2_cur_rg o2_byte_rg base_val fst snd];
        rewrite ?E9, ?S1u, ?E32; rewrite ?unsigned_lit_small by lia;
        unfold LS_ODD, LS_P, LS_N, LF_MFRAME in *; lia.
      - split; [|split; exact I]. cbn [o2_facts1 f_atoms atoms_ok].
        split.
        { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9, S1u.
          split; [unfold LF_MFRAME in *; lia|]. split; [|lia].
          unfold lf_sp1, lf_sp1_of. rewrite Z.mul_comm. change (2 ^ 5) with 32. apply Z_mod_mult. }
        unfold afact_ok; cbn [af_lo af_hi af_al2].
        rewrite E27, E32, E33, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF, LA_ODD; lia).
        change (2 ^ 0) with 1. rewrite !Z.mod_1_r. pose proof alloc_ceiling_lt as CL.
        unfold SHADOW_OFF, LA_ODD in *. repeat split; try lia; try exact I. }
    pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
    pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
    pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
    assert (RA : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (P + 1) 1)
      by (eapply range_addressable_of_block; [eassumption | eassumption | exact Hin | lia | rewrite Rn; lia]).
    assert (RO : range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF LA_ODD 48)
      by (rewrite <- ard_aview; exact (sel_odd_ra B TB HSEGS ly3 S3 _ (proj1 HAR))).
    assert (SHOK : sh_ok pa_segs hd_Bx o2_SH E
      (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_op2)) (ms_mem ms3) (seg_rom SEGS))))).
    { unfold sh_ok, o2_SH. constructor; [|constructor; [|constructor]]; unfold shent_ok, app_apart, hd_Bx;
        cbn [she_m she_lo she_hi ms_mem mkst].
      - rewrite (U_atom E 32 (P + 1) E32) by lia. rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
        split; [rewrite Z.add_0_r, Z.sub_0_r; exact RA|].
        intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
      - rewrite (U_atom E 35 LA_ODD E35) by (unfold LA_ODD; lia).
        rewrite (U_atom E 27 SHADOW_OFF E27) by (unfold SHADOW_OFF; lia).
        split; [rewrite Z.add_0_r, Z.sub_0_r; exact RO|].
        intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, LA_ODD in *. lia. }
    paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
    rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
    psrr_branch_tok RUN BR HS SHOK hd_span.
    + (* +0x6dc taken: b <> 0xff *)
      paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      rename Hc into Hc1.
      psrr_branch_tok RUN BR HS SHOK hd_span.
      * (* +0xa40 taken: 0x3f < b, odd[b mod 6] *)
        paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
        rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
        o2_kag cx HFrA E9 S1u KA. o2_kag cx HFrB E9 S1u KB. o2_kag cx HFrC E9 S1u KC.
        assert (KAC : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
                  (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC)))
          by exact (hd_kt _ _ _ _ _ (hd_kt _ _ _ _ _ KA KB) KC).
        assert (HROC : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) (ms_mem msC))).
        { rewrite <- ard_aview. apply (arodata_keep SEGS _ _ _ _ _ B KAC); [|rewrite ard_aview; exact J13].
          intros a Hr Hx. pose proof (in_roP_low a Hr) as L.
          rewrite Z.mod_small in Hx by (unfold kLowMemEnd in *; lia). unfold LS_P, LS_N, kLowMemEnd in *. lia. }
        lazymatch type of HS with st_ok_pi _ _ ?EC ?ssC _ =>
          lazymatch goal with HE : img_env _ _ EC |- _ =>
            pose proof (st_ok_pi_add_region EC ssC _ w_c6_rg HS eq_refl (w_c6_ok B TB HSEGS LV EC W3 (ms_mem msC) HE HROC)) as HS0
          end end.
        pose proof (blk_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) HAR Hin) as Hoff.
        rewrite Rn in Hoff. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff.
        lazymatch type of HS0 with ?d -> _ => assert (HD : d) end.
        { pose proof (w_atom346 LV E HEI) as E346.
          cbn [all_disjoint ss_mem]. repeat match goal with |- _ /\ _ => split end; try exact I;
          unfold extent_disjoint, zdisj, extent_of_region; cbn [r_base r_lo r_hi w_c6_rg base_val fst snd];
          repeat rewrite ew_ewset_other by (unfold A_OBJ; lia); rewrite ?E346, ?E9, ?S1u, ?E32;
          rewrite ?unsigned_lit_small by lia;
          unfold LS_ODD, LS_P, LS_N, LF_MFRAME, LLVMF_STK, kLowMemEnd in *;
          lia. }
        specialize (HS0 HD). clear HD HS. rename HS0 into HS1.
        paj_run_to_tok RUNTO HS1 HJ SHOK hd_span (AF_LLVMFuzzerTestOneInput + 0xab8); [o2_awr E9 S1u|].
        rename ms into msD, HF into HFD, HFr into HFrD, HG into HGD.
        o2_kag cx HFrD E9 S1u KD.
        assert (KAD : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
                  (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msD))) by exact (hd_kt _ _ _ _ _ KAC KD).
        assert (HROD : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) (ms_mem msD))).
        { rewrite <- ard_aview. apply (arodata_keep SEGS _ _ _ _ _ B KAD); [|rewrite ard_aview; exact J13].
          intros a Hr Hx. pose proof (in_roP_low a Hr) as L.
          rewrite Z.mod_small in Hx by (unfold kLowMemEnd in *; lia). unfold LS_P, LS_N, kLowMemEnd in *. lia. }
        destruct (w_k6 (bv_unsigned bb) Rb) as (k & Hk6 & Ek).
        lazymatch type of HS1 with st_ok_pi _ _ ?ED ?ssD _ =>
          assert (E34D : ew ED 34 = Z_to_bv 64 (bv_unsigned bb)) by (repeat rewrite ew_ewset_other by lia; exact E34);
          assert (E35D : ew ED 35 = Z_to_bv 64 LA_ODD) by (repeat rewrite ew_ewset_other by lia; exact E35);
          assert (A0 : getr (ms_regs msD) 10%bv = sv_denot ED (SOff 35 (8 * k)))
            by (rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W3) _ _ msD 10%bv HS1);
                replace (sr_get (ss_regs ssD) 10%bv) with w_a0 by (vm_compute; reflexivity);
                rewrite (w_a0_val ED (bv_unsigned bb) E34D E35D Rb), Ek;
                rewrite (lf_sv_off ED 35 LA_ODD (8 * k) E35D) by (cbn in Hk6; unfold LA_ODD; lia); reflexivity);
          pose proof (st_ok_pi_set_reg ED ssD _ 10%bv (SOff 35 (8 * k)) HS1
            ltac:(intros Habs; apply (f_equal (@bv_unsigned 5)) in Habs; discriminate Habs) A0) as HS2
        end.
        clear HS1.
        cbn [In] in Hk6. destruct Hk6 as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]].
        all: lazymatch type of HS2 with st_ok_pi _ _ ?ED ?ssD _ =>
          lazymatch goal with HE : img_env _ _ ED |- _ =>
            lazymatch type of A0 with _ = sv_denot _ (SOff 35 (8 * ?kk)) =>
              pose proof (st_ok_pi_add_region ED ssD _ (w_odd_tab kk) HS2 eq_refl
                (w_odd_tab_ok B TB HSEGS ED W3 (ms_mem msD) kk E35D HROD ltac:(lia))) as HS3
            end end end.
        all: lazymatch type of HS3 with ?d -> _ => assert (HD : d) end;
          [ pose proof (w_atom346 LV E HEI) as E346; pose proof E346 as E252; change (A_OBJ 11) with 252%nat in E252;
            cbn [all_disjoint ss_mem]; repeat match goal with |- _ /\ _ => split end; try exact I;
            unfold extent_disjoint, zdisj, extent_of_region; cbn [r_base r_lo r_hi w_c6_rg w_odd_tab base_val fst snd];
            repeat rewrite ew_ewset_other by (unfold A_OBJ; lia); rewrite ?E346, ?E252, ?E9, ?S1u, ?E32, ?E35;
            rewrite ?unsigned_lit_small by (unfold LA_ODD; lia);
            unfold LS_ODD, LS_P, LS_N, LF_MFRAME, LLVMF_STK, kLowMemEnd, LA_ODD in *;
            lia
          | specialize (HS3 HD); clear HD HS2 ].
        all: paj_run_tok RUN HS3 HJ SHOK hd_span; [o2_awr E9 S1u|].
        all: rename ms into msE, HF into HFE, HFr into HFrE, HG into HGE.
        all: o2_kag cx HFrE E9 S1u KE.
        all: assert (KX : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
          (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msE))) by exact (hd_kt _ _ _ _ _ KAD KE).
        all: assert (GX : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msE)))
          by (intros x Hx; apply HGE, HGD, HGC, HGB, HGA, Hx).
        all: lazymatch type of A0 with _ = sv_denot _ (SOff 35 (8 * ?kk)) =>
          assert (Hnm : w_name (nth (Z.to_nat kk) ODD_PTRS 0) (Some (nth (Z.to_nat kk) lf_odd_strs [])))
            by (right; right; exists (Z.to_nat kk); split; [cbn; lia | split; reflexivity])
          end.
        all: lazymatch type of HS3 with st_ok _ ?EB (setpc ?ssB _) _ =>
          lazymatch type of Hnm with w_name ?s ?nm =>
          assert (R20 : sv_denot EB (sr_get (ss_regs ssB) 20%bv) = w64 s)
            by (rewrite w_odd_ptrs; vm_compute; reflexivity);
          o2_fin CLOSE LV E E9 S1u s nm (P + 2) (N - 2) 3%nat (SOff 32 1) (SOff 33 (-1)) (q + 2) R20 Hnm KX GX
          end end.
      * (* +0xa40 not taken: b <= 0x3f, g_names + 8 b *)
        paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
        rename ms into msC, HF into HFC, HFr into HFrC, HG into HGC.
        o2_kag cx HFrA E9 S1u KA. o2_kag cx HFrB E9 S1u KB. o2_kag cx HFrC E9 S1u KC.
        assert (Hb63 : bv_unsigned bb <= 63).
        { lazymatch type of Hc with context [sv_denot ?EH (SOff 34 0)] =>
            rewrite (lf_sv_off EH 34 (bv_unsigned bb) 0 ltac:(repeat rewrite ew_ewset_other by lia; exact E34)
              ltac:(lia) ltac:(lia)) in Hc end.
          cbn [sv_denot] in Hc. rewrite YK0f.branch_ltu_lit_l, !unsigned_lit_small in Hc by lia.
          apply Z.ltb_ge in Hc. lia. }
        assert (KX : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
          (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC))) by exact (hd_kt _ _ _ _ _ (hd_kt _ _ _ _ _ KA KB) KC).
        assert (GX : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msC))) by (intros x Hx; apply HGC, HGB, HGA, Hx).
        assert (Hnm : w_name (LA_G_NAMES + 8 * bv_unsigned bb) (Some (lf_gname (bv_unsigned bb))))
          by (right; left; exists (bv_unsigned bb); split; [lia|]; split; reflexivity).
        lazymatch type of HS with st_ok _ ?EB (setpc ?ssB _) _ =>
          assert (R20 : sv_denot EB (sr_get (ss_regs ssB) 20%bv) = w64 (LA_G_NAMES + 8 * bv_unsigned bb))
            by (replace (sr_get (ss_regs ssB) 20%bv) with w_gn by (vm_compute; reflexivity);
                rewrite (w_gn_val EB (bv_unsigned bb) ltac:(repeat rewrite ew_ewset_other by lia; exact E34)
                  (w_atom246 LV EB ltac:(assumption)) Rb); reflexivity)
        end.
        o2_fin CLOSE LV E E9 S1u (LA_G_NAMES + 8 * bv_unsigned bb) (Some (lf_gname (bv_unsigned bb))) (P + 2) (N - 2)
          1%nat (SOff 32 1) (SOff 33 (-1)) (q + 2) R20 Hnm KX GX.
    + (* +0x6dc not taken: b = 0xff, s4 := 0 *)
      paj_run_tok RUN HS HJ SHOK hd_span; [o2_awr E9 S1u|].
      rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
      o2_kag cx HFrA E9 S1u KA. o2_kag cx HFrB E9 S1u KB.
      assert (KX : kagree SEGS (fun a => lf_sp1 cx + LS_P <= a mod 2 ^ 64 < lf_sp1 cx + LS_N + 8)
        (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by exact (hd_kt _ _ _ _ _ KA KB).
      assert (GX : mem_grows (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msB))) by (intros x Hx; apply HGB, HGA, Hx).
      assert (Hnm : w_name 0 None) by (left; split; reflexivity).
      lazymatch type of HS with st_ok _ ?EB (setpc ?ssB _) _ =>
        assert (R20 : sv_denot EB (sr_get (ss_regs ssB) 20%bv) = w64 0)
          by (replace (sr_get (ss_regs ssB) 20%bv) with (SLit 0) by (vm_compute; reflexivity); reflexivity)
      end.
      o2_fin CLOSE LV E E9 S1u 0 (@None (list byte)) (P + 2) (N - 2) 1%nat (SOff 32 1) (SOff 33 (-1)) (q + 2)
        R20 Hnm KX GX.
Qed.

End a.
